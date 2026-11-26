/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.X86TSO.Axiomatic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tests for the axiomatic x86-TSO model

* Owens, Sarkar and Sewell's example `tso1` (TPHOLs 2009, Section 3), in which processor 0 writes
  1 to `x` and then reads `x` into a register and processor 1 writes 2 to `x`, has the valid
  execution witness of Fig. 3, left (Section 3.2), in which the read sees processor 1's write: the
  validity conditions are satisfiable, with a register write and intra-instruction causality.
* Store buffering: with `x = y = 0` initially, processor 0 writes 1 to `x` and reads `y`, and
  processor 1 writes 1 to `y` and reads `x`. The execution in which both reads return 0 has a
  valid execution witness, in which both reads precede both writes in memory order.
* With an MFENCE between the write and the read on each processor, the same reads have no valid
  execution witness.
* Register reads: processor 0 writes 1 and then 2 to a register and then reads it. The read of 2
  has a valid execution witness, and the read of 1, a value that the second write overwrote
  earlier in program order, has none.
-/

@[expose] public section

namespace Cslib.Distributed.X86TSO.Tests

open EventStructure

/-! ### The example `tso1` -/

/-- The events of `tso1`: `a` writes 1 to `x`, `b` reads 2 from `x`, `c` writes 2 to register
`EAX` of processor 0, and `d` writes 2 to `x`. -/
inductive Tso1
  | a
  | b
  | c
  | d
  deriving DecidableEq

instance : Finite Tso1 :=
  Finite.of_surjective ![.a, .b, .c, .d] fun e => by
    cases e
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The event structure of `tso1`, with `x` the address 0 and `EAX` the register 0. The
instruction `MOV EAX←[x]` of processor 0 has the events `b` and `c`, and its intra-instruction
causality is a partial order with `b` before `c`. -/
def tso1 : EventStructure Tso1 ℕ ℕ ℕ ℕ where
  proc | .d => 1 | _ => 0
  poi | .b => 1 | .c => 1 | _ => 0
  action
    | .a => .write (.mem 0) 1
    | .b => .read (.mem 0) 2
    | .c => .write (.reg 0 0) 2
    | .d => .write (.mem 0) 2
  intraCausality e₁ e₂ := e₁ = e₂ ∨ e₁ = .b ∧ e₂ = .c
  atomicity := ∅

/-- The position of each memory access of `tso1` in the memory order `a, d, b`. -/
def tso1Rank : Tso1 → ℕ
  | .a => 0
  | .d => 1
  | .b => 2
  | .c => 3

/-- The execution witness of Fig. 3, left: memory order `a, d, b`, and `b` reads from `d`. -/
def tso1Witness : ExecutionWitness Tso1 ℕ ℕ ℕ ℕ where
  mo e₁ e₂ := e₁ ≠ .c ∧ e₂ ≠ .c ∧ tso1Rank e₁ ≤ tso1Rank e₂
  rf w r := w = .d ∧ r = .b
  initialState _ := some 0

lemma mem_memAccesses_tso1 (e : Tso1) : e ∈ tso1.memAccesses ↔ e ≠ .c := by
  cases e <;> simp [memAccesses, memReads, memWrites, tso1]

lemma mem_memWrites_tso1 (e : Tso1) : e ∈ tso1.memWrites ↔ e = .a ∨ e = .d := by
  cases e <;> simp [memWrites, tso1]

lemma mem_memReads_tso1 (e : Tso1) : e ∈ tso1.memReads ↔ e = .b := by
  cases e <;> simp [memReads, tso1]

lemma mem_previousWrites_tso1 (r : Tso1 → Tso1 → Prop) (w e : Tso1) :
    w ∈ tso1.previousWrites r e ↔
      (w = .a ∨ w = .c ∨ w = .d) ∧ r w e ∧ (tso1.action w).loc = (tso1.action e).loc := by
  cases w <;> simp [previousWrites, tso1]

/-- The validity conditions are satisfiable: `tso1Witness` is a valid execution of `tso1`. -/
example : ValidExecution tso1 tso1Witness where
  mem_of_mo e₁ e₂ h := by simp only [mem_memAccesses_tso1]; exact ⟨h.1, h.2.1⟩
  isPartialOrder_mo :=
    { refl := fun x => ⟨(mem_memAccesses_tso1 _).1 x.2, (mem_memAccesses_tso1 _).1 x.2, le_rfl⟩
      trans := fun _ _ _ h₁ h₂ => ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩
      antisymm := fun ⟨x, _⟩ ⟨y, _⟩ h₁ h₂ => by
        cases x <;> cases y <;> simp_all [tso1Witness, tso1Rank] }
  isLinearOrder_mo :=
    { refl := fun ⟨x, hx⟩ => by
        rw [mem_memWrites_tso1] at hx; rcases hx with rfl | rfl <;> simp [tso1Witness, tso1Rank]
      trans := fun _ _ _ h₁ h₂ => ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩
      antisymm := fun ⟨x, _⟩ ⟨y, _⟩ h₁ h₂ => by
        cases x <;> cases y <;> simp_all [tso1Witness, tso1Rank]
      total := fun ⟨x, hx⟩ ⟨y, hy⟩ => by
        rw [mem_memWrites_tso1] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [tso1Witness, tso1Rank] }
  finite_mo_prefix _ _ := Set.toFinite _
  finite_unrelated _ _ := Set.toFinite _
  mo_of_po_read r hr e he hre := by
    rw [mem_memReads_tso1] at hr
    rw [mem_memAccesses_tso1] at he
    subst hr
    cases e <;> simp_all [po, tso1, tso1Witness, tso1Rank]
  mo_of_po_write w₁ hw₁ w₂ hw₂ h := by
    rw [mem_memWrites_tso1] at hw₁ hw₂
    rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl <;>
      simp_all [po, tso1, tso1Witness, tso1Rank]
  mo_of_po_mfence _ _ _ _ f hf := by cases f <;> simp [mfences, tso1] at hf
  mo_of_po_locked _ _ _ _ _ hes := by simp [tso1] at hes
  atomic _ hes := by simp [tso1] at hes
  rf_read_write w r h := by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.mem 0, 2, rfl, rfl⟩
  rf_mem w r h _ := by
    obtain ⟨rfl, rfl⟩ := h
    simp only [Set.mem_union, mem_previousWrites_tso1]
    refine ⟨Or.inl ⟨by simp, by simp [tso1Witness, tso1Rank], rfl⟩, ?_⟩
    rintro w' (⟨hw', -, -⟩ | ⟨hw', -, -⟩) hmo <;> rcases hw' with rfl | rfl | rfl <;>
      simp_all [tso1Witness, tso1Rank]
  rf_reg w r h hw := by
    obtain ⟨rfl, rfl⟩ := h
    exact absurd ((mem_memAccesses_tso1 _).2 (by simp)) hw
  initial r l v hr hnot := by
    cases r <;> simp only [tso1, reduceCtorEq] at hr
    exact absurd ⟨rfl, rfl⟩ (hnot .d)

/-! ### Store buffering -/

/-- The events of the store-buffering test: `wx` and `ry` on processor 0, `wy` and `rx` on
processor 1. -/
inductive SB
  | wx
  | ry
  | wy
  | rx
  deriving DecidableEq

instance : Finite SB :=
  Finite.of_surjective ![.wx, .ry, .wy, .rx] fun e => by
    cases e
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The store-buffering event structure, with `x` and `y` the addresses 0 and 1, in which both
reads return 0. -/
def sb : EventStructure SB ℕ ℕ ℕ ℕ where
  proc | .wx => 0 | .ry => 0 | _ => 1
  poi | .ry => 1 | .rx => 1 | _ => 0
  action
    | .wx => .write (.mem 0) 1
    | .ry => .read (.mem 1) 0
    | .wy => .write (.mem 1) 1
    | .rx => .read (.mem 0) 0
  intraCausality := (· = ·)
  atomicity := ∅

/-- The position of each event of the store-buffering test in the memory order `ry, rx, wx, wy`. -/
def sbRank : SB → ℕ
  | .ry => 0
  | .rx => 1
  | .wx => 2
  | .wy => 3

/-- The witness for store buffering: both reads precede both writes in memory order, nothing is
read from a write, and memory starts at 0. -/
def sbWitness : ExecutionWitness SB ℕ ℕ ℕ ℕ where
  mo e₁ e₂ := sbRank e₁ ≤ sbRank e₂
  rf _ _ := False
  initialState _ := some 0

lemma mem_memAccesses_sb (e : SB) : e ∈ sb.memAccesses := by
  cases e <;> simp [memAccesses, memReads, memWrites, sb]

lemma mem_memWrites_sb (e : SB) : e ∈ sb.memWrites ↔ e = .wx ∨ e = .wy := by
  cases e <;> simp [memWrites, sb]

lemma mem_memReads_sb (e : SB) : e ∈ sb.memReads ↔ e = .ry ∨ e = .rx := by
  cases e <;> simp [memReads, sb]

/-- Store buffering is allowed: the reads of `y` and of `x` both return 0 in a valid
execution. -/
example : ValidExecution sb sbWitness where
  mem_of_mo e₁ e₂ _ := ⟨mem_memAccesses_sb e₁, mem_memAccesses_sb e₂⟩
  isPartialOrder_mo :=
    { refl := fun _ => le_rfl
      trans := fun _ _ _ h₁ h₂ => le_trans h₁ h₂
      antisymm := fun ⟨x, _⟩ ⟨y, _⟩ h₁ h₂ => by
        cases x <;> cases y <;> simp_all [sbWitness, sbRank] }
  isLinearOrder_mo :=
    { refl := fun _ => le_rfl
      trans := fun _ _ _ h₁ h₂ => le_trans h₁ h₂
      antisymm := fun ⟨x, _⟩ ⟨y, _⟩ h₁ h₂ => by
        cases x <;> cases y <;> simp_all [sbWitness, sbRank]
      total := fun _ _ => le_total _ _ }
  finite_mo_prefix _ _ := Set.toFinite _
  finite_unrelated _ _ := Set.toFinite _
  mo_of_po_read r hr e _ h := by
    rw [mem_memReads_sb] at hr
    rcases hr with rfl | rfl <;> cases e <;> simp_all [po, sb, sbWitness, sbRank]
  mo_of_po_write w₁ hw₁ w₂ hw₂ h := by
    rw [mem_memWrites_sb] at hw₁ hw₂
    rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl <;>
      simp_all [po, sb, sbWitness, sbRank]
  mo_of_po_mfence _ _ _ _ f hf := by cases f <;> simp [mfences, sb] at hf
  mo_of_po_locked _ _ _ _ _ hes := by simp [sb] at hes
  atomic _ hes := by simp [sb] at hes
  rf_read_write _ _ h := h.elim
  rf_mem _ _ h := h.elim
  rf_reg _ _ h := h.elim
  initial r l v hr _ := by
    cases r <;> simp only [sb, reduceCtorEq, Action.read.injEq] at hr <;>
      obtain ⟨rfl, rfl⟩ := hr <;>
      refine ⟨rfl, Set.eq_empty_of_forall_notMem fun w hw => ?_⟩ <;>
      cases w <;> simp_all [previousWrites, po, sb, sbWitness, sbRank, Action.loc]

/-- The store-buffering events with an MFENCE `fx` between `wx` and `ry` on processor 0 and an
MFENCE `fy` between `wy` and `rx` on processor 1. -/
inductive SBFenced
  | wx
  | fx
  | ry
  | wy
  | fy
  | rx
  deriving DecidableEq

instance : Finite SBFenced :=
  Finite.of_surjective ![.wx, .fx, .ry, .wy, .fy, .rx] fun e => by
    cases e
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

/-- The fenced store-buffering event structure, in which both reads return 0. -/
def sbFenced : EventStructure SBFenced ℕ ℕ ℕ ℕ where
  proc | .wx => 0 | .fx => 0 | .ry => 0 | _ => 1
  poi | .fx => 1 | .fy => 1 | .ry => 2 | .rx => 2 | _ => 0
  action
    | .wx => .write (.mem 0) 1
    | .ry => .read (.mem 1) 0
    | .wy => .write (.mem 1) 1
    | .rx => .read (.mem 0) 0
    | _ => .mfence
  intraCausality := (· = ·)
  atomicity := ∅

/-- With an MFENCE between the write and the read on each processor, store buffering is
forbidden: the event structure in which both reads return 0 has no valid execution witness. -/
example (X : ExecutionWitness SBFenced ℕ ℕ ℕ ℕ) : ¬ ValidExecution sbFenced X := by
  intro hX
  -- Nothing reads from a write, since every write writes 1 and both reads return 0.
  have hrf : ∀ (l : Location ℕ ℕ ℕ) w r, sbFenced.action r = .read l 0 → ¬ X.rf w r := by
    intro l w r hr hwr
    obtain ⟨l', v, hw, hr'⟩ := hX.rf_read_write hwr
    rw [hr] at hr'
    cases Action.read.inj hr' |>.2
    cases w <;> simp [sbFenced] at hw
  -- So both reads take the initial value, and no write to their location precedes them.
  have hy := (hX.initial (r := .ry) rfl (hrf (.mem 1) · .ry rfl)).2
  have hx := (hX.initial (r := .rx) rfl (hrf (.mem 0) · .rx rfl)).2
  have hwy : ¬ X.mo .wy .ry := fun h => by
    have : SBFenced.wy ∈ (∅ : Set SBFenced) := hy ▸ Or.inl ⟨⟨_, _, rfl⟩, h, rfl⟩
    exact this
  have hwx : ¬ X.mo .wx .rx := fun h => by
    have : SBFenced.wx ∈ (∅ : Set SBFenced) := hx ▸ Or.inl ⟨⟨_, _, rfl⟩, h, rfl⟩
    exact this
  -- The MFENCEs order each write before the read of its processor in memory order.
  have h0 : X.mo .wx .ry :=
    hX.mo_of_po_mfence _ ⟨0, 1, rfl⟩ _ ⟨1, 0, rfl⟩ .fx rfl (Or.inl ⟨rfl, by decide⟩)
      (Or.inl ⟨rfl, by decide⟩)
  have h1 : X.mo .wy .rx :=
    hX.mo_of_po_mfence _ ⟨1, 1, rfl⟩ _ ⟨0, 0, rfl⟩ .fy rfl (Or.inl ⟨rfl, by decide⟩)
      (Or.inl ⟨rfl, by decide⟩)
  -- The two writes are ordered, and either order contradicts one of the reads.
  have hmem : ∀ e, e ∈ sbFenced.memAccesses ↔ e ∉ ({.fx, .fy} : Set SBFenced) := by
    intro e; cases e <;> simp [memAccesses, memReads, memWrites, sbFenced]
  have htrans := hX.isPartialOrder_mo.toIsTrans
  have hlin := hX.isLinearOrder_mo.toTotal
  rcases hlin.total ⟨.wx, 0, 1, rfl⟩ ⟨.wy, 1, 1, rfl⟩ with h | h
  · exact hwx (htrans.trans ⟨.wx, (hmem _).2 (by simp)⟩ ⟨.wy, (hmem _).2 (by simp)⟩
      ⟨.rx, (hmem _).2 (by simp)⟩ h h1)
  · exact hwy (htrans.trans ⟨.wy, (hmem _).2 (by simp)⟩ ⟨.wx, (hmem _).2 (by simp)⟩
      ⟨.ry, (hmem _).2 (by simp)⟩ h h0)

/-! ### Register reads -/

/-- The events of the register test: `w1` writes 1 and `w2` writes 2 to register `EAX` of
processor 0, and `rd` then reads `EAX`. -/
inductive Regs
  | w1
  | w2
  | rd
  deriving DecidableEq

instance : Finite Regs :=
  Finite.of_surjective ![.w1, .w2, .rd] fun e => by
    cases e
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- The register test in which `rd` reads the value `v`, with one instruction for each event, in
the order `w1`, `w2`, `rd`, and with `EAX` the register 0. -/
def regs (v : ℕ) : EventStructure Regs ℕ ℕ ℕ ℕ where
  proc _ := 0
  poi | .w1 => 0 | .w2 => 1 | .rd => 2
  action
    | .w1 => .write (.reg 0 0) 1
    | .w2 => .write (.reg 0 0) 2
    | .rd => .read (.reg 0 0) v
  intraCausality := (· = ·)
  atomicity := ∅

/-- The witness in which `rd` reads from `w2`. The test has no memory accesses, so the memory
order is empty. -/
def regsWitness : ExecutionWitness Regs ℕ ℕ ℕ ℕ where
  mo _ _ := False
  rf w r := w = .w2 ∧ r = .rd
  initialState _ := none

lemma not_mem_memAccesses_regs (v : ℕ) (e : Regs) : e ∉ (regs v).memAccesses := by
  cases e <;> simp [memAccesses, memReads, memWrites, regs]

lemma w2_mem_previousWrites_regs (v : ℕ) : Regs.w2 ∈ (regs v).previousWrites (regs v).po .rd :=
  ⟨⟨_, _, rfl⟩, Or.inl ⟨rfl, by simp [regs]⟩, rfl⟩

/-- A register read may read the latest earlier write to its register in program order: when `rd`
reads 2, `regsWitness` is a valid execution. -/
example : ValidExecution (regs 2) regsWitness where
  mem_of_mo _ _ h := h.elim
  isPartialOrder_mo :=
    { refl := fun x => absurd x.2 (not_mem_memAccesses_regs _ _)
      trans := fun _ _ _ h => h.elim
      antisymm := fun _ _ h => h.elim }
  isLinearOrder_mo :=
    { refl := fun x => absurd (Or.inr x.2) (not_mem_memAccesses_regs _ _)
      trans := fun _ _ _ h => h.elim
      antisymm := fun _ _ h => h.elim
      total := fun x => absurd (Or.inr x.2) (not_mem_memAccesses_regs _ _) }
  finite_mo_prefix _ _ := Set.toFinite _
  finite_unrelated _ _ := Set.toFinite _
  mo_of_po_read r hr := absurd (Or.inl hr) (not_mem_memAccesses_regs _ r)
  mo_of_po_write w hw := absurd (Or.inr hw) (not_mem_memAccesses_regs _ w)
  mo_of_po_mfence _ _ _ _ f hf := by cases f <;> simp [mfences, regs] at hf
  mo_of_po_locked _ _ _ _ _ hes := by simp [regs] at hes
  atomic _ hes := by simp [regs] at hes
  rf_read_write w r h := by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, rfl, rfl⟩
  rf_mem w _ _ hw := absurd hw (not_mem_memAccesses_regs _ w)
  rf_reg w r h _ := by
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨w2_mem_previousWrites_regs 2, fun w' hw' hpo => ?_⟩
    obtain ⟨⟨l, v, hw⟩, -, -⟩ := hw'
    cases w' <;> simp_all [po, regs]
  initial r l v hr hnot := by
    cases r <;> simp only [regs, reduceCtorEq] at hr
    exact absurd ⟨rfl, rfl⟩ (hnot .w2)

/-- A register read sees the latest earlier write to its register in program order: when `rd`
reads 1, which `w2` overwrote, the register test has no valid execution witness. -/
example (X : ExecutionWitness Regs ℕ ℕ ℕ ℕ) : ¬ ValidExecution (regs 1) X := by
  intro hX
  by_cases h : ∃ w, X.rf w .rd
  · -- `rd` can only read from `w1`, the write of 1, which is not the latest write to `EAX`.
    obtain ⟨w, hw⟩ := h
    obtain ⟨l, v, hwa, hra⟩ := hX.rf_read_write hw
    simp only [regs, Action.read.injEq] at hra
    obtain ⟨rfl, rfl⟩ := hra
    cases w <;> simp only [regs, Action.write.injEq, reduceCtorEq] at hwa
    · have := (hX.rf_reg hw (not_mem_memAccesses_regs _ _)).2 _ (w2_mem_previousWrites_regs 1)
        (Or.inl ⟨rfl, by simp [regs]⟩)
      exact absurd this (by decide)
    · exact absurd hwa.2 (by decide)
  · -- Otherwise `rd` takes the initial value, but `w2` precedes it in program order.
    have := (hX.initial (r := .rd) rfl fun w hw => h ⟨w, hw⟩).2
    have hw2 : Regs.w2 ∈ (∅ : Set Regs) := this ▸ Or.inr (w2_mem_previousWrites_regs 1)
    exact hw2

end Cslib.Distributed.X86TSO.Tests
