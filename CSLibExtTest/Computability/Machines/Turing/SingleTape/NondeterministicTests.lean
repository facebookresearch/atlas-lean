/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Nondeterministic

@[expose] public section

/-!
# Tests for nondeterministic single-tape machines

A concrete NTM, `containsTrue`, scans right and accepts on reading `true`: it accepts exactly the
words that contain `true`. Through the binary codes of natural numbers it recognizes `n ≠ 0`, while
no NTM recognizes `n = 0` (the code of `0` is the empty word, and an NTM that accepts the empty
word accepts every word), though a deterministic machine decides it.
-/

set_option autoImplicit false

open Computability Cslib.Turing Cslib.Automata Cslib.Decidability
  Cslib.Computability.Turing.SingleTape

namespace CSLibExtTest.Computability.Machines.Turing.SingleTape

/-- Scan right in state `false`; on reading `true`, move to the accepting state `true`. -/
def containsTrue : SingleTapeNTM Bool Bool where
  Tr s μ s' := s = false ∧ (μ = .move .right ∧ s' = false ∨ μ = .read true ∧ s' = true)
  start := {false}
  accept := {true}
  accept_halting hmem := by
    rintro ⟨_, _, h, -⟩
    simp_all

/-- Moving right `k + 1` times from the cell before `l₁ ++ true :: l₂`, then reading `true`,
applies to the tape. -/
theorem isSome_foldl_scan (l₂ : List Bool) :
    ∀ (l₁ : List Bool) (a : Bool) (L : StackTape Bool),
      (List.foldl TrLabel.applyToTape (some ⟨some a, L, StackTape.mapSome (l₁ ++ true :: l₂)⟩)
        (List.replicate (l₁.length + 1) (.move .right) ++ [.read true])).isSome
  | [], a, L => rfl
  | b :: l₁, a, L => by
    simp only [List.length_cons, List.replicate_succ, List.cons_append, List.foldl_cons]
    exact isSome_foldl_scan l₂ l₁ b (StackTape.cons (some a) L)

/-- Moving right `k` times keeps `containsTrue` in its scanning state. -/
theorem mTr_scan (k : ℕ) : containsTrue.MTr false (List.replicate k (.move .right)) false := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact .stepL ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ih

/-- **`containsTrue` accepts exactly the words that contain `true`.** -/
theorem accepts_containsTrue_iff (xs : List Bool) :
    Acceptor.Accepts containsTrue xs ↔ true ∈ xs := by
  constructor
  · -- Invariant: the machine scans in state `false` and never writes, so without `true` on the
    -- input no cell holds `true` and the read that leads to the accepting state fails.
    intro ⟨s, hs, c', hc', hy⟩
    by_contra hx
    let P : Cfg Bool Bool → Prop := fun c ↦ c.state = false ∧ c.tape.head ≠ some true ∧
      some true ∉ c.tape.left.toList ∧ some true ∉ c.tape.right.toList
    have hP : P c' := by
      clear hc'
      induction hy with
      | refl =>
        cases xs <;>
          simp_all [P, containsTrue, Cfg.mk₁, BiTape.mk₁, BiTape.nil, StackTape.mapSome]
      | @tail b c _ hstep ih =>
        obtain ⟨hq, hh, hl, hr⟩ := ih
        obtain ⟨q', t'⟩ := c
        obtain ⟨μ, ⟨-, ⟨rfl, hq'⟩ | ⟨rfl, -⟩⟩, ht⟩ := hstep
        · simp only [TrLabel.applyToTape, BiTape.move, BiTape.moveRight,
            Option.some.injEq] at ht
          subst ht
          refine ⟨hq', ?_, ?_, ?_⟩
          · rw [StackTape.head_eq_headI]
            cases h : b.tape.right.toList with
            | nil => simp
            | cons x l =>
              rintro rfl
              exact hr (by simp [h])
          · rw [StackTape.toList_cons]
            unfold SingleTapeTM.codedCons
            split
            · simp
            · simp only [List.mem_cons, not_or]
              exact ⟨fun e ↦ hh e.symm, hl⟩
          · rw [StackTape.toList_tail]
            exact fun h ↦ hr (List.mem_of_mem_tail h)
        · simp [TrLabel.applyToTape, Ne.symm hh] at ht
    obtain ⟨h₁, -⟩ := hP
    simp_all [containsTrue]
  · intro hx
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
    refine (containsTrue.accepts_iff_exists_labels).mpr ?_
    cases l₁ with
    | nil => exact ⟨[.read true], rfl, false, rfl, true, rfl, .single _ ⟨rfl, .inr ⟨rfl, rfl⟩⟩⟩
    | cons a l₁ =>
      exact ⟨_, isSome_foldl_scan l₂ l₁ a ∅, false, rfl, true, rfl,
        Cslib.LTS.MTr.comp _ (mTr_scan _) (.single _ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)⟩

example : Acceptor.Accepts containsTrue [false, false, true, false] :=
  (accepts_containsTrue_iff _).mpr (by decide)

example : ¬Acceptor.Accepts containsTrue [false, false] :=
  fun h ↦ absurd ((accepts_containsTrue_iff _).mp h) (by decide)

/-! Acceptance is r.e., so a deterministic single-tape machine recognizes it. -/

example : REPred fun xs : List Bool ↦ Acceptor.Accepts containsTrue xs :=
  containsTrue.rePred_accepts

example : SingleTapeRecognizable fun xs : List Bool ↦ Acceptor.Accepts containsTrue xs :=
  singleTapeRecognizable_accepts containsTrue

/-- With a tape alphabet that has no `Primcodable` instance, code it through `Fintype.equivFin`. -/
example {State Symbol : Type} [Fintype State] [Fintype Symbol] [DecidableEq Symbol]
    (m : SingleTapeNTM State Symbol) :
    letI : Primcodable Symbol := Primcodable.ofEquiv _ (Fintype.equivFin _)
    REPred fun xs : List Symbol ↦ Acceptor.Accepts m xs := by
  let _ : Primcodable Symbol := Primcodable.ofEquiv _ (Fintype.equivFin _)
  exact m.rePred_accepts

example : SingleTapeRecognizable fun n : ℕ ↦ Acceptor.Accepts containsTrue (encodeNat n) :=
  singleTapeRecognizable_accepts_comp containsTrue
    MetaMathlibExt.TM2Recursive.primrec_encodeNat.to_comp

/-- The binary code of `n` contains a `true` bit iff `n ≠ 0`. -/
theorem true_mem_encodeNat_iff (n : ℕ) : true ∈ encodeNat n ↔ n ≠ 0 := by
  have hpos : ∀ p : PosNum, true ∈ encodePosNum p := fun p ↦ by
    induction p <;> simp_all [encodePosNum]
  have hzero : (n : Num) = 0 ↔ n = 0 := by
    rw [← Nat.cast_zero, Num.of_nat_inj]
  unfold encodeNat
  rcases h : (n : Num) with _ | p
  · simp [encodeNum, hzero.mp h]
  · have hn : n ≠ 0 := fun hn ↦ by
      rw [hn, Nat.cast_zero] at h
      cases h
    simp [encodeNum, hpos, hn]

/-- **`n ≠ 0` is recognized by a single-tape NTM**: `containsTrue` on the binary code of `n`. -/
theorem singleTapeNTMRecognizable_ne_zero : SingleTapeNTMRecognizable fun n : ℕ ↦ n ≠ 0 :=
  ⟨Bool, Bool, inferInstance, inferInstance, inferInstance, id, Function.injective_id,
    containsTrue, fun n ↦ by
      rw [List.map_id, accepts_containsTrue_iff, true_mem_encodeNat_iff, Encodable.encode_nat]⟩

example : SingleTapeRecognizable fun n : ℕ ↦ n ≠ 0 :=
  singleTapeNTMRecognizable_ne_zero.singleTapeRecognizable

/-! The defect: acceptance is closed under extension on the right, so the complement `n = 0` is
recognized by no NTM, though a deterministic machine decides it. -/

example : Acceptor.Accepts containsTrue [true, false, false] :=
  containsTrue.accepts_append [false, false] ((accepts_containsTrue_iff [true]).mpr (by decide))

example : ¬∀ n : ℕ, Acceptor.Accepts containsTrue (encodeNat n) ↔ n = 0 := by
  simpa using containsTrue.not_forall_accepts_encodeNat_iff_eq_zero id

example : ¬SingleTapeNTMRecognizable fun n : ℕ ↦ n = 0 :=
  not_singleTapeNTMRecognizable_eq_zero

example : ∃ p : ℕ → Prop, SingleTapeDecidable p ∧ ¬SingleTapeNTMRecognizable p :=
  exists_singleTapeDecidable_not_singleTapeNTMRecognizable

end CSLibExtTest.Computability.Machines.Turing.SingleTape
