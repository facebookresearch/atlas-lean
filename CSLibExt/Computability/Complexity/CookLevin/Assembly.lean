/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Asm.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Asm.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`Cslib.Complexity.CookLevin` namespaces, deprecated lemma
names updated; module docstring rewritten for this repository (the source's notes and status lines
dropped), missing docstrings added, long lines wrapped.
-/

module

public import MathlibExt.Computability.TuringMachine.StackEmbedding
public import CSLibExt.Computability.Complexity.CookLevin.Accept
public import CSLibExt.Computability.Complexity.CookLevin.InitFamily

/-!
# Cook-Levin: the five generators as sub-machines of one host

* The host stacks: one shared output, one input-code stack, and a private, disjoint counter block
  per generator (update, situation definition, shift, accept, init), with the five stack
  embeddings (`TM2Embedding.SEmb`).
* The host program `hprog` runs init, update, situation definition, shift and accept in sequence
  (one chaining step between generators); `seq_run` is the sequencing theorem, generic in the five
  sub-programs.
* `realProg` instantiates the five real generators for a verifier; `real_run` shows that, from
  preloaded counters, the host emits exactly `encodeCNF (Phi …)`, and `phi_iff` that `Phi` is
  satisfiable iff some certificate makes the verifier accept (from `Situation.Enc.five_iff`).
-/

@[expose] public section


namespace Cslib.Complexity.CookLevin.Assembly

open MetaMathlibExt

open MetaMathlibExt.TM2Program Cslib.Complexity.DenseSAT MetaMathlibExt.TM2Embedding Turing Function
open Cslib.Complexity.CookLevin.CounterView (SK SΓ)
open Cslib.Complexity.CookLevin.InitFamily (IK IΓ emb)

/-! ## [HOST] Host stacks and the five embeddings -/

/-- Host stacks: shared output, input codes, and one private counter block per generator. -/
inductive HK
  | out
  | inp
  | up (x : Family.CK)
  | sd (x : Family.CK)
  | sh (x : Shift.CK)
  | ac (x : Accept.CK)
  | ini (x : InitFamily.CK)
  deriving DecidableEq, Fintype

/-- Host alphabets: Bool output, input codes `Fin g`, unit counters. -/
abbrev HΓ (g : ℕ) : HK → Type
  | .out => Bool
  | .inp => Fin g
  | .up _ => Unit
  | .sd _ => Unit
  | .sh _ => Unit
  | .ac _ => Unit
  | .ini _ => Unit

section Embs

variable (g : ℕ)

/-- Stack renaming of the update generator. -/
def eU : Family.GK → HK
  | .out => .out
  | .c x => .up x

/-- Stack renaming of the situation-definition generator. -/
def eS : Family.GK → HK
  | .out => .out
  | .c x => .sd x

/-- Stack renaming of the shift generator. -/
def eH : SK Shift.CK → HK
  | .out => .out
  | .c x => .sh x

/-- Stack renaming of the accept generator. -/
def eA : SK Accept.CK → HK
  | .out => .out
  | .c x => .ac x

/-- Stack renaming of the init generator. -/
def eI : IK InitFamily.CK → HK
  | .b .out => .out
  | .b (.c x) => .ini x
  | .inp => .inp

/-- Update generator's stacks: `out ↦ out`, counters into block `up`. -/
def embU : SEmb Family.GΓ (HΓ g) where
  e := eU
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eU]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- S-definition generator (second copy of `D3Fam`): counters into block `sd`. -/
def embS : SEmb Family.GΓ (HΓ g) where
  e := eS
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eS]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- Shift generator's stacks: `out ↦ out`, counters into block `sh`. -/
def embH : SEmb (SΓ Shift.CK) (HΓ g) where
  e := eH
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eH]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- Accept generator's stacks: `out ↦ out`, counters into block `ac`. -/
def embA : SEmb (SΓ Accept.CK) (HΓ g) where
  e := eA
  inj := by intro a b h; cases a <;> cases b <;> simp_all [eA]
  ι := fun k => match k with
    | .out => Equiv.refl _
    | .c _ => Equiv.refl _

/-- Init generator: `out ↦ out`, its input stack onto the host's `inp`, counters into `ini`. -/
def embI : SEmb (IΓ InitFamily.CK (Fin g)) (HΓ g) where
  e := eI
  inj := by
    intro a b h
    rcases a with (_ | a) | _ <;> rcases b with (_ | b) | _ <;> simp_all [eI]
  ι := fun k => match k with
    | .b .out => Equiv.refl _
    | .b (.c _) => Equiv.refl _
    | .inp => Equiv.refl _

end Embs

/-! ### `Agree` from host stack values, and the output after a run -/

section AgreeLemmas

variable {g : ℕ} (S : ∀ k, List (HΓ g k))

theorem agree_U {F : Family.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.up x) = cnt () (F x)) : Agree (embU g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embU, eU, ho, hc]
  exact (List.map_id _).symm

theorem agree_S {F : Family.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.sd x) = cnt () (F x)) : Agree (embS g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embS, eS, ho, hc]
  exact (List.map_id _).symm

theorem agree_H {F : Shift.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.sh x) = cnt () (F x)) : Agree (embH g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embH, eH, ho, hc]
  exact (List.map_id _).symm

theorem agree_A {F : Accept.CK → ℕ} {o : List Bool} (ho : S .out = o)
    (hc : ∀ x, S (.ac x) = cnt () (F x)) : Agree (embA g) (CounterView.st F o) S := by
  intro k; cases k <;> simp [embA, eA, ho, hc]
  exact (List.map_id _).symm

theorem agree_I {F : InitFamily.CK → ℕ} {o : List Bool} {xs : List (Fin g)} (ho : S .out = o)
    (hi : S .inp = xs) (hc : ∀ x, S (.ini x) = cnt () (F x)) :
    Agree (embI g) (emb (CounterView.st F o) xs) S := by
  intro k; rcases k with (_ | x) | _ <;> simp [embI, eI, ho, hi, hc] <;> exact (List.map_id _).symm

end AgreeLemmas

/-! ## [SEQ] The host program and the sequencing theorem -/

/-- Host labels: one copy of each generator's labels (two of `D3Fam`'s), and the final halt. -/
inductive HL (N nL KK g d n1 ny : ℕ)
  | up (l : Family.GL N nL)
  | sd (l : Family.GL N nL)
  | sh (l : Shift.GL N KK g d)
  | ac (l : Accept.GL n1 g)
  | ini (l : InitFamily.GL g ny)
  | fin
  deriving DecidableEq, Fintype

section Seq

variable {g N nL KK d n1 ny : ℕ}
  (Pu Ps : Family.GL N nL → TM2.Stmt Family.GΓ (Family.GL N nL) Bool)
  (Ph : Shift.GL N KK g d → TM2.Stmt (SΓ Shift.CK) (Shift.GL N KK g d) Bool)
  (Pa : Accept.GL n1 g → TM2.Stmt (SΓ Accept.CK) (Accept.GL n1 g) Bool)
  (Pi : InitFamily.GL g ny → TM2.Stmt (IΓ InitFamily.CK (Fin g)) (InitFamily.GL g ny) Bool)

/-- Chaining step: reset the state bit (every generator starts with `false`) and jump. -/
def chain (l : HL N nL KK g d n1 ny) : TM2.Stmt (HΓ g) (HL N nL KK g d n1 ny) Bool :=
  .load (fun _ => false) (.goto fun _ => l)

/-- **The host program**: init, update, S-def, shift, accept, each run embedded on its own counter
block; at each generator's `done` the host chains to the next one. -/
def hprog : HL N nL KK g d n1 ny → TM2.Stmt (HΓ g) (HL N nL KK g d n1 ny) Bool
  | .ini l => if l = .done then chain (.up (.pre .eg)) else mapS (embI g) HL.ini (Pi l)
  | .up l => if l = .done then chain (.sd (.pre .eg)) else mapS (embU g) HL.up (Pu l)
  | .sd l => if l = .done then chain (.sh (.pre .eg)) else mapS (embS g) HL.sd (Ps l)
  | .sh l => if l = .done then chain (.ac (.pre .eg)) else mapS (embH g) HL.sh (Ph l)
  | .ac l => if l = .done then chain .fin else mapS (embA g) HL.ac (Pa l)
  | .fin => .halt

/-- **The host as a genuine `FinTM2`** (finiteness check only; input/output stacks provisional
until the precomputation is attached). -/
def hostTM : FinTM2 where
  K := HK
  k₀ := .inp
  k₁ := .out
  Γ := HΓ g
  Λ := HL N nL KK g d n1 ny
  main := .ini (.pre1 .eg)
  σ := Bool
  initialState := false
  m := hprog Pu Ps Ph Pa Pi

variable {Pu Ps Ph Pa Pi}

theorem embeds_I (h : Pi .done = .halt) : Embeds (embI g) HL.ini Pi (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_U (h : Pu .done = .halt) : Embeds (embU g) HL.up Pu (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_S (h : Ps .done = .halt) : Embeds (embS g) HL.sd Ps (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_H (h : Ph .done = .halt) : Embeds (embH g) HL.sh Ph (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem embeds_A (h : Pa .done = .halt) : Embeds (embA g) HL.ac Pa (hprog Pu Ps Ph Pa Pi) := by
  intro l; by_cases hl : l = .done
  · exact Or.inr (hl ▸ h)
  · exact Or.inl (by simp only [hprog, ite_eq_right hl])

theorem chain_run {l l' : HL N nL KK g d n1 ny} (h : hprog Pu Ps Ph Pa Pi l = chain l') (v : Bool)
    (S : ∀ k, List (HΓ g k)) :
    RunLe (hprog Pu Ps Ph Pa Pi) 1 ⟨some l, v, S⟩ ⟨some l', false, S⟩ :=
  (Run.single (by rw [h]; rfl)).le le_rfl

/-- **Sequencing.** Given each generator's run (in the form of its time lemma: from its start
configuration on output `o` to `done` within its bound, prepending its word), and host stacks with
every private block preloaded with that generator's start counters (and init's codes on `inp`),
the host runs all five and halts with the five words prepended in order. -/
theorem seq_run (hu0 : Pu .done = .halt) (hs0 : Ps .done = .halt) (hh0 : Ph .done = .halt)
    (ha0 : Pa .done = .halt) (hi0 : Pi .done = .halt)
    {Fu Fs : Family.CK → ℕ} {Fh : Shift.CK → ℕ} {Fa : Accept.CK → ℕ} {Fi : InitFamily.CK → ℕ}
    {xs : List (Fin g)} {wu ws wh wa wi : List Bool} {Bu Bs Bh Ba Bi : ℕ}
    (hu : ∀ o, ∃ (v : Bool) (S : ∀ k, List (Family.GΓ k)),
      RunLe Pu Bu ⟨some (.pre .eg), false, CounterView.st Fu o⟩ ⟨some .done, v, S⟩ ∧ S .out = wu ++ o)
    (hs : ∀ o, ∃ (v : Bool) (S : ∀ k, List (Family.GΓ k)),
      RunLe Ps Bs ⟨some (.pre .eg), false, CounterView.st Fs o⟩ ⟨some .done, v, S⟩ ∧ S .out = ws ++ o)
    (hh : ∀ o, ∃ (v : Bool) (S : ∀ k, List (SΓ Shift.CK k)),
      RunLe Ph Bh ⟨some (.pre .eg), false, CounterView.st Fh o⟩ ⟨some .done, v, S⟩ ∧ S .out = wh ++ o)
    (ha : ∀ o, ∃ (v : Bool) (S : ∀ k, List (SΓ Accept.CK k)),
      RunLe Pa Ba ⟨some (.pre .eg), false, CounterView.st Fa o⟩ ⟨some .done, v, S⟩ ∧ S .out = wa ++ o)
    (hi : ∀ o, ∃ (v : Bool) (S : ∀ k, List (IΓ InitFamily.CK (Fin g) k)),
      RunLe Pi Bi ⟨some (.pre1 .eg), false, emb (CounterView.st Fi o) xs⟩ ⟨some .done, v, S⟩ ∧
        S (.b .out) = wi ++ o)
    (S₀ : ∀ k, List (HΓ g k)) (o : List Bool) (ho : S₀ .out = o) (hin : S₀ .inp = xs)
    (cu : ∀ x, S₀ (.up x) = cnt () (Fu x)) (cs : ∀ x, S₀ (.sd x) = cnt () (Fs x))
    (ch : ∀ x, S₀ (.sh x) = cnt () (Fh x)) (ca : ∀ x, S₀ (.ac x) = cnt () (Fa x))
    (ci : ∀ x, S₀ (.ini x) = cnt () (Fi x)) :
    ∃ (v : Bool) (S : ∀ k, List (HΓ g k)),
      RunLe (hprog Pu Ps Ph Pa Pi) (Bi + Bu + Bs + Bh + Ba + 5)
        ⟨some (.ini (.pre1 .eg)), false, S₀⟩ ⟨some .fin, v, S⟩ ∧
      S .out = wa ++ (wh ++ (ws ++ (wu ++ (wi ++ o)))) := by
  -- init
  obtain ⟨v1, S1, r1, o1⟩ := hi o
  obtain ⟨T1, q1, a1, f1⟩ := runLe_embed HL.ini (embeds_I hi0) r1 (agree_I S₀ ho hin ci)
  have t1o : T1 .out = wi ++ o := ((a1 (.b .out)).trans (List.map_id _)).trans o1
  have t1u : ∀ x, T1 (.up x) = S₀ (.up x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1s : ∀ x, T1 (.sd x) = S₀ (.sd x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1h : ∀ x, T1 (.sh x) = S₀ (.sh x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  have t1a : ∀ x, T1 (.ac x) = S₀ (.ac x) := fun x =>
    f1 _ (fun k => by rcases k with (_ | _) | _ <;> simp [embI, eI])
  -- update
  obtain ⟨v2, S2, r2, o2⟩ := hu (wi ++ o)
  obtain ⟨T2, q2, a2, f2⟩ := runLe_embed HL.up (embeds_U hu0) r2
    (agree_U T1 t1o (fun x => (t1u x).trans (cu x)))
  have t2o : T2 .out = wu ++ (wi ++ o) := ((a2 .out).trans (List.map_id _)).trans o2
  have t2s : ∀ x, T2 (.sd x) = S₀ (.sd x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1s x)
  have t2h : ∀ x, T2 (.sh x) = S₀ (.sh x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1h x)
  have t2a : ∀ x, T2 (.ac x) = S₀ (.ac x) := fun x =>
    (f2 _ (fun k => by cases k <;> simp [embU, eU])).trans (t1a x)
  -- S-definition
  obtain ⟨v3, S3, r3, o3⟩ := hs (wu ++ (wi ++ o))
  obtain ⟨T3, q3, a3, f3⟩ := runLe_embed HL.sd (embeds_S hs0) r3
    (agree_S T2 t2o (fun x => (t2s x).trans (cs x)))
  have t3o : T3 .out = ws ++ (wu ++ (wi ++ o)) := ((a3 .out).trans (List.map_id _)).trans o3
  have t3h : ∀ x, T3 (.sh x) = S₀ (.sh x) := fun x =>
    (f3 _ (fun k => by cases k <;> simp [embS, eS])).trans (t2h x)
  have t3a : ∀ x, T3 (.ac x) = S₀ (.ac x) := fun x =>
    (f3 _ (fun k => by cases k <;> simp [embS, eS])).trans (t2a x)
  -- shift
  obtain ⟨v4, S4, r4, o4⟩ := hh (ws ++ (wu ++ (wi ++ o)))
  obtain ⟨T4, q4, a4, f4⟩ := runLe_embed HL.sh (embeds_H hh0) r4
    (agree_H T3 t3o (fun x => (t3h x).trans (ch x)))
  have t4o : T4 .out = wh ++ (ws ++ (wu ++ (wi ++ o))) :=
    ((a4 .out).trans (List.map_id _)).trans o4
  have t4a : ∀ x, T4 (.ac x) = S₀ (.ac x) := fun x =>
    (f4 _ (fun k => by cases k <;> simp [embH, eH])).trans (t3a x)
  -- accept
  obtain ⟨v5, S5, r5, o5⟩ := ha (wh ++ (ws ++ (wu ++ (wi ++ o))))
  obtain ⟨T5, q5, a5, _⟩ := runLe_embed HL.ac (embeds_A ha0) r5
    (agree_A T4 t4o (fun x => (t4a x).trans (ca x)))
  have t5o : T5 .out = wa ++ (wh ++ (ws ++ (wu ++ (wi ++ o)))) :=
    ((a5 .out).trans (List.map_id _)).trans o5
  refine ⟨false, T5, ?_, t5o⟩
  have c1 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .ini .done) (l' := .up (.pre .eg)) (by simp [hprog]) v1 T1
  have c2 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .up .done) (l' := .sd (.pre .eg)) (by simp [hprog]) v2 T2
  have c3 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .sd .done) (l' := .sh (.pre .eg)) (by simp [hprog]) v3 T3
  have c4 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .sh .done) (l' := .ac (.pre .eg)) (by simp [hprog]) v4 T4
  have c5 := chain_run (Pu := Pu) (Ps := Ps) (Ph := Ph) (Pa := Pa) (Pi := Pi)
    (l := .ac .done) (l' := .fin) (by simp [hprog]) v5 T5
  exact ((((((((((q1.trans c1).trans q2).trans c2).trans q3).trans c3).trans q4).trans c4).trans
    q5).trans c5).mono (by omega))

end Seq

/-! ## [REAL] The host on the five real generators of a machine `M`, linked to `five_iff` -/

section Real

open Cslib.Complexity.CookLevin.Situation

variable {M : FinTM2} (E : Enc M)

/-- The host running the real generators of `M` (init on `x`/`Ys`, accept on `acc`). -/
noncomputable abbrev realProg (Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) :=
  hprog (Family.prog E.layout E.la E.na E.wa E.N) (Family.prog E.layout E.la E.sa E.wa E.N)
    (Shift.prog E.layout E.sa E.pl E.cn E.pu E.N)
    (Accept.prog E.layout E.A0 E.acode (E.kc M.k₁) (E.enc M.k₁ acc))
    (InitFamily.iprog E.layout (E.lc (some M.main,
        M.initialState)) (E.kc M.k₀) (InitFamily.ycs E Ys))

/-- The formula the host emits: the five families of `five_iff`, at `H = capH m T (depth M)`. -/
noncomputable def Phi (x Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (m T : ℕ) : CNF :=
  E.accFamily acc T (capH m T (depth M)) ++
    (Shift.shFamily E.layout E.sa E.pl E.cn E.pu E.N T (capH m T (depth M)) ++
      (Family.family E.layout E.la E.sa E.wa T (capH m T (depth M)) E.N ++
        (Family.family E.layout E.la E.na E.wa T (capH m T (depth M)) E.N ++
          E.initFamily x Ys m T (capH m T (depth M)))))

/-- The host's step bound: the five generators' bounds plus five chaining steps. -/
noncomputable def realB (Ys : List (M.Γ M.k₀)) (m T : ℕ) : ℕ :=
  InitFamily.initC E.layout (InitFamily.ycs E Ys).length (E.kc M.k₀) * (T + capH m T (depth M) + 1) ^ 5 +
    Family.genC E.layout E.N * (T + capH m T (depth M) + 1) ^ 5 +
    Family.genC E.layout E.N * (T + capH m T (depth M) + 1) ^ 5 +
    Shift.shC E.layout E.N * (T + capH m T (depth M) + 1) ^ 6 +
    Accept.accC E.layout E.A0 (E.kc M.k₁) * (T + capH m T (depth M) + 1) ^ 4 + 5

/-- **The assembled generator, after the precomputation.** From host stacks with every private
block preloaded (`T`, `H = capH m T (depth M)`; init: `T`, `|x|`, `m - |x|`, `H - m`, and the
reversed codes of `x` on `inp`), the host halts within `realB` steps with exactly
`encodeCNF (Phi …)` prepended to the output. Only `|x| ≤ m` is assumed. -/
theorem real_run (x Ys : List (M.Γ M.k₀)) (acc : M.Γ M.k₁) (m T : ℕ) (hx : x.length ≤ m)
    (S₀ : ∀ k, List (HΓ E.layout.g k)) (o : List Bool) (ho : S₀ .out = o)
    (hin : S₀ .inp = (x.map (InitFamily.encF E)).reverse)
    (cu : ∀ z, S₀ (.up z) = cnt () (Family.initF T (capH m T (depth M)) z))
    (cs : ∀ z, S₀ (.sd z) = cnt () (Family.initF T (capH m T (depth M)) z))
    (ch : ∀ z, S₀ (.sh z) = cnt () (Shift.initF T (capH m T (depth M)) z))
    (ca : ∀ z, S₀ (.ac z) = cnt () (Accept.initF T (capH m T (depth M)) z))
    (ci : ∀ z, S₀ (.ini z) = cnt () (InitFamily.initF T x.length (m - x.length)
      (capH m T (depth M) - m) z)) :
    ∃ (v : Bool) (S : ∀ k, List (HΓ E.layout.g k)),
      RunLe (realProg E Ys acc) (realB E Ys m T)
        ⟨some (.ini (.pre1 .eg)), false, S₀⟩ ⟨some .fin, v, S⟩ ∧
      S .out = encodeCNF (Phi E x Ys acc m T) ++ o := by
  have hH := depth_le_capH M m T
  have hpos : 0 < capH m T (depth M) := by unfold capH; omega
  obtain ⟨v, S, h, h'⟩ := seq_run rfl rfl rfl rfl rfl
    (fun o => upd_time E hH T o) (fun o => sdef_time E hH T o) (fun o => shift_time E hH T o)
    (fun o => Accept.acc_gen_time E acc T _ hpos o)
    (fun o => InitFamily.init_gen_capH E x Ys m T hx o) S₀ o ho hin cu cs ch ca ci
  refine ⟨v, S, h, ?_⟩
  rw [h']
  simp only [Phi, encodeCNF, List.flatMap_append, List.append_assoc]

/-- **Correctness of the assembled formula** (`five_iff` through the concatenation): the host's
output formula is satisfiable iff some certificate `y ∈ Ys*` with `|x ++ y| ≤ m` makes `M` accept
at step `T`. -/
theorem phi_iff {x Ys : List (M.Γ M.k₀)} {acc : M.Γ M.k₁} {m T : ℕ} (hx : x.length ≤ m)
    (hacc : ∃ i, E.dec M.k₁ i = acc) :
    (∃ a, cnfSat (Phi E x Ys acc m T) a) ↔
      ∃ y : List (M.Γ M.k₀), (∀ z ∈ y, z ∈ Ys) ∧ (x ++ y).length ≤ m ∧
        Accepts M (runI M (initList M (x ++ y)) T) acc := by
  rw [← E.five_iff hx hacc]
  simp only [Phi, cnfSat_append]
  constructor
  · rintro ⟨a, ha, hh, hs, hu, hi⟩; exact ⟨a, hu, hs, hh, hi, ha⟩
  · rintro ⟨a, hu, hs, hh, hi, ha⟩; exact ⟨a, ha, hh, hs, hu, hi⟩

end Real

end Cslib.Complexity.CookLevin.Assembly
