/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.MapFirst
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
public import CSLibExt.Computability.Complexity.Host
import Mathlib.Tactic.FinCases

/-!
# Boolean closure of canonical P

Duplicate the full input, run each decider on one preserved copy, and combine
its one-bit answers. All arrows use the existing canonical `IsPolyTime`;
conversions to and from the tagged raw pair format are charged explicitly.
The machine endpoints include control reset and empty non-output stacks.

The concrete machines below expose their exact runs for clients and regression
tests. Their stack and label indices are finite, not a new machine framework.
-/

@[expose] public section

namespace Cslib.Complexity.BoolClosure

open Turing Function MetaMathlibExt TM2Program ComplexityTheory BitstringEncoding DenseSAT
open PolynomialEncoding

/-- Turn the one-bit Bool encoding into the three-bit encoding of its singleton
list. The same stack is used for input and output. -/
def singletonTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := .pop () (fun _ o => o.getD false) <|
    .push () (fun _ => false) <| .push () id <| .push () (fun _ => true) <|
      .load (fun _ => false) .halt

/-- Singleton encoding takes exactly one TM2 step and resets the control. -/
theorem singletonTM_run (b : Bool) :
    Run singletonTM.m 1 (initList singletonTM [b])
      (haltList singletonTM [true, b, false]) := by
  apply Run.single
  apply congrArg (TM2.Cfg.mk none false)
  funext k
  cases k
  rfl

private noncomputable def singletonComputable :
    TM2ComputableInPolyTime bitEncode bitEncode (fun b : Bool => [b]) where
  tm := singletonTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun b := by
    refine ⟨⟨1, ?_⟩, by simp⟩
    change Run singletonTM.m 1 (initList singletonTM [b])
      (haltList singletonTM [true, b, false])
    exact singletonTM_run b

/-- Duplicate raw bits into the tagged pair encoding, using input stack 0,
output stack 1 and scratch stack 2. -/
abbrev dupTM : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ
    | 0 => Bool
    | 1 => Verifier.G
    | _ => Bool
  Λ := Fin 6
  main := 0
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m
    | 0 => moveB 0 2 some id 0 1
    | 1 => splitB 2 0 1 some id (fun b => .inr (some b)) 1 2
    | 2 => .push 1 (fun _ => .inr none) (.goto fun _ => 3)
    | 3 => moveB 0 2 some id 3 4
    | 4 => moveB 2 1 some Sum.inl 4 5
    | _ => .load (fun _ => false) .halt

private abbrev DupΓ := dupTM.Γ

/-- Raw duplication preserves order in both copies and clears input/scratch,
in exactly `4 * x.length + 6` steps. -/
theorem dupTM_run (x : List Bool) :
    Run dupTM.m (4 * x.length + 6) (initList dupTM x)
      (haltList dupTM (Verifier.pairEncode (x, x))) := by
  let S₀ : ∀ k, List (DupΓ k) := update (fun _ => []) 0 x
  obtain ⟨S₁, r₁, h10, h12, h11, _⟩ := copyB_run
    (M := dupTM.m) (a := 0) (b := 1) (t := 2)
    (da := some) (dt := some) (ga := id) (gt := id)
    (gb := fun b => Sum.inr (some b)) (first := 0) (second := 1) (next := 2)
    rfl rfl (by decide) (by decide) (by decide) (fun _ => rfl) (fun _ => rfl)
    x [] false S₀ (by simp [S₀]) rfl (by simp [S₀, EndsBitBlock])
  let S₂ : ∀ k, List (DupΓ k) := update S₁ 1 (.inr none :: S₁ 1)
  have r₂ : Run dupTM.m 1 ⟨some 2, false, S₁⟩ ⟨some 3, false, S₂⟩ :=
    Run.single rfl
  obtain ⟨v₃, S₃, r₃, h30, h32, h31, _⟩ := Host.move2_run
    (M := dupTM.m) (a := 0) (t := 2) (b := 1)
    (d := some) (gt := id) (dt := some) (g := Sum.inl)
    (l₁ := 3) (l₂ := 4) (l₃ := 5)
    rfl rfl (by decide) (by decide) (by decide) (fun _ => rfl)
    x x [] false S₂ (by simp [S₂, h10, S₀]) rfl rfl (by simp [S₂, h12, S₀])
  have hS₃ : S₃ = update (fun k => ([] : List (DupΓ k))) (1 : Fin 3)
      (Verifier.pairEncode (x, x)) := by
    funext k
    fin_cases k
    · simpa using h30
    · simpa [S₂, h11, S₀, Verifier.pairEncode] using h31
    · simpa using h32
  have r₄ : Run dupTM.m 1 ⟨some 5, v₃, S₃⟩ ⟨none, false, S₃⟩ :=
    Run.single rfl
  have r := ((r₁.trans r₂).trans r₃).trans r₄
  rw [hS₃] at r
  rw [Host.initList_eq, Host.haltList_eq]
  exact r.of_eq (by omega)

private noncomputable def dupComputable :
    TM2ComputableInPolyTime (fun x : List Bool => x) Verifier.pairEncode
      (fun x => (x, x)) where
  tm := dupTM
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 4 * Polynomial.X + Polynomial.C 6
  outputsFun x := by
    refine ⟨⟨4 * x.length + 6, ?_⟩, by simp⟩
    change Run dupTM.m _ (initList dupTM (x.map id))
      (haltList dupTM ((Verifier.pairEncode (x, x)).map id))
    erw [List.map_id, List.map_id]
    exact dupTM_run x

/-- Swap two tagged bit blocks in place on stack 0; stacks 1 and 2 are scratch.
In particular, input and output stack indices coincide. -/
abbrev swapTM : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 0
  Γ
    | 0 => Verifier.G
    | _ => Bool
  Λ := Fin 7
  main := 0
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Verifier.G)
  m
    | 0 => moveB 0 1 Host.dX id 0 1
    | 1 => .pop 0 (fun s _ => s) (.goto fun _ => 2)
    | 2 => moveB 0 2 Host.dW id 2 3
    | 3 => moveB 1 0 some (fun b => .inr (some b)) 3 4
    | 4 => .push 0 (fun _ => .inr none) (.goto fun _ => 5)
    | 5 => moveB 2 0 some Sum.inl 5 6
    | _ => .load (fun _ => false) .halt

private abbrev SwapΓ := swapTM.Γ

/-- Swapping tagged pairs takes two steps per payload bit plus seven, with
both scratch stacks empty and control reset at the exact halting endpoint. -/
theorem swapTM_run (a b : List Bool) :
    Run swapTM.m (2 * a.length + 2 * b.length + 7)
      (initList swapTM (Verifier.pairEncode (a, b)))
      (haltList swapTM (Verifier.pairEncode (b, a))) := by
  let S₀ : ∀ k, List (SwapΓ k) := update (fun _ => []) 0 (Verifier.pairEncode (a, b))
  obtain ⟨v₁, S₁, r₁, h10, h11, h1k⟩ := moveB_run
    (M := swapTM.m) (self := 0) (next := 1) (a := 0) (b := 1)
    (d := Host.dX) (g := id) rfl (by decide)
    a (a.map Sum.inl) (.inr none :: b.map (fun t => .inr (some t))) false S₀
    (by simp [S₀, Verifier.pairEncode]) (by simp [IsBitBlock, Host.dX, comp_def]) rfl
  let S₂ : ∀ k, List (SwapΓ k) := update S₁ 0 (b.map fun t => .inr (some t))
  have r₂ : Run swapTM.m 1 ⟨some 1, v₁, S₁⟩ ⟨some 2, v₁, S₂⟩ :=
    Run.single (by simp [swapTM, TM2.stepAux, h10, S₂])
  obtain ⟨v₃, S₃, r₃, h30, h32, h3k⟩ := moveB_run
    (M := swapTM.m) (self := 2) (next := 3) (a := 0) (b := 2)
    (d := Host.dW) (g := id) rfl (by decide)
    b (b.map fun t => .inr (some t)) [] v₁ S₂ (by simp [S₂])
    (by simp [IsBitBlock, Host.dW, comp_def]) rfl
  have h31 : S₃ 1 = a.reverse := by
    rw [h3k 1 (by decide) (by decide)]
    simp [S₂, h11, S₀]
  have h32' : S₃ 2 = b.reverse := by
    rw [h32]
    simp [S₂, h1k 2 (by decide) (by decide), S₀]
  obtain ⟨v₄, S₄, r₄, h41, h40, h4k⟩ := moveB_run
    (M := swapTM.m) (self := 3) (next := 4) (a := 1) (b := 0)
    (d := some) (g := fun t => Sum.inr (some t)) rfl (by decide)
    a.reverse a.reverse [] v₃ S₃ (by simp [h31]) rfl rfl
  have h40' : S₄ 0 = a.map (fun t => Sum.inr (some t)) := by
    simpa [List.map_reverse, h30] using h40
  let S₅ : ∀ k, List (SwapΓ k) := update S₄ 0 (.inr none :: S₄ 0)
  have r₅ : Run swapTM.m 1 ⟨some 4, v₄, S₄⟩ ⟨some 5, v₄, S₅⟩ :=
    Run.single rfl
  obtain ⟨v₆, S₆, r₆, h62, h60, h6k⟩ := moveB_run
    (M := swapTM.m) (self := 5) (next := 6) (a := 2) (b := 0)
    (d := some) (g := Sum.inl) rfl (by decide)
    b.reverse b.reverse [] v₄ S₅
    (by simp [S₅, h4k 2 (by decide) (by decide), h32']) rfl rfl
  have hS₆ : S₆ = update (fun k => ([] : List (SwapΓ k))) (0 : Fin 3)
      (Verifier.pairEncode (b, a)) := by
    funext k
    fin_cases k
    · simpa [S₅, h40', List.map_reverse, Verifier.pairEncode] using h60
    · change S₆ (1 : Fin 3) = []
      rw [h6k 1 (by decide) (by decide)]
      simpa [S₅] using h41
    · simpa using h62
  have r₇ : Run swapTM.m 1 ⟨some 6, v₆, S₆⟩ ⟨none, false, S₆⟩ :=
    Run.single rfl
  have r := (((((r₁.trans r₂).trans r₃).trans r₄).trans r₅).trans r₆).trans r₇
  rw [hS₆] at r
  rw [Host.initList_eq, Host.haltList_eq]
  exact r.of_eq (by simp only [List.length_reverse]; omega)

private noncomputable def swapComputable :
    TM2ComputableInPolyTime Verifier.pairEncode Verifier.pairEncode
      (Prod.swap : List Bool × List Bool → List Bool × List Bool) where
  tm := swapTM
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  outputsFun q := by
    obtain ⟨a, b⟩ := q
    refine ⟨⟨2 * a.length + 2 * b.length + 7, ?_⟩, ?_⟩
    · change Run swapTM.m _ (initList swapTM ((Verifier.pairEncode (a, b)).map id))
        (haltList swapTM ((Verifier.pairEncode (b, a)).map id))
      erw [List.map_id, List.map_id]
      exact swapTM_run a b
    · simp [Verifier.pairEncode]
      omega

/-- Two peeks combine the second stack's head with the first stack's head,
in that order. Labels 3 and 4 are the true and false exits. Empty heads are false. -/
abbrev headsComp (op : Bool → Bool → Bool) : Host.Comp where
  K := Bool
  Γ _ := Bool
  L := Fin 5
  prog
    | 0 => .peek true (fun _ o => o.getD false) (.goto fun s => if s then 2 else 1)
    | 1 => .peek false (fun _ o => o.getD false) (.goto fun s => if op false s then 3 else 4)
    | 2 => .peek false (fun _ o => o.getD false) (.goto fun s => if op true s then 3 else 4)
    | _ => .halt
  ks := [false, true]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- The head component reaches its answer exit in exactly two steps without
changing either stack. Cleanup belongs to the existing verifier host. -/
theorem headsComp_run (op : Bool → Bool → Bool) (x w : List Bool) :
    Run (headsComp op).prog 2
      ⟨some 0, false, update (update (fun _ => []) false x) true w⟩
      ⟨some (if op (w.headD false) (x.headD false) then 3 else 4), x.headD false,
        update (update (fun _ => []) false x) true w⟩ := by
  cases x <;> cases w with
  | nil => rfl
  | cons b w => cases b <;> rfl

end Cslib.Complexity.BoolClosure

namespace MetaMathlibExt.ComplexityTheory

open Cslib.Complexity Cslib.Complexity.BoolClosure Cslib.Complexity.DenseSAT

/-- Wrapping a Bool in a singleton list is polynomial-time for the canonical encodings. -/
theorem isPolyTime_singleton : IsPolyTime (fun b : Bool => [b]) :=
  ⟨singletonComputable⟩

/-- Duplicating a bit list into a canonical pair is polynomial-time. -/
theorem isPolyTime_dup : IsPolyTime (fun x : List Bool => (x, x)) := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable dupComputable
  exact tm2ComputableInPolyTime_comp h ToCanonical.computable

/-- Swapping the components of a canonical bit-list pair is polynomial-time. -/
theorem isPolyTime_swap :
    IsPolyTime (Prod.swap : List Bool × List Bool → List Bool × List Bool) := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp Converter.computable swapComputable
  exact tm2ComputableInPolyTime_comp h ToCanonical.computable

/-- A fixed Boolean operation on the second and first heads of a canonical pair
is polynomial-time; empty lists contribute false. -/
theorem isPolyTime_heads (op : Bool → Bool → Bool) :
    IsPolyTime (fun q : List Bool × List Bool => op (q.2.headD false) (q.1.headD false)) := by
  apply Host.isPolyTime_verifier (c := headsComp op) (cX := false) (cW := true)
    (gX := id) (gW := id) (start := 0) (yes := 3) (no := 4)
    (fun x w => op (w.headD false) (x.headD false)) (Polynomial.C 2)
    (by change (false : Bool) ≠ true; decide)
    (by change (3 : Fin 5) ≠ 4; decide) rfl rfl
  intro x w
  refine ⟨x.headD false,
    Function.update (Function.update (fun _ : Bool => []) false x) true w, ?_⟩
  simpa using (headsComp_run op x w).le (show 2 ≤ 2 from le_rfl)

/-- Any fixed Boolean combination of two canonical polynomial-time deciders
is polynomial-time. Both deciders receive the same full input. -/
theorem IsPolyTime.combine (op : Bool → Bool → Bool) {L₁ L₂ : List Bool → Bool}
    (h₁ : IsPolyTime L₁) (h₂ : IsPolyTime L₂) :
    IsPolyTime (fun x => op (L₁ x) (L₂ x)) := by
  have h := (((isPolyTime_dup.comp (h₁.comp isPolyTime_singleton).map_fst).comp
    isPolyTime_swap).comp (h₂.comp isPolyTime_singleton).map_fst).comp (isPolyTime_heads op)
  exact h

/-- Canonical P is closed under each fixed Boolean operation. -/
theorem combine_mem_P (op : Bool → Bool → Bool) {L₁ L₂ : DecisionProblem}
    (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) : (fun x => op (L₁ x) (L₂ x)) ∈ P :=
  IsPolyTime.combine op h₁ h₂

/-- Canonical P is closed under pointwise complement. -/
theorem compl_mem_P {L : DecisionProblem} (h : L ∈ P) : Lᶜ ∈ P :=
  combine_mem_P (fun a _ => !a) h h

/-- Canonical P is closed under pointwise intersection. -/
theorem inf_mem_P {L₁ L₂ : DecisionProblem} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    L₁ ⊓ L₂ ∈ P :=
  combine_mem_P Bool.and h₁ h₂

/-- Canonical P is closed under pointwise union. -/
theorem sup_mem_P {L₁ L₂ : DecisionProblem} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    L₁ ⊔ L₂ ∈ P :=
  combine_mem_P Bool.or h₁ h₂

end MetaMathlibExt.ComplexityTheory
