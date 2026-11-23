/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Consequences -- shake: keep (anonymous theorem consumers)

/-! Canonical P/NP consumers, zero certificates, and a negative reduction-direction check. -/

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.Complexity

private abbrev headComponent : Host.Comp where
  K := Bool
  Γ := fun _ => Bool
  L := Bool
  prog
    | false => .pop false (fun _ o => o.getD false)
        (.push true id (.goto fun _ => true))
    | true => .halt
  ks := [false, true]
  ks_nodup := by decide
  mem_ks := fun k => by cases k <;> decide

-- A nonconstant positive example: read the first raw bit (false on empty input).
private theorem head_mem_P : (fun x : List Bool => x.head?.getD false) ∈ P := by
  apply Host.isPolyTime_decider (c := headComponent) (cX := false) (cO := true)
    (gX := id) (start := false) (done := true) (Equiv.refl Bool)
    (fun x => x.head?.getD false) (Polynomial.C 1) rfl
  intro x
  refine ⟨x.head?.getD false,
    update (update (fun _ => []) false x.tail) true [x.head?.getD false], ?_, by simp⟩
  refine Run.le (n := 1) ?_ (by simp)
  apply Run.single
  simp [headComponent, TM2.stepAux]

example : (fun x : List Bool => x.head?.getD false) ∈ NP := P_subset_NP head_mem_P

-- The certificate budget is exactly zero, including at input length zero.
example {L : DecisionProblem} (hL : L ∈ P) :
    ∃ R : (List Bool × List Bool) → Bool, IsPolyTime R ∧
      ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ (0 : Polynomial ℕ).eval x.length ∧ R (x, w) := by
  refine ⟨L ∘ Prod.fst, isPolyTime_fst.comp hL, ?_⟩
  intro x
  simp

example : ([] : List Bool).length ≤ (0 : Polynomial ℕ).eval 0 := by simp
example : ¬ ([true] : List Bool).length ≤ (0 : Polynomial ℕ).eval 0 := by simp

example {A B : DecisionProblem} (h : PolyManyOneRed A B) (hB : B ∈ P) : A ∈ P := h.mem_P hB
example : (fun x : List Bool => x.head?.getD false) ∈ P :=
  (PolyManyOneRed.refl _).mem_P head_mem_P

-- A reduction B ≤ A cannot be used to transfer B ∈ P to A ∈ P.
example {A B : DecisionProblem} (_h : PolyManyOneRed B A) (_hB : B ∈ P) : True := by
  fail_if_success have : A ∈ P := _h.mem_P _hB
  trivial

-- Reduction direction is not merely an elaboration convention: constant false cannot
-- many-one reduce to constant true, regardless of running time.
example : ¬ PolyManyOneRed (fun _ => false) (fun _ => true) := by
  rintro ⟨f, _, h⟩
  have he := h []
  cases he

example {L : DecisionProblem} (h : NPHard L) (hP : L ∈ P) : NP ⊆ P := h.NP_subset_P hP
example {L : DecisionProblem} (h : NPComplete L) (hP : L ∈ P) : P = NP := h.P_eq_NP hP

-- Compatibility is definitional: these are the original classes, not look-alike definitions.
example : MetaMathlibExt.ComplexityTheory.P ⊆ MetaMathlibExt.ComplexityTheory.NP := P_subset_NP
