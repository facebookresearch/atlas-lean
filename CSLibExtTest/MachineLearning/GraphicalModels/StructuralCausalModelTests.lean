/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.StructuralCausalModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Tests for structural causal models, interventions and counterfactuals

The model `X₀ = U₀`, `X₁ = X₀ xor U₁` on `Bool`, with fair-coin disturbances. In the unit
`u = (false, true)` the factual values are `(false, true)`; had `X₀` been `true`, `X₁` would
have been `false`: the counterfactual differs from the factual outcome, and consistency
recovers the factual values when the antecedent already holds.
-/

@[expose] public section

namespace Cslib.MachineLearning.StructuralCausalModelTests

open Cslib.MachineLearning GraphicalModels Convexity Finset

/-- The fair coin on `Bool`. -/
noncomputable def fair : StdSimplex ℝ Bool :=
  StdSimplex.duple (s := 1 / 2) (t := 1 / 2) true false (by norm_num) (by norm_num) (by norm_num)

/-- The parents: `X₀ → X₁`. -/
def xorPa : (k : Fin 2) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨_ + 2, h⟩ => absurd h (by omega)

/-- The structural equations `X₀ = U₀` and `X₁ = X₀ xor U₁`. -/
def xorMech : (k : Fin 2) → (xorPa k → Bool) → Bool → Bool
  | ⟨0, _⟩ => fun _ e => e
  | ⟨1, _⟩ => fun z e => xor (z ⟨0, by simp [xorPa]⟩) e
  | ⟨_ + 2, h⟩ => absurd h (by omega)

/-- The model. -/
noncomputable def xorSCM : SCM Bool Bool 2 where
  pa := xorPa
  noise _ := fair
  mech := xorMech

/-- The unit with disturbances `U₀ = false`, `U₁ = true`. -/
def u₀ : Fin 2 → Bool := ![false, true]

/-- Its factual values are `X₀ = false`, `X₁ = true`. -/
theorem solve_u₀ : xorSCM.solve u₀ = ![false, true] := by
  rw [SCM.solve_eq_iff]
  intro k
  fin_cases k <;> rfl

/-- Had `X₀` been `true`, `X₁` would have been `false`. -/
theorem counterfactual_u₀ :
    xorSCM.counterfactual {0} (fun _ => true) u₀ = ![true, false] := by
  rw [SCM.counterfactual, SCM.solve_eq_iff]
  intro k
  fin_cases k <;> rfl

/-- The counterfactual outcome differs from the factual one. -/
example : xorSCM.counterfactual {0} (fun _ => true) u₀ 1 ≠ xorSCM.solve u₀ 1 := by
  rw [counterfactual_u₀, solve_u₀]
  decide

/-- Effectiveness: the intervened node takes its forced value. -/
example : xorSCM.counterfactual {0} (fun _ => true) u₀ 0 = true :=
  xorSCM.counterfactual_of_mem _ u₀ (mem_singleton_self 0)

/-- Consistency: forcing `X₀ = false`, its factual value in `u₀`, changes nothing. -/
example : xorSCM.counterfactual {0} (fun _ => false) u₀ = ![false, true] := by
  rw [xorSCM.counterfactual_eq_solve, solve_u₀]
  intro i hi
  rw [mem_singleton.1 hi, solve_u₀]
  rfl

/-- The causal Markov condition and the truncated factorization apply to the model. -/
example (x : Fin 2 → Bool) : xorSCM.law x = xorSCM.toBayesNet.joint x :=
  xorSCM.law_eq_joint x

example : ∑ x, xorSCM.law x = 1 :=
  xorSCM.sum_law

example (x : Fin 2 → Bool) :
    (xorSCM.doSet {0} fun _ => true).law x = (xorSCM.toBayesNet.intervene 0 true).joint x := by
  rw [xorSCM.law_doSet_singleton]

/-- Without evidence, the counterfactual probability is the interventional one. -/
example (Y : (Fin 2 → Bool) → Prop) [DecidablePred Y] :
    xorSCM.cfProb {0} (fun _ => true) (fun _ => True) Y =
      ∑ x with Y x, (xorSCM.doSet {0} fun _ => true).law x :=
  xorSCM.cfProb_true _ _ Y

/-! ### The probability of necessity in a monotone model -/

/-- The structural equations `X₀ = U₀` and `X₁ = X₀ || U₁`: the outcome is monotone in the
treatment. -/
def orMech : (k : Fin 2) → (xorPa k → Bool) → Bool → Bool
  | ⟨0, _⟩ => fun _ e => e
  | ⟨1, _⟩ => fun z e => z ⟨0, by simp [xorPa]⟩ || e
  | ⟨_ + 2, h⟩ => absurd h (by omega)

/-- The monotone model. -/
noncomputable def orSCM : SCM Bool Bool 2 where
  pa := xorPa
  noise _ := fair
  mech := orMech

/-- In every unit, the outcome under `do(X₀ = b)` is `b || U₁`. -/
theorem orSCM_counterfactual (b : Bool) (u : Fin 2 → Bool) :
    orSCM.counterfactual {0} (fun _ => b) u = ![b, b || u 1] := by
  rw [SCM.counterfactual, SCM.solve_eq_iff]
  intro k
  fin_cases k <;> rfl

/-- The model is monotone, so Pearl's formula for the probability of necessity applies. -/
example : orSCM.cfProb {0} (fun _ => false) (fun x => x 0 = true ∧ x 1 = true)
      (fun x => x 1 = false) =
    ((∑ x with x 1 = true, orSCM.law x) -
        ∑ x with x 1 = true, (orSCM.doSet {0} fun _ => false).law x) /
      ∑ x with x 0 = true ∧ x 1 = true, orSCM.law x := by
  refine orSCM.cfProb_necessity 0 1 fun u _ => ?_
  rw [orSCM_counterfactual]
  rfl

end Cslib.MachineLearning.StructuralCausalModelTests
