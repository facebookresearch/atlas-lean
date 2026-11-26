/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.PolynomialNetworks.MassAction
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.FinCases

/-!
# Tests for the mass-action vector field

On the reversible isomerization `A ⇌ B`, the field is analytic and its values lie in the
stoichiometric subspace, so they conserve the total concentration. With unit rate constants its
value at `(2, 0)` is the nonzero vector `(-2, 2)`.
-/

open MathlibExt.Biology.Dynamics.ComplexBalanced

namespace MathlibExtTest.Dynamics.PolynomialNetworks.MassAction

-- The reactions are `A → B` and `B → A`, in that order (`0 = A`, `1 = B`).
private def revAB : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

-- Every vector of the stoichiometric subspace of `A ⇌ B` has coordinate sum zero.
private theorem sum_eq_zero_of_mem {v : Fin 2 → ℝ}
    (hv : v ∈ revAB.stoichiometricSubspace) : v 0 + v 1 = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨r, rfl⟩ := hv
    fin_cases r <;> norm_num [revAB]
  | zero => simp
  | add u v _ _ hu hv => simp only [Pi.add_apply]; linarith
  | smul c v _ hv => simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_add, hv, mul_zero]

/-- `massActionField_mem`: for all rate constants and states, the field conserves `A + B`. -/
example (k z : Fin 2 → ℝ) :
    revAB.massActionField k z 0 + revAB.massActionField k z 1 = 0 :=
  sum_eq_zero_of_mem (revAB.massActionField_mem k z)

/-- `massActionField_mem` at a state where the field is not zero. -/
example : (![-2, 2] : Fin 2 → ℝ) ∈ revAB.stoichiometricSubspace := by
  have h : revAB.massActionField (fun _ => 1) ![2, 0] = ![-2, 2] := by
    ext s
    fin_cases s <;>
      simp [ReactionNetwork.massActionField, revAB, Fin.sum_univ_two, Fin.prod_univ_two]
  rw [← h]
  exact revAB.massActionField_mem _ _

/-- `massActionField_contDiff`: the field is differentiable for all rate constants. -/
example (k : Fin 2 → ℝ) : Differentiable ℝ (revAB.massActionField k) :=
  (revAB.massActionField_contDiff k).differentiable (by simp)

/-- `massActionField_contDiff` at order `⊤ = ω`: the field is analytic near every state. -/
example (k : Fin 2 → ℝ) : AnalyticOnNhd ℝ (revAB.massActionField k) Set.univ :=
  (revAB.massActionField_contDiff k).analyticOnNhd

#print axioms ReactionNetwork.massActionField_contDiff
#print axioms ReactionNetwork.massActionField_mem

end MathlibExtTest.Dynamics.PolynomialNetworks.MassAction
