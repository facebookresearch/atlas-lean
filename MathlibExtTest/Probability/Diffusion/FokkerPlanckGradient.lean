/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Diffusion.FokkerPlanckGradient
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for stationary densities of gradient-drift diffusions

Non-vacuity witness: the Ornstein–Uhlenbeck potential `Ψ(x) = x₀² / 2` on `ℝ¹` with `D = 1`
has the Gaussian Gibbs density with zero flux. Identifiability: shifting a potential by a
constant keeps zero flux, and the theorem recovers the constant. The explicit rotational drift
on `ℝ²` with nonzero flux. Boundary case documenting the junk value at `D = 0`: Lean's
`x / 0 = 0` makes `gibbs Ψ 0 = 1`, whose flux under `-∇Ψ` is `-∇Ψ`, not zero.
-/

@[expose] public section

open MathlibExt.Probability.FokkerPlanck

namespace MathlibExtTest.Probability.Diffusion.FokkerPlanckGradient

/-- The Ornstein–Uhlenbeck potential on `ℝ¹`. -/
noncomputable def ψOU : (Fin 1 → ℝ) → ℝ := fun x => x 0 ^ 2 / 2

theorem ψOU_differentiable : Differentiable ℝ ψOU := by
  unfold ψOU; fun_prop

-- Non-vacuity witness: the Gaussian density has zero flux and is stationary.
example : flux 1 (fun x => -grad ψOU x) (fun x => 1 * gibbs ψOU 1 x) = 0 :=
  flux_gibbs_eq_zero ψOU_differentiable one_ne_zero 1
example (x : Fin 1 → ℝ) :
    fokkerPlanckOp 1 (fun x => -grad ψOU x) (fun x => 1 * gibbs ψOU 1 x) x = 0 :=
  fokkerPlanckOp_gibbs_eq_zero ψOU_differentiable one_ne_zero 1 x

-- Identifiability: `ψOU + 3` has zero flux for the same density, and differs by a constant.
example : ∃ C, ∀ x, (fun x => ψOU x + 3) x = ψOU x + C := by
  have hp : Differentiable ℝ (fun x => 1 * gibbs ψOU 1 x) := by
    unfold gibbs ψOU; fun_prop
  have hpos : ∀ x, 0 < 1 * gibbs ψOU 1 x := fun x => by simp [gibbs, Real.exp_pos]
  have h₂ : flux 1 (fun x => -grad (fun x => ψOU x + 3) x) (fun x => 1 * gibbs ψOU 1 x) = 0 := by
    have h := flux_gibbs_eq_zero (ψOU_differentiable.add_const 3) one_ne_zero (Real.exp (3 : ℝ))
    convert h using 2 with x
    simp [gibbs, ← Real.exp_add]
  exact exists_const_of_flux_eq_zero (ψOU_differentiable.add_const 3) ψOU_differentiable hp hpos
    h₂ (flux_gibbs_eq_zero ψOU_differentiable one_ne_zero 1)

-- Non-identifiability: a rotational drift with the same stationary density and nonzero flux.
example := exists_rotational_flux_ne_zero

-- Junk value outside the domain `D ≠ 0`: `gibbs Ψ 0 = 1`.
example (x : Fin 1 → ℝ) : gibbs ψOU 0 x = 1 := by simp [gibbs]

end MathlibExtTest.Probability.Diffusion.FokkerPlanckGradient
