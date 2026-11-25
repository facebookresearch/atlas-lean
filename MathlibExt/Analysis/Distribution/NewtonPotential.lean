/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import MathlibExt.Analysis.InnerProductSpace.InvNormHarmonic

/-!
# Harmonicity of the Newton potential

Orthonormal coordinates identify the three-dimensional Newton potential with a constant
multiple of the harmonic function `y ↦ ‖y‖⁻¹` on punctured Euclidean space.
-/

open Laplacian

namespace MathlibExt.Analysis.Distribution.NewtonPotentialWanted

private theorem laplacian_comp_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (x : E) :
    Δ (f ∘ e) x = Δ f (e x) := by
  change Δ (f ∘ e.toContinuousLinearEquiv) x = _
  let b := stdOrthonormalBasis ℝ E
  have h := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (Set.mem_univ (e x)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (b.map e)]
  simp only [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> rfl

/--
**The Newton potential is harmonic away from the origin.** Let $E$ be a real inner product space
of dimension $3$, and define $N : E \to \mathbb{R}$ by $N(y) = -1/(4\pi\|y\|)$ for $y \neq 0$ and
$N(0) = 0$. Then the Laplacian of $N$ vanishes at every point $x \neq 0$ of $E$.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Applications" / entry "fundamental solution of the Laplacian";
L. Evans, *Partial Differential Equations*, §2.2.
-/
public theorem newton_potential_harmonic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) (x : E) (hx : x ≠ 0) :
    (Δ (fun (y : E) => (-((4 * Real.pi * ‖y‖))⁻¹ : ℝ)) : E → ℝ) x = 0 := by
  let e := ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim)).repr
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := fun y => ‖y‖⁻¹
  have hform : (fun y : E => -(4 * Real.pi * ‖y‖)⁻¹) = -(4 * Real.pi)⁻¹ • (f ∘ e) := by
    funext y
    simp [f, smul_eq_mul, mul_comm]
  have hs : ContDiffAt ℝ 2 (f ∘ e) x := by
    simpa [f, Function.comp_def, Pi.inv_def] using
      (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)
  have hzero : Δ f (e x) = 0 := laplacian_inv_norm_eq_zero (e.map_ne_zero_iff.mpr hx)
  rw [hform, InnerProductSpace.laplacian_smul _ hs, laplacian_comp_linearIsometryEquiv,
    hzero, smul_zero]

end MathlibExt.Analysis.Distribution.NewtonPotentialWanted
