/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDeriv

@[expose] public section

open scoped Topology ContDiff
open Manifold
open MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted

noncomputable section

namespace MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv

-- The parabola has a computed injective differential and finite-dimensional complemented range.
example :
    IsImmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun t : ℝ => (t, t ^ 2)) 1 := by
  apply IsImmersionAt.of_injective_mfderiv_of_closedComplemented_range (n := ∞)
    (by simp)
  · exact Filter.Eventually.of_forall fun _ =>
      contMDiffAt_iff_contDiffAt.mpr <| by
        simpa [pow_two] using
          contDiffAt_id.prodMk (contDiffAt_id.mul contDiffAt_id)
  · have hparabola :
        HasFDerivAt (fun t : ℝ => (t, t ^ 2))
          ((ContinuousLinearMap.id ℝ ℝ).prod
            ((1 : ℝ) • ContinuousLinearMap.id ℝ ℝ +
              (1 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) 1 := by
      simpa [pow_two] using
        (hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)).prodMk
          ((hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)).mul
            (hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)))
    rw [mfderiv_eq_fderiv, hparabola.fderiv]
    intro u v huv
    change ℝ at u v
    change (u : ℝ) = v
    have hfirst := congrArg Prod.fst huv
    change u = v at hfirst
    exact hfirst
  · let L : ℝ →L[ℝ] ℝ × ℝ :=
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun t : ℝ => (t, t ^ 2)) 1 :
        ℝ →L[ℝ] ℝ × ℝ)
    change L.range.ClosedComplemented
    exact Submodule.ClosedComplemented.of_finiteDimensional _

-- The circle differential is u ↦ u • (-sin t₀, cos t₀), which is never zero.
theorem circle_isImmersionAt (t₀ : ℝ) :
    IsImmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun t : ℝ => (Real.cos t, Real.sin t)) t₀ := by
  apply immersionAt_of_injective_mfderiv (n := ∞) (by simp)
  · exact Filter.Eventually.of_forall fun _ =>
      contMDiffAt_iff_contDiffAt.mpr
        (Real.contDiff_cos.contDiffAt.prodMk Real.contDiff_sin.contDiffAt)
  · have hcircle :=
      (Real.hasDerivAt_cos t₀).hasFDerivAt.prodMk
        (Real.hasDerivAt_sin t₀).hasFDerivAt
    rw [mfderiv_eq_fderiv, hcircle.fderiv]
    intro u v huv
    change ℝ at u v
    change (u : ℝ) = v
    have hsin := congrArg Prod.fst huv
    have hcos := congrArg Prod.snd huv
    change u * (-Real.sin t₀) = v * (-Real.sin t₀) at hsin
    change u * Real.cos t₀ = v * Real.cos t₀ at hcos
    by_cases hs : Real.sin t₀ = 0
    · have hc : Real.cos t₀ ≠ 0 := by
        intro hc
        have htrig := Real.sin_sq_add_cos_sq t₀
        rw [hs, hc] at htrig
        norm_num at htrig
      exact mul_right_cancel₀ hc hcos
    · exact mul_right_cancel₀ (neg_ne_zero.mpr hs) hsin

-- The graph differential keeps both input coordinates, so its computed map is injective.
example (p₀ : ℝ × ℝ) :
    IsImmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞
      (fun p : ℝ × ℝ => (p.1, p.2, p.1 * p.2)) p₀ := by
  apply immersionAt_of_injective_mfderiv (n := ∞) (by simp)
  · exact Filter.Eventually.of_forall fun _ =>
      contMDiffAt_iff_contDiffAt.mpr <|
        contDiffAt_fst.prodMk
          (contDiffAt_snd.prodMk (contDiffAt_fst.mul contDiffAt_snd))
  · have hgraph :
        HasFDerivAt (fun p : ℝ × ℝ => (p.1, p.2, p.1 * p.2))
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
            ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
              (p₀.1 • ContinuousLinearMap.snd ℝ ℝ ℝ +
                p₀.2 • ContinuousLinearMap.fst ℝ ℝ ℝ))) p₀ := by
      simpa only [Pi.mul_apply] using
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)).prodMk
          ((hasFDerivAt_snd (𝕜 := ℝ) (p := p₀)).prodMk
            ((hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)).mul
              (hasFDerivAt_snd (𝕜 := ℝ) (p := p₀))))
    rw [mfderiv_eq_fderiv, hgraph.fderiv]
    intro u v huv
    change ℝ × ℝ at u v
    change (u : ℝ × ℝ) = v
    apply Prod.ext
    · have hfirst := congrArg (fun q => q.1) huv
      change u.1 = v.1 at hfirst
      exact hfirst
    · have hsecond := congrArg (fun q => q.2.1) huv
      change u.2 = v.2 at hsecond
      exact hsecond

-- Mathlib's immersion API exposes the circle parametrisation's injective manifold differential.
example (t₀ : ℝ) :
    Function.Injective
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun t : ℝ => (Real.cos t, Real.sin t)) t₀) := by
  exact (circle_isImmersionAt t₀).mfderiv_injective (by simp)

end MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv
