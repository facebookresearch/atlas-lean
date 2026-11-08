/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.Calculus
import MathlibExt.Geometry.Manifold.Riemannian.Laplacian

/-!
# Tests for the Laplace-Beltrami operator

Tests for `Manifold.laplacian`, `Manifold.laplacian_norm_sq`,
`Manifold.laplacian_gaussian` and `Manifold.scalarCurvature_vectorSpace`:
the Laplacian of `‖x‖ ^ 2` on `ℝ⁴` is `8`, the Gaussian potential
`‖x‖ ^ 2 / 4` has Laplacian `2`, the trace of the Gaussian shrinker equation,
and positivity on a general nontrivial inner product space.
-/

open Bundle Manifold EuclideanSpace Module
open scoped Manifold ContDiff
open Laplacian

namespace LaplacianTests

/-- The Laplacian of `‖x‖ ^ 2` on `ℝ⁴` is `8`, that is `2n` with `n = 4`. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x = 8 := by
  have h := Manifold.laplacian_norm_sq (F := EuclideanSpace ℝ (Fin 4)) x
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
    simp
  rw [hfr] at h
  norm_num at h
  exact h

/-- Wrong-sign control: the Laplacian of `‖x‖ ^ 2` on `ℝ⁴` is not `-8`. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x ≠ -8 := by
  have h : laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x = 8 := by
    have h0 := Manifold.laplacian_norm_sq (F := EuclideanSpace ℝ (Fin 4)) x
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
      simp
    rw [hfr] at h0
    norm_num at h0
    exact h0
  rw [h]
  norm_num

/-- Nonvanishing control: the Laplacian of `‖x‖ ^ 2` on `ℝ⁴` is not `0`. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x ≠ 0 := by
  have h : laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x = 8 := by
    have h0 := Manifold.laplacian_norm_sq (F := EuclideanSpace ℝ (Fin 4)) x
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
      simp
    rw [hfr] at h0
    norm_num at h0
    exact h0
  rw [h]
  norm_num

/-- The Laplacian of the Gaussian potential `‖x‖ ^ 2 / 4` on `ℝ⁴` is `2`. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    laplacian (𝓡 4) (fun x => ‖x‖ ^ 2 / 4) x = 2 := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
      = (fun x => ((1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
    funext y
    ring
  have hg := Manifold.laplacian_gaussian (F := EuclideanSpace ℝ (Fin 4))
    (1 / 2 : ℝ) x
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
    simp
  have hval : (1 / 2 : ℝ) * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) : ℝ)
      = 2 := by
    rw [hfr]
    norm_num
  rw [hfun]
  exact hg.trans hval

/-- Wrong-sign control: the Laplacian of `‖x‖ ^ 2 / 4` on `ℝ⁴` is not `-2`. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    laplacian (𝓡 4) (fun x => ‖x‖ ^ 2 / 4) x ≠ -2 := by
  have h : laplacian (𝓡 4) (fun x => ‖x‖ ^ 2 / 4) x = 2 := by
    have hfun : (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        = (fun x => ((1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
      funext y
      ring
    have hg := Manifold.laplacian_gaussian (F := EuclideanSpace ℝ (Fin 4))
      (1 / 2 : ℝ) x
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
      simp
    have hval : (1 / 2 : ℝ) * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) : ℝ)
        = 2 := by
      rw [hfr]
      norm_num
    rw [hfun]
    exact hg.trans hval
  rw [h]
  norm_num

/-- Trace of the Gaussian shrinker equation on `ℝ⁴`: scalar plus Laplacian. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    scalarCurvature (𝓡 4) x
      + laplacian (𝓡 4) (fun x => ‖x‖ ^ 2 / 4) x = 4 * (1 / 2 : ℝ) := by
  have hscal : scalarCurvature (𝓡 4) x = 0 :=
    Manifold.scalarCurvature_vectorSpace x
  have hlap : laplacian (𝓡 4) (fun x => ‖x‖ ^ 2 / 4) x = 2 := by
    have hfun : (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        = (fun x => ((1 / 2 : ℝ) / 2) * ‖x‖ ^ 2) := by
      funext y
      ring
    have hg := Manifold.laplacian_gaussian (F := EuclideanSpace ℝ (Fin 4))
      (1 / 2 : ℝ) x
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
      simp
    have hval : (1 / 2 : ℝ) * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) : ℝ)
        = 2 := by
      rw [hfr]
      norm_num
    rw [hfun]
    exact hg.trans hval
  rw [hscal, hlap]
  norm_num

/-- Positivity: the Laplacian of `‖x‖ ^ 2` is positive on nontrivial `F`. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] (x : F) :
    0 < laplacian 𝓘(ℝ, F) (fun x => ‖x‖ ^ 2) x := by
  rw [Manifold.laplacian_norm_sq x]
  have hpos : 0 < Module.finrank ℝ F := Module.finrank_pos
  have hposR : (0 : ℝ) < (Module.finrank ℝ F : ℝ) := Nat.cast_pos.mpr hpos
  linarith

/-- Agreement on `ℝ⁴`: the manifold Laplacian of `‖x‖ ^ 2` equals Mathlib's `Δ`. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x
      = Δ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2) x := by
  have hcontTop : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 4) ↦ ‖x‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hcontD : ContDiff ℝ ∞
      (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 4) ↦ ‖x‖ ^ 2)) :=
    hcontTop.fderiv_right le_top
  have hdiff : DifferentiableAt ℝ
      (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2)) x :=
    (hcontD.differentiable (by simp)) x
  exact Manifold.laplacian_vectorSpace_eq_laplacian _ x hdiff

/-- Mathlib's `Δ` of `‖x‖ ^ 2` on `ℝ⁴` is `8`, through the manifold agreement. -/
example (x : EuclideanSpace ℝ (Fin 4)) :
    Δ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2) x = 8 := by
  have hcontTop : ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin 4) ↦ ‖x‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hcontD : ContDiff ℝ ∞
      (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 4) ↦ ‖x‖ ^ 2)) :=
    hcontTop.fderiv_right le_top
  have hdiff : DifferentiableAt ℝ
      (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2)) x :=
    (hcontD.differentiable (by simp)) x
  have hag : laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x
      = Δ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2) x :=
    Manifold.laplacian_vectorSpace_eq_laplacian _ x hdiff
  have hman : laplacian (𝓡 4) (fun x => ‖x‖ ^ 2) x = 8 := by
    have h0 := Manifold.laplacian_norm_sq (F := EuclideanSpace ℝ (Fin 4)) x
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
      simp
    rw [hfr] at h0
    norm_num at h0
    exact h0
  exact hag.symm.trans hman

end LaplacianTests
