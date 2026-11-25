/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import MathlibExt.Analysis.Complex.LogNormHarmonicPlane

/-! # Tests for `MathlibExt.Analysis.Complex.LogNormHarmonicPlane` -/

namespace MathlibExtTest.LogNormHarmonicPlane

open Filter InnerProductSpace Laplacian
open MathlibExt.Analysis.Complex.LogNormHarmonicPlaneWanted
open scoped Topology

-- The Laplacian of `log ‖x‖` vanishes at every nonzero point of the Euclidean plane.
example (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    Δ (fun y : EuclideanSpace ℝ (Fin 2) => Real.log ‖y‖) x = 0 :=
  (harmonicOnNhd_log_norm_euclideanSpace_two x hx).2.self_of_nhds

-- `log ‖x‖` is twice continuously differentiable on the punctured plane.
example : ContDiffOn ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) => Real.log ‖y‖) {0}ᶜ :=
  harmonicOnNhd_log_norm_euclideanSpace_two.contDiffOn

-- The origin cannot be added: `log ‖x‖` tends to `-∞` at `0`, where the junk value
-- `Real.log 0 = 0` is finite, so the function is not even continuous, let alone harmonic, there.
example : ¬HarmonicAt (fun y : EuclideanSpace ℝ (Fin 2) => Real.log ‖y‖) 0 := fun h =>
  not_tendsto_nhds_of_tendsto_atBot (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero) _
    (h.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

-- The two-dimensional statement also covers `ℂ` with its real inner product structure.
example : HarmonicOnNhd (fun z : ℂ => Real.log ‖z‖) {0}ᶜ :=
  harmonicOnNhd_log_norm_of_finrank_eq_two Complex.finrank_real_complex

-- Harmonicity pulls back along the linear isometry `ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)` given by
-- the coordinates in the basis `1, I`.
example (z : ℂ) (hz : z ≠ 0) :
    HarmonicAt
      ((fun y : EuclideanSpace ℝ (Fin 2) => Real.log ‖y‖) ∘ Complex.orthonormalBasisOneI.repr) z :=
  (harmonicAt_comp_linearIsometryEquiv_iff _).2
    (harmonicOnNhd_log_norm_euclideanSpace_two _
      (Complex.orthonormalBasisOneI.repr.map_eq_zero_iff.not.mpr hz))

-- The Laplacian commutes with the point reflection `x ↦ -x`, a linear isometry.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (x : E) : Δ (fun y => f (-y)) x = Δ f (-x) :=
  congrFun (laplacian_comp_linearIsometryEquiv f (LinearIsometryEquiv.neg ℝ)) x

end MathlibExtTest.LogNormHarmonicPlane
