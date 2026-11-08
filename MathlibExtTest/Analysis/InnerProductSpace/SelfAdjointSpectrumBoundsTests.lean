/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.SelfAdjointSpectrumBounds
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Tests for self-adjoint spectrum bounds via Rayleigh quotients

* The Rayleigh-quotient shift lemma, evaluated numerically: shifting the
  scalar operator `3 • 1` on `ℝ` by `1` gives the scalar operator `-2 • 1`,
  whose Rayleigh quotient at `2` is `-2 = 1 - 3`.
* The zero operator on `ℝ`: `0` is in its spectrum, its Rayleigh quotient
  vanishes identically, and the spectrum bounds collapse to `0 ≤ 0 ≤ 0`.
* The scalar operator `2 • 1` on `ℝ`: `2` is in its spectrum (the shift
  `2 • 1 - 2 • 1` is `0`, which is not a unit), its Rayleigh quotient is
  `2` at `1` and `0` at `0`, and the spectrum bounds give
  `⨅ x, Rayleigh x ≤ 2 ≤ ⨆ x, Rayleigh x`.
* Over nonzero vectors, both endpoints equal the scalar for `2 • 1` and
  `-2 • 1`. The stronger spectrum theorem uses this nonzero-vector domain.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.SelfAdjointSpectrumBoundsTests

open MathlibExt.Analysis.InnerProductSpace.SelfAdjointSpectrumBounds
open ContinuousLinearMap

private lemma scalar_rayleigh_nonzero (c : ℝ) (x : {x : ℝ // x ≠ 0}) :
    ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) c).rayleighQuotient x.1 = c := by
  simpa only [sub_zero, ContinuousLinearMap.rayleighQuotient_zero_apply,
    RCLike.ofReal_real_eq_id, id_eq] using
    (rayleighQuotient_algebraMap_sub (T := (0 : ℝ →L[ℝ] ℝ)) (t := c)
      (x := x.1) x.2)

private lemma scalar_rayleigh_endpoints (c : ℝ) :
    (⨅ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) c).rayleighQuotient x.1) = c ∧
    (⨆ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) c).rayleighQuotient x.1) = c := by
  haveI : Nonempty {x : ℝ // x ≠ 0} := ⟨⟨1, by norm_num⟩⟩
  constructor <;> simp only [scalar_rayleigh_nonzero, ciInf_const, ciSup_const]

/-- The shift lemma, evaluated at a concrete scalar operator. -/
example :
    ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (1 : ℝ) -
      (algebraMap ℝ (ℝ →L[ℝ] ℝ)) (3 : ℝ)).rayleighQuotient (2 : ℝ) = -2 := by
  have h := rayleighQuotient_algebraMap_sub
    (T := (algebraMap ℝ (ℝ →L[ℝ] ℝ)) (3 : ℝ)) (t := 1) (x := (2 : ℝ)) (by norm_num)
  have hray : ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (3 : ℝ)).rayleighQuotient (2 : ℝ) = 3 := by
    simp [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply]
    norm_num
  rw [hray] at h
  simp only [RCLike.ofReal_one] at h
  rw [h]
  norm_num

/-- The Rayleigh quotient of the zero operator vanishes identically. -/
example (x : ℝ) : (0 : ℝ →L[ℝ] ℝ).rayleighQuotient x = 0 := by
  simp [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply]

/-- The zero operator: `0` is in its spectrum and the bounds collapse. -/
example :
    ⨅ x : ℝ, (0 : ℝ →L[ℝ] ℝ).rayleighQuotient x ≤ RCLike.re (0 : ℝ) ∧
      RCLike.re (0 : ℝ) ≤ ⨆ x : ℝ, (0 : ℝ →L[ℝ] ℝ).rayleighQuotient x := by
  apply selfAdjoint_spectrum_subset_Icc (0 : ℝ →L[ℝ] ℝ)
    (IsSelfAdjoint.zero (ℝ →L[ℝ] ℝ))
  rw [spectrum.zero_mem_iff]
  exact not_isUnit_zero

/-- The scalar operator `2 • 1`: `2` is in its spectrum. -/
example : (2 : ℝ) ∈ spectrum ℝ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)) := by
  rw [spectrum.mem_iff]
  simp

/-- The scalar operator `2 • 1`: its Rayleigh quotient is `2` at `1`. -/
example : ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)).rayleighQuotient (1 : ℝ) = 2 := by
  simp [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply]

/-- The spectrum bounds for the scalar operator `2 • 1` on `ℝ`. -/
example :
    ⨅ x : ℝ, ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)).rayleighQuotient x ≤
      RCLike.re (2 : ℝ) ∧
    RCLike.re (2 : ℝ) ≤
      ⨆ x : ℝ, ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)).rayleighQuotient x := by
  apply selfAdjoint_spectrum_subset_Icc
    ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ))
    (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all 2))
  rw [spectrum.mem_iff]
  simp

/-- Positive scalar operators have the exact nonzero-vector endpoints. -/
example :
    (⨅ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)).rayleighQuotient x.1) = 2 ∧
    (⨆ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)).rayleighQuotient x.1) = 2 :=
  scalar_rayleigh_endpoints 2

/-- Negative scalar operators also have the exact nonzero-vector endpoints. -/
example :
    (⨅ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (-2 : ℝ)).rayleighQuotient x.1) = -2 ∧
    (⨆ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (-2 : ℝ)).rayleighQuotient x.1) = -2 :=
  scalar_rayleigh_endpoints (-2)

/-- The stronger public theorem keeps zero outside both extrema. -/
example (c : ℝ) :
    (⨅ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) c).rayleighQuotient x.1) ≤ RCLike.re c ∧
    RCLike.re c ≤ (⨆ x : {x : ℝ // x ≠ 0},
      ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) c).rayleighQuotient x.1) := by
  have hc : c ∈ spectrum ℝ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) c) := by
    rw [spectrum.mem_iff]
    simp
  exact selfAdjoint_spectrum_subset_Icc_nonzero
    ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) c)
    (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c)) hc

end MathlibExtTest.Analysis.InnerProductSpace.SelfAdjointSpectrumBoundsTests
