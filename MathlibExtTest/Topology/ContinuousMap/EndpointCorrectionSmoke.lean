/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.ContinuousMap.EndpointCorrection
public import Mathlib.Tactic.NormNum

/-!
# Affine endpoint correction of a curved real path

The original curve is `t ↦ t²` on the lifted closed unit interval.
Correcting its endpoints to two and four gives midpoint value `11/4`,
so the interior curvature survives the correction. Correcting to its
original zero and one endpoints fixes the whole nonzero curve.
-/

noncomputable section

namespace MathlibExtTest.EndpointCorrection

private def curve : C(TopCat.I.{0}, ℝ) where
  toFun s := (TopCat.I.homeomorph s : ℝ) ^ 2
  continuous_toFun := TopCat.I.homeomorph.continuous.subtype_val.pow 2

private def midpoint : TopCat.I.{0} :=
  TopCat.I.homeomorph.symm ⟨(1 / 2 : ℝ), by norm_num⟩

example :
    ContinuousMap.endpointCorrection curve 2 4 0 = 2 ∧
      ContinuousMap.endpointCorrection curve 2 4 1 = 4 :=
  ⟨ContinuousMap.endpointCorrection_zero curve 2 4,
    ContinuousMap.endpointCorrection_one curve 2 4⟩

example : ContinuousMap.endpointCorrection curve 2 4 midpoint = 11 / 4 := by
  rw [ContinuousMap.endpointCorrection_apply]
  norm_num [curve, midpoint, TopCat.I.homeomorph_zero, TopCat.I.homeomorph_one]

example : ContinuousMap.endpointCorrection curve 0 1 = curve ∧ curve ≠ 0 := by
  constructor
  · apply ContinuousMap.endpointCorrection_eq_self <;>
      norm_num [curve, TopCat.I.homeomorph_zero, TopCat.I.homeomorph_one]
  · intro h
    have h1 := congrArg (fun f : C(TopCat.I.{0}, ℝ) => f 1) h
    norm_num [curve, TopCat.I.homeomorph_one] at h1

example :
    Continuous (fun p : C(TopCat.I.{0}, ℝ) × ℝ × ℝ =>
      ContinuousMap.endpointCorrection p.1 p.2.1 p.2.2) :=
  ContinuousMap.continuous_endpointCorrection

end MathlibExtTest.EndpointCorrection
