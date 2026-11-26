/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Explicit homeomorphism from the real line to the open unit interval

The map `x ↦ (1+x/(1+|x|))/2` is a homeomorphism `ℝ ≃ (0,1)`. Its inverse sends `t` to
`(2t-1)/(1-|2t-1|)`.

The first stage maps the real line to `(-1,1)` by `x/(1+|x|)`; an affine map then gives the open
unit interval.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace AlgebraicTopology

/-- **Real-line homeomorphism with the open unit interval.** `realHomeomorphUnitOpenInterval :
ℝ ≃ₜ (0,1)` is `x ↦ (1+x/(1+|x|))/2`, with inverse `t ↦ (2t-1)/(1-|2t-1|)`. The target has
its interval subspace topology. -/
noncomputable def realHomeomorphUnitOpenInterval :
    ℝ ≃ₜ Set.Ioo (0 : ℝ) 1 := by
  let e₀ : ℝ ≃ₜ Set.Ioo (-1 : ℝ) 1 :=
    (orderIsoIooNegOneOne ℝ).toHomeomorph
  let a : ℝ ≃ₜ ℝ :=
    affineHomeomorph (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num)
  let e₁ : Set.Ioo (-1 : ℝ) 1 ≃ₜ Set.Ioo (0 : ℝ) 1 :=
    (Homeomorph.image a (Set.Ioo (-1 : ℝ) 1)).trans
      (Homeomorph.setCongr (by
        rw [show a = affineHomeomorph (1 / 2 : ℝ) (1 / 2 : ℝ)
            (by norm_num) from rfl,
          affineHomeomorph_image_Ioo (1 / 2 : ℝ) (1 / 2 : ℝ)
            (-1 : ℝ) 1 (by positivity)]
        norm_num))
  exact e₀.trans e₁

end AlgebraicTopology
