/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories

noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories

namespace MathlibExtTest.AlgebraicGeometry.DeligneFaltingsCategories

/-- Nonintegral weight categories retain distinct monoid arrows even when
all weights collapse in groupification. -/
abbrev IdempotentMonoid : CommMonCat := CommMonCat.of (WithZero Unit)

private theorem groupified_zero :
    Algebra.GrothendieckGroup.of (M := IdempotentMonoid) 0 = 1 := by
  have h := congrArg (Algebra.GrothendieckGroup.of (M := IdempotentMonoid))
    (zero_mul (0 : IdempotentMonoid))
  rw [map_mul] at h
  exact mul_left_cancel (show
    Algebra.GrothendieckGroup.of (M := IdempotentMonoid) 0 *
      Algebra.GrothendieckGroup.of (M := IdempotentMonoid) 0 =
    Algebra.GrothendieckGroup.of (M := IdempotentMonoid) 0 * 1 from
      h.trans (mul_one _).symm)

/-- The zero-labelled endomorphism is well-defined at the unit weight. -/
def zeroWeightArrow : (1 : Weight IdempotentMonoid) ⟶ 1 :=
  ⟨0, by
    change Algebra.GrothendieckGroup.of (M := IdempotentMonoid) 0 * 1 = 1
    rw [groupified_zero, one_mul]⟩

example : zeroWeightArrow ≠ (𝟙 (1 : Weight IdempotentMonoid)) := by
  intro h
  have hh := congrArg WeightHom.label h
  exact zero_ne_one hh

example : zeroWeightArrow ≫ zeroWeightArrow = zeroWeightArrow := by
  apply WeightHom.ext
  change (0 : IdempotentMonoid) * 0 = 0
  exact zero_mul _

/-- The actual module unit is a usable divisor object on every scheme. -/
example (X : Scheme) :
    (DivisorObject.unitObject X).sectionMap =
      𝟙 (MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.structureModule X) := rfl

end MathlibExtTest.AlgebraicGeometry.DeligneFaltingsCategories
