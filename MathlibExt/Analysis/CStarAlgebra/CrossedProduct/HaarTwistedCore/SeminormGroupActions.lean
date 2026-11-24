/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MultiplierActions
public import MathlibExt.Analysis.CStarAlgebra.Seminorm

/-!
# Group isometries for every actual Haar-core C-star seminorm

The original left and modular right translations preserve the mixed products
used by the C-star square identity. This follows from the exact source star
exchange, centralizer equations and inverse group composition. Every actual
C-star seminorm is consequently invariant under both translations, including
the zero seminorm. No normed or C-star ring is imposed on the raw core.

These are strict algebraic prerequisites for the actual unitary group action
in a covariant norm-model construction. No Hilbert space, isometry or desired
invariance is supplied as an output premise.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] (α : PointNormCStarAction G A)

/-- Original inverse left translations preserve the exact mixed star-convolution product. -/
theorem star_groupLeft_mul_groupLeft (g : G) (f h : Carrier μ α) :
    star (groupLeft μ α g f) * groupLeft μ α g h = star f * h := by
  change convolution μ α (crossedStar μ α (groupLeft μ α g f)) (groupLeft μ α g h) =
    convolution μ α (crossedStar μ α f) h
  rw [crossedStar_groupLeft]
  rw [← convolution_groupLeft μ α g⁻¹ (crossedStar μ α f) (groupLeft μ α g h)]
  have hCancel : groupLeft μ α g⁻¹ (groupLeft μ α g h) = h := by
    have hm := congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => T h)
      (groupLeft_mul μ α g⁻¹ g).symm
    simpa only [LinearMap.comp_apply, inv_mul_cancel, groupLeft_one, LinearMap.id_apply] using hm
  rw [hCancel]

/-- Original modular right translations preserve the mixed product in the reversed C-star law. -/
theorem groupRight_mul_star_groupRight (g : G) (f h : Carrier μ α) :
    groupRight μ α g f * star (groupRight μ α g h) = f * star h := by
  change convolution μ α (groupRight μ α g f) (crossedStar μ α (groupRight μ α g h)) =
    convolution μ α f (crossedStar μ α h)
  rw [crossedStar_groupRight]
  rw [← convolution_groupLeft μ α g f (groupLeft μ α g⁻¹ (crossedStar μ α h))]
  have hCancel : groupLeft μ α g (groupLeft μ α g⁻¹ (crossedStar μ α h)) = crossedStar μ α h := by
    have hm := congrArg (fun T : Carrier μ α →ₗ[ℂ] Carrier μ α => T (crossedStar μ α h))
      (groupLeft_mul μ α g g⁻¹).symm
    simpa only [LinearMap.comp_apply, mul_inv_cancel, groupLeft_one, LinearMap.id_apply] using hm
  rw [hCancel]

/-- Every actual C-star seminorm is invariant under the original inverse left translation. -/
theorem cstarSeminorm_groupLeft (p : CStarSeminorm (Carrier μ α)) (g : G) (f : Carrier μ α) :
    p (groupLeft μ α g f) = p f := by
  apply (sq_eq_sq₀ (apply_nonneg p (groupLeft μ α g f)) (apply_nonneg p f)).mp
  calc
    p (groupLeft μ α g f) ^ 2 = p (star (groupLeft μ α g f) * groupLeft μ α g f) :=
      (p.map_star_mul_self (groupLeft μ α g f)).symm
    _ = p (star f * f) := congrArg p (star_groupLeft_mul_groupLeft μ α g f f)
    _ = p f ^ 2 := p.map_star_mul_self f

/-- Every actual C-star seminorm is invariant under the original modular right translation. -/
theorem cstarSeminorm_groupRight (p : CStarSeminorm (Carrier μ α)) (g : G) (f : Carrier μ α) :
    p (groupRight μ α g f) = p f := by
  have hReverse (x : Carrier μ α) : p (x * star x) = p x ^ 2 := by
    simpa only [star_star, CStarSeminorm.map_star] using p.map_star_mul_self (star x)
  apply (sq_eq_sq₀ (apply_nonneg p (groupRight μ α g f)) (apply_nonneg p f)).mp
  calc
    p (groupRight μ α g f) ^ 2 = p (groupRight μ α g f * star (groupRight μ α g f)) :=
      (hReverse (groupRight μ α g f)).symm
    _ = p (f * star f) := congrArg p (groupRight_mul_star_groupRight μ α g f f)
    _ = p f ^ 2 := hReverse f

end

end HaarTwistedCore
