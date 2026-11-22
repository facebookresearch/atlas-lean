/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Carrier
public import MathlibExt.CategoryTheory.Presentable.FunctorCategory

/-!
# Presentability of the actual Day and R-module carriers

The original small finite-bijection index and the existing Day equivalence
transport the source's local presentability to Day functors. The existing
tensor-monad comparison then produces local presentability of the same original
R-module category. No R-module model or factorization is assumed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C] [HasPullbacks C]
  [IsLocallyPresentable.{w} C]

local instance presentableBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

omit [SymmetricCategory C] [MonoidalClosed C] [HasColimitsOfSize.{w, w} C]
  [HasLimitsOfSize.{0, 0} C] in
/-- Local presentability is produced on the actual original Day carrier through its existing equivalence. -/
theorem dayIsLocallyPresentable : IsLocallyPresentable.{w} (DayFunctor I C) := by
  obtain ⟨κ, hκ, hC⟩ := IsLocallyPresentable.exists_cardinal C
  let _ : Fact κ.IsRegular := hκ
  let _ : IsCardinalLocallyPresentable C κ := hC
  let _ : IsCardinalLocallyPresentable (I ⥤ C) κ :=
    Functor.isCardinalLocallyPresentable_of_essentiallySmall κ
  let _ : IsCardinalLocallyPresentable (DayFunctor I C) κ :=
    (DayFunctor.equiv I C).symm.isCardinalLocallyPresentable κ
  exact ⟨κ, inferInstance, inferInstance⟩

variable (R : DayFunctor I C) [MonObj R]

/-- The actual original R-module category is locally presentable by the proved tensor-monad/module producer. -/
theorem moduleIsLocallyPresentable : IsLocallyPresentable.{w} (CategoryTheory.Mod (DayFunctor I C) R) := by
  let _ : IsLocallyPresentable.{w} (DayFunctor I C) := dayIsLocallyPresentable
  let _ : PreservesColimitsOfSize.{w, w} (tensorLeft R) := dayTensorPreservesColimits R
  exact CategoryTheory.Mod.isLocallyPresentable R

end HomotopicalAlgebra.PositiveLevelModel
