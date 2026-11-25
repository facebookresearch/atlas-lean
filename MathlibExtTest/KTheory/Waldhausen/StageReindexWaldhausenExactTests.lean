/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageReindexWaldhausenExact

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.StageReindexWaldhausenExact

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- All original simplex operators earn exactness in arbitrary Waldhausen categories. -/
theorem originalReindexExact {a b : SimplexCategory} (α : a ⟶ b) :
    letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
    letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
    letI : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
    letI : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
    (reindexStage (C := C) α).IsWaldhausenExact :=
  reindexStage_general_isWaldhausenExact C α

/-- The original selected morphism components remain literal precomposition. -/
theorem originalReindexComponent {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B) (x : Ar a.len) :
    ((reindexStage (C := C) α).map f).hom.app x =
      f.hom.app ((indexFunctor α).obj x) := reindexStage_general_app C α f x

/-- The generic original comparison is available through the canonical
reindex module without importing any first-quotient development. -/
def originalGenericComparison {a b : SimplexCategory} (f g : a ⟶ b)
    (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) :
    reindexStage (C := C) f ⟶ reindexStage (C := C) g :=
  reindexStageNatTransOfLE C f g h

/-- Every complete comparison component remains the original diagram
applied to the actual original ordinal comparison arrow. -/
theorem originalComparisonComponent {a b : SimplexCategory} (f g : a ⟶ b)
    (h : ∀ i, f.toOrderHom i ≤ g.toOrderHom i) (A : Stage C b.len) (x : Ar a.len) :
    ((originalGenericComparison C f g h).app A).hom.app x =
      A.obj.map ((indexFunctorNatTransOfLE f g h).app x) :=
  reindexStageNatTransOfLE_app C f g h A x

end MathlibExtTest.StageReindexWaldhausenExact
