/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneFunctorNaturality

/-!
# The original S₁ comparison on the original weak categories

The earned whole stage natural isomorphism has original weak components,
since each component is an actual stage isomorphism. Restricting those
same maps retains the literal insertion, exact stage-map functor and
original object/morphism readouts.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v uD vD
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.Waldhausen.SConstruction
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The actual original stage comparison restricts to its original weak isomorphism. -/
def stageOnePostcompWeakIso (X : CategoryTheory.Waldhausen.WeakCategory C) :
    (stageOneGeneralWeak C ⋙ hF.mapStageWeak 1).obj X ≅
      (hF.mapWeakCategory ⋙ stageOneGeneralWeak D).obj X := by
  let e := stageOnePostcompStageIso hF X.obj
  exact WideSubcategory.isoMk e
    ((stageWeak D 1).isomorphisms_le_of_containsIdentities e.hom e.isIso_hom)
    ((stageWeak D 1).isomorphisms_le_of_containsIdentities e.inv e.symm.isIso_hom)

/-- Restriction of the whole original S₁ natural square to the original weak maps. -/
def stageOnePostcompWeakNatIso : stageOneGeneralWeak C ⋙ hF.mapStageWeak 1 ≅
    hF.mapWeakCategory ⋙ stageOneGeneralWeak D :=
  NatIso.ofComponents (stageOnePostcompWeakIso hF) (by
    intro X Y f
    apply WideSubcategory.hom_ext
    exact stageOnePostcompStageIso_naturality hF f.hom)

/-- The forward original weak comparison retains the same full original stage morphism. -/
theorem stageOnePostcompWeakIso_hom (X : CategoryTheory.Waldhausen.WeakCategory C) :
    (stageOnePostcompWeakIso hF X).hom.hom = (stageOnePostcompStageIso hF X.obj).hom := rfl

/-- The inverse original weak comparison retains the same full original stage morphism. -/
theorem stageOnePostcompWeakIso_inv (X : CategoryTheory.Waldhausen.WeakCategory C) :
    (stageOnePostcompWeakIso hF X).inv.hom = (stageOnePostcompStageIso hF X.obj).inv := rfl

/-- The original weak interval insertion comparison is the same earned S₁ square after literal
pullback. -/
def stageOneWeakIntervalPostcompNatIso {a : SimplexCategory} (f : a ⟶ ⦋1⦌) :
    stageOneGeneralWeak C ⋙ reindexStageWeak C f ⋙ hF.mapStageWeak a.len ≅
      hF.mapWeakCategory ⋙ stageOneGeneralWeak D ⋙ reindexStageWeak D f := by
  let e := Functor.isoWhiskerRight (stageOnePostcompWeakNatIso hF) (reindexStageWeak D f)
  have h := hF.mapStageWeak_reindex f
  change stageOneGeneralWeak C ⋙ (reindexStageWeak C f ⋙ hF.mapStageWeak a.len) ≅ _
  rw [h]
  exact e

end CategoryTheory.Waldhausen.SConstruction
