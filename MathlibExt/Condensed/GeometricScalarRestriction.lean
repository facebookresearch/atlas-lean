/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Condensed.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import MathlibExt.Condensed.TopologicalRings

/-!
# Actual constant-scalar restriction of geometric condensed modules

A module over the topological condensed ring C(-,A) becomes a genuine
condensed R-module along a fixed ring map R -> A. Every section module
and restriction retains the original elements; scalars act through the
actual constant continuous functions. This is distinct from replacing
the topological coefficient ring by a constant discrete ring.

Derived restriction is the Kan-derived functor of this actual cochain
source. Its ordinary exactness/derived-existence input is explicit.
References: Clausen--Scholze, condensed mathematics Lectures II/V;
Anschuetz--Mann, arXiv:2403.01951v2, Section2.1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.GeometricScalarRestriction

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalRings

variable (A : Type 1) [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] (R : Type 1) [CommRing R] (φ : R →+* A)

abbrev GeometricModules := SheafOfModules.{1} (ringSheaf A)

/-- The prescribed constants in the actual continuous section ring. -/
def constantScalars (S : CompHaus.{0}ᵒᵖ) : R →+* C(S.unop, A) where
  toFun r := ContinuousMap.const S.unop (φ r)
  map_one' := by ext x; exact map_one φ
  map_mul' a b := by ext x; exact map_mul φ a b
  map_zero' := by ext x; exact map_zero φ
  map_add' a b := by ext x; exact map_add φ a b

/-- The actual section modules after the specified scalar restriction. -/
def restrictionPresheaf (M : GeometricModules A) :
    CompHaus.{0}ᵒᵖ ⥤ ModuleCat.{1} R where
  obj S := (ModuleCat.restrictScalars (constantScalars A R φ S)).obj (M.val.obj S)
  map {S T} f := ConcreteCategory.ofHom
    { toFun x := M.val.restrictₛₗ f x
      map_add' x y := (M.val.restrictₛₗ f).map_add x y
      map_smul' r x := by
        change M.val.restrictₛₗ f ((constantScalars A R φ S) r • x) =
          (constantScalars A R φ T) r • (M.val.restrictₛₗ f x)
        rw [(M.val.restrictₛₗ f).map_smulₛₗ]
        rfl }
  map_id S := by
    apply ModuleCat.hom_ext
    ext x
    change M.val.map (𝟙 S) x = x
    rw [M.val.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    exact M.val.map_comp_apply f g x

/-- Scalar restriction retains the actual sheaf descent of its elements. -/
theorem restrictionIsSheaf (M : GeometricModules A) :
    Presheaf.IsSheaf (coherentTopology CompHaus.{0})
      (restrictionPresheaf A R φ M) := by
  let : HasLimitsOfSize.{0, 1} (ModuleCat.{1} R) :=
    ModuleCat.hasLimitsOfSize.{0, 1, 1, 1}
  let : ReflectsLimitsOfSize.{0, 1}
      (forget₂ (ModuleCat.{1} R) AddCommGrpCat.{1}) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ _
    (forget₂ (ModuleCat.{1} R) AddCommGrpCat.{1})
  change Presheaf.IsSheaf (coherentTopology CompHaus.{0}) M.val.presheaf
  exact M.isSheaf

/-- The literal constant-scalar restriction, on objects and maps. -/
def restriction : GeometricModules A ⥤ CondensedMod.{0} R where
  obj M := ⟨restrictionPresheaf A R φ M, restrictionIsSheaf A R φ M⟩
  map f := ⟨
    { app S := (ModuleCat.restrictScalars (constantScalars A R φ S)).map
        (f.val.app S)
      naturality {S T} g := by
        apply ModuleCat.hom_ext
        ext x
        exact PresheafOfModules.naturality_apply f.val g x }⟩
  map_id M := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ModuleCat.hom_ext
    ext x
    rfl

instance restriction_additive : (restriction A R φ).Additive where
  map_add {X Y} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ModuleCat.hom_ext
    ext x
    rfl

attribute [local instance] HasDerivedCategory.standard

/-- The fixed ordinary cochain source, followed by native Q. -/
def derivedRestrictionSource :
    CochainComplex (GeometricModules A) ℤ ⥤ DerivedCategory (CondensedMod.{0} R) :=
  (restriction A R φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- Ordinary derived existence for this fixed coefficient source. -/
class HasDerivedRestriction : Prop where
  exists_derived : (derivedRestrictionSource A R φ).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (GeometricModules A) (ComplexShape.up ℤ))

attribute [instance] HasDerivedRestriction.exists_derived

/-- Native Kan-derived restriction of the actual geometric coefficients. -/
def derivedRestriction [HasDerivedRestriction A R φ] :
    DerivedCategory (GeometricModules A) ⥤ DerivedCategory (CondensedMod.{0} R) :=
  (derivedRestrictionSource A R φ).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (GeometricModules A) (ComplexShape.up ℤ))

end MathlibExt.Condensed.GeometricScalarRestriction
