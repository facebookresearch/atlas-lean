/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeDataComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory

/-!
# The original native localization and replacement at every caller bottom

The fixed-bottom convenience model and the caller-bottom native model use
the same original ordinal. The existing model and factor comparisons identify
their complete data under that actual bottom transport. This file retains
the localization carriers, both functors, both Hom functions, all unit and
counit maps, and the two original replacements. No independently chosen
replacement or limiting data are compared.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Construction

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The literal localization of the existing fixed-bottom native model. -/
abbrev fixedModelHomotopyCategory :=
  @HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) inferInstance
    (Construction.modelCategory (A := A))

/-- The complete weak-class localization functor of the fixed-bottom model. -/
abbrev fixedModelProjection :
    EnrichedFunctorCat PointedCGWH.{u, v} A ⥤ fixedModelHomotopyCategory (A := A) :=
  @toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) inferInstance
    (Construction.modelCategory (A := A))

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The literal localization of the existing caller-bottom native model. -/
abbrev nativeModelHomotopyCategory :=
  @HomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) inferInstance
    (Native.modelCategory (A := A) (B := B))

/-- The complete original weak-class localization functor at the caller bottom. -/
abbrev nativeModelProjection :
    EnrichedFunctorCat PointedCGWH.{u, v} A ⥤ nativeModelHomotopyCategory (A := A) :=
  @toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} A) inferInstance
    (Native.modelCategory (A := A) (B := B))

/-- Both literal localization carriers agree under the actual original bottom. -/
theorem fixedModelHomotopyCategory_eq_native :
    fixedModelHomotopyCategory (A := A) = nativeModelHomotopyCategory (A := A) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete category dictionaries retain their actual localization composition. -/
theorem fixedHomotopyCategory_heq_native :
    HEq (inferInstance : Category (fixedModelHomotopyCategory (A := A)))
      (inferInstance : Category (nativeModelHomotopyCategory (A := A))) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole Q functors, including every original map function, agree. -/
theorem fixedModelProjection_heq_native :
    HEq (fixedModelProjection (A := A)) (nativeModelProjection (A := A)) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The full original localizations are related by their actual identity comparison. -/
def fixedHomotopyEquivalence :
    fixedModelHomotopyCategory (A := A) ≌ nativeModelHomotopyCategory (A := A) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact CategoryTheory.Equivalence.refl

/-- The complete forward functor retains the identity on the actual localization. -/
theorem fixedHomotopyEquivalence_functor :
    HEq (fixedHomotopyEquivalence (A := A)).functor
      (𝟭 (nativeModelHomotopyCategory (A := A))) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete inverse functor retains the original localization identity. -/
theorem fixedHomotopyEquivalence_inverse :
    HEq (fixedHomotopyEquivalence (A := A)).inverse
      (𝟭 (fixedModelHomotopyCategory (A := A))) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every forward object keeps its original underlying localization object. -/
theorem fixedHomotopyEquivalence_obj (X : fixedModelHomotopyCategory (A := A)) :
    HEq ((fixedHomotopyEquivalence (A := A)).functor.obj X) X := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every inverse object keeps the original caller localization object. -/
theorem fixedHomotopyEquivalence_inverse_obj (X : nativeModelHomotopyCategory (A := A)) :
    HEq ((fixedHomotopyEquivalence (A := A)).inverse.obj X) X := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every original forward localization morphism keeps its complete function. -/
theorem fixedHomotopyEquivalence_map
    {X Y : fixedModelHomotopyCategory (A := A)} (f : X ⟶ Y) :
    HEq ((fixedHomotopyEquivalence (A := A)).functor.map f) f := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every original inverse localization morphism keeps its complete function. -/
theorem fixedHomotopyEquivalence_inverse_map
    {X Y : nativeModelHomotopyCategory (A := A)} (f : X ⟶ Y) :
    HEq ((fixedHomotopyEquivalence (A := A)).inverse.map f) f := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The entire original unit is the literal localization identity isomorphism. -/
theorem fixedHomotopyEquivalence_unitIso :
    HEq (fixedHomotopyEquivalence (A := A)).unitIso
      (Iso.refl (𝟭 (fixedModelHomotopyCategory (A := A)))) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The entire original counit is the literal caller localization identity. -/
theorem fixedHomotopyEquivalence_counitIso :
    HEq (fixedHomotopyEquivalence (A := A)).counitIso
      (Iso.refl (𝟭 (nativeModelHomotopyCategory (A := A)))) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The original Q functors commute through the full forward comparison. -/
def fixedProjectionIso :
    fixedModelProjection (A := A) ⋙ (fixedHomotopyEquivalence (A := A)).functor ≅
      nativeModelProjection (A := A) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact Iso.refl _

/-- The original Q functors also commute through the entire inverse comparison. -/
def nativeProjectionIso :
    nativeModelProjection (A := A) ⋙ (fixedHomotopyEquivalence (A := A)).inverse ≅
      fixedModelProjection (A := A) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact Iso.refl _

/-- The whole forward Q transformation is the actual identity transformation. -/
theorem fixedProjectionIso_hom :
    HEq (fixedProjectionIso (A := A)).hom (𝟙 (nativeModelProjection (A := A))) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole inverse Q transformation retains the same identity function. -/
theorem fixedProjectionIso_inv :
    HEq (fixedProjectionIso (A := A)).inv (𝟙 (nativeModelProjection (A := A))) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Both original forward Q maps retain the complete naturality square. -/
theorem fixedProjectionIso_input
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (fixedHomotopyEquivalence (A := A)).functor.map ((fixedModelProjection (A := A)).map f) ≫
        (fixedProjectionIso (A := A)).hom.app Y =
      (fixedProjectionIso (A := A)).hom.app X ≫ (nativeModelProjection (A := A)).map f :=
  (fixedProjectionIso (A := A)).hom.naturality f

/-- Both original inverse Q maps retain every native input square. -/
theorem fixedProjectionIso_inv_input
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (nativeModelProjection (A := A)).map f ≫ (fixedProjectionIso (A := A)).inv.app Y =
      (fixedProjectionIso (A := A)).inv.app X ≫
        (fixedHomotopyEquivalence (A := A)).functor.map ((fixedModelProjection (A := A)).map f) :=
  (fixedProjectionIso (A := A)).inv.naturality f

/-- The two full original Q Hom carriers have the actual complete correspondence. -/
def fixedHoHomEquiv (X Y : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    ((fixedModelProjection (A := A)).obj X ⟶ (fixedModelProjection (A := A)).obj Y) ≃
      ((nativeModelProjection (A := A)).obj X ⟶ (nativeModelProjection (A := A)).obj Y) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact Equiv.refl _

/-- The whole forward Hom function uses the actual forward functor and Q isomorphism. -/
theorem fixedHoHomEquiv_toFun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (fixedHoHomEquiv X Y).toFun =
      (fun g => (fixedProjectionIso (A := A)).inv.app X ≫
        (fixedHomotopyEquivalence (A := A)).functor.map g ≫
          (fixedProjectionIso (A := A)).hom.app Y) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  funext g
  change g = (𝟙 _) ≫ g ≫ (𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

/-- The entire inverse Hom function keeps both unit maps and the original inverse functor. -/
theorem fixedHoHomEquiv_invFun (X Y : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (fixedHoHomEquiv X Y).invFun =
      (fun g => (fixedHomotopyEquivalence (A := A)).unitIso.hom.app
          ((fixedModelProjection (A := A)).obj X) ≫
        (fixedHomotopyEquivalence (A := A)).inverse.map
          ((fixedProjectionIso (A := A)).hom.app X ≫ g ≫
            (fixedProjectionIso (A := A)).inv.app Y) ≫
        (fixedHomotopyEquivalence (A := A)).unitIso.inv.app
          ((fixedModelProjection (A := A)).obj Y)) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  funext g
  change g = (𝟙 _) ≫ ((𝟙 _) ≫ g ≫ (𝟙 _)) ≫ (𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

/-- The forward Hom map retains the original projected native arrow. -/
theorem fixedHoHomEquiv_projection
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    fixedHoHomEquiv X Y ((fixedModelProjection (A := A)).map f) =
      (nativeModelProjection (A := A)).map f := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The inverse Hom map retains the actual original fixed-bottom projection. -/
theorem fixedHoHomEquiv_projection_symm
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X ⟶ Y) :
    (fixedHoHomEquiv X Y).symm ((nativeModelProjection (A := A)).map f) =
      (fixedModelProjection (A := A)).map f := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The actual forward correspondence preserves localization identities. -/
theorem fixedHoHomEquiv_id (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    fixedHoHomEquiv X X (𝟙 _) = 𝟙 _ := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every pair of original localization maps retains its entire composite. -/
theorem fixedHoHomEquiv_comp (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} A)
    (f : (fixedModelProjection (A := A)).obj X ⟶ (fixedModelProjection (A := A)).obj Y)
    (g : (fixedModelProjection (A := A)).obj Y ⟶ (fixedModelProjection (A := A)).obj Z) :
    fixedHoHomEquiv X Z (f ≫ g) = fixedHoHomEquiv X Y f ≫ fixedHoHomEquiv Y Z g := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The inverse correspondence preserves the complete native localization composite. -/
theorem fixedHoHomEquiv_comp_symm (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} A)
    (f : (nativeModelProjection (A := A)).obj X ⟶ (nativeModelProjection (A := A)).obj Y)
    (g : (nativeModelProjection (A := A)).obj Y ⟶ (nativeModelProjection (A := A)).obj Z) :
    (fixedHoHomEquiv X Z).symm (f ≫ g) =
      (fixedHoHomEquiv X Y).symm f ≫ (fixedHoHomEquiv Y Z).symm g := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every actual source map preserves the whole original forward Hom function. -/
theorem fixedHoHomEquiv_source
    {X X' Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X' ⟶ X)
    (g : (fixedModelProjection (A := A)).obj X ⟶ (fixedModelProjection (A := A)).obj Y) :
    fixedHoHomEquiv X' Y ((fixedModelProjection (A := A)).map f ≫ g) =
      (nativeModelProjection (A := A)).map f ≫ fixedHoHomEquiv X Y g := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every actual target map preserves the complete original forward Hom function. -/
theorem fixedHoHomEquiv_target
    {X Y Y' : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : Y ⟶ Y')
    (g : (fixedModelProjection (A := A)).obj X ⟶ (fixedModelProjection (A := A)).obj Y) :
    fixedHoHomEquiv X Y' (g ≫ (fixedModelProjection (A := A)).map f) =
      fixedHoHomEquiv X Y g ≫ (nativeModelProjection (A := A)).map f := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every actual source map retains the entire inverse Hom naturality function. -/
theorem fixedHoHomEquiv_source_symm
    {X X' Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : X' ⟶ X)
    (g : (nativeModelProjection (A := A)).obj X ⟶ (nativeModelProjection (A := A)).obj Y) :
    (fixedHoHomEquiv X' Y).symm ((nativeModelProjection (A := A)).map f ≫ g) =
      (fixedModelProjection (A := A)).map f ≫ (fixedHoHomEquiv X Y).symm g := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every actual target map retains the entire inverse Hom naturality function. -/
theorem fixedHoHomEquiv_target_symm
    {X Y Y' : EnrichedFunctorCat PointedCGWH.{u, v} A} (f : Y ⟶ Y')
    (g : (nativeModelProjection (A := A)).obj X ⟶ (nativeModelProjection (A := A)).obj Y) :
    (fixedHoHomEquiv X Y').symm (g ≫ (nativeModelProjection (A := A)).map f) =
      (fixedHoHomEquiv X Y).symm g ≫ (fixedModelProjection (A := A)).map f := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The full original I-replacement uses the same original factor functor at both bottoms. -/
theorem fixedCofibrantReplacement_eq_native :
    Replacement.cofibrantReplacement (A := A) (B := generatorOrderBot.{v}) =
      Replacement.cofibrantReplacement (A := A) (B := B) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The full original J-replacement keeps its same original object-to-zero factor. -/
theorem fixedFibrantReplacement_eq_native :
    Replacement.fibrantReplacement (A := A) (B := generatorOrderBot.{v}) =
      Replacement.fibrantReplacement (A := A) (B := B) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The entire original I counit is retained under actual bottom transport. -/
theorem fixedCofibrantReplacementCounit_heq_native :
    HEq (Replacement.cofibrantReplacementCounit (A := A) (B := generatorOrderBot.{v}))
      (Replacement.cofibrantReplacementCounit (A := A) (B := B)) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete original J unit keeps every diagram component. -/
theorem fixedFibrantReplacementUnit_heq_native :
    HEq (Replacement.fibrantReplacementUnit (A := A) (B := generatorOrderBot.{v}))
      (Replacement.fibrantReplacementUnit (A := A) (B := B)) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The actual full initial I arrow retains the original zero diagram and maps. -/
theorem fixedInitialToCofibrantReplacement_heq_native :
    HEq (Replacement.initialToCofibrantReplacement (A := A) (B := generatorOrderBot.{v}))
      (Replacement.initialToCofibrantReplacement (A := A) (B := B)) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The entire terminal J arrow keeps its original target and every original map. -/
theorem fixedFibrantReplacementToZero_heq_native :
    HEq (Replacement.fibrantReplacementToZero (A := A) (B := generatorOrderBot.{v}))
      (Replacement.fibrantReplacementToZero (A := A) (B := B)) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

end HomotopicalAlgebra.EnrichedProjective.Native.Construction
