/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty
open CategoryTheory.SimplicialCategory SSet

namespace HomotopicalAlgebra.DerivedMappingBasicTests

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

section SymbolicUniverses

variable {X X' X'' Y Y' Y'' : C}

example : Cᵒᵖ ⥤ C ⥤ SSet.{v} := derivedMappingObject (C := C)

example :
    ((derivedMappingObject (C := C)).obj (.op X)).obj Y =
      SimplicialCategory.sHom
        ((cofibrantReplacement (C := C)).obj X)
        ((fibrantReplacement (C := C)).obj Y) := rfl

example (f : X ⟶ X') :
    ((derivedMappingObject (C := C)).obj (.op X')).obj Y ⟶
      ((derivedMappingObject (C := C)).obj (.op X)).obj Y :=
  derivedMappingPrecomp (C := C) f Y

example (g : Y ⟶ Y') :
    ((derivedMappingObject (C := C)).obj (.op X)).obj Y ⟶
      ((derivedMappingObject (C := C)).obj (.op X)).obj Y' :=
  derivedMappingPostcomp (C := C) X g

example :
    derivedMappingPrecomp (C := C) (𝟙 X) Y =
      𝟙 (((derivedMappingObject (C := C)).obj (.op X)).obj Y) :=
  derivedMappingPrecomp_id (C := C) X Y

example (f : X ⟶ X') (g : X' ⟶ X'') :
    derivedMappingPrecomp (C := C) (f ≫ g) Y =
      derivedMappingPrecomp (C := C) g Y ≫ derivedMappingPrecomp (C := C) f Y :=
  derivedMappingPrecomp_comp (C := C) f g Y

example :
    derivedMappingPostcomp (C := C) X (𝟙 Y) =
      𝟙 (((derivedMappingObject (C := C)).obj (.op X)).obj Y) :=
  derivedMappingPostcomp_id (C := C) X Y

example (f : Y ⟶ Y') (g : Y' ⟶ Y'') :
    derivedMappingPostcomp (C := C) X (f ≫ g) =
      derivedMappingPostcomp (C := C) X f ≫ derivedMappingPostcomp (C := C) X g :=
  derivedMappingPostcomp_comp (C := C) X f g

example (f : X ⟶ X') (g : Y ⟶ Y') :
    derivedMappingPrecomp (C := C) f Y ≫ derivedMappingPostcomp (C := C) X g =
      derivedMappingPostcomp (C := C) X' g ≫ derivedMappingPrecomp (C := C) f Y' :=
  derivedMappingPrecomp_postcomp (C := C) f g

end SymbolicUniverses

section UniverseOneZero

variable {C₁ : Type 1} [Category.{0} C₁] [ModelCategory C₁] [SimplicialCategory C₁]
variable [HasFunctorialFactorization (cofibrations C₁) (trivialFibrations C₁)]
variable [HasFunctorialFactorization (trivialCofibrations C₁) (fibrations C₁)]
variable {X Y Z : C₁}

example : C₁ᵒᵖ ⥤ C₁ ⥤ SSet := derivedMappingObject (C := C₁)

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedMappingPrecomp (C := C₁) (f ≫ g) X =
      derivedMappingPrecomp (C := C₁) g X ≫ derivedMappingPrecomp (C := C₁) f X :=
  derivedMappingPrecomp_comp (C := C₁) f g X

end UniverseOneZero

section UniverseZero

variable {C₀ : Type} [Category C₀] [ModelCategory C₀] [SimplicialCategory C₀]
variable [HasFunctorialFactorization (cofibrations C₀) (trivialFibrations C₀)]
variable [HasFunctorialFactorization (trivialCofibrations C₀) (fibrations C₀)]
variable {X Y Z : C₀}

example : C₀ᵒᵖ ⥤ C₀ ⥤ SSet := derivedMappingObject (C := C₀)

example (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedMappingPostcomp (C := C₀) X (f ≫ g) =
      derivedMappingPostcomp (C := C₀) X f ≫
        derivedMappingPostcomp (C := C₀) X g :=
  derivedMappingPostcomp_comp (C := C₀) X f g

end UniverseZero

/- The rejected outer/pointwise comparison and its transported endpoints must stay absent. -/

/-- error: Unknown identifier `simplicialSpaceOuterPointwiseHomIso` -/
#guard_msgs (error) in
#check simplicialSpaceOuterPointwiseHomIso

/-- error: Unknown identifier `simplicialSpaceOuterPointwiseHomIso_hom_projection` -/
#guard_msgs (error) in
#check simplicialSpaceOuterPointwiseHomIso_hom_projection

/-- error: Unknown identifier `simplicialSpaceOuterPointwiseHomIso_naturality_source` -/
#guard_msgs (error) in
#check simplicialSpaceOuterPointwiseHomIso_naturality_source

/-- error: Unknown identifier `simplicialSpaceOuterPointwiseHomIso_naturality_target` -/
#guard_msgs (error) in
#check simplicialSpaceOuterPointwiseHomIso_naturality_target

/-- error: Unknown identifier `outerYonedaIso` -/
#guard_msgs (error) in
#check outerYonedaIso

/-- error: Unknown identifier `outerYonedaIso_hom_evaluation` -/
#guard_msgs (error) in
#check outerYonedaIso_hom_evaluation

/-- error: Unknown identifier `outerYonedaIso_naturality_target` -/
#guard_msgs (error) in
#check outerYonedaIso_naturality_target

/-- error: Unknown identifier `outerYonedaIso_naturality_index` -/
#guard_msgs (error) in
#check outerYonedaIso_naturality_index

/-- error: Unknown identifier `outerYonedaIso_consecutiveEdge` -/
#guard_msgs (error) in
#check outerYonedaIso_consecutiveEdge

/-- error: Unknown identifier `segalTwoComparison` -/
#guard_msgs (error) in
#check segalTwoComparison

/-- error: Unknown identifier `spineTwoMappingIso` -/
#guard_msgs (error) in
#check spineTwoMappingIso

/-- error: Unknown identifier `spineTwoMappingIso_fst` -/
#guard_msgs (error) in
#check spineTwoMappingIso_fst

/-- error: Unknown identifier `spineTwoMappingIso_snd` -/
#guard_msgs (error) in
#check spineTwoMappingIso_snd

/-- error: Unknown identifier `segalTwoComparison_under_yoneda` -/
#guard_msgs (error) in
#check segalTwoComparison_under_yoneda

/-- error: Unknown identifier `completenessMappingComparison` -/
#guard_msgs (error) in
#check completenessMappingComparison

/-- error: Unknown identifier `completenessMappingComparison_naturality` -/
#guard_msgs (error) in
#check completenessMappingComparison_naturality

/-- error: Unknown identifier `completenessMappingComparison_evaluation` -/
#guard_msgs (error) in
#check completenessMappingComparison_evaluation

end HomotopicalAlgebra.DerivedMappingBasicTests
