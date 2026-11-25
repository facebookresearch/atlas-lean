/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.Replacement

/-!
# Chosen derived mapping objects

This file packages the outer simplicial mapping object
`sHom (cofibrantReplacement.obj X) (fibrantReplacement.obj Y)` and its variance maps.

The construction uses the chosen functorial replacements. It is not the pointwise enriched end for
a functor category, and no replacement-independence or homotopical-invariance claim is made here.

Adapted from the Formal-Math development by Tsutomu Okano and Avocado.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]
variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- The chosen outer simplicial mapping bifunctor `sHom (Q X) (R Y)`. -/
noncomputable def derivedMappingObject : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  (cofibrantReplacement (C := C)).op ⋙
    SimplicialCategory.sHomFunctor C ⋙
      (Functor.whiskeringLeft C C SSet.{v}).obj (fibrantReplacement (C := C))

/-- Precomposition in the source variable of the chosen derived mapping object. -/
noncomputable def derivedMappingPrecomp {X Y : C} (f : X ⟶ Y) (Z : C) :
    ((derivedMappingObject (C := C)).obj (.op Y)).obj Z ⟶
      ((derivedMappingObject (C := C)).obj (.op X)).obj Z :=
  ((derivedMappingObject (C := C)).map f.op).app Z

/-- Postcomposition in the target variable of the chosen derived mapping object. -/
noncomputable def derivedMappingPostcomp (X : C) {Y Z : C} (g : Y ⟶ Z) :
    ((derivedMappingObject (C := C)).obj (.op X)).obj Y ⟶
      ((derivedMappingObject (C := C)).obj (.op X)).obj Z :=
  ((derivedMappingObject (C := C)).obj (.op X)).map g

/-- In the raw simplicial enrichment, source precomposition uses the
cofibrant replacement of the original arrow. -/
theorem derivedMappingPrecomp_eq_whisker {X Y : C} (f : X ⟶ Y) (Z : C) :
    derivedMappingPrecomp f Z =
      eHomWhiskerRight SSet (cofibrantReplacement.map f) (fibrantReplacement.obj Z) := rfl

/-- In the raw simplicial enrichment, target postcomposition uses the
fibrant replacement of the original arrow. -/
theorem derivedMappingPostcomp_eq_whisker (X : C) {Y Z : C} (g : Y ⟶ Z) :
    derivedMappingPostcomp X g =
      eHomWhiskerLeft SSet (cofibrantReplacement.obj X) (fibrantReplacement.map g) := rfl

/-- Precomposition by an identity is the identity. -/
@[simp]
theorem derivedMappingPrecomp_id (X Z : C) :
    derivedMappingPrecomp (C := C) (𝟙 X) Z =
      𝟙 (((derivedMappingObject (C := C)).obj (.op X)).obj Z) := by
  simp [derivedMappingPrecomp]

/-- Precomposition reverses composition in the source variable. -/
@[simp]
theorem derivedMappingPrecomp_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (W : C) :
    derivedMappingPrecomp (C := C) (f ≫ g) W =
      derivedMappingPrecomp (C := C) g W ≫ derivedMappingPrecomp (C := C) f W := by
  simp [derivedMappingPrecomp]

/-- Postcomposition by an identity is the identity. -/
@[simp]
theorem derivedMappingPostcomp_id (X Y : C) :
    derivedMappingPostcomp (C := C) X (𝟙 Y) =
      𝟙 (((derivedMappingObject (C := C)).obj (.op X)).obj Y) := by
  simp [derivedMappingPostcomp]

/-- Postcomposition preserves composition in the target variable. -/
@[simp]
theorem derivedMappingPostcomp_comp (X : C) {Y Z W : C} (f : Y ⟶ Z) (g : Z ⟶ W) :
    derivedMappingPostcomp (C := C) X (f ≫ g) =
      derivedMappingPostcomp (C := C) X f ≫ derivedMappingPostcomp (C := C) X g := by
  simp [derivedMappingPostcomp]

/-- Source precomposition and target postcomposition commute. -/
theorem derivedMappingPrecomp_postcomp {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    derivedMappingPrecomp (C := C) f Y ≫ derivedMappingPostcomp (C := C) X g =
      derivedMappingPostcomp (C := C) X' g ≫ derivedMappingPrecomp (C := C) f Y' :=
  (((derivedMappingObject (C := C)).map f.op).naturality g).symm

end HomotopicalAlgebra
