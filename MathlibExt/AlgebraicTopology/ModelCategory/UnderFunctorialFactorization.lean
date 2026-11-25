/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.Under

/-!
# Functorial factorizations in Under categories

A functorial factorization in a category induces one in every Under category.
The intermediate object is equipped with the composite from the fixed source,
and functoriality is inherited from the chosen base factorization.
-/

set_option autoImplicit false

noncomputable section

universe v u

namespace CategoryTheory.MorphismProperty

open CategoryTheory

variable {C : Type u} [Category.{v} C] {W₁ W₂ : MorphismProperty C}

namespace FunctorialFactorizationData

/-- A functorial factorization in `C` induces a functorial factorization in
`Under S` by creating the two factor classes through the forgetful functor. -/
def under (data : FunctorialFactorizationData W₁ W₂) (S : C) :
    FunctorialFactorizationData (W₁.under (X := S)) (W₂.under (X := S)) := by
  let baseMap : {f g : CategoryTheory.Arrow (CategoryTheory.Under S)} →
      (f ⟶ g) →
      (CategoryTheory.Arrow.mk f.hom.right ⟶
        CategoryTheory.Arrow.mk g.hom.right) := fun {f g} φ ↦
    CategoryTheory.Arrow.homMk φ.left.right φ.right.right
      (congrArg CommaMorphism.right φ.w)
  let Z : CategoryTheory.Arrow (CategoryTheory.Under S) ⥤
      CategoryTheory.Under S :=
    { obj := fun f ↦ CategoryTheory.Under.mk
        (f.left.hom ≫ (data.factorizationData f.hom.right).i)
      map := fun {f g} φ ↦
        CategoryTheory.Under.homMk (data.mapZ (baseMap φ)) (by
        change (f.left.hom ≫ (data.factorizationData f.hom.right).i) ≫
          data.mapZ (baseMap φ) =
            g.left.hom ≫ (data.factorizationData g.hom.right).i
        rw [Category.assoc, data.i_mapZ, ← Category.assoc]
        change (f.left.hom ≫ φ.left.right) ≫
          (data.factorizationData g.hom.right).i =
            g.left.hom ≫ (data.factorizationData g.hom.right).i
        rw [CategoryTheory.Under.w])
      map_id := fun f ↦ by
        apply CategoryTheory.Under.UnderMorphism.ext
        change data.mapZ (baseMap (𝟙 f)) = 𝟙 _
        rw [← data.mapZ_id f.hom.right]
        congr 1
      map_comp := fun φ ψ ↦ by
        apply CategoryTheory.Under.UnderMorphism.ext
        change data.mapZ (baseMap (φ ≫ ψ)) =
          data.mapZ (baseMap φ) ≫ data.mapZ (baseMap ψ)
        rw [← data.mapZ_comp]
        congr 1 }
  let i : CategoryTheory.Arrow.leftFunc ⟶ Z :=
    { app := fun f ↦ CategoryTheory.Under.homMk
        (data.factorizationData f.hom.right).i (by rfl)
      naturality := fun _ _ φ ↦ by
        apply CategoryTheory.Under.UnderMorphism.ext
        exact (data.i_mapZ (baseMap φ)).symm }
  let p : Z ⟶ CategoryTheory.Arrow.rightFunc :=
    { app := fun f ↦ CategoryTheory.Under.homMk
        (data.factorizationData f.hom.right).p (by
          change (f.left.hom ≫ (data.factorizationData f.hom.right).i) ≫
            (data.factorizationData f.hom.right).p = f.right.hom
          rw [Category.assoc, (data.factorizationData f.hom.right).fac,
            CategoryTheory.Under.w])
      naturality := fun _ _ φ ↦ by
        apply CategoryTheory.Under.UnderMorphism.ext
        exact data.mapZ_p (baseMap φ) }
  exact
    { Z := Z
      i := i
      p := p
      fac := by
        ext f
        exact data.fac_app
      hi := fun f ↦ data.hi (CategoryTheory.Arrow.mk f.hom.right)
      hp := fun f ↦ data.hp (CategoryTheory.Arrow.mk f.hom.right) }

end FunctorialFactorizationData

/-- Functorial factorizations in the base category induce functorial
factorizations in every Under category. -/
instance (S : C) [HasFunctorialFactorization W₁ W₂] :
    HasFunctorialFactorization (W₁.under (X := S)) (W₂.under (X := S)) :=
  ⟨⟨(functorialFactorizationData W₁ W₂).under S⟩⟩

end CategoryTheory.MorphismProperty
