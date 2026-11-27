/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct

/-!
# Tests for orthogonality and pushout-products
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v₁ u₁ v₂ u₂ v u

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.MorphismProperty

#check strictMap_rlp_eq_inverseImage_rlp
#check pushoutProduct_mem_rlp_llp

section StrictImage

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (P : MorphismProperty C) (L : C ⥤ D) (R : D ⥤ C)
variable (adj : L ⊣ R)

example : (P.strictMap L).rlp = P.rlp.inverseImage R :=
  strictMap_rlp_eq_inverseImage_rlp P L R adj

example (_P : MorphismProperty C) (_L : C ⥤ D) : True := by
  fail_if_success
    let _ : (_P.strictMap _L).RespectsIso := inferInstance
  trivial

end StrictImage

section PushoutProduct

variable {E : Type u} [Category.{v} E]
variable [HasPushouts E] [HasPullbacks E]
variable [MonoidalCategory E] [MonoidalClosed E] [BraidedCategory E]

variable (A B K : MorphismProperty E)
variable
  (hfree : ∀ ⦃X Y W Z : E⦄ (a : X ⟶ Y), A a →
    ∀ (b : W ⟶ Z), B b →
      K.rlp.llp ((Arrow.mk a □ Arrow.mk b).hom))

example {X Y W Z : E} {i : X ⟶ Y} {j : W ⟶ Z}
    (hi : A.rlp.llp i) (hj : B.rlp.llp j) :
    K.rlp.llp ((Arrow.mk i □ Arrow.mk j).hom) :=
  pushoutProduct_mem_rlp_llp A B K hfree hi hj

-- The independent right-first nesting order guards both adjunction
-- orientations used by the public left-first proof.
example {X Y W Z : E} {i : X ⟶ Y} {j : W ⟶ Z}
    (hi : A.rlp.llp i) (hj : B.rlp.llp j) :
    K.rlp.llp ((Arrow.mk i □ Arrow.mk j).hom) := by
  intro P Q p hp
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff.mpr
  apply hj
  intro W' Z' b hb
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff.mp
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.mpr
  apply hi
  intro X' Y' a ha
  apply MonoidalCategory.Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.mp
  exact hfree a ha b hb p hp

variable (Cof Triv : MorphismProperty E)
variable
  (hcc : ∀ ⦃X Y W Z : E⦄ (a : X ⟶ Y), Cof a →
    ∀ (b : W ⟶ Z), Cof b →
      Cof.rlp.llp ((Arrow.mk a □ Arrow.mk b).hom))
  (htc : ∀ ⦃X Y W Z : E⦄ (a : X ⟶ Y), Triv a →
    ∀ (b : W ⟶ Z), Cof b →
      Triv.rlp.llp ((Arrow.mk a □ Arrow.mk b).hom))
  (hct : ∀ ⦃X Y W Z : E⦄ (a : X ⟶ Y), Cof a →
    ∀ (b : W ⟶ Z), Triv b →
      Triv.rlp.llp ((Arrow.mk a □ Arrow.mk b).hom))

example {X Y W Z : E} {i : X ⟶ Y} {j : W ⟶ Z}
    (hiC : Cof.rlp.llp i) (hiT : Triv.rlp.llp i)
    (hjC : Cof.rlp.llp j) (hjT : Triv.rlp.llp j) :
    Cof.rlp.llp ((Arrow.mk i □ Arrow.mk j).hom) ∧
      Triv.rlp.llp ((Arrow.mk i □ Arrow.mk j).hom) ∧
      Triv.rlp.llp ((Arrow.mk i □ Arrow.mk j).hom) := by
  exact ⟨pushoutProduct_mem_rlp_llp Cof Cof Cof hcc hiC hjC,
    pushoutProduct_mem_rlp_llp Triv Cof Triv htc hiT hjC,
    pushoutProduct_mem_rlp_llp Cof Triv Triv hct hiC hjT⟩

end PushoutProduct

#print axioms strictMap_rlp_eq_inverseImage_rlp
#print axioms pushoutProduct_mem_rlp_llp

end CategoryTheory.MorphismProperty
