/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal

/-!
# Tests for the cartesian monoidal structure on CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace MathlibExtTest.CGWH.CartesianMonoidalTests

section Instance

#check CGWH.instCartesianMonoidalCategory

example : (inferInstance : CartesianMonoidalCategory CGWH.{u, v}) =
    CGWH.instCartesianMonoidalCategory := rfl

example : CGWH.instCartesianMonoidalCategory =
    (CartesianMonoidalCategory.ofHasFiniteProducts :
      CartesianMonoidalCategory CGWH.{u, v}) := rfl

example : CartesianMonoidalCategory CGWH.{0, 0} := inferInstance
example : CartesianMonoidalCategory CGWH.{1, 1} := inferInstance
example : CartesianMonoidalCategory CGWH.{0, 1} := inferInstance
example : CartesianMonoidalCategory CGWH.{1, 0} := inferInstance

end Instance

section SelectedLimits

variable (X Y : CGWH.{u, v})

example : X ⊗ Y = (X ⨯ Y) := rfl

example : CartesianMonoidalCategory.fst X Y = Limits.prod.fst := rfl

example : CartesianMonoidalCategory.snd X Y = Limits.prod.snd := rfl

example : IsLimit (BinaryFan.mk
    (CartesianMonoidalCategory.fst X Y)
    (CartesianMonoidalCategory.snd X Y)) :=
  CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y

example : (𝟙_ CGWH.{u, v}) = (⊤_ CGWH.{u, v}) := rfl

example : IsTerminal (𝟙_ CGWH.{u, v}) :=
  CartesianMonoidalCategory.isTerminalTensorUnit

end SelectedLimits

section SelectedProductIso

variable (A Y : CGWH.{u, v})

example : A ⊗ Y ≅ A ⨯ Y :=
  CGWH.tensorSelectedProductIso A Y

example : (CGWH.tensorSelectedProductIso A Y).hom ≫ Limits.prod.fst =
    CartesianMonoidalCategory.fst A Y :=
  CGWH.tensorSelectedProductIso_hom_fst A Y

example : (CGWH.tensorSelectedProductIso A Y).hom ≫ Limits.prod.snd =
    CartesianMonoidalCategory.snd A Y :=
  CGWH.tensorSelectedProductIso_hom_snd A Y

example : (CGWH.tensorSelectedProductIso A Y).inv ≫
    CartesianMonoidalCategory.fst A Y = Limits.prod.fst :=
  CGWH.tensorSelectedProductIso_inv_fst A Y

example : (CGWH.tensorSelectedProductIso A Y).inv ≫
    CartesianMonoidalCategory.snd A Y = Limits.prod.snd :=
  CGWH.tensorSelectedProductIso_inv_snd A Y

end SelectedProductIso

section CarrierEquivalence

variable (A Y : CGWH.{u, v})

example : (A ⊗ Y : CGWH.{u, v}) ≃ (A × Y) :=
  CGWH.tensorEquivProd A Y

example (z : (A ⊗ Y : CGWH.{u, v})) :
    (CGWH.tensorEquivProd A Y z).1 =
      CartesianMonoidalCategory.fst A Y z :=
  CGWH.tensorEquivProd_apply_fst A Y z

example (z : (A ⊗ Y : CGWH.{u, v})) :
    (CGWH.tensorEquivProd A Y z).2 =
      CartesianMonoidalCategory.snd A Y z :=
  CGWH.tensorEquivProd_apply_snd A Y z

example {A' Y' : CGWH.{u, v}} (f : A ⟶ A') (g : Y ⟶ Y')
    (z : (A ⊗ Y : CGWH.{u, v})) :
    CGWH.tensorEquivProd A' Y' ((f ⊗ₘ g) z) =
      (f (CGWH.tensorEquivProd A Y z).1,
        g (CGWH.tensorEquivProd A Y z).2) :=
  CGWH.tensorEquivProd_map f g z

end CarrierEquivalence

section UniverseMatrix

#check CGWH.tensorEquivProd.{0, 0}
#check CGWH.tensorEquivProd_map.{0, 0}
#check CGWH.tensorEquivProd.{1, 1}
#check CGWH.tensorEquivProd_map.{1, 1}
#check CGWH.tensorEquivProd.{0, 1}
#check CGWH.tensorEquivProd_map.{0, 1}
#check CGWH.tensorEquivProd.{1, 0}
#check CGWH.tensorEquivProd_map.{1, 0}
#check CGWH.tensorEquivProd.{u, v}
#check CGWH.tensorEquivProd_map.{u, v}

#check CGWH.tensorSelectedProductIso.{0, 0}
#check CGWH.tensorSelectedProductIso.{1, 1}
#check CGWH.tensorSelectedProductIso.{0, 1}
#check CGWH.tensorSelectedProductIso.{1, 0}

#check CGWH.tensorSelectedProductIso_hom_fst.{0, 0}
#check CGWH.tensorSelectedProductIso_hom_fst.{1, 1}
#check CGWH.tensorSelectedProductIso_hom_fst.{0, 1}
#check CGWH.tensorSelectedProductIso_hom_fst.{1, 0}

#check CGWH.tensorSelectedProductIso_hom_snd.{0, 0}
#check CGWH.tensorSelectedProductIso_hom_snd.{1, 1}
#check CGWH.tensorSelectedProductIso_hom_snd.{0, 1}
#check CGWH.tensorSelectedProductIso_hom_snd.{1, 0}

#check CGWH.tensorSelectedProductIso_inv_fst.{0, 0}
#check CGWH.tensorSelectedProductIso_inv_fst.{1, 1}
#check CGWH.tensorSelectedProductIso_inv_fst.{0, 1}
#check CGWH.tensorSelectedProductIso_inv_fst.{1, 0}

#check CGWH.tensorSelectedProductIso_inv_snd.{0, 0}
#check CGWH.tensorSelectedProductIso_inv_snd.{1, 1}
#check CGWH.tensorSelectedProductIso_inv_snd.{0, 1}
#check CGWH.tensorSelectedProductIso_inv_snd.{1, 0}

#check CGWH.tensorSelectedProductIso_hom_fst_assoc
#check CGWH.tensorSelectedProductIso_hom_snd_assoc
#check CGWH.tensorSelectedProductIso_inv_fst_assoc
#check CGWH.tensorSelectedProductIso_inv_snd_assoc

end UniverseMatrix

section NoRawProductClaim

variable (X Y : CGWH.{u, v})

example : True := by
  fail_if_success
    have : CGWH.cgwhToTop.obj (X ⊗ Y) =
        TopCat.of (↥(CGWH.cgwhToTop.obj X) ×
          ↥(CGWH.cgwhToTop.obj Y)) := rfl
  trivial

end NoRawProductClaim

section NoSecondDictionary

attribute [-instance] CGWH.instCartesianMonoidalCategory

example : HasProducts.{v} CGWH.{u, v} := inferInstance
example : HasFiniteProducts CGWH.{u, v} := inferInstance

example : True := by
  fail_if_success
    let _ : CartesianMonoidalCategory CGWH.{u, v} := inferInstance
  trivial

end NoSecondDictionary

section NoGlobalBraiding

example : CartesianMonoidalCategory CGWH.{u, v} := inferInstance

example : True := by
  fail_if_success
    let _ : BraidedCategory CGWH.{u, v} := inferInstance
  trivial

end NoGlobalBraiding

#guard_msgs (error, substring := true) in
#check CGWH.point

#print axioms CGWH.instCartesianMonoidalCategory
#print axioms CGWH.tensorEquivProd
#print axioms CGWH.tensorEquivProd_apply_fst
#print axioms CGWH.tensorEquivProd_apply_snd
#print axioms CGWH.tensorEquivProd_map
#print axioms CGWH.tensorSelectedProductIso
#print axioms CGWH.tensorSelectedProductIso_hom_fst
#print axioms CGWH.tensorSelectedProductIso_hom_snd
#print axioms CGWH.tensorSelectedProductIso_inv_fst
#print axioms CGWH.tensorSelectedProductIso_inv_snd

end MathlibExtTest.CGWH.CartesianMonoidalTests
