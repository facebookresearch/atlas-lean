/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Monoidal.Mod.RelativeTensor

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe v u

namespace MathlibExtTest.CategoryTheory.Mod.RelativeTensor

section PublicSurface

#check Mod.relativeTensor
#check Mod.relativeTensorUnit
#check Mod.relativeTensorπ
#check Mod.relativeTensorπ_balance
#check Mod.relativeTensorDesc
#check Mod.relativeTensorDesc_π
#check Mod.relativeTensor_hom_ext
#check Mod.relativeTensorMap
#check Mod.relativeTensorMap_π
#check Mod.relativeTensorAssociator
#check Mod.relativeTensorAssociator_hom_π
#check Mod.relativeTensorBraiding
#check Mod.relativeTensorBraiding_hom_π
#check Mod.relativeTensorLeftUnitor_hom_π
#check Mod.relativeTensorRightUnitor_hom_π
#check Mod.relativeTensorSymmetry
#check Mod.instMonoidalCategory
#check Mod.instSymmetricCategory

#check @Mod.relativeTensor.{1, 1}
#check @Mod.relativeTensor.{0, 0}
#check @Mod.relativeTensorUnit.{1, 1}
#check @Mod.relativeTensorUnit.{0, 0}
#check @Mod.relativeTensorπ.{1, 1}
#check @Mod.relativeTensorπ.{0, 0}
#check @Mod.relativeTensorDesc.{1, 1}
#check @Mod.relativeTensorDesc.{0, 0}
#check @Mod.relativeTensorMap.{1, 1}
#check @Mod.relativeTensorMap.{0, 0}
#check @Mod.relativeTensorMap_π.{1, 1}
#check @Mod.relativeTensorMap_π.{0, 0}
#check @Mod.relativeTensorAssociator.{1, 1}
#check @Mod.relativeTensorAssociator.{0, 0}
#check @Mod.relativeTensorAssociator_hom_π.{1, 1}
#check @Mod.relativeTensorAssociator_hom_π.{0, 0}
#check @Mod.relativeTensorBraiding.{1, 1}
#check @Mod.relativeTensorBraiding.{0, 0}
#check @Mod.relativeTensorBraiding_hom_π.{1, 1}
#check @Mod.relativeTensorBraiding_hom_π.{0, 0}
#check @Mod.relativeTensorLeftUnitor_hom_π.{1, 1}
#check @Mod.relativeTensorLeftUnitor_hom_π.{0, 0}
#check @Mod.relativeTensorRightUnitor_hom_π.{1, 1}
#check @Mod.relativeTensorRightUnitor_hom_π.{0, 0}
#check @Mod.instMonoidalCategory.{1, 1}
#check @Mod.instMonoidalCategory.{0, 0}
#check @Mod.instSymmetricCategory.{1, 1}
#check @Mod.instSymmetricCategory.{0, 0}

end PublicSurface

section BalancedQuotient

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C]
variable (A : CommMon C)
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

example (M N : Mod C A.X) :
    M.X ⊗ N.X ⟶ ((Mod.relativeTensor A).obj M).obj N |>.X :=
  Mod.relativeTensorπ A M N

example (M N : Mod C A.X) :
    ((β_ M.X A.X).hom ≫ M.mod.smul) ▷ N.X ≫
        Mod.relativeTensorπ A M N =
      (α_ M.X A.X N.X).hom ≫ (M.X ◁ N.mod.smul) ≫
        Mod.relativeTensorπ A M N :=
  Mod.relativeTensorπ_balance A M N

example (M N P : Mod C A.X) (f : M.X ⊗ N.X ⟶ P.X)
    (hbal : ((β_ M.X A.X).hom ≫ M.mod.smul) ▷ N.X ≫ f =
      (α_ M.X A.X N.X).hom ≫ (M.X ◁ N.mod.smul) ≫ f)
    (hlin : (α_ A.X M.X N.X).inv ≫ (M.mod.smul ▷ N.X) ≫ f =
      (A.X ◁ f) ≫ P.mod.smul) :
    ((Mod.relativeTensor A).obj M).obj N ⟶ P :=
  Mod.relativeTensorDesc A M N P f hbal hlin

example (M N P : Mod C A.X) (f : M.X ⊗ N.X ⟶ P.X)
    (hbal : ((β_ M.X A.X).hom ≫ M.mod.smul) ▷ N.X ≫ f =
      (α_ M.X A.X N.X).hom ≫ (M.X ◁ N.mod.smul) ≫ f)
    (hlin : (α_ A.X M.X N.X).inv ≫ (M.mod.smul ▷ N.X) ≫ f =
      (A.X ◁ f) ≫ P.mod.smul) :
    Mod.relativeTensorπ A M N ≫
      (Mod.relativeTensorDesc A M N P f hbal hlin).hom = f :=
  Mod.relativeTensorDesc_π A M N P f hbal hlin

example (M N P : Mod C A.X)
    (f g : ((Mod.relativeTensor A).obj M).obj N ⟶ P)
    (h : Mod.relativeTensorπ A M N ≫ f.hom =
      Mod.relativeTensorπ A M N ≫ g.hom) : f = g :=
  Mod.relativeTensor_hom_ext A M N P f g h

example : Mod.relativeTensorUnit A = Mod.regular A.X := rfl

end BalancedQuotient

section BraidedMapAndCoherence

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C]
variable (A : CommMon C)
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

local instance : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A

example (M N : Mod C A.X) : M ⊗ N = ((Mod.relativeTensor A).obj M).obj N := rfl

example : (𝟙_ (Mod C A.X)) = Mod.relativeTensorUnit A := rfl

example (M : Mod C A.X) :
    Mod.relativeTensorπ A (Mod.relativeTensorUnit A) M ≫
        (λ_ M).hom.hom = M.mod.smul :=
  Mod.relativeTensorLeftUnitor_hom_π A M

example (M : Mod C A.X) :
    Mod.relativeTensorπ A M (Mod.relativeTensorUnit A) ≫
        (ρ_ M).hom.hom = (β_ M.X A.X).hom ≫ M.mod.smul :=
  Mod.relativeTensorRightUnitor_hom_π A M

example {M M' N N' : Mod C A.X} (f : M ⟶ M') (g : N ⟶ N') :
    f ⊗ₘ g = Mod.relativeTensorMap A f g := rfl

example {M M' N N' : Mod C A.X} (f : M ⟶ M') (g : N ⟶ N') :
    Mod.relativeTensorπ A M N ≫ (Mod.relativeTensorMap A f g).hom =
      (f.hom ⊗ₘ g.hom) ≫ Mod.relativeTensorπ A M' N' :=
  Mod.relativeTensorMap_π A f g

example (M N P : Mod C A.X) :
    α_ M N P = Mod.relativeTensorAssociator A M N P := rfl

example (M N P : Mod C A.X) :
    (Mod.relativeTensorπ A M N ▷ P.X) ≫
        Mod.relativeTensorπ A (((Mod.relativeTensor A).obj M).obj N) P ≫
          (Mod.relativeTensorAssociator A M N P).hom.hom =
      (α_ M.X N.X P.X).hom ≫
        (M.X ◁ Mod.relativeTensorπ A N P) ≫
          Mod.relativeTensorπ A M (((Mod.relativeTensor A).obj N).obj P) :=
  Mod.relativeTensorAssociator_hom_π A M N P

example (M N : Mod C A.X) : 𝟙 M ⊗ₘ 𝟙 N = 𝟙 (M ⊗ N) := by simp

example {M₁ M₂ M₃ N₁ N₂ N₃ : Mod C A.X}
    (f₁ : M₁ ⟶ M₂) (g₁ : M₂ ⟶ M₃)
    (f₂ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) =
      (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) := by simp

example {M M' N N' : Mod C A.X} (f : M ⟶ M') (g : N ⟶ N') :
    M ◁ g ≫ f ▷ N' = f ▷ N ≫ M' ◁ g :=
  whisker_exchange f g

example {M₁ M₂ M₃ N₁ N₂ N₃ : Mod C A.X}
    (f₁ : M₁ ⟶ N₁) (f₂ : M₂ ⟶ N₂) (f₃ : M₃ ⟶ N₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ N₁ N₂ N₃).hom =
      (α_ M₁ M₂ M₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) :=
  associator_naturality f₁ f₂ f₃

example (W X Y Z : Mod C A.X) :
    (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫
        W ◁ (α_ X Y Z).hom =
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom :=
  pentagon W X Y Z

example (M N : Mod C A.X) :
    (α_ M (𝟙_ (Mod C A.X)) N).hom ≫ M ◁ (λ_ N).hom =
      (ρ_ M).hom ▷ N :=
  triangle M N

example (M N P : Mod C A.X) :
    (Mod.relativeTensorAssociator A M N P).hom ≫
      (Mod.relativeTensorAssociator A M N P).inv =
        𝟙 ((M ⊗ N) ⊗ P) :=
  (Mod.relativeTensorAssociator A M N P).hom_inv_id

example (M N P : Mod C A.X) :
    (Mod.relativeTensorAssociator A M N P).inv ≫
      (Mod.relativeTensorAssociator A M N P).hom =
        𝟙 (M ⊗ (N ⊗ P)) :=
  (Mod.relativeTensorAssociator A M N P).inv_hom_id

example {M N : Mod C A.X} (f : M ⟶ N) :
    (𝟙_ (Mod C A.X)) ◁ f ≫ (λ_ N).hom = (λ_ M).hom ≫ f :=
  leftUnitor_naturality f

example {M N : Mod C A.X} (f : M ⟶ N) :
    f ▷ (𝟙_ (Mod C A.X)) ≫ (ρ_ N).hom = (ρ_ M).hom ≫ f :=
  rightUnitor_naturality f

end BraidedMapAndCoherence

section SymmetricExtension

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [SymmetricCategory C]
variable (A : CommMon C)
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

local instance : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
local instance : SymmetricCategory (Mod C A.X) := Mod.instSymmetricCategory A

example (M N : Mod C A.X) :
    β_ M N = Mod.relativeTensorBraiding A M N := rfl

example (M N : Mod C A.X) :
    Mod.relativeTensorπ A M N ≫
        (Mod.relativeTensorBraiding A M N).hom.hom =
      (β_ M.X N.X).hom ≫ Mod.relativeTensorπ A N M :=
  Mod.relativeTensorBraiding_hom_π A M N

example {M M' N : Mod C A.X} (f : M ⟶ M') :
    f ▷ N ≫ (β_ M' N).hom = (β_ M N).hom ≫ N ◁ f :=
  BraidedCategory.braiding_naturality_left f N

example {M N N' : Mod C A.X} (g : N ⟶ N') :
    M ◁ g ≫ (β_ M N').hom = (β_ M N).hom ≫ g ▷ M :=
  BraidedCategory.braiding_naturality_right M g

example (M N P : Mod C A.X) :
    (α_ M N P).hom ≫ (β_ M (N ⊗ P)).hom ≫ (α_ N P M).hom =
      ((β_ M N).hom ▷ P) ≫ (α_ N M P).hom ≫
        (N ◁ (β_ M P).hom) :=
  BraidedCategory.hexagon_forward M N P

example (M N P : Mod C A.X) :
    (α_ M N P).inv ≫ (β_ (M ⊗ N) P).hom ≫ (α_ P M N).inv =
      (M ◁ (β_ N P).hom) ≫ (α_ M P N).inv ≫
        ((β_ M P).hom ▷ N) :=
  BraidedCategory.hexagon_reverse M N P

example (M N : Mod C A.X) :
    (β_ M N).hom ≫ (β_ N M).hom = 𝟙 (M ⊗ N) :=
  Mod.relativeTensorSymmetry A M N

example (M N : Mod C A.X) :
    (Mod.relativeTensorBraiding A M N).hom ≫
      (Mod.relativeTensorBraiding A M N).inv = 𝟙 (M ⊗ N) :=
  (Mod.relativeTensorBraiding A M N).hom_inv_id

example (M N : Mod C A.X) :
    (Mod.relativeTensorBraiding A M N).inv ≫
      (Mod.relativeTensorBraiding A M N).hom = 𝟙 (N ⊗ M) :=
  (Mod.relativeTensorBraiding A M N).inv_hom_id

example (M N : Mod C A.X) :
    (β_ M N).hom = (β_ N M).inv :=
  SymmetricCategory.braiding_swap_eq_inv_braiding N M

end SymmetricExtension

section InstanceIsolation

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C]

example (_A : CommMon C) : True := by
  fail_if_success
    let _ : MonoidalCategory (Mod C _A.X) := inferInstance
  trivial

variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

example (A B : CommMon C) (M : Mod C A.X) (N : Mod C B.X) : True := by
  let _ : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  let _ : MonoidalCategory (Mod C B.X) := Mod.instMonoidalCategory B
  fail_if_success
    let _ : SymmetricCategory (Mod C A.X) := inferInstance
  fail_if_success
    let _ : SymmetricCategory (Mod C B.X) := inferInstance
  have _ := M ⊗ M
  have _ := N ⊗ N
  trivial

end InstanceIsolation

section SymmetricInstanceIsolation

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [SymmetricCategory C]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

example (A B : CommMon C) (M : Mod C A.X) (N : Mod C B.X) : True := by
  let _ : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  let _ : SymmetricCategory (Mod C A.X) := Mod.instSymmetricCategory A
  let _ : MonoidalCategory (Mod C B.X) := Mod.instMonoidalCategory B
  let _ : SymmetricCategory (Mod C B.X) := Mod.instSymmetricCategory B
  have _ := (β_ M M).hom
  have _ := (β_ N N).hom
  trivial

end SymmetricInstanceIsolation

section MissingPremises

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C]
variable (A : CommMon C)

example : True := by
  fail_if_success
    let _ : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
  trivial

end MissingPremises

section PrivateAndNonclaims

#guard_msgs (error, substring := true) in
#check Mod.rightSmul
#guard_msgs (error, substring := true) in
#check Mod.rightSmul_one
#guard_msgs (error, substring := true) in
#check Mod.rightSmul_assoc
#guard_msgs (error, substring := true) in
#check Mod.smul_rightSmul
#guard_msgs (error, substring := true) in
#check Mod.toBimod
#guard_msgs (error, substring := true) in
#check Mod.toBimodMap
#guard_msgs (error, substring := true) in
#check Mod.regularBimodIso
#guard_msgs (error, substring := true) in
#check Mod.tensorBimodCanonical
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorWhiskerLeft
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorWhiskerRight
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorWhiskerLeft_π
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorWhiskerRight_π
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorLeftUnitor
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorRightUnitor
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorLeftUnitor_π
#guard_msgs (error, substring := true) in
#check Mod.relativeTensorRightUnitor_π

#guard_msgs (error, substring := true) in
#check Mod.homModuleObj
#guard_msgs (error, substring := true) in
#check Mod.internalHomPre
#guard_msgs (error, substring := true) in
#check Mod.internalHomPost
#guard_msgs (error, substring := true) in
#check Mod.internalHomOfEqualizer
#guard_msgs (error, substring := true) in
#check Mod.evaluation
#guard_msgs (error, substring := true) in
#check Mod.coevaluation
#guard_msgs (error, substring := true) in
#check Mod.instMonoidalClosed

end PrivateAndNonclaims

#print axioms Mod.relativeTensor
#print axioms Mod.relativeTensorUnit
#print axioms Mod.relativeTensorπ
#print axioms Mod.relativeTensorπ_balance
#print axioms Mod.relativeTensorDesc
#print axioms Mod.relativeTensorDesc_π
#print axioms Mod.relativeTensor_hom_ext
#print axioms Mod.relativeTensorMap
#print axioms Mod.relativeTensorMap_π
#print axioms Mod.relativeTensorAssociator
#print axioms Mod.relativeTensorAssociator_hom_π
#print axioms Mod.relativeTensorBraiding
#print axioms Mod.relativeTensorBraiding_hom_π
#print axioms Mod.relativeTensorLeftUnitor_hom_π
#print axioms Mod.relativeTensorRightUnitor_hom_π
#print axioms Mod.relativeTensorSymmetry
#print axioms Mod.instMonoidalCategory
#print axioms Mod.instSymmetricCategory

end MathlibExtTest.CategoryTheory.Mod.RelativeTensor
