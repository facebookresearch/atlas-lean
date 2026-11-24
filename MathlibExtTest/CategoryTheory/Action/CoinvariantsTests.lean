/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Action.Coinvariants
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.CategoryTheory.Limits.Types.Coequalizers

set_option autoImplicit false
noncomputable section

universe v u wH wE wG

open CategoryTheory CategoryTheory.Limits CategoryTheory.ActionCategory

namespace FinBijCoinvariantsTests

#check @coefficientDiagram
#check @coequalizerCoefficientIsColimit
#check @coefficientColimitIso
#check @coefficientColimitIso_generator
#check @coefficientColimitIso_naturality
#check @inverseRightMulAction
#check @inverseRightIndexEquiv
#check @inverseRightLeftAut
#check @inverseRightColimitIso_left
#check @balancedCoefficientCoforkIsColimit
#check @balancedCoefficientIso
#check @balancedCoefficientIso_generator

section Monoid

variable {C : Type u} [Category.{v} C]
variable (H E : Type) [Monoid H] [MulAction H E]
variable (Z : C) (rho : H →* Aut Z)

variable [HasCoproduct (fun _ : E => Z)] [HasCoproduct (fun _ : H × E => Z)]
variable [HasCoequalizer (coefficientSource H E Z)
  (coefficientTarget H E Z ((Aut.toEnd (X := Z)).comp rho))]

example : IsColimit (coequalizerCoefficientCocone H E Z ((Aut.toEnd (X := Z)).comp rho)) :=
  coequalizerCoefficientIsColimit H E Z ((Aut.toEnd (X := Z)).comp rho)

example [HasColimit (coefficientDiagram H E Z ((Aut.toEnd (X := Z)).comp rho))] :
    colimit (coefficientDiagram H E Z ((Aut.toEnd (X := Z)).comp rho)) ≅
      coequalizer (coefficientSource H E Z)
        (coefficientTarget H E Z ((Aut.toEnd (X := Z)).comp rho)) :=
  coefficientColimitIso H E Z ((Aut.toEnd (X := Z)).comp rho)

end Monoid

section InverseRight

variable {C : Type u} [Category.{v} C]
variable (H G : Type) [Monoid H] [Group G]
variable (Z : C) (rho : H →* Aut Z) (iota : H →* G)

variable [HasCoproduct (fun _ : G => Z)] [HasCoproduct (fun _ : H × G => Z)]
variable [HasCoequalizer (coefficientSource H G Z)
  (inverseRightCoefficientTarget H G Z ((Aut.toEnd (X := Z)).comp rho) iota)]

example (k g : G) :
    inverseRightGenerator H G Z ((Aut.toEnd (X := Z)).comp rho) iota g ≫
      (inverseRightLeftAut H G Z ((Aut.toEnd (X := Z)).comp rho) iota k).asIso.hom =
        inverseRightGenerator H G Z ((Aut.toEnd (X := Z)).comp rho) iota (k * g) :=
  inverseRightLeftMap_generator H G Z ((Aut.toEnd (X := Z)).comp rho) iota k g

example (k l : G) :
    (inverseRightLeftAut H G Z ((Aut.toEnd (X := Z)).comp rho) iota (k * l)).asIso.hom =
      (inverseRightLeftAut H G Z ((Aut.toEnd (X := Z)).comp rho) iota l).asIso.hom ≫
        (inverseRightLeftAut H G Z ((Aut.toEnd (X := Z)).comp rho) iota k).asIso.hom :=
  inverseRightLeftMap_mul H G Z ((Aut.toEnd (X := Z)).comp rho) iota k l

example (g : G) (a : H) :
    inverseRightIndexEquiv H G iota (g, a) = (a, g * iota a) := rfl

example (a : H) (g : G) :
    (inverseRightIndexEquiv H G iota).symm (a, g) = (g * (iota a)⁻¹, a) := rfl

example [HasColimit
    (inverseRightCoefficientDiagram H G Z ((Aut.toEnd (X := Z)).comp rho) iota)] (k : G) :
    inverseRightLeftColimitMap H G Z ((Aut.toEnd (X := Z)).comp rho) iota k ≫
        (inverseRightColimitIso H G Z ((Aut.toEnd (X := Z)).comp rho) iota).hom =
      (inverseRightColimitIso H G Z ((Aut.toEnd (X := Z)).comp rho) iota).hom ≫
        inverseRightLeftMap H G Z ((Aut.toEnd (X := Z)).comp rho) iota k :=
  inverseRightColimitIso_left H G Z ((Aut.toEnd (X := Z)).comp rho) iota k

variable [HasCoproduct (fun _ : G × H => Z)]
variable [HasCoequalizer (balancedGroupArrow H G Z iota)
  (balancedCoefficientArrow H G Z ((Aut.toEnd (X := Z)).comp rho))]

example : inverseRightCoinvariants H G Z ((Aut.toEnd (X := Z)).comp rho) iota ≅
    coequalizer (balancedGroupArrow H G Z iota)
      (balancedCoefficientArrow H G Z ((Aut.toEnd (X := Z)).comp rho)) :=
  balancedCoefficientIso H G Z ((Aut.toEnd (X := Z)).comp rho) iota

end InverseRight

section IndependentUniverses

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (E : Type wE) [Monoid H] [MulAction H E]
variable (Z : C) (rho : H →* End Z)
variable [HasCoproduct (fun _ : E => Z)] [HasCoproduct (fun _ : H × E => Z)]
variable [HasCoequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho)]

example : IsColimit (coequalizerCoefficientCocone H E Z rho) :=
  coequalizerCoefficientIsColimit H E Z rho

example [HasColimit (coefficientDiagram H E Z rho)] :
    colimit (coefficientDiagram H E Z rho) ≅
      coequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho) :=
  coefficientColimitIso H E Z rho

end IndependentUniverses

section IndependentTargetGroup

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (G : Type wG) [Monoid H] [Group G]
variable (Z : C) (rho : H →* End Z) (iota : H →* G)
variable [HasCoproduct (fun _ : G => Z)] [HasCoproduct (fun _ : H × G => Z)]
variable [HasCoequalizer (coefficientSource H G Z)
  (inverseRightCoefficientTarget H G Z rho iota)]

example : G →* Aut (inverseRightCoinvariants H G Z rho iota) :=
  inverseRightLeftAut H G Z rho iota

example (k g : G) :
    inverseRightGenerator H G Z rho iota g ≫
      (inverseRightLeftAut H G Z rho iota k).asIso.hom =
        inverseRightGenerator H G Z rho iota (k * g) :=
  inverseRightLeftMap_generator H G Z rho iota k g

end IndependentTargetGroup


section EndCoefficientNaturality

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (E : Type wE) [Monoid H] [MulAction H E]
variable (Z Z' : C) (rho : H →* End Z) (rho' : H →* End Z')
variable (f : Z ⟶ Z') (hf : ∀ a : H, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
variable [HasCoproduct (fun _ : E => Z)] [HasCoproduct (fun _ : H × E => Z)]
variable [HasCoproduct (fun _ : E => Z')] [HasCoproduct (fun _ : H × E => Z')]
variable [HasCoequalizer (coefficientSource H E Z) (coefficientTarget H E Z rho)]
variable [HasCoequalizer (coefficientSource H E Z') (coefficientTarget H E Z' rho')]

include hf

example (e : E) :
    coefficientGenerator H E Z rho e ≫ coefficientCoequalizerMap H E Z Z' rho rho' f hf =
      f ≫ coefficientGenerator H E Z' rho' e :=
  coefficientCoequalizerMap_generator H E Z Z' rho rho' f hf e

example [HasColimit (coefficientDiagram H E Z rho)]
    [HasColimit (coefficientDiagram H E Z' rho')] :
    colimMap (coefficientNatTrans H E Z Z' rho rho' f hf) ≫
        (coefficientColimitIso H E Z' rho').hom =
      (coefficientColimitIso H E Z rho).hom ≫
        coefficientCoequalizerMap H E Z Z' rho rho' f hf :=
  coefficientColimitIso_naturality H E Z Z' rho rho' f hf

end EndCoefficientNaturality

section AutCoefficientMaps

variable {C : Type u} [Category.{v} C]
variable (H : Type wH) (E : Type wE) [Monoid H] [MulAction H E]
variable (Z : C) (rho : H →* Aut Z)

example {x y : ActionCategory H E} (a : x ⟶ y) :
    (coefficientDiagram H E Z ((Aut.toEnd (X := Z)).comp rho)).map a = (rho a.hom).asIso.hom := rfl

end AutCoefficientMaps

section NoninvertibleCoefficient

private def zeroEnd : End (ℕ : Type) := End.of (TypeCat.ofHom (fun _ => 0))

private def zeroPowerAction : Multiplicative ℕ →* End (ℕ : Type) :=
  powersHom (End (ℕ : Type)) zeroEnd

@[instance_reducible]
private def trivialIndexAction : MulAction (Multiplicative ℕ) PUnit where
  smul _ e := e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] trivialIndexAction

private theorem zeroPowerAction_one :
    zeroPowerAction (Multiplicative.ofAdd 1) = zeroEnd := by
  change zeroEnd ^ 1 = zeroEnd
  exact pow_one zeroEnd

private theorem zeroEnd_not_isIso : ¬ IsIso zeroEnd.asHom := by
  intro h
  have hs := ((CategoryTheory.isIso_iff_bijective zeroEnd.asHom).1 h).2
  obtain ⟨n, hn⟩ := hs 1
  have : (0 : ℕ) = 1 := hn
  exact Nat.zero_ne_one this

example : ¬ IsIso (zeroPowerAction (Multiplicative.ofAdd 1)).asHom := by
  rw [zeroPowerAction_one]
  exact zeroEnd_not_isIso

example :
    (coefficientDiagram (Multiplicative ℕ) PUnit (ℕ : Type) zeroPowerAction).map
      (show (PUnit.unit : ActionCategory (Multiplicative ℕ) PUnit) ⟶
        (PUnit.unit : ActionCategory (Multiplicative ℕ) PUnit) from
        ⟨Multiplicative.ofAdd 1, rfl⟩) = zeroEnd.asHom := by
  exact congrArg (fun e : End (ℕ : Type) => e.asHom) zeroPowerAction_one

example (n : ℕ) : zeroEnd.asHom.hom n = 0 := rfl

example :
    (zeroPowerAction (Multiplicative.ofAdd 1)).asHom ≫
      coefficientGenerator (Multiplicative ℕ) PUnit (ℕ : Type) zeroPowerAction PUnit.unit =
    coefficientGenerator (Multiplicative ℕ) PUnit (ℕ : Type) zeroPowerAction PUnit.unit :=
  (coforkCoefficientFamily (Multiplicative ℕ) PUnit (ℕ : Type) zeroPowerAction
    (coequalizer.cofork (coefficientSource (Multiplicative ℕ) PUnit (ℕ : Type))
      (coefficientTarget (Multiplicative ℕ) PUnit (ℕ : Type) zeroPowerAction))).relation
        (Multiplicative.ofAdd 1) PUnit.unit

example : IsColimit
    (coequalizerCoefficientCocone (Multiplicative ℕ) PUnit (ℕ : Type) zeroPowerAction) :=
  coequalizerCoefficientIsColimit (Multiplicative ℕ) PUnit (ℕ : Type) zeroPowerAction

end NoninvertibleCoefficient

#print axioms coefficientColimitIso
#print axioms coefficientColimitIso_generator
#print axioms coefficientColimitIso_naturality
#print axioms inverseRightLeftAut
#print axioms inverseRightColimitIso_left
#print axioms balancedCoefficientCoforkIsColimit
#print axioms balancedCoefficientIso
#print axioms balancedCoefficientIso_generator

end FinBijCoinvariantsTests
