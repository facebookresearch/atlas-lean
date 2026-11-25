/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Operad.Tensor.EnvelopingOperad
public import Batteries.Tactic.Lint



/-!
# Original heterogeneous, nullary, symmetric and whole-map enveloping clients
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uc u v us

namespace CategoryTheory.Operad.Tensor.Enveloping.Client

open CategoryTheory Limits

variable {W : Type uc} {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
variable [Small.{us} W] [HasColimitsOfSize.{us, us} C]

local instance : FiniteTensor C := FiniteTensor.ofSymmetric C
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} C :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot C
local instance (d : W) : HasColimitsOfShape (AnalyticIndex W d) C :=
  hasProfileColimitsOfSmallColors C d

def heterogeneousProfile (a b d : W) : ColoredProfile W where
  inputs := FintypeCat.of Bool
  inputColor i := if i then a else b
  outputColor := d

example (O : ColoredOperadObj W C) (A : Algebra O) (a b d : W) :
    (envelopingOperad O A).toCollection.obj (heterogeneousProfile a b d) =
      envelopingCoefficientObj O A (heterogeneousProfile a b d) := rfl

example (O : ColoredOperadObj W C) (A : Algebra O) {P Q : ColoredProfile W} (f : P ⟶ Q) :
    (envelopingOperad O A).toCollection.map f = (Variable.envelopingCoefficientCollection O A).map f := rfl

example (O : ColoredOperadObj W C) (A : Algebra O) (s : ColoredSubstitutionData W) :
    ColoredOperadObj.HomData.sourceHom (envelopingOperadProjection O A).toCollectionHom s ≫
      (envelopingOperad O A).subst.app s =
        envelopingLinearSubstitution O A.carrier s ≫ envelopingCoefficientπ O A s.totalProfile :=
  envelopingOperad_substitution_projection O A s

example (O : ColoredOperadObj W C) (A : Algebra O) (d : W) (Q : ColoredInputs W) :
    linearCoefficientι O.toCollection A.carrier (ColoredProfile.nullary d) Q ≫
      (envelopingOperadProjection O A).toCollectionHom.app (ColoredProfile.nullary d) ≫
      (envelopingOperadNullaryIso O A d).hom =
        (nullaryLinearDiagramIso O.toCollection A.carrier d).hom.app Q ≫
          A.operations.app d ((inputsToProfile d).obj Q) := envelopingOperadNullaryIso_cofan O A d Q

example (O : ColoredOperadObj W C) (A : Algebra O) :
    Algebra (envelopingOperad O A) ≌ Under A := envelopingUnderAEquivalence O A

example (O : ColoredOperadObj W C) (A : Algebra O) (M : Algebra (envelopingOperad O A)) :
    ((envelopingUnderAEquivalence O A).functor.obj M).right =
      Algebra.restrict (originalOperadToEnveloping O A) M := envelopingUnderAEquivalence_original O A M

example (O : ColoredOperadObj W C) (A : Algebra O) (M : Algebra (envelopingOperad O A)) (d : W) :
    ((envelopingUnderAEquivalence O A).functor.obj M).hom.hom d =
      (envelopingOperadNullaryIso O A d).inv ≫ FrozenAlgebra.nullaryEvaluation M d :=
  envelopingUnderAEquivalence_A_map O A M d

example (O : ColoredOperadObj W C) (A : Algebra O) {M N : Algebra (envelopingOperad O A)} (f : M ⟶ N) :
    ((envelopingUnderAEquivalence O A).functor.map f).right.hom = f.hom := rfl

example (O : ColoredOperadObj W C) (A : Algebra O) {B D : Under A} (f : B ⟶ D) :
    ((envelopingUnderAEquivalence O A).inverse.map f).hom = f.right.hom := rfl

example (O : ColoredOperadObj W C) (A : Algebra O) (B : Under A) :
    Algebra.restrict (originalOperadToEnveloping O A) ((envelopingUnderAEquivalence O A).inverse.obj B) =
      B.right := underAEnvelopingObject_original O A B

example (O : ColoredOperadObj W C) (A : Algebra O) (B : Under A) :
    (envelopingUnderAObject O A ((envelopingUnderAEquivalence O A).inverse.obj B)).hom.hom = B.hom.hom :=
  underAEnvelopingObject_underA_hom O A B

example (O : ColoredOperadObj W C) (A : Algebra O) (M : Algebra (envelopingOperad O A)) :
    HEq (underAEnvelopingObject O A (envelopingUnderAObject O A M)).operations M.operations :=
  envelopingUnderA_roundTrip_operations O A M

example (O : ColoredOperadObj W C) (A : Algebra O) (M : Algebra (envelopingOperad O A)) :
    ((envelopingUnderAEquivalence O A).unitIso.app M).hom.hom = 𝟙 M.carrier :=
  envelopingUnderA_roundTripIso_inv O A M

example (O : ColoredOperadObj W C) (A : Algebra O) (B : Under A) :
    ((envelopingUnderAEquivalence O A).counitIso.app B).hom.right.hom = 𝟙 B.right.carrier := rfl

end CategoryTheory.Operad.Tensor.Enveloping.Client

#print axioms CategoryTheory.Operad.Tensor.Enveloping.envelopingUnderAEquivalence
#print axioms CategoryTheory.Operad.Tensor.Enveloping.envelopingUnderAEquivalence_A_map
#print axioms CategoryTheory.Operad.Tensor.Enveloping.envelopingUnderA_roundTrip_operations

#lint+ only unusedArguments in MathlibExt.CategoryTheory.Operad.Tensor.EnvelopingOperad
#lint+ only unusedArguments in MathlibExtTest.CategoryTheory.Operad.Tensor.EnvelopingOperad
