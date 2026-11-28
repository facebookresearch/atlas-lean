/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.BialgebraNaturality
public import Mathlib.Data.ZMod.Basic

/-!
# Primitive generator and coefficient squares over `ZMod 6`

Multiplication by two on the abelian Lie algebra `ZMod 6` induces an
enveloping bialgebra map. Its primitive generator image evaluates to two.
The sum of the scalar coefficient three and the generator maps to an
element evaluating to five, while its augmentation remains three.
Negation induces a bialgebra equivalence, and a mixed tensor evaluation
detects the cocommutativity of the squared generator coproduct.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace BialgebraNaturalityTests

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev R := ZMod 6

private abbrev U := UniversalEnvelopingAlgebra R R

private abbrev P := Bialgebra.primitiveLieSubalgebra R U

private def coefficientLieMap (c : R) : R →ₗ⁅R⁆ R where
  __ := c • (LinearMap.id : R →ₗ[R] R)
  map_lie' := by
    intro x y
    simp only [LieRing.of_associative_ring_bracket, mul_comm, sub_self]
    exact (c • (LinearMap.id : R →ₗ[R] R)).map_zero

private theorem coefficientLieMap_apply (c x : R) : coefficientLieMap c x = c * x :=
  rfl

private abbrev dilation := UniversalEnvelopingAlgebra.mapBialgHom R (coefficientLieMap 2)

private def generator : P := UniversalEnvelopingAlgebra.ιPrimitive R R 1

private def evaluate : U →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (LieHom.id : R →ₗ⁅R⁆ R)

private theorem evaluate_coefficient (c : R) : evaluate (algebraMap R U c) = c :=
  evaluate.commutes c

private theorem dilation_coefficient (c : R) :
    dilation (algebraMap R U c) = algebraMap R U c :=
  dilation.toAlgHom.commutes c

private theorem primitive_image_two_value :
    evaluate (dilation.primitiveLieMap generator : U) = 2 := by
  calc
    evaluate (dilation.primitiveLieMap generator : U) =
        evaluate (UniversalEnvelopingAlgebra.ιPrimitive R R (coefficientLieMap 2 1) : U) :=
      congrArg (fun p : P => evaluate (p : U))
        (congrArg (fun f : R →ₗ⁅R⁆ P => f 1)
          (UniversalEnvelopingAlgebra.ιPrimitive_naturality R (coefficientLieMap 2)))
    _ = 2 := by
      change UniversalEnvelopingAlgebra.lift R (LieHom.id : R →ₗ⁅R⁆ R)
        (UniversalEnvelopingAlgebra.ιPrimitive R R (coefficientLieMap 2 1) : U) = 2
      rw [UniversalEnvelopingAlgebra.coe_ιPrimitive,
        UniversalEnvelopingAlgebra.lift_ι_apply]
      simp only [LieHom.id_apply, coefficientLieMap_apply, mul_one]

private theorem image_two_value : evaluate (dilation (generator : U)) = 2 := by
  simpa only [BialgHom.primitiveLieMap_apply] using primitive_image_two_value

private theorem primitive_image_two_ne_zero : dilation.primitiveLieMap generator ≠ 0 := by
  intro hzero
  have h := congrArg (fun p : P => evaluate (p : U)) hzero
  change evaluate (dilation.primitiveLieMap generator : U) = evaluate (0 : U) at h
  rw [primitive_image_two_value, map_zero] at h
  exact (by decide : (2 : R) ≠ 0) h

private def coefficientWord : U := algebraMap R U 3 + (generator : U)

private theorem coefficientWord_value : evaluate (dilation coefficientWord) = 5 := by
  simp only [coefficientWord, map_add]
  rw [dilation_coefficient, evaluate_coefficient, image_two_value]
  decide

private def negLieEquiv : R ≃ₗ⁅R⁆ R where
  __ := coefficientLieMap (-1)
  invFun := fun x => -x
  left_inv := by
    intro x
    change -(coefficientLieMap (-1) x) = x
    simp only [coefficientLieMap_apply, neg_one_mul, neg_neg]
  right_inv := by
    intro x
    change coefficientLieMap (-1) (-x) = x
    simp only [coefficientLieMap_apply, neg_one_mul, neg_neg]

private theorem neg_generator_value :
    evaluate (UniversalEnvelopingAlgebra.mapBialgEquiv R negLieEquiv (generator : U)) = -1 := by
  change UniversalEnvelopingAlgebra.lift R (LieHom.id : R →ₗ⁅R⁆ R)
    (UniversalEnvelopingAlgebra.mapBialgEquiv R negLieEquiv
      (UniversalEnvelopingAlgebra.ιPrimitive R R 1 : U)) = -1
  rw [UniversalEnvelopingAlgebra.coe_ιPrimitive,
    UniversalEnvelopingAlgebra.mapBialgEquiv_apply, UniversalEnvelopingAlgebra.map_ι,
    UniversalEnvelopingAlgebra.lift_ι_apply]
  change coefficientLieMap (-1) 1 = -1
  simp only [coefficientLieMap_apply, mul_one]

private theorem neg_inverse_generator_value :
    evaluate ((UniversalEnvelopingAlgebra.mapBialgEquiv R negLieEquiv).symm
      (generator : U)) = -1 := by
  change UniversalEnvelopingAlgebra.lift R (LieHom.id : R →ₗ⁅R⁆ R)
    ((UniversalEnvelopingAlgebra.mapBialgEquiv R negLieEquiv).symm
      (UniversalEnvelopingAlgebra.ιPrimitive R R 1 : U)) = -1
  rw [UniversalEnvelopingAlgebra.coe_ιPrimitive,
    UniversalEnvelopingAlgebra.mapBialgEquiv_symm_apply, UniversalEnvelopingAlgebra.map_ι,
    UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

private def evaluateTwo : U →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (coefficientLieMap 2)

private def tensorEvaluate : U ⊗[R] U →ₐ[R] R :=
  (Algebra.TensorProduct.lid R R).toAlgHom.comp (Algebra.TensorProduct.map evaluate evaluateTwo)

private theorem tensorGenerator_value :
    tensorEvaluate (Coalgebra.comul (R := R) (generator : U)) = 3 := by
  change Algebra.TensorProduct.lid R R
    (Algebra.TensorProduct.map evaluate evaluateTwo
      (Coalgebra.comul (R := R) (UniversalEnvelopingAlgebra.ιPrimitive R R 1 : U))) = 3
  rw [UniversalEnvelopingAlgebra.coe_ιPrimitive, UniversalEnvelopingAlgebra.comul_ι]
  simp only [map_add, Algebra.TensorProduct.map_tmul, map_one,
    Algebra.TensorProduct.lid_tmul, evaluate, evaluateTwo,
    UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.id_apply,
    coefficientLieMap_apply, smul_eq_mul, mul_one, one_mul]
  decide

example : evaluate (dilation.primitiveLieMap generator : U) = 2 := primitive_image_two_value

example : dilation.primitiveLieMap generator ≠ 0 := primitive_image_two_ne_zero

example : evaluate (dilation coefficientWord) = 5 := coefficientWord_value

example : Coalgebra.counit (R := R) (dilation coefficientWord) = 3 := by
  have h := congrArg (fun f : U →ₐ[R] R => f coefficientWord)
    (UniversalEnvelopingAlgebra.map_counitAlgHom R (coefficientLieMap 2))
  calc
    Coalgebra.counit (R := R) (dilation coefficientWord) =
        Coalgebra.counit (R := R) coefficientWord := by
      change (Bialgebra.counitAlgHom R U) (dilation coefficientWord) =
        (Bialgebra.counitAlgHom R U) coefficientWord
      simpa only [dilation, UniversalEnvelopingAlgebra.mapBialgHom_apply, AlgHom.comp_apply]
        using h
    _ = 3 := by
      change (Bialgebra.counitAlgHom R U) coefficientWord = 3
      rw [UniversalEnvelopingAlgebra.counitAlgHom_eq_augmentation]
      simp only [coefficientWord, map_add, generator,
        UniversalEnvelopingAlgebra.coe_ιPrimitive, UniversalEnvelopingAlgebra.augmentation_ι,
        add_zero]
      exact (UniversalEnvelopingAlgebra.augmentation R R).commutes 3

example : evaluate (UniversalEnvelopingAlgebra.mapBialgEquiv R negLieEquiv (generator : U)) = -1 :=
  neg_generator_value

example : evaluate ((UniversalEnvelopingAlgebra.mapBialgEquiv R negLieEquiv).symm
    (generator : U)) = -1 := neg_inverse_generator_value

example : tensorEvaluate (TensorProduct.comm R U U
    (Coalgebra.comul (R := R) ((generator : U) * (generator : U)))) = 3 := by
  rw [Coalgebra.comm_comul]
  simp only [Bialgebra.comul_mul, map_mul, tensorGenerator_value]
  decide

end BialgebraNaturalityTests
