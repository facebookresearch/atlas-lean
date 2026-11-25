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

public import MathlibExt.RingTheory.Bialgebra.PrimitiveLie
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Bialgebra
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basis

/-!
# Primitive maps over a ring with zero divisors

In the symmetric bialgebra on `ZMod 6`, the generator and twice the generator
are nonzero primitive elements. The bialgebra endomorphisms induced by
multiplication by two and three have zero composite on the generator.
Evaluation at one detects the corresponding enveloping-generator images.

In the enveloping bialgebra of two-by-two matrices, the generators of the
two off-diagonal matrix units are primitive. Their commutator evaluates
to the diagonal matrix with entries `1` and `-1`, and is therefore nonzero.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace PrimitiveLieTests

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev R := ZMod 6

private abbrev A := SymmetricAlgebra R R

private abbrev P := Bialgebra.primitiveLieSubalgebra R A

private def scalarAlgMap (c : R) : A →ₐ[R] A :=
  SymmetricAlgebra.lift (c • SymmetricAlgebra.ι R R)

private lemma scalarAlgMap_ι (c a : R) :
    scalarAlgMap c (SymmetricAlgebra.ι R R a) = c • SymmetricAlgebra.ι R R a :=
  SymmetricAlgebra.lift_ι_apply (c • SymmetricAlgebra.ι R R) a

private lemma scalarAlgMap_counit (c : R) :
    (Bialgebra.counitAlgHom R A).comp (scalarAlgMap c) = Bialgebra.counitAlgHom R A := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro a
  change Coalgebra.counit (R := R) (scalarAlgMap c (SymmetricAlgebra.ι R R a)) =
    Coalgebra.counit (R := R) (SymmetricAlgebra.ι R R a)
  rw [scalarAlgMap_ι]
  simp only [map_smul, SymmetricAlgebra.counit_ι, smul_zero]

private lemma scalarAlgMap_comul (c : R) :
    (Algebra.TensorProduct.map (scalarAlgMap c) (scalarAlgMap c)).comp
        (Bialgebra.comulAlgHom R A) =
      (Bialgebra.comulAlgHom R A).comp (scalarAlgMap c) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro a
  change Algebra.TensorProduct.map (scalarAlgMap c) (scalarAlgMap c)
      (Coalgebra.comul (R := R) (SymmetricAlgebra.ι R R a)) =
    Coalgebra.comul (R := R) (scalarAlgMap c (SymmetricAlgebra.ι R R a))
  simp only [SymmetricAlgebra.comul_ι, map_add, Algebra.TensorProduct.map_tmul,
    scalarAlgMap_ι, map_one, map_smul, smul_add, TensorProduct.smul_tmul',
    TensorProduct.tmul_smul]

private def dilation (c : R) : A →ₐc[R] A :=
  BialgHom.ofAlgHom (scalarAlgMap c) (scalarAlgMap_counit c) (scalarAlgMap_comul c)

private lemma dilation_ι (c a : R) :
    dilation c (SymmetricAlgebra.ι R R a) = c • SymmetricAlgebra.ι R R a :=
  scalarAlgMap_ι c a

private def x : P :=
  ⟨SymmetricAlgebra.ι R R 1,
    (Bialgebra.mem_primitiveLieSubalgebra R A).mpr
      ⟨SymmetricAlgebra.counit_ι R R 1,
        by simpa only [add_comm] using SymmetricAlgebra.comul_ι R R 1⟩⟩

private def evaluateAtOne : A →ₐ[R] R :=
  SymmetricAlgebra.lift (LinearMap.id : R →ₗ[R] R)

private lemma evaluateAtOne_x : evaluateAtOne (x : A) = 1 :=
  SymmetricAlgebra.lift_ι_apply (LinearMap.id : R →ₗ[R] R) 1

private lemma evaluateAtOne_dilation (c : R) : evaluateAtOne (dilation c (x : A)) = c := by
  change evaluateAtOne (dilation c (SymmetricAlgebra.ι R R 1)) = c
  rw [dilation_ι, map_smul]
  change c • evaluateAtOne (x : A) = c
  rw [evaluateAtOne_x]
  exact mul_one c

private lemma x_ne_zero : x ≠ 0 := by
  intro hx
  have hxA : (x : A) = 0 := congrArg (fun y : P => (y : A)) hx
  have h := congrArg evaluateAtOne hxA
  rw [evaluateAtOne_x, map_zero] at h
  exact (by decide : (1 : R) ≠ 0) h

private lemma dilation_two_ne_zero : (dilation 2).primitiveLieMap x ≠ 0 := by
  intro hx
  have hxA : dilation 2 (x : A) = 0 := by
    have hcast := congrArg (fun y : P => (y : A)) hx
    change dilation 2 (x : A) = 0 at hcast
    exact hcast
  have h := congrArg evaluateAtOne hxA
  rw [evaluateAtOne_dilation, map_zero] at h
  exact (by decide : (2 : R) ≠ 0) h

private lemma dilation_three_two_zero :
    (dilation 3).primitiveLieMap ((dilation 2).primitiveLieMap x) = 0 := by
  apply Subtype.ext
  simp only [BialgHom.primitiveLieMap_apply]
  change dilation 3 (dilation 2 (SymmetricAlgebra.ι R R 1)) = 0
  rw [dilation_ι, map_smul, dilation_ι, smul_smul]
  rw [show (2 : R) * 3 = 0 from by decide, zero_smul]

example : x ≠ 0 := x_ne_zero

example : (dilation 2).primitiveLieMap x = (2 : R) • x := by
  apply Subtype.ext
  change dilation 2 (SymmetricAlgebra.ι R R 1) =
    (2 : R) • SymmetricAlgebra.ι R R 1
  exact dilation_ι 2 1

example : (dilation 2).primitiveLieMap x ≠ 0 := dilation_two_ne_zero

example : (dilation 3).primitiveLieMap ((dilation 2).primitiveLieMap x) = 0 :=
  dilation_three_two_zero

example : ((dilation 3).comp (dilation 2)).primitiveLieMap x = 0 := by
  rw [BialgHom.primitiveLieMap_comp]
  exact dilation_three_two_zero

example : UniversalEnvelopingAlgebra.ι R x ≠ 0 := by
  intro hx
  have h := congrArg (UniversalEnvelopingAlgebra.lift R P.incl) hx
  rw [UniversalEnvelopingAlgebra.lift_ι_apply, map_zero] at h
  exact x_ne_zero (Subtype.ext h)

example :
    evaluateAtOne (UniversalEnvelopingAlgebra.lift R P.incl
      (UniversalEnvelopingAlgebra.map R (dilation 2).primitiveLieMap
        (UniversalEnvelopingAlgebra.ι R x))) = 2 := by
  have h := congrArg
    (fun f : UniversalEnvelopingAlgebra R P →ₐ[R] A =>
      evaluateAtOne (f (UniversalEnvelopingAlgebra.ι R x)))
    (BialgHom.primitive_enveloping_naturality (dilation 2))
  have hleft : evaluateAtOne
      (((dilation 2).toAlgHom.comp (UniversalEnvelopingAlgebra.lift R P.incl))
        (UniversalEnvelopingAlgebra.ι R x)) = 2 := by
    change evaluateAtOne (dilation 2
      (UniversalEnvelopingAlgebra.lift R P.incl (UniversalEnvelopingAlgebra.ι R x))) = 2
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    exact evaluateAtOne_dilation 2
  exact h.symm.trans hleft

example :
    UniversalEnvelopingAlgebra.map R (dilation 3).primitiveLieMap
      (UniversalEnvelopingAlgebra.map R (dilation 2).primitiveLieMap
        (UniversalEnvelopingAlgebra.ι R x)) = 0 := by
  rw [UniversalEnvelopingAlgebra.map_ι, UniversalEnvelopingAlgebra.map_ι,
    dilation_three_two_zero, map_zero]

section Noncommutative

private abbrev MatrixLie := Matrix (Fin 2) (Fin 2) R

private abbrev MatrixU := UniversalEnvelopingAlgebra R MatrixLie

private abbrev MatrixPrimitives := Bialgebra.primitiveLieSubalgebra R MatrixU

private def matrixE01 : MatrixLie := Matrix.single 0 1 (1 : R)

private def matrixE10 : MatrixLie := Matrix.single 1 0 (1 : R)

private def matrixPrimitive01 : MatrixPrimitives :=
  ⟨UniversalEnvelopingAlgebra.ι R matrixE01,
    (Bialgebra.mem_primitiveLieSubalgebra R MatrixU).mpr
      (UniversalEnvelopingAlgebra.isPrimitiveElem_ι R MatrixLie matrixE01)⟩

private def matrixPrimitive10 : MatrixPrimitives :=
  ⟨UniversalEnvelopingAlgebra.ι R matrixE10,
    (Bialgebra.mem_primitiveLieSubalgebra R MatrixU).mpr
      (UniversalEnvelopingAlgebra.isPrimitiveElem_ι R MatrixLie matrixE10)⟩

private def matrixEvaluate : MatrixU →ₐ[R] MatrixLie :=
  UniversalEnvelopingAlgebra.lift R (LieHom.id : MatrixLie →ₗ⁅R⁆ MatrixLie)

private theorem matrixCommutator_value :
    matrixEvaluate (⁅matrixPrimitive01, matrixPrimitive10⁆ : MatrixU) =
      Matrix.single (0 : Fin 2) 0 (1 : R) - Matrix.single (1 : Fin 2) 1 (1 : R) := by
  change UniversalEnvelopingAlgebra.lift R (LieHom.id : MatrixLie →ₗ⁅R⁆ MatrixLie)
      ⁅UniversalEnvelopingAlgebra.ι R matrixE01, UniversalEnvelopingAlgebra.ι R matrixE10⁆ = _
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul,
    UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.id_apply]
  simp only [matrixE01, matrixE10, Matrix.single_mul_single_same, mul_one]

private theorem matrixCommutator_entry :
    matrixEvaluate (⁅matrixPrimitive01, matrixPrimitive10⁆ : MatrixU) (0 : Fin 2) 0 = 1 := by
  rw [matrixCommutator_value]
  change Matrix.single (0 : Fin 2) 0 (1 : R) (0 : Fin 2) 0 -
    Matrix.single (1 : Fin 2) 1 (1 : R) (0 : Fin 2) 0 = 1
  rw [Matrix.single_apply_same,
    Matrix.single_apply_of_ne (1 : Fin 2) (1 : Fin 2) (1 : R)
      (0 : Fin 2) (0 : Fin 2) (by decide)]
  exact sub_zero 1

private theorem matrixPrimitiveCommutator_ne_zero :
    ⁅matrixPrimitive01, matrixPrimitive10⁆ ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun p : MatrixPrimitives => matrixEvaluate (p : MatrixU) (0 : Fin 2) 0) hzero
  change matrixEvaluate (⁅matrixPrimitive01, matrixPrimitive10⁆ : MatrixU) (0 : Fin 2) 0 =
    matrixEvaluate (0 : MatrixU) (0 : Fin 2) 0 at h
  rw [matrixCommutator_entry, map_zero] at h
  change (1 : R) = 0 at h
  exact (by decide : (1 : R) ≠ 0) h

example : matrixEvaluate (⁅matrixPrimitive01, matrixPrimitive10⁆ : MatrixU) =
    Matrix.single (0 : Fin 2) 0 (1 : R) - Matrix.single (1 : Fin 2) 1 (1 : R) :=
  matrixCommutator_value

example : ⁅matrixPrimitive01, matrixPrimitive10⁆ ≠ 0 := matrixPrimitiveCommutator_ne_zero

end Noncommutative

end PrimitiveLieTests
