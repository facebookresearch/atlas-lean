/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Normalized
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Opposite
public import MathlibExt.Algebra.Module.CommutingOpposite

/-!
# Symmetric Hochschild coefficients and their canonical right action

For a semiring A and an A-module M whose scalar operators commute, an element of Aᵐᵒᵖ acts
through its image in A. The resulting left and right actions commute. If k is a commutative
ring and A a commutative k-algebra, any compatible A-module M therefore gives symmetric
Hochschild chains M ⊗[k] A⊗n, their coefficient-bar simplicial model, and normalization with
tails A/(k·1). The degree-one boundary is zero because its two endpoint actions coincide.

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.2.10, for symmetric Hochschild coefficients.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric


section GroundCompatibility

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]

/-- The ground-linear Hochschild complex of a symmetric coefficient module.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, degree n is M
⊗[k] A⊗n with the Hochschild differential and the canonical right A-action. -/
def chainComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact ModuleCat.Algebra.Hochschild.chainComplex k A M

/-- The normalized Hochschild complex of symmetric coefficients.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, degree n is M
⊗[k] (A/(k·1))⊗n, with the differential induced by the raw Hochschild boundary. -/
def normalizedChainComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M

/-- The simplicial coefficient bar for a symmetric A-module.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, this
simplicial k-module has degree n identified with M ⊗[k] A⊗n through coefficient-bar
coordinates. -/
def coefficientBar : SimplicialObject (ModuleCat.{max u v w} k) := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact ModuleCat.Algebra.Hochschild.coefficientBar k A M

/-- The degreewise symmetric coefficient-bar tensor isomorphism.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
coefficientBar in simplicial degree n is isomorphic to the k-module M ⊗[k] A⊗n. Ground,
algebra and coefficient carrier universes remain independent. -/
def coefficientBarObjIso (n : ℕ) :
    (coefficientBar k A M).obj (Opposite.op ⦋n⦌) ≅
      ModuleCat.of k (M ⊗[k] TensorPower k n A) := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact ModuleCat.Algebra.Hochschild.coefficientBarObjIso k A M n

/-- The symmetric Hochschild complex equals the coefficient bar's face complex.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the chain
complex is isomorphic to the alternating-face complex of coefficientBar; the degreewise maps
are its tensor-coordinate isomorphisms. -/
def chainComplexIso :
    chainComplex k A M ≅
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
        (coefficientBar k A M) := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact ModuleCat.Algebra.Hochschild.chainComplexIso k A M

/-- The chain projection from raw to normalized symmetric Hochschild tensors.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, quotient each
A-tail by k·1 while retaining M, giving chainComplex → normalizedChainComplex. -/
def normalizationProjection :
    chainComplex k A M ⟶ normalizedChainComplex k A M := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact ModuleCat.Algebra.Hochschild.normalizationProjection k A M

/-- The symmetric coefficient boundary vanishes in degree one.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the
differential C₁ → C₀ is zero because a • m and m • a agree. -/
@[simp]
lemma boundary_one_zero :
    (chainComplex k A M).d 1 0 = 0 := by
  let := Module.oppositeOfCommutingAction A M
  let := Module.oppositeOfCommutingAction_actionsComm A M
  let := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  let := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  change (ModuleCat.Algebra.Hochschild.chainComplex k A M).d 1 0 = 0
  rw [ModuleCat.Algebra.Hochschild.chainComplex_d]
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  rw [ModuleCat.Algebra.Hochschild.boundary_one_tprod]
  change (a 0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
      (ModuleCat.Algebra.Hochschild.hochschildDropFirst a) -
    (a 0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
      (ModuleCat.Algebra.Hochschild.hochschildDropLast a) = 0
  have h : ModuleCat.Algebra.Hochschild.hochschildDropFirst a =
      ModuleCat.Algebra.Hochschild.hochschildDropLast a := by
    funext i
    exact Fin.elim0 i
  rw [h, sub_self]

/-- The ground tensor action on a symmetric coefficient module.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the k-linear
map A ⊗[k] M → M sends a ⊗ m to a • m. -/
def coefficientTensorAction : A ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift (Algebra.lsmul k k M : A →ₐ[k] Module.End k M).toLinearMap

/-- The value of the coefficient tensor action on a pure tensor.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
coefficientTensorAction(a ⊗ m) = a • m. -/
@[simp]
lemma coefficientTensorAction_tmul (a : A) (m : M) :
    coefficientTensorAction k A M (a ⊗ₜ[k] m) = a • m := by
  unfold coefficientTensorAction
  rw [TensorProduct.lift.tmul]
  exact Algebra.lsmul_apply k k M a m

end GroundCompatibility

end ModuleCat.Algebra.Hochschild.Symmetric
