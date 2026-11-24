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
# Hochschild complexes with symmetric coefficients

Commuting scalar operators give a module its canonical opposite
right action. For a commutative ground ring and commutative unital
algebra, this defines the symmetric coefficient raw, simplicial
and normalized Hochschild complexes. Their degree-one boundary
is zero because the two endpoint actions agree.

Reference: Loday, Cyclic Homology, second edition, §4.2.10.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

section CanonicalRightCoefficients

variable (A : Type v) [Semiring A] (M : Type w) [AddCommMonoid M] [Module A M]
  [SMulCommClass A A M]

/-- The original A-module supplies its symmetric right coefficient action. -/
@[instance_reducible]
def opModule : Module Aᵐᵒᵖ M :=
  Module.oppositeOfCommutingAction A M

/-- Scalars for the symmetric opposite module retain the original scalar value. -/
@[simp] theorem opModule_smul (a : Aᵐᵒᵖ) (m : M) :
    (letI := opModule A M; a • m) = MulOpposite.unop a • m :=
  Module.oppositeOfCommutingAction_smul A M a m

/-- Left and constructed right actions commute by the original scalar operators on M. -/
theorem actionsComm :
    letI := opModule A M
    SMulCommClass A Aᵐᵒᵖ M :=
  Module.oppositeOfCommutingAction_actionsComm A M

end CanonicalRightCoefficients

section GroundCommutation

variable (k : Type u) (A : Type v) (M : Type w) [Semiring A]
  [AddCommMonoid M] [Module A M] [SMulCommClass A A M]
  [SMul k M] [SMulCommClass k A M]

/-- Any original commuting scalar action commutes with the canonical opposite action. -/
theorem kOpComm :
    letI := opModule A M
    SMulCommClass k Aᵐᵒᵖ M :=
  Module.oppositeOfCommutingAction_smulComm A M (R := k)

end GroundCommutation

section GroundCompatibility

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]

/-- The constructed right action retains the original k/A scalar tower. -/
theorem kOpTower :
    letI := opModule A M
    IsScalarTower k Aᵐᵒᵖ M := by
  let := opModule A M
  constructor
  intro c a m
  change (c • MulOpposite.unop a) • m = c • (MulOpposite.unop a • m)
  exact smul_assoc c (MulOpposite.unop a) m

/-- The original raw coefficient Hochschild complex, with the symmetric right action. -/
def chainComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.chainComplex k A M

/-- The original normalized complex uses only the ground quotient A/(k*1) in its tail. -/
def normalizedChainComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M

/-- The original coefficient bar is reused rather than cloned. -/
def coefficientBar : SimplicialObject (ModuleCat.{max u v w} k) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.coefficientBar k A M

/-- Native bar coordinates retain exactly the original coefficient-first raw tensor carrier. -/
def coefficientBarObjIso (n : ℕ) :
    (coefficientBar k A M).obj (Opposite.op ⦋n⦌) ≅
      ModuleCat.of k (M ⊗[k] TensorPower k n A) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.coefficientBarObjIso k A M n

/-- The original raw/bar coordinate dictionary, with no comparison supplied by callers. -/
def chainComplexIso :
    chainComplex k A M ≅
      (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
        (coefficientBar k A M) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.chainComplexIso k A M

/-- The original raw-to-normalized projection, with unchanged coefficient and ground quotient. -/
def normalizationProjection :
    chainComplex k A M ⟶ normalizedChainComplex k A M := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  exact ModuleCat.Algebra.Hochschild.normalizationProjection k A M

/-- The degree-one endpoint vanishes for the symmetric coefficients.
This is indispensable for positive-factor relations to stay positive under the boundary. -/
@[simp]
lemma boundary_one_zero :
    (chainComplex k A M).d 1 0 = 0 := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
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

/-- The original algebra action as a ground-linear coefficient tensor map. -/
def coefficientTensorAction : A ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift (Algebra.lsmul k k M : A →ₐ[k] Module.End k M).toLinearMap

/-- A pure coefficient tensor is sent to the original algebra action. -/
@[simp]
lemma coefficientTensorAction_tmul (a : A) (m : M) :
    coefficientTensorAction k A M (a ⊗ₜ[k] m) = a • m := by
  unfold coefficientTensorAction
  rw [TensorProduct.lift.tmul]
  exact Algebra.lsmul_apply k k M a m

end GroundCompatibility

end ModuleCat.Algebra.Hochschild.Symmetric
