/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricShuffleCutOperator
public import MathlibExt.LinearAlgebra.TensorPower.PermutationShuffleActions

/-!
# Eulerian operators and coefficient shuffle pairings

The regular coefficient acts on the coefficient head,
and the signed permutation shuffle acts on the tensor
tails. Their pairing intertwines the rational Eulerian
operations by the permutation-algebra shuffle law.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The regular coefficient head acts on the original coefficient module. -/
def coefficientHeadAction : ULift.{w} A ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift ((Algebra.lsmul k k M).toLinearMap.comp
    (ULift.moduleEquiv : ULift.{w} A ≃ₗ[k] A).toLinearMap)

/-- The head action has the original algebra scalar value. -/
theorem coefficientHeadAction_tmul (a : ULift.{w} A) (m : M) :
    coefficientHeadAction k A M (a ⊗ₜ[k] m) = a.down • m := by
  rw [coefficientHeadAction, TensorProduct.lift.tmul]
  rfl

/-- Native tensor regrouping followed by the original coefficient action and original signed tail shuffle. -/
def coefficientShufflePairingMap (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A) →ₗ[k]
      M ⊗[k] TensorPower k (p + q) A :=
  (TensorProduct.map LinearMap.id (TensorPower.signedShuffleProduct (k := k) (V := A) p q)).comp
    ((TensorProduct.map (coefficientHeadAction k A M) LinearMap.id).comp
      (TensorProduct.tensorTensorTensorComm k (ULift.{w} A) (TensorPower k p A)
        M (TensorPower k q A)).toLinearMap)

/-- The regrouping map has its value on the original four tensor factors. -/
theorem coefficientShufflePairingMap_tmul (p q : ℕ) (a0 : ULift.{w} A) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    coefficientShufflePairingMap k A M p q ((a0 ⊗ₜ[k] x) ⊗ₜ[k] (m ⊗ₜ[k] y)) =
      (a0.down • m) ⊗ₜ[k] TensorPower.signedShuffleProduct (k := k) (V := A) p q (x ⊗ₜ[k] y) := by
  change TensorProduct.map LinearMap.id (TensorPower.signedShuffleProduct (k := k) (V := A) p q)
      (TensorProduct.map (coefficientHeadAction k A M) LinearMap.id
        (TensorProduct.tensorTensorTensorComm k (ULift.{w} A) (TensorPower k p A)
          M (TensorPower k q A) ((a0 ⊗ₜ[k] x) ⊗ₜ[k] (m ⊗ₜ[k] y)))) = _
  rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    coefficientHeadAction_tmul, LinearMap.id_apply, TensorProduct.map_tmul, LinearMap.id_apply]

/-- The original Hochschild shuffle is exactly the head action followed by the signed tail
  product. -/
theorem pairing_pair_eq_coefficientShuffleMap (p q : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((pairing.{u, v, w} k A M).pair p q).hom = coefficientShufflePairingMap k A M p q := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  apply TensorProduct.curry_injective
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro a0 a
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m b
  change ((pairing.{u, v, w} k A M).pair p q).hom
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    coefficientShufflePairingMap k A M p q
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b))
  rw [pairing_pair_tprod_as_tmul]
  have hvalue := coefficientShufflePairingMap_tmul k A M p q a0 m
    (PiTensorProduct.tprod k a) (PiTensorProduct.tprod k b)
  have htail := TensorPower.signedShuffleProduct_tprod (k := k) (V := A) p q a b
  exact (congrArg (fun t : TensorPower k (p + q) A => (a0.down • m) ⊗ₜ[k] t) htail.symm).trans hvalue.symm

/-- The original pairing value for arbitrary original tensor tails follows from the regrouping
  identity. -/
theorem pairing_pair_as_tmul (p q : ℕ) (a0 : ULift.{w} A) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((pairing.{u, v, w} k A M).pair p q).hom ((a0 ⊗ₜ[k] x) ⊗ₜ[k] (m ⊗ₜ[k] y)) =
    (a0.down • m) ⊗ₜ[k] TensorPower.signedShuffleProduct (k := k) (V := A) p q (x ⊗ₜ[k] y) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  rw [pairing_pair_eq_coefficientShuffleMap]
  exact coefficientShufflePairingMap_tmul k A M p q a0 m x y

/-- The rational Eulerian evaluation respects the original coefficient shuffle pairing. -/
theorem coefficientEulerianLambda_pairing [Algebra ℚ k] (p q m : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  (TensorPower.coefficientRationalPermutationAction (k := k) (M := M) (V := A) (p + q)
      (Equiv.Perm.eulerianLambda (p + q) (m : ℚ))).comp ((pairing.{u, v, w} k A M).pair p q).hom =
    ((pairing.{u, v, w} k A M).pair p q).hom.comp
      (TensorProduct.map
        (TensorPower.coefficientRationalPermutationAction (k := k) (M := ULift.{w} A) (V := A) p
          (Equiv.Perm.eulerianLambda p (m : ℚ)))
        (TensorPower.coefficientRationalPermutationAction (k := k) (M := M) (V := A) q
          (Equiv.Perm.eulerianLambda q (m : ℚ)))) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  apply TensorProduct.curry_injective
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro a0 a
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro z b
  change TensorPower.coefficientRationalPermutationAction (k := k) (M := M) (V := A) (p + q)
      (Equiv.Perm.eulerianLambda (p + q) (m : ℚ))
      (((pairing.{u, v, w} k A M).pair p q).hom
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (z ⊗ₜ[k] PiTensorProduct.tprod k b))) =
    ((pairing.{u, v, w} k A M).pair p q).hom
      (TensorProduct.map
        (TensorPower.coefficientRationalPermutationAction (k := k) (M := ULift.{w} A) (V := A) p
          (Equiv.Perm.eulerianLambda p (m : ℚ)))
        (TensorPower.coefficientRationalPermutationAction (k := k) (M := M) (V := A) q
          (Equiv.Perm.eulerianLambda q (m : ℚ)))
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (z ⊗ₜ[k] PiTensorProduct.tprod k b)))
  simp only [TensorPower.coefficientRationalPermutationAction_eq_map, TensorProduct.map_tmul,
    LinearMap.id_apply, pairing_pair_as_tmul, LinearMap.comp_apply]
  have htail := DFunLike.congr_fun
    (TensorPower.rationalEulerianLambda_signedShuffleProduct (k := k) (V := A) p q m)
      (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)
  change TensorPower.rationalPermutationAction (k := k) (V := A) (p + q)
      (Equiv.Perm.eulerianLambda (p + q) (m : ℚ))
        (TensorPower.signedShuffleProduct (k := k) (V := A) p q
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    TensorPower.signedShuffleProduct (k := k) (V := A) p q
      (TensorProduct.map
        (TensorPower.rationalPermutationAction (k := k) (V := A) p (Equiv.Perm.eulerianLambda p (m : ℚ)))
        (TensorPower.rationalPermutationAction (k := k) (V := A) q (Equiv.Perm.eulerianLambda q (m : ℚ)))
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) at htail
  rw [TensorProduct.map_tmul] at htail
  have hpair := pairing_pair_as_tmul k A M p q a0 z
    ((TensorPower.rationalPermutationAction (k := k) (V := A) p
      (Equiv.Perm.eulerianLambda p (m : ℚ))) (PiTensorProduct.tprod k a))
    ((TensorPower.rationalPermutationAction (k := k) (V := A) q
      (Equiv.Perm.eulerianLambda q (m : ℚ))) (PiTensorProduct.tprod k b))
  exact (congrArg (fun t : TensorPower k (p + q) A => (a0.down • z) ⊗ₜ[k] t) htail).trans hpair.symm

end ModuleCat.Algebra.Hochschild.Symmetric
