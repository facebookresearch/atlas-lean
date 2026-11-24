/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricAlgebraComplex
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianShuffle
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Balanced Hochschild deconcatenation and shuffle cuts

Tensor associativity and base-change cancellation identify
the A-balanced product of two coefficient chain levels
with the coefficient and their two ground tensor tails.
The inverse inserts the regular coefficient head 1.
These coordinates define A-linear deconcatenation and
balanced shuffle multiplication.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Native base-change and tensor coherence identify the A-balanced coefficient product. -/
def balancedCoefficientShuffleEquiv (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) ≃ₗ[A]
      M ⊗[k] (TensorPower k p A ⊗[k] TensorPower k q A) :=
  (TensorProduct.congr
    (TensorProduct.AlgebraTensorModule.congr
      (ULift.moduleEquiv : ULift.{w} A ≃ₗ[A] A) (LinearEquiv.refl k (TensorPower k p A)))
    (LinearEquiv.refl A (M ⊗[k] TensorPower k q A))).trans
      ((TensorProduct.comm A (A ⊗[k] TensorPower k p A) (M ⊗[k] TensorPower k q A)).trans
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange k A A
          (M ⊗[k] TensorPower k q A) (TensorPower k p A)).trans
          ((TensorProduct.AlgebraTensorModule.rightComm k k A M
            (TensorPower k q A) (TensorPower k p A)).trans
              (TensorProduct.AlgebraTensorModule.assoc k k A M
                (TensorPower k p A) (TensorPower k q A)))))

/-- The A-balanced equivalence has the original coefficient-head action value. -/
theorem balancedCoefficientShuffleEquiv_tmul (p q : ℕ) (a0 : ULift.{w} A) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    balancedCoefficientShuffleEquiv k A M p q ((a0 ⊗ₜ[k] x) ⊗ₜ[A] (m ⊗ₜ[k] y)) =
      (a0.down • m) ⊗ₜ[k] (x ⊗ₜ[k] y) := by
  simp only [balancedCoefficientShuffleEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.comm_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.rightComm_tmul,
    TensorProduct.AlgebraTensorModule.assoc_tmul]
  rfl

/-- The inverse inserts head one and keeps the original coefficient in the other factor. -/
theorem balancedCoefficientShuffleEquiv_symm_tmul (p q : ℕ) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    (balancedCoefficientShuffleEquiv k A M p q).symm (m ⊗ₜ[k] (x ⊗ₜ[k] y)) =
      (ULift.up (1 : A) ⊗ₜ[k] x) ⊗ₜ[A] (m ⊗ₜ[k] y) := by
  apply (balancedCoefficientShuffleEquiv k A M p q).injective
  rw [LinearEquiv.apply_symm_apply, balancedCoefficientShuffleEquiv_tmul, one_smul]

/-- Actual coefficient-head deconcatenation in the original A-module world. -/
def algebraDeconcatCut (p q : ℕ) :
    M ⊗[k] TensorPower k (p + q) A →ₗ[A]
      (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) :=
  (balancedCoefficientShuffleEquiv k A M p q).symm.toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.lTensor A M
      (TensorPower.mulEquiv (R := k) (M := A) (n := p) (m := q)).symm.toLinearMap)

/-- The A-linear cut has the original split tensor-word value. -/
theorem algebraDeconcatCut_tprod (p q : ℕ) (m : M) (a : Fin p → A) (b : Fin q → A) :
    algebraDeconcatCut k A M p q (m ⊗ₜ[k] PiTensorProduct.tprod k (Fin.append a b)) =
      (ULift.up (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[A]
        (m ⊗ₜ[k] PiTensorProduct.tprod k b) := by
  let E := TensorPower.mulEquiv (R := k) (M := A) (n := p) (m := q)
  have hconcat : E (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
      PiTensorProduct.tprod k (Fin.append a b) :=
    (TensorPower.gMul_def (R := k) (M := A) (PiTensorProduct.tprod k a) (PiTensorProduct.tprod k b)).symm.trans
      (TensorPower.tprod_mul_tprod k a b)
  have hinverse : E.symm (PiTensorProduct.tprod k (Fin.append a b)) =
      PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b :=
    (congrArg E.symm hconcat).symm.trans (E.symm_apply_apply _)
  rw [algebraDeconcatCut, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.lTensor_tmul]
  change (balancedCoefficientShuffleEquiv k A M p q).symm
      (m ⊗ₜ[k] E.symm (PiTensorProduct.tprod k (Fin.append a b))) = _
  rw [hinverse]
  exact balancedCoefficientShuffleEquiv_symm_tmul k A M p q m _ _

/-- The original signed shuffle multiplication on the original A-balanced coefficient tensor. -/
def algebraShufflePairCut (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) →ₗ[A]
      M ⊗[k] TensorPower k (p + q) A :=
  (TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorPower.signedShuffleProduct (k := k) (V := A) p q)).comp
      (balancedCoefficientShuffleEquiv k A M p q).toLinearMap

/-- The balanced shuffle value retains the original coefficient action and signed tail product. -/
theorem algebraShufflePairCut_tmul (p q : ℕ) (a0 : ULift.{w} A) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    algebraShufflePairCut k A M p q ((a0 ⊗ₜ[k] x) ⊗ₜ[A] (m ⊗ₜ[k] y)) =
      (a0.down • m) ⊗ₜ[k] TensorPower.signedShuffleProduct (k := k) (V := A) p q (x ⊗ₜ[k] y) := by
  let F := TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorPower.signedShuffleProduct (k := k) (V := A) p q)
  change F (balancedCoefficientShuffleEquiv k A M p q ((a0 ⊗ₜ[k] x) ⊗ₜ[A] (m ⊗ₜ[k] y))) = _
  have h := balancedCoefficientShuffleEquiv_tmul k A M p q a0 m x y
  exact (congrArg F h).trans (TensorProduct.AlgebraTensorModule.lTensor_tmul (A := A) (M := M)
    (TensorPower.signedShuffleProduct (k := k) (V := A) p q) (a0.down • m) (x ⊗ₜ[k] y))

/-- The native canonical change-of-balancing map on the original two coefficient levels. -/
def algebraTensorComparison (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A) →ₗ[k]
      (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) :=
  TensorProduct.mapOfCompatibleSMul A k k
    (ULift.{w} A ⊗[k] TensorPower k p A) (M ⊗[k] TensorPower k q A)

/-- The original canonical change-of-balancing map retains each original pure tensor. -/
theorem algebraTensorComparison_tmul (p q : ℕ)
    (x : ULift.{w} A ⊗[k] TensorPower k p A) (y : M ⊗[k] TensorPower k q A) :
    algebraTensorComparison k A M p q (x ⊗ₜ[k] y) = x ⊗ₜ[A] y :=
  TensorProduct.mapOfCompatibleSMul_tmul _ _ _ _ _ _ _

/-- The original canonical comparison is genuinely surjective, without flatness. -/
theorem algebraTensorComparison_surjective (p q : ℕ) :
    Function.Surjective (algebraTensorComparison k A M p q) :=
  TensorProduct.mapOfCompatibleSMul_surjective _ _ _ _ _

/-- The original k-shuffle is exactly the balanced shuffle after its canonical comparison. -/
theorem algebraShufflePairCut_comparison (p q : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((algebraShufflePairCut k A M p q).restrictScalars k).comp
      (algebraTensorComparison k A M p q) = ((pairing.{u, v, w} k A M).pair p q).hom := by
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
  change ((algebraShufflePairCut k A M p q).restrictScalars k)
      (algebraTensorComparison k A M p q
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b))) =
    ((pairing.{u, v, w} k A M).pair p q).hom
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k] (m ⊗ₜ[k] PiTensorProduct.tprod k b))
  rw [LinearMap.restrictScalars_apply, algebraTensorComparison_tmul]
  exact (algebraShufflePairCut_tmul k A M p q a0 m
    (PiTensorProduct.tprod k a) (PiTensorProduct.tprod k b)).trans
      (pairing_pair_as_tmul k A M p q a0 m (PiTensorProduct.tprod k a) (PiTensorProduct.tprod k b)).symm

/-- Original middle coefficient terms agree by the A-balancing relation before multiplication. -/
theorem algebraMiddleHead_balance (p q : ℕ) (a : A) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    (ULift.up a ⊗ₜ[k] x) ⊗ₜ[A] (m ⊗ₜ[k] y) =
      (ULift.up (1 : A) ⊗ₜ[k] x) ⊗ₜ[A] ((a • m) ⊗ₜ[k] y) := by
  have hhead : a • (ULift.up (1 : A) ⊗ₜ[k] x) = (ULift.up a ⊗ₜ[k] x) := by
    rw [TensorProduct.smul_tmul']
    congr 1
    apply ULift.ext
    change a * 1 = a
    exact mul_one a
  calc
    _ = (a • (ULift.up (1 : A) ⊗ₜ[k] x)) ⊗ₜ[A] (m ⊗ₜ[k] y) := by rw [hhead]
    _ = (ULift.up (1 : A) ⊗ₜ[k] x) ⊗ₜ[A] (a • (m ⊗ₜ[k] y)) := TensorProduct.smul_tmul _ _ _
    _ = _ := by rw [TensorProduct.smul_tmul']

end ModuleCat.Algebra.Hochschild.Symmetric
