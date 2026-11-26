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
# A-balanced deconcatenation and signed shuffle coordinates

Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module. The
balanced tensor (ULift A ⊗[k] A⊗p) ⊗[A] (M ⊗[k] A⊗q) identifies with M ⊗[k] (A⊗p ⊗[k] A⊗q) by
moving the regular coefficient onto M. Its inverse inserts coefficient 1_A. These coordinates
define A-linear deconcatenation and signed shuffle multiplication, retaining the order of the
two ground tensor blocks.

For tensor balancing and associativity, see N. Bourbaki, Algebra I, Chapter III; for signed
shuffles, see J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
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

/-- The A-balanced coefficient-and-two-tail equivalence.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, (ULift A ⊗[k] A⊗p) ⊗[A] (M ⊗[k] A⊗q) is A-linearly equivalent to M ⊗[k] (A⊗p ⊗[k]
A⊗q). The regular coefficient is absorbed into M. -/
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

/-- The coefficient formula for the balanced shuffle equivalence.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, the equivalence sends (a₀ ⊗ x) ⊗[A] (m ⊗ y) to (a₀.down • m) ⊗[k] (x ⊗[k] y), for x
∈ A⊗p and y ∈ A⊗q. -/
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

/-- The inverse balanced equivalence inserts the regular unit coefficient.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, m ⊗[k] (x ⊗[k] y) maps back to (ULift.up(1_A) ⊗[k] x) ⊗[A] (m ⊗[k] y). -/
theorem balancedCoefficientShuffleEquiv_symm_tmul (p q : ℕ) (m : M)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    (balancedCoefficientShuffleEquiv k A M p q).symm (m ⊗ₜ[k] (x ⊗ₜ[k] y)) =
      (ULift.up (1 : A) ⊗ₜ[k] x) ⊗ₜ[A] (m ⊗ₜ[k] y) := by
  apply (balancedCoefficientShuffleEquiv k A M p q).injective
  rw [LinearEquiv.apply_symm_apply, balancedCoefficientShuffleEquiv_tmul, one_smul]

/-- A-linear deconcatenation at a prescribed two-block cut.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, the cut p+q splits M ⊗[k] A⊗(p+q) into the A-balanced tensor of a regular-
coefficient p-word and an M-coefficient q-word, inserting 1_A in the regular head. -/
def algebraDeconcatCut (p q : ℕ) :
    M ⊗[k] TensorPower k (p + q) A →ₗ[A]
      (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) :=
  (balancedCoefficientShuffleEquiv k A M p q).symm.toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.lTensor A M
      (TensorPower.mulEquiv (R := k) (M := A) (n := p) (m := q)).symm.toLinearMap)

/-- The pure-word formula for A-balanced deconcatenation.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, m ⊗ tprod(append(a,b)) maps to (ULift.up(1_A) ⊗ tprod(a)) ⊗[A] (m ⊗ tprod(b)), with
a : Fin p → A and b : Fin q → A. -/
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

/-- The A-balanced signed shuffle multiplication of two coefficient words.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, this A-linear map combines a regular-coefficient p-word and an M-coefficient q-word,
then sums (p,q)-shuffles with their integer permutation signs. -/
def algebraShufflePairCut (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) →ₗ[A]
      M ⊗[k] TensorPower k (p + q) A :=
  (TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorPower.signedShuffleProduct (k := k) (V := A) p q)).comp
      (balancedCoefficientShuffleEquiv k A M p q).toLinearMap

/-- The balanced shuffle value on a pair of pure coefficient tensors.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, (a₀ ⊗ x) ⊗[A] (m ⊗ y) maps to (a₀.down • m) ⊗ signedShuffleProduct(p,q)(x ⊗ y). The
shuffle sign is the integer sign of its permutation. -/
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

/-- The comparison from ground balancing to algebra balancing.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, this k-linear quotient map sends the k-tensor product of the two coefficient-word
modules to their A-balanced tensor product, without changing either factor. -/
def algebraTensorComparison (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A) →ₗ[k]
      (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) :=
  TensorProduct.mapOfCompatibleSMul A k k
    (ULift.{w} A ⊗[k] TensorPower k p A) (M ⊗[k] TensorPower k q A)

/-- The pure-tensor value of the ground-to-A comparison.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, algebraTensorComparison(x ⊗[k] y) = x ⊗[A] y for a regular-coefficient p-word x and
an M-coefficient q-word y. -/
theorem algebraTensorComparison_tmul (p q : ℕ)
    (x : ULift.{w} A ⊗[k] TensorPower k p A) (y : M ⊗[k] TensorPower k q A) :
    algebraTensorComparison k A M p q (x ⊗ₜ[k] y) = x ⊗ₜ[A] y :=
  TensorProduct.mapOfCompatibleSMul_tmul _ _ _ _ _ _ _

/-- The ground-to-A coefficient tensor comparison is surjective.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, every element of the A-balanced two-word tensor has a preimage under
algebraTensorComparison. -/
theorem algebraTensorComparison_surjective (p q : ℕ) :
    Function.Surjective (algebraTensorComparison k A M p q) :=
  TensorProduct.mapOfCompatibleSMul_surjective _ _ _ _ _

/-- Balanced shuffle after ground comparison is the coefficient chain pairing.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, the k-linear restriction of algebraShufflePairCut(p,q), composed with
algebraTensorComparison(p,q), equals the (p,q) component of the Hochschild coefficient
pairing. -/
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

/-- A middle regular coefficient moves onto the second coefficient module.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, (ULift.up(c) ⊗ x) ⊗[A] (m ⊗ y) = (ULift.up(1_A) ⊗ x) ⊗[A] ((c • m) ⊗ y). -/
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
