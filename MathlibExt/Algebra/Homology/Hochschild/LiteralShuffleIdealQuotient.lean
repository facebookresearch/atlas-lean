/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositive
public import MathlibExt.Algebra.Homology.ChainGradedPairingFirstPositiveImages
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricDiagonal
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricShuffleCoordinates

/-!
# The full coefficient-ideal shuffle quotient

The ideal action uses a positive-degree regular first factor
and the entire coefficient complex, including degree zero.
The proper positive-shuffle quotient instead requires both
input degrees to be positive. Normalization acts on tensor
tails and retains the first-factor coefficient unit.

Reference: Loday, Cyclic Homology, second edition,
§4.2, printed p.126.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped MonoidalCategory TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The zero coefficient block is retained by the full signed shuffle in every degree. -/
theorem pairing_pair_right_zero_tprod (n : ℕ) (a0 : ULift.{w} A) (m : M)
    (a : Fin n → A) (b : Fin 0 → A) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((pairing.{u, v, w} k A M).pair n 0).hom
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
        (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    (a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k a := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  classical
  let : Unique (AlgebraicTopology.EilenbergZilber.Shuffle n 0) :=
    { default := AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle n
      uniq := fun s => AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle s }
  have h := pairing_pair_tprod k A M n 0 a0 m a b
  have hd : (default : AlgebraicTopology.EilenbergZilber.Shuffle n 0) =
      AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle n :=
    AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle _
  rw [Fintype.sum_unique, hd, AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle_sign,
    one_smul] at h
  have hw : (fun i : Fin (n + 0) => Fin.append a b
      ((AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle n).perm.symm i)) = a := by
    funext i
    exact Fin.append_left a b i
  exact h.trans (congrArg (fun c => (a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k c) hw)

/-- Head one in the positive algebra factor acts as the identity on the full coefficient word. -/
theorem pairing_pair_head_one_right_zero (n : ℕ) (m : M) (a : Fin n → A) (b : Fin 0 → A) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((pairing.{u, v, w} k A M).pair n 0).hom
      (((ULift.up (1 : A) : ULift.{w} A) ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
        (m ⊗ₜ[k] PiTensorProduct.tprod k b)) = m ⊗ₜ[k] PiTensorProduct.tprod k a := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact (pairing_pair_right_zero_tprod k A M n (ULift.up 1) m a b).trans
    (congrArg (fun x : M => x ⊗ₜ[k] PiTensorProduct.tprod k a) (one_smul A m))

/-- Actual cokernel of the positive regular factor acting on the full coefficient chains. -/
def literalShuffleIdealQuotient : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.firstPositiveCokernel (pairing.{u, v, w} k A M)
    (boundary_one_zero k A (ULift.{w} A))

/-- Native projection from the original coefficient chain model to that literal quotient. -/
def literalShuffleIdealProjection : chainComplex k A M ⟶ literalShuffleIdealQuotient k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.firstPositiveProjection (pairing.{u, v, w} k A M)
    (boundary_one_zero k A (ULift.{w} A))

/-- Normalize the target first, then quotient by the pushed-forward ideal image. -/
def literalNormalizedShuffleIdealQuotient : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.firstPositiveCokernel
      ((pairing.{u, v, w} k A M).postcomp (normalizationProjection.{u, v, w} k A M))
      (boundary_one_zero k A (ULift.{w} A))

/-- The normalization map induces the ideal-image quotient map. -/
def literalNormalizationQuotientMap :
    literalShuffleIdealQuotient k A M ⟶ literalNormalizedShuffleIdealQuotient k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.firstPositiveCokernelPostcompMap (pairing.{u, v, w} k A M)
      (boundary_one_zero k A (ULift.{w} A)) (normalizationProjection.{u, v, w} k A M)

theorem literalNormalizationQuotientMap_projection :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  literalShuffleIdealProjection k A M ≫ literalNormalizationQuotientMap k A M =
    normalizationProjection.{u, v, w} k A M ≫
      HomologicalComplex.ChainGradedPairing.firstPositiveProjection
        ((pairing.{u, v, w} k A M).postcomp (normalizationProjection.{u, v, w} k A M))
        (boundary_one_zero k A (ULift.{w} A)) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.firstPositiveProjection_postcompMap
    (pairing.{u, v, w} k A M) (boundary_one_zero k A (ULift.{w} A))
    (normalizationProjection.{u, v, w} k A M)

end ModuleCat.Algebra.Hochschild.Symmetric
