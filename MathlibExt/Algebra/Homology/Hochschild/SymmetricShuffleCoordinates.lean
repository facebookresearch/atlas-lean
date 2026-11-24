/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricDiagonal
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleUnit
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleCoordinates
public import MathlibExt.Algebra.Homology.Hochschild.SimplexCoordinates

/-!
# Signed coefficient shuffle coordinates

The Eilenberg–Zilber shuffle and coefficient diagonal
give a signed sum indexed by ordered block shuffles.
Ordinal surjections and complementary edge ranks
identify its tensor representatives in every degree
and describe their target normalization.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct Simplicial MonoidalCategory BigOperators ModuleCat.UniverseTensor

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M]

attribute [local instance] opModule actionsComm kOpComm kOpTower

/-- One unsigned native shuffle term, before applying the original permutation sign. -/
def rawShuffleTerm {p q : ℕ} (s : AlgebraicTopology.EilenbergZilber.Shuffle p q) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
      (M ⊗[k] TensorPower k q A) →ₗ[k] M ⊗[k] TensorPower k (p + q) A :=
  (diagonalRaw.{u, v, w} k A M (p + q)).comp
    (TensorProduct.map (ModuleCat.Algebra.Hochschild.simplexMap k A (ULift.{w} A) s.leftHom).hom
      (ModuleCat.Algebra.Hochschild.simplexMap k A M s.rightHom).hom)


/-- An unsigned shuffle term is the original coefficient times the σ⁻¹ tensor word. -/
theorem rawShuffleTerm_tprod {p q : ℕ}
    (s : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (a0 : ULift.{w} A) (m : M) (a : Fin p → A) (b : Fin q → A) :
    rawShuffleTerm k A M s
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
      (a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k
        (fun i => Fin.append a b (s.perm.symm i)) := by
  rw [rawShuffleTerm, LinearMap.comp_apply, TensorProduct.map_tmul,
    ModuleCat.Algebra.Hochschild.simplexMap_of_epi_tprod,
    ModuleCat.Algebra.Hochschild.simplexMap_of_epi_tprod, diagonalRaw_tprod]
  exact congrArg (fun c : Fin (p + q) → A =>
    (a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k c)
      (AlgebraicTopology.EilenbergZilber.Shuffle.pullbackEdges_mul s a b)

/-- The native signed shuffle sum in the original coefficient-first tensor carriers. -/
def signedRawShuffle (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
      (M ⊗[k] TensorPower k q A) →ₗ[k] M ⊗[k] TensorPower k (p + q) A := by
  classical
  exact ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
    AlgebraicTopology.EilenbergZilber.shuffleSignZ s • rawShuffleTerm k A M s


/-- The signed shuffle acts on every original tensor word by the full σ⁻¹ sum. -/
theorem signedRawShuffle_tprod (p q : ℕ) (a0 : ULift.{w} A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
    signedRawShuffle k A M p q
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          ((a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k
            (fun i => Fin.append a b (s.perm.symm i))) := by
  classical
  simp only [signedRawShuffle, LinearMap.sum_apply, LinearMap.smul_apply,
    rawShuffleTerm_tprod]

/-- Evaluating the native signed map retains every coefficient simplex action. -/
theorem signedRawShuffle_apply (p q : ℕ)
    (x : ULift.{w} A ⊗[k] TensorPower k p A)
    (y : M ⊗[k] TensorPower k q A) :
    signedRawShuffle k A M p q (x ⊗ₜ[k] y) =
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          diagonalRaw.{u, v, w} k A M (p + q)
            (((ModuleCat.Algebra.Hochschild.simplexMap k A (ULift.{w} A) s.leftHom).hom x) ⊗ₜ[k]
              ((ModuleCat.Algebra.Hochschild.simplexMap k A M s.rightHom).hom y)) := by
  classical
  simp only [signedRawShuffle, LinearMap.sum_apply, LinearMap.smul_apply,
    rawShuffleTerm, LinearMap.comp_apply, TensorProduct.map_tmul]

/-- The chain pairing is exactly the signed native map in raw tensor coordinates. -/
theorem pairing_pair_signedRawShuffle (p q : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  ((pairing.{u, v, w} k A M).pair p q).hom = signedRawShuffle k A M p q := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  classical
  have hterm (t : AlgebraicTopology.EilenbergZilber.Shuffle p q) :
      (((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) p).inv ⊗ₘ
          (coefficientBarObjIso.{u, v, w} k A M q).inv) ≫
        AlgebraicTopology.EilenbergZilber.shuffleSummand
          (coefficientBar.{u, v, max v w} k A (ULift.{w} A))
          (coefficientBar.{u, v, w} k A M) t ≫
        diagonalComponent.{u, v, w} k A M (p + q)).hom =
      AlgebraicTopology.EilenbergZilber.shuffleSignZ t • rawShuffleTerm k A M t := by
    change ((((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) p).inv ⊗ₘ
        (coefficientBarObjIso.{u, v, w} k A M q).inv) ≫
        (AlgebraicTopology.EilenbergZilber.shuffleSignZ t •
          ((coefficientBar.{u, v, max v w} k A (ULift.{w} A)).map t.leftHom.op ⊗ₘ
            (coefficientBar.{u, v, w} k A M).map t.rightHom.op)) ≫
        (((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) (p + q)).hom ⊗ₘ
          (coefficientBarObjIso.{u, v, w} k A M (p + q)).hom) ≫
            ModuleCat.ofHom (diagonalRaw.{u, v, w} k A M (p + q)))).hom) = _
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ModuleCat.hom_zsmul]
    congr 1
    change ((((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) p).inv ⊗ₘ
        (coefficientBarObjIso.{u, v, w} k A M q).inv) ≫
        ((coefficientBar.{u, v, max v w} k A (ULift.{w} A)).map t.leftHom.op ⊗ₘ
          (coefficientBar.{u, v, w} k A M).map t.rightHom.op) ≫
        (((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) (p + q)).hom ⊗ₘ
          (coefficientBarObjIso.{u, v, w} k A M (p + q)).hom) ≫
            ModuleCat.ofHom (diagonalRaw.{u, v, w} k A M (p + q)))).hom) =
      ((ModuleCat.Algebra.Hochschild.simplexMap k A (ULift.{w} A) t.leftHom ⊗ₘ
        ModuleCat.Algebra.Hochschild.simplexMap k A M t.rightHom) ≫
          ModuleCat.ofHom (diagonalRaw.{u, v, w} k A M (p + q))).hom
    congr 1
    simp only [ModuleCat.Algebra.Hochschild.simplexMap,
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
    rfl
  rw [pairing_pair.{u, v, w} k A M]
  change (((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) p).inv ⊗ₘ
      (coefficientBarObjIso.{u, v, w} k A M q).inv) ≫
    AlgebraicTopology.EilenbergZilber.shuffleBidegree
      (coefficientBar.{u, v, max v w} k A (ULift.{w} A))
      (coefficientBar.{u, v, w} k A M) p q ≫
    diagonalComponent.{u, v, w} k A M (p + q)).hom = _
  unfold AlgebraicTopology.EilenbergZilber.shuffleBidegree signedRawShuffle
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, ModuleCat.hom_sum]
  exact Finset.sum_congr rfl (fun t _ => hterm t)

/-- Every bidegree of the original chain pairing has the full signed tensor-word formula. -/
theorem pairing_pair_tprod (p q : ℕ) (a0 : ULift.{w} A) (m : M)
    (a : Fin p → A) (b : Fin q → A) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  ((pairing.{u, v, w} k A M).pair p q).hom
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
        (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
      AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
        ((a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k
          (fun i => Fin.append a b (s.perm.symm i))) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  rw [pairing_pair_signedRawShuffle]
  exact signedRawShuffle_tprod k A M p q a0 m a b

/-- Both empty blocks give the original diagonal, without normalization of either input. -/
theorem signedRawShuffle_zero_zero :
    signedRawShuffle k A M 0 0 = diagonalRaw.{u, v, w} k A M 0 := by
  classical
  letI : Unique (AlgebraicTopology.EilenbergZilber.Shuffle 0 0) :=
    { default := AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0
      uniq := fun s => AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle s }
  unfold signedRawShuffle
  rw [Fintype.sum_unique]
  have hdefault :
      (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 0) =
        AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0 :=
    AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle _
  rw [hdefault, AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle_sign, one_smul]
  have hleft : (AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0).leftHom = 𝟙 ⦋0⦌ := by
    exact SimplexCategory.hom_zero_zero _
  have hright : (AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0).rightHom = 𝟙 ⦋0⦌ := by
    exact SimplexCategory.hom_zero_zero _
  simp only [rawShuffleTerm, hleft, hright, ModuleCat.Algebra.Hochschild.simplexMap_id,
    ModuleCat.hom_id, TensorProduct.map_id, LinearMap.comp_id]


/-- Target-only normalization retains the same raw signed shuffle, then the original quotient. -/
theorem pairing_pair_target_normalization (p q : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  (((pairing.{u, v, w} k A M).postcomp (normalizationProjection k A M)).pair p q).hom =
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A M (p + q)).hom.comp
      (signedRawShuffle k A M p q) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  rw [HomologicalComplex.ChainGradedPairing.pair_postcomp]
  change ((normalizationProjection k A M).f (p + q)).hom.comp
      (((pairing.{u, v, w} k A M).pair p q).hom) = _
  rw [pairing_pair_signedRawShuffle]
  change ((ModuleCat.Algebra.Hochschild.normalizationProjection k A M).f (p + q)).hom.comp
      (signedRawShuffle k A M p q) = _
  rw [ModuleCat.Algebra.Hochschild.normalizationProjection_f]
  rfl

/-- The diagonal's coefficient and pointwise-tail products survive target normalization as classes. -/
theorem diagonalRaw_target_normalization_tprod (n : ℕ) (a0 : ULift.{w} A) (m : M)
    (a b : Fin n → A) :
    ((normalizationProjection k A M).f n).hom
        (diagonalRaw.{u, v, w} k A M n
          ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
            (m ⊗ₜ[k] PiTensorProduct.tprod k b))) =
      (a0.down • m) ⊗ₜ[k]
        PiTensorProduct.tprod k
          (fun i => (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ (a i * b i)) := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  rw [diagonalRaw_tprod]
  change ((ModuleCat.Algebra.Hochschild.normalizationProjection k A M).f n).hom
      ((a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k (fun i => a i * b i)) = _
  rw [ModuleCat.Algebra.Hochschild.normalizationProjection_f]
  exact ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod
    k A M n (a0.down • m) (fun i => a i * b i)

end ModuleCat.Algebra.Hochschild.Symmetric
