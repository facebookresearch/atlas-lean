/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficients
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleUnit
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleChainPairing
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The coefficient diagonal and Hochschild shuffle pairing

Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module. In equal
simplicial degree n, the diagonal sends (a₀ ⊗ a) ⊗ (m ⊗ b) to (a₀.down • m) ⊗ (i ↦ aᵢbᵢ). It
commutes with each coefficient-bar face. Composing its alternating-face chain map with the
signed Eilenberg–Zilber shuffle gives a pairing Cₚ(ULift A) ⊗ Cᵩ(M) → Cₚ₊ᵩ(M).

For commutative Hochschild diagonals, see J.-L. Loday, Cyclic Homology, 2nd ed., §§4.2.1–4.2.2
and 4.2.10.
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

/-- The regular coefficient action in the Hochschild diagonal.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, ULift A ⊗[k]
M maps to M by a₀ ⊗ m ↦ a₀.down • m. -/
def diagonalCoefficient : ULift.{w} A ⊗[k] M →ₗ[k] M :=
  (coefficientTensorAction k A M).comp
    (TensorProduct.map (ULift.moduleEquiv : ULift.{w} A ≃ₗ[k] A).toLinearMap LinearMap.id)

/-- The pure coefficient value of the Hochschild diagonal.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
diagonalCoefficient(a₀ ⊗ m) = a₀.down • m, retaining the lifted regular coefficient. -/
lemma diagonalCoefficient_tmul (a0 : ULift.{w} A) (m : M) :
    diagonalCoefficient k A M (a0 ⊗ₜ[k] m) = a0.down • m := by
  unfold diagonalCoefficient
  rw [LinearMap.comp_apply, TensorProduct.map_tmul]
  change TensorProduct.lift (Algebra.lsmul k k M : A →ₐ[k] Module.End k M).toLinearMap
      (a0.down ⊗ₜ[k] m) = _
  rw [TensorProduct.lift.tmul]
  exact Algebra.lsmul_apply k k M a0.down m

/-- Coordinatewise multiplication of two equal-length tensor tails.

For a commutative ring k and a commutative k-algebra A, this k-linear map A⊗n ⊗[k] A⊗n → A⊗n
multiplies corresponding entries of the two words. -/
def diagonalTail (n : ℕ) :
    TensorPower k n A ⊗[k] TensorPower k n A →ₗ[k] TensorPower k n A :=
  TensorProduct.lift (PiTensorProduct.map₂ (fun _ : Fin n => LinearMap.mul k A))

/-- The equal-degree diagonal tail formula.

For a commutative ring k, a commutative k-algebra A and a,b : Fin n → A, diagonalTail(tprod(a)
⊗ tprod(b)) = tprod(i ↦ aᵢbᵢ). -/
lemma diagonalTail_tprod (n : ℕ) (a b : Fin n → A) :
    diagonalTail k A n
      (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
      PiTensorProduct.tprod k (fun i => a i * b i) := by
  unfold diagonalTail
  rw [TensorProduct.lift.tmul, PiTensorProduct.map₂_tprod_tprod]
  simp only [LinearMap.mul_apply']

/-- The raw coefficient-and-tail diagonal in degree n.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, combine a
regular-coefficient n-word and an M-coefficient n-word by multiplying corresponding A entries
and applying the regular head to M. -/
def diagonalRaw (n : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k n A) ⊗[k]
        (M ⊗[k] TensorPower k n A) →ₗ[k] M ⊗[k] TensorPower k n A :=
  (TensorProduct.map (diagonalCoefficient k A M)
    (diagonalTail k A n)).comp
    (TensorProduct.tensorTensorTensorComm k (ULift.{w} A) (TensorPower k n A)
      M (TensorPower k n A)).toLinearMap

/-- The complete pure-word formula for the raw Hochschild diagonal.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, (a₀ ⊗
tprod(a)) ⊗ (m ⊗ tprod(b)) maps to (a₀.down • m) ⊗ tprod(i ↦ aᵢbᵢ). -/
lemma diagonalRaw_tprod (n : ℕ) (a0 : ULift.{w} A) (m : M)
    (a b : Fin n → A) :
    diagonalRaw k A M n
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
      (a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k (fun i => a i * b i) := by
  unfold diagonalRaw
  change TensorProduct.map (diagonalCoefficient k A M)
      (diagonalTail k A n)
      ((TensorProduct.tensorTensorTensorComm k (ULift.{w} A) (TensorPower k n A)
        M (TensorPower k n A))
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b))) = _
  rw [TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
    diagonalCoefficient_tmul, diagonalTail_tprod]

/-- A symmetric Hochschild face in raw tensor coordinates.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, face i :
Cₙ₊₁(M) → Cₙ(M) acts on the first coefficient when i=0, multiplies adjacent entries for
0<i<n+1, and acts by the last coefficient when i=n+1. -/
def rawFace (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of k (M ⊗[k] TensorPower k (n + 1) A) ⟶
      ModuleCat.of k (M ⊗[k] TensorPower k n A) :=
  (coefficientBarObjIso k A M (n + 1)).inv ≫
    (coefficientBar k A M).δ i ≫
      (coefficientBarObjIso k A M n).hom

/-- The three cases of a symmetric raw face on a tensor word.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, face zero
removes a₀ and acts by a₀ on m; face n+1 removes aₙ and acts by aₙ; face i=j+1 multiplies
aⱼaⱼ₊₁. This is an unsigned face formula. -/
lemma rawFace_tprod (n : ℕ) (i : Fin (n + 2)) (m : M)
    (a : Fin (n + 1) → A) :
    (rawFace k A M n i).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      Fin.cases
        ((a 0 • m) ⊗ₜ[k] PiTensorProduct.tprod k
          (ModuleCat.Algebra.Hochschild.hochschildDropFirst a))
        (Fin.lastCases
          ((a (Fin.last n) • m) ⊗ₜ[k] PiTensorProduct.tprod k
            (ModuleCat.Algebra.Hochschild.hochschildDropLast a))
          (fun j : Fin n => m ⊗ₜ[k] PiTensorProduct.tprod k
            (ModuleCat.Algebra.Hochschild.hochschildMulAdjacent j a))) i := by
  let := Module.oppositeOfCommutingAction A M
  let := Module.oppositeOfCommutingAction_actionsComm A M
  let := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  let := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  change (ModuleCat.Algebra.Hochschild.face k A M n i).hom
      (m ⊗ₜ[k] PiTensorProduct.tprod k a) = _
  rw [ModuleCat.Algebra.Hochschild.face_tprod]
  rfl

/-- The raw diagonal commutes with each equal-degree face.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, applying the
raw diagonal in degree n+1 and then face i equals applying face i to both source words and
then the degree-n diagonal. -/
lemma diagonalRaw_face (n : ℕ) (i : Fin (n + 2)) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  ModuleCat.ofHom (diagonalRaw k A M (n + 1)) ≫
      rawFace k A M n i =
    (rawFace k A (ULift.{w} A) n i ⊗ₘ
      rawFace k A M n i) ≫
        ModuleCat.ofHom (diagonalRaw k A M n) := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  apply ModuleCat.hom_ext
  apply TensorProduct.curry_injective
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro a0 a
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m b
  change (rawFace k A M n i).hom
      (diagonalRaw k A M (n + 1)
        ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
          (m ⊗ₜ[k] PiTensorProduct.tprod k b))) =
    diagonalRaw k A M n
      (((rawFace k A (ULift.{w} A) n i).hom
          (a0 ⊗ₜ[k] PiTensorProduct.tprod k a)) ⊗ₜ[k]
        ((rawFace k A M n i).hom
          (m ⊗ₜ[k] PiTensorProduct.tprod k b)))
  rw [diagonalRaw_tprod, rawFace_tprod,
    rawFace_tprod, rawFace_tprod]
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
  · simp only [Fin.cases_zero, diagonalRaw_tprod]
    change ((a 0 * b 0) • (a0.down • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j : Fin n => a j.succ * b j.succ) =
      ((a 0 * a0.down) • (b 0 • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j : Fin n => a j.succ * b j.succ)
    congr 1
    simp only [smul_smul]
    rw [mul_right_comm]
  · simp only [Fin.cases_succ, Fin.lastCases_last, diagonalRaw_tprod]
    change ((a (Fin.last n) * b (Fin.last n)) • (a0.down • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j : Fin n => a j.castSucc * b j.castSucc) =
      ((a (Fin.last n) * a0.down) • (b (Fin.last n) • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun j : Fin n => a j.castSucc * b j.castSucc)
    congr 1
    simp only [smul_smul]
    rw [mul_right_comm]
  · simp only [Fin.cases_succ, Fin.lastCases_castSucc, diagonalRaw_tprod]
    congr 1
    apply congrArg (PiTensorProduct.tprod k)
    funext j
    by_cases hj : j = l
    · subst j
      simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent]
      exact mul_mul_mul_comm _ _ _ _
    · simp only [ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, ite_eq_right hj]

/-- The coefficient-bar diagonal component in chain degree n.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, this map
takes degree n of the alternating-face complex of the levelwise tensor product of the two
coefficient bars to Cₙ(M). -/
def diagonalComponent (n : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
    ((coefficientBar k A (ULift.{w} A)) ⊗ (coefficientBar k A M))).X n ⟶ (chainComplex k A M).X n :=
        by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact ((coefficientBarObjIso k A (ULift.{w} A) n).hom ⊗ₘ
    (coefficientBarObjIso k A M n).hom) ≫
      ModuleCat.ofHom (diagonalRaw k A M n)

/-- The coefficient-bar diagonal component intertwines faces.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, its
degree-n+1 component followed by rawFace(i) equals the tensor product of the two simplicial
faces followed by its degree-n component. -/
lemma diagonalComponent_face (n : ℕ) (i : Fin (n + 2)) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  diagonalComponent k A M (n + 1) ≫ rawFace k A M n i =
    ((coefficientBar k A (ULift.{w} A)).δ i ⊗ₘ (coefficientBar k A M).δ i) ≫ diagonalComponent k A M
        n := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  have hX :
      (coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ≫
        rawFace k A (ULift.{w} A) n i =
      (coefficientBar k A (ULift.{w} A)).δ i ≫ (coefficientBarObjIso k A (ULift.{w} A) n).hom := by
    simp only [rawFace, Iso.hom_inv_id_assoc]
  have hY :
      (coefficientBarObjIso k A M (n + 1)).hom ≫ rawFace k A M n i =
      (coefficientBar k A M).δ i ≫ (coefficientBarObjIso k A M n).hom := by
    simp only [rawFace, Iso.hom_inv_id_assoc]
  have hTensor :
      ((coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ⊗ₘ
        (coefficientBarObjIso k A M (n + 1)).hom) ≫
        (rawFace k A (ULift.{w} A) n i ⊗ₘ rawFace k A M n i) =
      ((coefficientBar k A (ULift.{w} A)).δ i ⊗ₘ
        (coefficientBar k A M).δ i) ≫
        ((coefficientBarObjIso k A (ULift.{w} A) n).hom ⊗ₘ
          (coefficientBarObjIso k A M n).hom) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, hX, hY,
      MonoidalCategory.tensorHom_comp_tensorHom]
  have hTyped :
      (((coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ⊗ₘ
          (coefficientBarObjIso k A M (n + 1)).hom) ≫
        ModuleCat.ofHom (diagonalRaw k A M (n + 1))) ≫
        rawFace k A M n i =
      ((coefficientBar k A (ULift.{w} A)).δ i ⊗ₘ
        (coefficientBar k A M).δ i) ≫
        (((coefficientBarObjIso k A (ULift.{w} A) n).hom ⊗ₘ
          (coefficientBarObjIso k A M n).hom) ≫
          ModuleCat.ofHom (diagonalRaw k A M n)) := by
    calc
      _ = ((coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ⊗ₘ
          (coefficientBarObjIso k A M (n + 1)).hom) ≫
          (ModuleCat.ofHom (diagonalRaw k A M (n + 1)) ≫
            rawFace k A M n i) := Category.assoc _ _ _
      _ = ((coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ⊗ₘ
          (coefficientBarObjIso k A M (n + 1)).hom) ≫
          ((rawFace k A (ULift.{w} A) n i ⊗ₘ
            rawFace k A M n i) ≫
              ModuleCat.ofHom (diagonalRaw k A M n)) :=
        congrArg (fun f => ((coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ⊗ₘ
          (coefficientBarObjIso k A M (n + 1)).hom) ≫ f)
          (diagonalRaw_face k A M n i)
      _ = (((coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ⊗ₘ
          (coefficientBarObjIso k A M (n + 1)).hom) ≫
          (rawFace k A (ULift.{w} A) n i ⊗ₘ
            rawFace k A M n i)) ≫
            ModuleCat.ofHom (diagonalRaw k A M n) :=
        (Category.assoc _ _ _).symm
      _ = (((coefficientBar k A (ULift.{w} A)).δ i ⊗ₘ
          (coefficientBar k A M).δ i) ≫
          ((coefficientBarObjIso k A (ULift.{w} A) n).hom ⊗ₘ
            (coefficientBarObjIso k A M n).hom)) ≫
            ModuleCat.ofHom (diagonalRaw k A M n) :=
        congrArg (fun f => f ≫ ModuleCat.ofHom (diagonalRaw k A M n)) hTensor
      _ = _ := Category.assoc _ _ _
  exact hTyped

/-- The symmetric target differential is the alternating sum of raw faces.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, d : Cₙ₊₁ → Cₙ
is ∑ᵢ₌₀ⁿ⁺¹ (-1)ⁱ rawFace(n,i), with integer signs. -/
lemma targetDifferential (n : ℕ) :
    (chainComplex k A M).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • rawFace k A M n i := by
  let := Module.oppositeOfCommutingAction A M
  let := Module.oppositeOfCommutingAction_actionsComm A M
  let := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  let := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  change (ModuleCat.Algebra.Hochschild.chainComplex k A M).d (n + 1) n = _
  rw [ModuleCat.Algebra.Hochschild.chainComplex_d,
    ModuleCat.Algebra.Hochschild.boundary_eq_sum]
  rfl

/-- The chain map induced by the coefficient simplicial diagonal.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the
alternating-face complex of coefficientBar(ULift A) ⊗ coefficientBar(M) maps to
chainComplex(M) through diagonalComponent in every degree. -/
def diagonalChainMap :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
      ((coefficientBar k A (ULift.{w} A)) ⊗ (coefficientBar k A M)) ⟶
    chainComplex k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact ChainComplex.ofHom (diagonalComponent k A M) (by
    intro n
    have hSum :
        (((coefficientBarObjIso k A (ULift.{w} A) (n + 1)).hom ⊗ₘ
          (coefficientBarObjIso k A M (n + 1)).hom) ≫
          ModuleCat.ofHom (diagonalRaw k A M (n + 1))) ≫
          (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • rawFace k A M n i) =
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          ((coefficientBar k A (ULift.{w} A)).δ i ⊗ₘ
            (coefficientBar k A M).δ i)) ≫
          (((coefficientBarObjIso k A (ULift.{w} A) n).hom ⊗ₘ
            (coefficientBarObjIso k A M n).hom) ≫
            ModuleCat.ofHom (diagonalRaw k A M n)) := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      exact Finset.sum_congr rfl (fun i _ => congrArg
        (fun f => (-1 : ℤ) ^ (i : ℕ) • f)
        (diagonalComponent_face k A M n i))
    have hSource :
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
          ((coefficientBar k A (ULift.{w} A)) ⊗
            (coefficientBar k A M))).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          ((coefficientBar k A (ULift.{w} A)).δ i ⊗ₘ
            (coefficientBar k A M).δ i) := by
      rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.AlternatingFaceMapComplex.objD]
      rfl
    have hTargetComp := congrArg
      (fun f : (chainComplex k A M).X (n + 1) ⟶
          (chainComplex k A M).X n =>
        diagonalComponent k A M (n + 1) ≫ f)
      (targetDifferential k A M n)
    have hSourceComp := congrArg
      (fun f : ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
          ((coefficientBar k A (ULift.{w} A)) ⊗
            (coefficientBar k A M))).X (n + 1) ⟶
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v w} k)).obj
          ((coefficientBar k A (ULift.{w} A)) ⊗
            (coefficientBar k A M))).X n =>
        f ≫ diagonalComponent k A M n) hSource
    exact hTargetComp.trans (hSum.trans hSourceComp.symm))

/-- The signed coefficient Hochschild chain pairing.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the
Eilenberg–Zilber shuffle followed by the diagonal gives a chain pairing Cₚ(ULift A) ⊗ Cᵩ(M) →
Cₚ₊ᵩ(M). The shuffle uses integer permutation signs. -/
def pairing :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  HomologicalComplex.ChainGradedPairing
    (chainComplex k A (ULift.{w} A)) (chainComplex k A M) (chainComplex k A M) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.tensorHom
      (chainComplexIso k A (ULift.{w} A)).hom
      (chainComplexIso k A M).hom ≫
    AlgebraicTopology.EilenbergZilber.alternatingPairing (coefficientBar k A (ULift.{w} A))
        (coefficientBar k A M) ≫
      diagonalChainMap k A M


section PairingComponents

/-- The shuffle-and-diagonal formula for one coefficient pairing component.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the (p,q)
component first uses the two coefficient-bar chain isomorphisms, then shuffleBidegree(p,q),
then diagonalComponent(p+q). -/
theorem pairing_pair (p q : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  (pairing.{u, v, w} k A M).pair p q =
    (((chainComplexIso.{u, v, max v w} k A (ULift.{w} A)).hom.f p) ⊗ₘ
      ((chainComplexIso.{u, v, w} k A M).hom.f q)) ≫
    AlgebraicTopology.EilenbergZilber.shuffleBidegree
      (C := ModuleCat.{max u v w} k)
      (coefficientBar.{u, v, max v w} k A (ULift.{w} A)) (coefficientBar.{u, v, w} k A M) p q ≫
    diagonalComponent.{u, v, w} k A M (p + q) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  let X : SimplicialObject (ModuleCat.{max u v w} k) :=
    coefficientBar.{u, v, max v w} k A (ULift.{w} A)
  let Y : SimplicialObject (ModuleCat.{max u v w} k) :=
    coefficientBar.{u, v, w} k A M
  let K : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    chainComplex.{u, v, max v w} k A (ULift.{w} A)
  let L : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
    chainComplex.{u, v, w} k A M
  let f := (chainComplexIso.{u, v, max v w} k A (ULift.{w} A)).hom
  let g := (chainComplexIso.{u, v, w} k A M).hom
  let N := AlgebraicTopology.EilenbergZilber.alternatingPairing
    (C := ModuleCat.{max u v w} k) X Y
  let D := diagonalChainMap.{u, v, w} k A M
  let P : HomologicalComplex.ChainGradedPairing K L
      ((AlgebraicTopology.alternatingFaceMapComplex
        (ModuleCat.{max u v w} k)).obj (X ⊗ Y)) :=
    HomologicalComplex.tensorHom f g ≫ N
  have hDefinition : pairing.{u, v, w} k A M = P.postcomp D := by
    change HomologicalComplex.tensorHom f g ≫ N ≫ D =
      (HomologicalComplex.tensorHom f g ≫ N) ≫ D
    exact (Category.assoc _ _ _).symm
  have hPre : (f.f p ⊗ₘ g.f q) ≫ N.pair p q = P.pair p q := by
    have h := HomologicalComplex.ChainGradedPairing.pair_naturality
      P N f g (𝟙 _)
      (show HomologicalComplex.tensorHom f g ≫ N = P ≫ 𝟙 _ from
        (Category.comp_id P).symm) p q
    simpa only [HomologicalComplex.id_f, Category.comp_id] using h
  calc
    (pairing.{u, v, w} k A M).pair p q = (P.postcomp D).pair p q :=
      congrArg (fun Q : HomologicalComplex.ChainGradedPairing K L L => Q.pair p q) hDefinition
    _ = P.pair p q ≫ D.f (p + q) :=
      HomologicalComplex.ChainGradedPairing.pair_postcomp P D p q
    _ = (f.f p ⊗ₘ g.f q) ≫ N.pair p q ≫ D.f (p + q) := by
      rw [← hPre, Category.assoc]
    _ = _ := by
      rw [AlgebraicTopology.EilenbergZilber.alternatingPairing_pair
        (C := ModuleCat.{max u v w} k) X Y p q]
      simp only [Category.assoc,
        AlgebraicTopology.EilenbergZilber.ιTensorObj_comp_shuffleComponent_assoc,
        AlgebraicTopology.alternatingFaceMapComplex_obj_X, eqToHom_refl,
        Category.id_comp]
      rfl

/-- The coefficient pairing in bidegree zero retains the head action.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, two empty
words with heads a₀ and m pair to (a₀.down • m) ⊗ the empty tensor word. -/
theorem pairing_pair_zero_zero_tprod (a0 : ULift.{w} A) (m : M)
    (a b : Fin 0 → A) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  ((pairing.{u, v, w} k A M).pair 0 0).hom
      ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
        (m ⊗ₜ[k] PiTensorProduct.tprod k b)) =
    (a0.down • m) ⊗ₜ[k] PiTensorProduct.tprod k (fun i => a i * b i) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)

  have hl : (AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0).leftHom =
      𝟙 ⦋0⦌ :=
    SimplexCategory.hom_zero_zero _
  have hr : (AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0).rightHom =
      𝟙 ⦋0⦌ :=
    SimplexCategory.hom_zero_zero _
  have hmX : (coefficientBar.{u, v, max v w} k A (ULift.{w} A)).map (𝟙 ⦋0⦌).op =
      𝟙 ((coefficientBar.{u, v, max v w} k A (ULift.{w} A)).obj (Opposite.op ⦋0⦌)) := by
    rw [op_id]
    exact (coefficientBar.{u, v, max v w} k A (ULift.{w} A)).map_id _
  have hmY : (coefficientBar.{u, v, w} k A M).map (𝟙 ⦋0⦌).op =
      𝟙 ((coefficientBar.{u, v, w} k A M).obj (Opposite.op ⦋0⦌)) := by
    rw [op_id]
    exact (coefficientBar.{u, v, w} k A M).map_id _
  have hcomp : (pairing.{u, v, w} k A M).pair 0 0 = ModuleCat.ofHom (diagonalRaw.{u, v, w} k A M 0)
      := by
    rw [pairing_pair.{u, v, w} k A M,
      AlgebraicTopology.EilenbergZilber.shuffleBidegree_right_zero_eq_summand
        (C := ModuleCat.{max u v w} k)
        (coefficientBar.{u, v, max v w} k A (ULift.{w} A))
        (coefficientBar.{u, v, w} k A M) 0]
    change ((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) 0).inv ⊗ₘ
        (coefficientBarObjIso.{u, v, w} k A M 0).inv) ≫
      (AlgebraicTopology.EilenbergZilber.shuffleSignZ
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0) •
        ((coefficientBar.{u, v, max v w} k A (ULift.{w} A)).map
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0).leftHom.op ⊗ₘ
          (coefficientBar.{u, v, w} k A M).map
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle 0).rightHom.op)) ≫
      (((coefficientBarObjIso.{u, v, max v w} k A (ULift.{w} A) 0).hom ⊗ₘ
        (coefficientBarObjIso.{u, v, w} k A M 0).hom) ≫
          ModuleCat.ofHom (diagonalRaw.{u, v, w} k A M 0)) = _
    rw [AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle_sign,
      hl, hr, hmX, hmY, one_smul, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Iso.inv_hom_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rfl
  rw [hcomp]
  change diagonalRaw.{u, v, w} k A M 0
    ((a0 ⊗ₜ[k] PiTensorProduct.tprod k a) ⊗ₜ[k]
      (m ⊗ₜ[k] PiTensorProduct.tprod k b)) = _
  exact diagonalRaw_tprod.{u, v, w} k A M 0 a0 m a b

end PairingComponents

end ModuleCat.Algebra.Hochschild.Symmetric
