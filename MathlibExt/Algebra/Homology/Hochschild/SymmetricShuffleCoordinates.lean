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

Let k be a commutative ring, A a commutative k-algebra and M a compatible symmetric coefficient
module. A (p,q)-shuffle gives a coefficient simplex map on each input, followed by the symmetric
diagonal. On tensor words its unsigned value is (a₀·m) ⊗ ⊗ᵢappend(a,b)(s.perm⁻¹i). Summing with
the integer shuffle signs gives the bidegree component of the symmetric Hochschild chain
pairing.

The formulas include arbitrary p,q : ℕ, with the unique (0,0)-shuffle giving the degree-zero
diagonal. Postcomposing with normalization projects every target tail to A/(k·1). For the
degreewise diagonal, pointwise products are formed in A first and then projected to their
quotient classes. The quotient tails are used as k-modules.

For shuffle products and Hochschild chain coordinates, see J.-L. Loday, Cyclic Homology, second
edition, §4.2.
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For a (p,q)-shuffle s, apply its left and right simplex maps to the degree-p
regular and degree-q coefficient tensors, then apply the degree-p+q symmetric diagonal. The
resulting k-linear map is rawShuffleTerm k A M s. -/
def rawShuffleTerm {p q : ℕ} (s : AlgebraicTopology.EilenbergZilber.Shuffle p q) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
      (M ⊗[k] TensorPower k q A) →ₗ[k] M ⊗[k] TensorPower k (p + q) A :=
  (diagonalRaw.{u, v, w} k A M (p + q)).comp
    (TensorProduct.map (ModuleCat.Algebra.Hochschild.simplexMap k A (ULift.{w} A) s.leftHom).hom
      (ModuleCat.Algebra.Hochschild.simplexMap k A M s.rightHom).hom)


/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For a lifted a₀, m ∈ M and tail words a,b of lengths p,q, rawShuffleTerm(s)
sends (a₀ ⊗ ⊗a) ⊗ (m ⊗ ⊗b) to (a₀·m) ⊗ ⊗ᵢappend(a,b)(s.perm⁻¹i). The coefficient action uses the
underlying A-element of a₀. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For p,q : ℕ, signedRawShuffle is the k-linear map ∑s
shuffleSignZ(s)·rawShuffleTerm(s), over all ordered (p,q)-block shuffles, from the tensor of the
degree-p regular and degree-q coefficient terms to degree p+q. -/
def signedRawShuffle (p q : ℕ) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k]
      (M ⊗[k] TensorPower k q A) →ₗ[k] M ⊗[k] TensorPower k (p + q) A := by
  classical
  exact ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
    AlgebraicTopology.EilenbergZilber.shuffleSignZ s • rawShuffleTerm k A M s


/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For tail words a,b and coefficients a₀,m, signedRawShuffle sends (a₀ ⊗ ⊗a) ⊗
(m ⊗ ⊗b) to ∑s sign(s)·((a₀·m) ⊗ ⊗ᵢappend(a,b)(s.perm⁻¹i)). The sum includes every (p,q)-shuffle
with its integer permutation sign. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For degree-p and degree-q tensors x,y, signedRawShuffle(x ⊗ y) = ∑s
sign(s)·Δₚ₊q(s_Lx ⊗ s_Ry), where s_L,s_R are the coefficient simplex maps of the shuffle's
ordinal surjections and Δ is the raw symmetric diagonal. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For every p,q : ℕ, the underlying linear map of the (p,q)-component of pairing
k A M equals signedRawShuffle k A M p q. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For p,q : ℕ, lifted a₀, m ∈ M and words a,b, the chain pairing component sends
(a₀ ⊗ ⊗a) ⊗ (m ⊗ ⊗b) to ∑s sign(s)·((a₀·m) ⊗ ⊗ᵢappend(a,b)(s.perm⁻¹i)). Both zero and positive
block degrees are included. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For p=q=0 there is a unique shuffle with sign +1. Consequently
signedRawShuffle k A M 0 0 equals diagonalRaw k A M 0, the degree-zero coefficient diagonal. -/
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


/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. In bidegree (p,q), the pairing postcomposed with Hochschild normalization has
underlying linear map Nₚ₊q ∘ signedRawShuffle k A M p q, where N applies A → A/(k·1) to every
tail factor. -/
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

/-- Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module with
symmetric right action. The regular coefficient is a chosen universe lift of A, and the target
coefficient is M. For words a,b of length n and coefficients a₀,m, normalization of Δₙ((a₀ ⊗ ⊗a)
⊗ (m ⊗ ⊗b)) equals (a₀·m) ⊗ ⊗ᵢ[aᵢbᵢ] in M ⊗_k(A/(k·1))^{⊗n}. Each product aᵢbᵢ is formed in A
before taking its k-module quotient class. -/
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
