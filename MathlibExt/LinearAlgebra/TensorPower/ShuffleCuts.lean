/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleUnit
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.Data.Fintype.OfMap

/-!
# Actual signed shuffle multiplication and the two-cut convolution operation

Every cut has the original exact equality p+q=n. Tensor splitting, signed
shuffle multiplication and the original target cast define its endomorphism.
The full two-cut operation includes both empty blocks. Their actual unit
shuffles contribute two identities in positive degree and one identity in
degree zero. The proper-cut identity is proved from that finite index split.

This is the concrete convolution operation. Its equality with a rational
Eulerian-polynomial expansion is a separate theorem and is not assumed here.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct BigOperators

universe u v w

namespace TensorPower

/-- An actual weak cut with its original total degree. -/
abbrev ShuffleDegreeCut (n : ℕ) := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- A proper cut is a weak cut whose two original factors are positive. -/
abbrev ProperShuffleDegreeCut (n : ℕ) :=
  {z : ShuffleDegreeCut n // 0 < z.1.1 ∧ 0 < z.1.2}

/-- The actual bounded pair of block lengths, used to enumerate the original finite cut type. -/
def cutBound (n : ℕ) (z : ShuffleDegreeCut n) : Fin (n + 1) × Fin (n + 1) :=
  (⟨z.1.1, by have h := z.2; omega⟩, ⟨z.1.2, by have h := z.2; omega⟩)

/-- The bounded pair retains both original block lengths. -/
theorem cutBound_injective (n : ℕ) : Function.Injective (cutBound n) := by
  intro z z' h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun t : Fin (n + 1) × Fin (n + 1) => t.1.val) h
  · exact congrArg (fun t : Fin (n + 1) × Fin (n + 1) => t.2.val) h

instance shuffleDegreeCutFintype (n : ℕ) : Fintype (ShuffleDegreeCut n) :=
  Fintype.ofInjective (cutBound n) (cutBound_injective n)

instance properShuffleDegreeCutFintype (n : ℕ) : Fintype (ProperShuffleDegreeCut n) :=
  Fintype.ofFinite _

/-- The actual empty first block at the original total degree. -/
def leftUnitDegreeCut (n : ℕ) : ShuffleDegreeCut n := ⟨(0, n), Nat.zero_add n⟩

/-- The actual empty second block at the original total degree. -/
def rightUnitDegreeCut (n : ℕ) : ShuffleDegreeCut n := ⟨(n, 0), Nat.add_zero n⟩

/-- The weak cut set is two unit cuts plus the proper cuts in positive degree. -/
def shuffleDegreeCutEquivUnitsProper (n : ℕ) (hn : 0 < n) :
    ShuffleDegreeCut n ≃ Fin 2 ⊕ ProperShuffleDegreeCut n where
  toFun z :=
    if hp : z.1.1 = 0 then Sum.inl 0
    else if hq : z.1.2 = 0 then Sum.inl 1
    else Sum.inr ⟨z, Nat.pos_of_ne_zero hp, Nat.pos_of_ne_zero hq⟩
  invFun z := match z with
    | Sum.inl i => Fin.cases (leftUnitDegreeCut n) (fun _ => rightUnitDegreeCut n) i
    | Sum.inr z => z.val
  left_inv z := by
    by_cases hp : z.1.1 = 0
    · simp only [dite_eq_left hp]
      apply Subtype.ext
      apply Prod.ext
      · exact hp.symm
      · have h := z.2; simp only [hp, Nat.zero_add] at h; exact h.symm
    · by_cases hq : z.1.2 = 0
      · simp only [dite_eq_right hp, dite_eq_left hq]
        apply Subtype.ext
        apply Prod.ext
        · have h := z.2; simp only [hq, Nat.add_zero] at h; exact h.symm
        · exact hq.symm
      · simp only [dite_eq_right hp, dite_eq_right hq]
  right_inv z := by
    cases z with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [leftUnitDegreeCut]
      · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        have hcases : Fin.cases (leftUnitDegreeCut n)
            (fun _ : Fin 1 => rightUnitDegreeCut n) (Fin.succ (0 : Fin 1)) = rightUnitDegreeCut n := rfl
        dsimp only
        rw [hcases]
        simp [rightUnitDegreeCut, Nat.ne_of_gt hn]
    | inr z =>
      simp [Nat.ne_of_gt z.2.1, Nat.ne_of_gt z.2.2]

variable {k : Type u} [CommRing k] {V : Type v} [AddCommGroup V] [Module k V]

/-- The original finite signed inverse-place permutation sum on one homogeneous tail. -/
def signedShuffleEnd (p q : ℕ) : Module.End k (TensorPower k (p + q) V) := by
  classical
  exact ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
    AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
      (PiTensorProduct.reindex k (fun _ : Fin (p + q) => V) s.perm).toLinearMap

/-- Actual tensor concatenation followed by the actual signed shuffle. -/
def signedShuffleProduct (p q : ℕ) :
    TensorPower k p V ⊗[k] TensorPower k q V →ₗ[k] TensorPower k (p + q) V :=
  (signedShuffleEnd (k := k) (V := V) p q).comp
    (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap

/-- The exact signed shuffle tensor-word formula. -/
theorem signedShuffleProduct_tprod (p q : ℕ) (a : Fin p → V) (b : Fin q → V) :
    signedShuffleProduct (k := k) (V := V) p q (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
      ∑ s : AlgebraicTopology.EilenbergZilber.Shuffle p q,
        AlgebraicTopology.EilenbergZilber.shuffleSignZ s •
          PiTensorProduct.tprod k (fun i => Fin.append a b (s.perm.symm i)) := by
  classical
  have hmul :
      (TensorPower.mulEquiv (R := k) (M := V) (n := p) (m := q)).toLinearMap
          (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
        PiTensorProduct.tprod k (Fin.append a b) :=
    TensorPower.tprod_mul_tprod k a b
  rw [signedShuffleProduct, LinearMap.comp_apply, hmul]
  simp only [signedShuffleEnd, LinearMap.sum_apply, ← Int.cast_smul_eq_zsmul k,
    LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, PiTensorProduct.reindex_tprod]

/-- The original left unit shuffle gives the actual identity tail endomorphism. -/
theorem signedShuffleEnd_left_zero (n : ℕ) : signedShuffleEnd (k := k) (V := V) 0 n = LinearMap.id := by
  classical
  letI : Unique (AlgebraicTopology.EilenbergZilber.Shuffle 0 n) :=
    { default := AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle n
      uniq := AlgebraicTopology.EilenbergZilber.Shuffle.eq_leftUnitShuffle }
  have hdefault : (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 n) =
      AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle n :=
    AlgebraicTopology.EilenbergZilber.Shuffle.eq_leftUnitShuffle _
  have hsign : AlgebraicTopology.EilenbergZilber.shuffleSignZ
      (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 n) = 1 := by
    rw [hdefault]
    exact AlgebraicTopology.EilenbergZilber.Shuffle.leftUnitShuffle_sign n
  have hperm : (default : AlgebraicTopology.EilenbergZilber.Shuffle 0 n).perm =
      Equiv.refl (Fin (0 + n)) := by
    rw [hdefault]
    rfl
  unfold signedShuffleEnd
  rw [Fintype.sum_unique, hsign, one_smul, hperm, PiTensorProduct.reindex_refl]
  rfl

/-- The original right unit shuffle gives the actual identity tail endomorphism. -/
theorem signedShuffleEnd_right_zero (n : ℕ) : signedShuffleEnd (k := k) (V := V) n 0 = LinearMap.id := by
  classical
  letI : Unique (AlgebraicTopology.EilenbergZilber.Shuffle n 0) :=
    { default := AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle n
      uniq := AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle }
  have hdefault : (default : AlgebraicTopology.EilenbergZilber.Shuffle n 0) =
      AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle n :=
    AlgebraicTopology.EilenbergZilber.Shuffle.eq_rightUnitShuffle _
  have hsign : AlgebraicTopology.EilenbergZilber.shuffleSignZ
      (default : AlgebraicTopology.EilenbergZilber.Shuffle n 0) = 1 := by
    rw [hdefault]
    exact AlgebraicTopology.EilenbergZilber.Shuffle.rightUnitShuffle_sign n
  have hperm : (default : AlgebraicTopology.EilenbergZilber.Shuffle n 0).perm =
      Equiv.refl (Fin (n + 0)) := by
    rw [hdefault]
    rfl
  unfold signedShuffleEnd
  rw [Fintype.sum_unique, hsign, one_smul, hperm, PiTensorProduct.reindex_refl]
  rfl

/-- One actual split/multiply/shuffle cut, in its original total degree. -/
def shuffleCutEnd {n : ℕ} (z : ShuffleDegreeCut n) : Module.End k (TensorPower k n V) :=
  (TensorPower.cast k V z.2).toLinearMap.comp
    ((signedShuffleProduct (k := k) (V := V) z.1.1 z.1.2).comp
      ((TensorPower.mulEquiv (R := k) (M := V) (n := z.1.1) (m := z.1.2)).symm.toLinearMap.comp
        (TensorPower.cast k V z.2).symm.toLinearMap))

/-- The actual tensor split and concatenation cancel, leaving the original target cast and signed sum. -/
theorem shuffleCutEnd_eq_cast {n : ℕ} (z : ShuffleDegreeCut n) :
    shuffleCutEnd (k := k) (V := V) z = (TensorPower.cast k V z.2).toLinearMap.comp
      ((signedShuffleEnd (k := k) (V := V) z.1.1 z.1.2).comp (TensorPower.cast k V z.2).symm.toLinearMap) := by
  apply LinearMap.ext
  intro x
  change TensorPower.cast k V z.2
      (signedShuffleEnd (k := k) (V := V) z.1.1 z.1.2
        ((TensorPower.mulEquiv (R := k) (M := V) (n := z.1.1) (m := z.1.2))
          ((TensorPower.mulEquiv (R := k) (M := V) (n := z.1.1) (m := z.1.2)).symm
            ((TensorPower.cast k V z.2).symm x)))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual left-empty cut is identity after its original degree cast. -/
theorem shuffleCutEnd_left_unit (n : ℕ) :
    shuffleCutEnd (k := k) (V := V) (leftUnitDegreeCut n) = LinearMap.id := by
  rw [shuffleCutEnd_eq_cast]
  change (TensorPower.cast k V (Nat.zero_add n)).toLinearMap.comp
    ((signedShuffleEnd (k := k) (V := V) 0 n).comp
      (TensorPower.cast k V (Nat.zero_add n)).symm.toLinearMap) = LinearMap.id
  rw [signedShuffleEnd_left_zero]
  apply LinearMap.ext
  intro x
  exact (TensorPower.cast k V (leftUnitDegreeCut n).2).apply_symm_apply x

/-- The actual right-empty cut is identity after its original degree cast. -/
theorem shuffleCutEnd_right_unit (n : ℕ) :
    shuffleCutEnd (k := k) (V := V) (rightUnitDegreeCut n) = LinearMap.id := by
  rw [shuffleCutEnd_eq_cast]
  change (TensorPower.cast k V (Nat.add_zero n)).toLinearMap.comp
    ((signedShuffleEnd (k := k) (V := V) n 0).comp
      (TensorPower.cast k V (Nat.add_zero n)).symm.toLinearMap) = LinearMap.id
  rw [signedShuffleEnd_right_zero]
  apply LinearMap.ext
  intro x
  exact (TensorPower.cast k V (rightUnitDegreeCut n).2).apply_symm_apply x

/-- The actual second shuffle-convolution operation is the full weak-cut sum. -/
def shuffleConvolutionTwo (n : ℕ) : Module.End k (TensorPower k n V) :=
  ∑ z : ShuffleDegreeCut n, shuffleCutEnd (k := k) (V := V) z

/-- The actual proper cut sum omits both unit cuts. -/
def properShuffleConvolutionTwo (n : ℕ) : Module.End k (TensorPower k n V) :=
  ∑ z : ProperShuffleDegreeCut n, shuffleCutEnd (k := k) (V := V) z.val

/-- The exact full two-cut operation is two identities plus the actual proper cuts in positive degree. -/
theorem shuffleConvolutionTwo_eq_two_add_proper (n : ℕ) (hn : 0 < n) :
    shuffleConvolutionTwo (k := k) (V := V) n =
      (2 : k) • LinearMap.id + properShuffleConvolutionTwo (k := k) (V := V) n := by
  classical
  let e := shuffleDegreeCutEquivUnitsProper n hn
  unfold shuffleConvolutionTwo properShuffleConvolutionTwo
  rw [← e.symm.sum_comp (fun z => shuffleCutEnd (k := k) (V := V) z), Fintype.sum_sum_type, Fin.sum_univ_two]
  change shuffleCutEnd (k := k) (V := V) (leftUnitDegreeCut n) +
      shuffleCutEnd (k := k) (V := V) (rightUnitDegreeCut n) +
        (∑ z : ProperShuffleDegreeCut n, shuffleCutEnd (k := k) (V := V) z.val) = _
  rw [shuffleCutEnd_left_unit, shuffleCutEnd_right_unit, two_smul]

end TensorPower
