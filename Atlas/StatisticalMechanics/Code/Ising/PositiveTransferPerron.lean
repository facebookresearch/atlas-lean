/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib





open Finset Matrix Filter Topology

namespace StatMech.Ising

noncomputable section

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]

private def coordinateAbs (v : EuclideanSpace Real alpha) :
    EuclideanSpace Real alpha :=
  WithLp.toLp 2 fun i => |v i|

@[simp] private theorem coordinateAbs_apply
    (v : EuclideanSpace Real alpha) (i : alpha) :
    coordinateAbs v i = |v i| := rfl

private theorem norm_coordinateAbs (v : EuclideanSpace Real alpha) :
    norm (coordinateAbs v) = norm v := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  simp

private theorem matrix_inner_le_abs
    (A : Matrix alpha alpha Real) (hA : forall i j, 0 <= A i j)
    (v : EuclideanSpace Real alpha) :
    @inner Real _ _ (Matrix.toEuclideanLin A v) v <=
      @inner Real _ _ (Matrix.toEuclideanLin A (coordinateAbs v))
        (coordinateAbs v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct,
    coordinateAbs, WithLp.ofLp_toLp]
  change (∑ i, v i * ∑ j, A i j * v j) <=
    ∑ i, |v i| * ∑ j, A i j * |v j|
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  calc
    v i * (A i j * v j) <= |v i * (A i j * v j)| := le_abs_self _
    _ = |v i| * (A i j * |v j|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hA i j)]


def positiveTransferTopIndex : Fin (Fintype.card alpha) :=
  ⟨0, Fintype.card_pos⟩


def positiveTransferTopEigenvalue (A : Matrix alpha alpha Real)
    (hA : A.IsHermitian) : Real :=
  hA.eigenvalues₀ (positiveTransferTopIndex (alpha := alpha))

private theorem positiveTransferTopEigenvalue_ge
    (A : Matrix alpha alpha Real) (hA : A.IsHermitian)
    (i : Fin (Fintype.card alpha)) :
    hA.eigenvalues₀ i <= positiveTransferTopEigenvalue A hA := by
  apply hA.eigenvalues₀_antitone
  exact Nat.zero_le _

private theorem exists_nonnegative_top_eigenvector
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hA : forall i j, 0 <= A i j) :
    exists v : EuclideanSpace Real alpha,
      v ≠ 0 ∧ (forall i, 0 <= v i) ∧
        A *ᵥ (fun i => v i) =
          positiveTransferTopEigenvalue A hHerm • (fun i => v i) := by
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  let Ts := hT.toSelfAdjoint
  let p : alpha := Classical.choice inferInstance
  let e : EuclideanSpace Real alpha := EuclideanSpace.single p 1
  have he : norm e = 1 := by simp [e]
  have hsphere : (Metric.sphere (0 : EuclideanSpace Real alpha) 1).Nonempty :=
    ⟨e, by simp [he]⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace Real alpha) 1).exists_isMaxOn hsphere
      Ts.val.reApplyInnerSelf_continuous.continuousOn
  have hvnorm : norm v = 1 := by simpa using hv
  let w := coordinateAbs v
  have hwnorm : norm w = 1 := by rw [norm_coordinateAbs, hvnorm]
  have hw : w ∈ Metric.sphere (0 : EuclideanSpace Real alpha) 1 := by
    simp [hwnorm]
  have hle : Ts.val.reApplyInnerSelf v <= Ts.val.reApplyInnerSelf w := by
    simpa [Ts, T, ContinuousLinearMap.reApplyInnerSelf_apply] using
      matrix_inner_le_abs A hA v
  have heq : Ts.val.reApplyInnerSelf w = Ts.val.reApplyInnerSelf v :=
    le_antisymm (hmax hw) hle
  have hwmax : IsMaxOn Ts.val.reApplyInnerSelf
      (Metric.sphere 0 1) w := by
    intro z hz
    rw [heq]
    exact hmax hz
  have hwne : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at hwnorm
    norm_num at hwnorm
  let mu : Real := Ts.val.rayleighQuotient w
  have heig : Module.End.HasEigenvector T mu w := by
    have hwmax' : IsMaxOn Ts.val.reApplyInnerSelf
        (Metric.sphere 0 (norm w)) w := by
      simpa only [hwnorm] using hwmax
    exact Ts.prop.hasEigenvector_of_isLocalExtrOn hwne
      (Or.inr hwmax'.localize)
  have hmu : mu = Ts.val.reApplyInnerSelf w := by
    simp [mu, ContinuousLinearMap.rayleighQuotient, hwnorm]
  have hmuEig : Module.End.HasEigenvalue T mu :=
    Module.End.hasEigenvalue_of_hasEigenvector heig
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace hmuEig
  have hmuTop : mu <= positiveTransferTopEigenvalue A hHerm := by
    rw [← hi]
    exact positiveTransferTopEigenvalue_ge A hHerm i
  let i0 := positiveTransferTopIndex (alpha := alpha)
  let u := hT.eigenvectorBasis finrank_euclideanSpace i0
  have hunorm : norm u = 1 :=
    (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.1 i0
  have hu : u ∈ Metric.sphere (0 : EuclideanSpace Real alpha) 1 := by
    simp [hunorm]
  have htopMu : positiveTransferTopEigenvalue A hHerm <= mu := by
    have hmaxu := hwmax hu
    rw [← hmu] at hmaxu
    have huEig := hT.apply_eigenvectorBasis finrank_euclideanSpace i0
    have huq : Ts.val.reApplyInnerSelf u =
        positiveTransferTopEigenvalue A hHerm := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      change @inner Real _ _ (T u) u = _
      rw [huEig, inner_smul_left, real_inner_self_eq_norm_sq, hunorm]
      simp only [one_pow, mul_one]
      change hT.eigenvalues finrank_euclideanSpace i0 =
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm).eigenvalues
          finrank_euclideanSpace i0
      exact congrArg
        (fun h : T.IsSymmetric => h.eigenvalues finrank_euclideanSpace i0)
        (Subsingleton.elim _ _)
    change Ts.val.reApplyInnerSelf u <= mu at hmaxu
    rw [huq] at hmaxu
    exact hmaxu
  have hmuEq : mu = positiveTransferTopEigenvalue A hHerm :=
    le_antisymm hmuTop htopMu
  refine ⟨w, hwne, fun i => abs_nonneg _, ?_⟩
  have heqT : T w = mu • w := Module.End.mem_eigenspace_iff.mp heig.1
  have heqFn := congrArg WithLp.ofLp heqT
  simpa [T, Matrix.ofLp_toLpLin, hmuEq] using heqFn

private theorem positive_eigenvector_and_top_pos
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j) :
    0 < positiveTransferTopEigenvalue A hHerm ∧
      exists v : EuclideanSpace Real alpha,
        (forall i, 0 < v i) ∧
          A *ᵥ (fun i => v i) =
            positiveTransferTopEigenvalue A hHerm • (fun i => v i) := by
  obtain ⟨v, hvne, hvnonneg, hveig⟩ :=
    exists_nonnegative_top_eigenvector A hHerm
      (fun i j => (hpos i j).le)
  have hvpos : forall i, 0 < v i := by
    intro i
    apply lt_of_le_of_ne (hvnonneg i)
    intro hvi
    have hvi0 : v i = 0 := hvi.symm
    obtain ⟨j, hvj⟩ : exists j, v j ≠ 0 := by
      by_contra! hall
      apply hvne
      apply WithLp.ofLp_injective 2
      funext j
      simpa using hall j
    have hvjpos : 0 < v j := lt_of_le_of_ne (hvnonneg j) (Ne.symm hvj)
    have hsum : 0 < (A *ᵥ (fun k => v k)) i := by
      rw [Matrix.mulVec]
      apply Finset.sum_pos'
      · intro k hk
        exact mul_nonneg (hpos i k).le (hvnonneg k)
      · exact ⟨j, Finset.mem_univ j, mul_pos (hpos i j) hvjpos⟩
    have hi := congrFun hveig i
    simp only [Pi.smul_apply, smul_eq_mul, hvi0, mul_zero] at hi
    linarith
  let i : alpha := Classical.choice inferInstance
  have hi := congrFun hveig i
  have hsum : 0 < (A *ᵥ (fun k => v k)) i := by
    rw [Matrix.mulVec]
    apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (hpos i k).le (hvpos k).le
    · exact ⟨i, Finset.mem_univ i, mul_pos (hpos i i) (hvpos i)⟩
  have htop : 0 < positiveTransferTopEigenvalue A hHerm := by
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    nlinarith [hvpos i]
  exact ⟨htop, v, hvpos, hveig⟩

private theorem positiveMatrix_eigenvectors_collinear
    (B : Matrix alpha alpha Real) (hBpos : forall i j, 0 < B i j)
    {rho : Real} {v z : EuclideanSpace Real alpha}
    (hvpos : forall i, 0 < v i)
    (hveig : B *ᵥ (fun i => v i) = rho • (fun i => v i))
    (hzeig : B *ᵥ (fun i => z i) = rho • (fun i => z i)) :
    exists r : Real, r • v = z := by
  let ratio : alpha -> Real := fun i => z i / v i
  have himage : (Finset.univ.image ratio).Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  let r : Real := (Finset.univ.image ratio).min' himage
  have hr (i : alpha) : r <= ratio i :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  obtain ⟨i0, hi0mem, hi0⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image ratio) himage)
  let w : EuclideanSpace Real alpha := z - r • v
  have hwnonneg : forall i, 0 <= w i := by
    intro i
    change 0 <= z i - r * v i
    exact sub_nonneg.mpr ((le_div_iff₀ (hvpos i)).mp (hr i))
  have hwi0 : w i0 = 0 := by
    change z i0 - r * v i0 = 0
    have hir : ratio i0 = r := hi0
    dsimp [ratio] at hir
    rw [← hir]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ (hvpos i0).ne').symm
  have hweig : B *ᵥ (fun i => w i) = rho • (fun i => w i) := by
    change B *ᵥ ((fun i => z i) - r • (fun i => v i)) =
      rho • ((fun i => z i) - r • (fun i => v i))
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hzeig, hveig]
    module
  have hwzero : w = 0 := by
    by_contra hwne
    obtain ⟨j, hwj⟩ : exists j, w j ≠ 0 := by
      by_contra! hall
      apply hwne
      apply WithLp.ofLp_injective 2
      funext j
      simpa using hall j
    have hwjpos : 0 < w j := lt_of_le_of_ne (hwnonneg j) (Ne.symm hwj)
    have hsum : 0 < (B *ᵥ (fun i => w i)) i0 := by
      rw [Matrix.mulVec]
      apply Finset.sum_pos'
      · intro i hi
        exact mul_nonneg (hBpos i0 i).le (hwnonneg i)
      · exact ⟨j, Finset.mem_univ j, mul_pos (hBpos i0 j) hwjpos⟩
    have hi := congrFun hweig i0
    simp only [Pi.smul_apply, smul_eq_mul, hwi0, mul_zero] at hi
    linarith
  refine ⟨r, ?_⟩
  change r • v = z
  exact (sub_eq_zero.mp hwzero).symm

private theorem matrix_pow_mulVec_of_eigenvector
    (A : Matrix alpha alpha Real) (v : alpha -> Real) (mu : Real)
    (h : A *ᵥ v = mu • v) (k : Nat) :
    (A ^ k) *ᵥ v = mu ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

private theorem top_eigenspace_finrank_one
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j) :
    Module.finrank Real (Module.End.eigenspace (Matrix.toEuclideanLin A)
      (positiveTransferTopEigenvalue A hHerm)) = 1 := by
  let T := Matrix.toEuclideanLin A
  let top := positiveTransferTopEigenvalue A hHerm
  obtain ⟨_htop, v, hvpos, hveig⟩ :=
    positive_eigenvector_and_top_pos A hHerm hpos
  have hvne : v ≠ 0 := by
    intro hv0
    let i : alpha := Classical.choice inferInstance
    have := hvpos i
    simp [hv0] at this
  have hvT : T v = top • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, top, Matrix.ofLp_toLpLin] using hveig
  have hvMem : v ∈ Module.End.eigenspace T top :=
    Module.End.mem_eigenspace_iff.mpr hvT
  let vv : Module.End.eigenspace T top := ⟨v, hvMem⟩
  have hvvne : vv ≠ 0 := by
    intro h
    apply hvne
    exact Subtype.ext_iff.mp h
  apply finrank_eq_one vv hvvne
  intro zz
  let z : EuclideanSpace Real alpha := zz.1
  have hzT : T z = top • z := Module.End.mem_eigenspace_iff.mp zz.2
  have hzeig : A *ᵥ (fun i => z i) = top • (fun i => z i) := by
    have hzT' := congrArg WithLp.ofLp hzT
    simpa [T, Matrix.ofLp_toLpLin] using hzT'
  obtain ⟨r, hr⟩ := positiveMatrix_eigenvectors_collinear
    A hpos hvpos hveig hzeig
  refine ⟨r, ?_⟩
  exact Subtype.ext hr

private theorem eigenvalue_abs_le_top
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j) {mu : Real}
    {z : EuclideanSpace Real alpha} (hzne : z ≠ 0)
    (hzeig : A *ᵥ (fun i => z i) = mu • (fun i => z i)) :
    |mu| <= positiveTransferTopEigenvalue A hHerm := by
  let top := positiveTransferTopEigenvalue A hHerm
  obtain ⟨_htop, v, hvpos, hveig⟩ :=
    positive_eigenvector_and_top_pos A hHerm hpos
  let S : Real := ∑ i, v i * |z i|
  have hSpos : 0 < S := by
    obtain ⟨j, hzj⟩ : exists j, z j ≠ 0 := by
      by_contra! hall
      apply hzne
      apply WithLp.ofLp_injective 2
      funext j
      simpa using hall j
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hvpos i).le (abs_nonneg _)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hvpos j) (abs_pos.mpr hzj)⟩
  have hcoord (i : alpha) :
      |mu| * |z i| <= ∑ j, A i j * |z j| := by
    have hi := congrFun hzeig i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    rw [← abs_mul, ← hi]
    calc
      |∑ j, A i j * z j| <= ∑ j, |A i j * z j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, A i j * |z j| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg (hpos i j).le]
  have hweighted :
      ∑ i, v i * (|mu| * |z i|) <=
        ∑ i, v i * ∑ j, A i j * |z j| := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hcoord i) (hvpos i).le
  have hleft : ∑ i, v i * (|mu| * |z i|) = |mu| * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright : ∑ i, v i * ∑ j, A i j * |z j| = top * S := by
    calc
      ∑ i, v i * ∑ j, A i j * |z j| =
          ∑ i, ∑ j, v i * (A i j * |z j|) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, v i * (A i j * |z j|) := Finset.sum_comm
      _ = ∑ j, |z j| * ∑ i, A j i * v i := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            have hsym : A i j = A j i := by
              have hh := hHerm
              rw [Matrix.IsHermitian.ext_iff] at hh
              simpa only [star_id_of_comm] using (hh i j).symm
            rw [hsym]
            ring
      _ = ∑ j, |z j| * (top * v j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' := congrFun hveig j
            simpa [top, Matrix.mulVec, dotProduct, Pi.smul_apply,
              smul_eq_mul] using congrArg (fun x : Real => |z j| * x) hj'
      _ = top * S := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [hleft, hright] at hweighted
  nlinarith

private theorem eigenvalue_abs_lt_top
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j) {mu : Real}
    (hmu : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) mu)
    (hne : mu ≠ positiveTransferTopEigenvalue A hHerm) :
    |mu| < positiveTransferTopEigenvalue A hHerm := by
  let T := Matrix.toEuclideanLin A
  let top := positiveTransferTopEigenvalue A hHerm
  obtain ⟨z, hz⟩ := hmu.exists_hasEigenvector
  have hzne : z ≠ 0 := hz.2
  have hzT : T z = mu • z := Module.End.mem_eigenspace_iff.mp hz.1
  have hzeig : A *ᵥ (fun i => z i) = mu • (fun i => z i) := by
    have hzT' := congrArg WithLp.ofLp hzT
    simpa [T, Matrix.ofLp_toLpLin] using hzT'
  have habsle : |mu| <= top :=
    eigenvalue_abs_le_top A hHerm hpos hzne hzeig
  apply lt_of_le_of_ne habsle
  intro habseq
  obtain ⟨htoppos, v, hvpos, hveig⟩ :=
    positive_eigenvector_and_top_pos A hHerm hpos
  have hmuneg : mu = -top := by
    rcases le_total 0 mu with hmunonneg | hmunonpos
    · rw [abs_of_nonneg hmunonneg] at habseq
      exact False.elim (hne habseq)
    · rw [abs_of_nonpos hmunonpos] at habseq
      linarith
  let B := A ^ 2
  have hBpos (i j : alpha) : 0 < B i j := by
    dsimp only [B]
    rw [pow_two, Matrix.mul_apply]
    let k : alpha := Classical.choice inferInstance
    apply Finset.sum_pos'
    · intro q hq
      exact mul_nonneg (hpos i q).le (hpos q j).le
    · exact ⟨k, Finset.mem_univ k, mul_pos (hpos i k) (hpos k j)⟩
  have hvpow : B *ᵥ (fun i => v i) = top ^ 2 • (fun i => v i) := by
    exact matrix_pow_mulVec_of_eigenvector A (fun i => v i) top hveig 2
  have hzpow : B *ᵥ (fun i => z i) = top ^ 2 • (fun i => z i) := by
    have hpow := matrix_pow_mulVec_of_eigenvector
      A (fun i => z i) mu hzeig 2
    rw [hmuneg] at hpow
    norm_num at hpow ⊢
    simpa [B] using hpow
  obtain ⟨r, hr⟩ := positiveMatrix_eigenvectors_collinear
    B hBpos hvpos hvpow hzpow
  have hrne : r ≠ 0 := by
    intro hr0
    apply hzne
    rw [← hr, hr0, zero_smul]
  have hvT : T v = top • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, Matrix.ofLp_toLpLin] using hveig
  rw [← hr] at hzT
  simp only [map_smul, hvT, smul_smul] at hzT
  let i : alpha := Classical.choice inferInstance
  have hi := congrArg (fun q : EuclideanSpace Real alpha => q i) hzT
  change (r * top) * v i = (mu * r) * v i at hi
  exfalso
  apply hne
  change mu = top
  have hi' : top * (r * v i) = mu * (r * v i) := by
    calc
      top * (r * v i) = r * top * v i := by ring
      _ = mu * r * v i := hi
      _ = mu * (r * v i) := by ring
  exact (mul_right_cancel₀ (mul_ne_zero hrne (hvpos i).ne') hi').symm


theorem positiveTransfer_isPerronFrobenius
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j) :
    0 < positiveTransferTopEigenvalue A hHerm ∧
      (exists v : EuclideanSpace Real alpha,
        (forall i, 0 < v i) ∧
          A *ᵥ (fun i => v i) =
            positiveTransferTopEigenvalue A hHerm • (fun i => v i)) ∧
      Module.finrank Real (Module.End.eigenspace (Matrix.toEuclideanLin A)
        (positiveTransferTopEigenvalue A hHerm)) = 1 ∧
      forall mu : Real,
        Module.End.HasEigenvalue (Matrix.toEuclideanLin A) mu ->
          mu ≠ positiveTransferTopEigenvalue A hHerm ->
            |mu| < positiveTransferTopEigenvalue A hHerm := by
  obtain ⟨htop, v, hvpos, hveig⟩ :=
    positive_eigenvector_and_top_pos A hHerm hpos
  exact ⟨htop, ⟨v, hvpos, hveig⟩,
    top_eigenspace_finrank_one A hHerm hpos,
    fun mu hmu hne => eigenvalue_abs_lt_top A hHerm hpos hmu hne⟩



theorem positiveTransfer_positive_eigenvalue_eq_top
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    {lam : Real} {u : EuclideanSpace Real alpha}
    (hupos : forall i, 0 < u i)
    (hueig : A *ᵥ (fun i => u i) = lam • (fun i => u i)) :
    lam = positiveTransferTopEigenvalue A hHerm := by
  obtain ⟨_htop, v, hvpos, hveig⟩ :=
    positive_eigenvector_and_top_pos A hHerm hpos
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  have huT : T u = lam • u := by
    apply WithLp.ofLp_injective 2
    simpa [T, Matrix.ofLp_toLpLin] using hueig
  have hvT : T v = positiveTransferTopEigenvalue A hHerm • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, Matrix.ofLp_toLpLin] using hveig
  have huvpos : 0 < @inner Real _ _ u v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct]
    apply Finset.sum_pos'
    · intro i hi
      exact (mul_pos (hvpos i) (hupos i)).le
    · let i : alpha := Classical.choice inferInstance
      exact ⟨i, Finset.mem_univ i, mul_pos (hvpos i) (hupos i)⟩
  have hsymmetric := hT u v
  rw [huT, hvT, inner_smul_left, inner_smul_right] at hsymmetric
  simp only [starRingEnd_apply, star_trivial] at hsymmetric
  exact mul_right_cancel₀ huvpos.ne' hsymmetric


theorem positiveTransfer_positive_unit_eigenvector_unique
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    {lam mu : Real} {u v : EuclideanSpace Real alpha}
    (hupos : forall i, 0 < u i) (hvpos : forall i, 0 < v i)
    (hunorm : norm u = 1) (hvnorm : norm v = 1)
    (hueig : A *ᵥ (fun i => u i) = lam • (fun i => u i))
    (hveig : A *ᵥ (fun i => v i) = mu • (fun i => v i)) :
    u = v := by
  have hlam := positiveTransfer_positive_eigenvalue_eq_top
    A hHerm hpos hupos hueig
  have hmu := positiveTransfer_positive_eigenvalue_eq_top
    A hHerm hpos hvpos hveig
  rw [hlam] at hueig
  rw [hmu] at hveig
  obtain ⟨r, hru⟩ := positiveMatrix_eigenvectors_collinear
    A hpos hupos hueig hveig
  let i : alpha := Classical.choice inferInstance
  have hcoord := congrArg (fun z : EuclideanSpace Real alpha => z i) hru
  change r * u i = v i at hcoord
  have hrpos : 0 < r := by
    nlinarith [hupos i, hvpos i]
  have hnorm := congrArg norm hru
  rw [norm_smul, hunorm, hvnorm, mul_one, Real.norm_eq_abs,
    abs_of_pos hrpos] at hnorm
  rw [← hru, hnorm, one_smul]

private theorem positiveTransfer_eigenvalues₀_ne_top_of_ne
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (i : Fin (Fintype.card alpha))
    (hi : i ≠ positiveTransferTopIndex (alpha := alpha)) :
    hHerm.eigenvalues₀ i ≠ positiveTransferTopEigenvalue A hHerm := by
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  let i0 := positiveTransferTopIndex (alpha := alpha)
  let top := hHerm.eigenvalues₀ i0
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  change hHerm.eigenvalues₀ i ≠ top
  intro heq
  let S := Module.End.eigenspace T top
  have huMem : b i0 ∈ S := by
    apply Module.End.mem_eigenspace_iff.mpr
    exact hT.apply_eigenvectorBasis finrank_euclideanSpace i0
  have hwMem : b i ∈ S := by
    apply Module.End.mem_eigenspace_iff.mpr
    have hw := hT.apply_eigenvectorBasis finrank_euclideanSpace i
    rw [← heq]
    exact hw
  let u : S := ⟨b i0, huMem⟩
  let w : S := ⟨b i, hwMem⟩
  have hune : u ≠ 0 := by
    intro hu0
    apply b.orthonormal.ne_zero i0
    exact congrArg Subtype.val hu0
  have hfin : Module.finrank Real S = 1 := by
    simpa [S, T, top, i0] using
      top_eigenspace_finrank_one A hHerm hpos
  have hspan : Real ∙ u = ⊤ :=
    (finrank_eq_one_iff_of_nonzero u hune).mp hfin
  have hwspan : w ∈ Real ∙ u := by
    rw [hspan]
    trivial
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hwspan
  have hrbase : r • b i0 = b i := congrArg Subtype.val hr
  have hself : @inner Real _ _ (b i0) (b i0) = 1 := by
    have h := orthonormal_iff_ite.mp b.orthonormal i0 i0
    rw [if_pos rfl] at h
    exact h
  have hcross : @inner Real _ _ (b i0) (b i) = 0 :=
    b.orthonormal.inner_eq_zero (Ne.symm hi)
  have hr0 : r = 0 := by
    have hinner := congrArg (fun z => @inner Real _ _ (b i0) z) hrbase
    change @inner Real _ _ (b i0) (r • b i0) =
      @inner Real _ _ (b i0) (b i) at hinner
    rw [inner_smul_right, hself, hcross, mul_one] at hinner
    exact hinner
  apply b.orthonormal.ne_zero i
  rw [← hrbase, hr0, zero_smul]



theorem positiveTransfer_normalized_mulVec_tendsto
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a : alpha -> Real) (ha : forall i, 0 < a i) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real alpha,
        (forall i, 0 < u i) ∧ norm u = 1 ∧
        A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧
        exists c : Real, 0 < c ∧
          Tendsto
            (fun n : Nat => WithLp.toLp 2
              (fun i => ((A ^ n) *ᵥ a) i / lam ^ n))
            atTop (nhds (c • u)) := by
  obtain ⟨hlam, v, hvpos, hveig⟩ :=
    positive_eigenvector_and_top_pos A hHerm hpos
  let lam := positiveTransferTopEigenvalue A hHerm
  have hvne : v ≠ 0 := by
    intro hv0
    let i : alpha := Classical.choice inferInstance
    have := hvpos i
    simp [hv0] at this
  have hvnorm : 0 < norm v := norm_pos_iff.mpr hvne
  let u : EuclideanSpace Real alpha := (norm v)⁻¹ • v
  have hupos : forall i, 0 < u i := by
    intro i
    change 0 < (norm v)⁻¹ * v i
    exact mul_pos (inv_pos.mpr hvnorm) (hvpos i)
  have hunorm : norm u = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm),
      inv_mul_cancel₀ hvnorm.ne']
  have hueig : A *ᵥ (fun i => u i) = lam • (fun i => u i) := by
    change A *ᵥ ((norm v)⁻¹ • (fun i => v i)) =
      lam • ((norm v)⁻¹ • (fun i => v i))
    rw [Matrix.mulVec_smul, hveig]
    module
  let avec : EuclideanSpace Real alpha := WithLp.toLp 2 a
  let c : Real := @inner Real _ _ u avec
  have hc : 0 < c := by
    change 0 < @inner Real _ _ u avec
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct, u, avec]
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (ha i).le (hupos i).le
    · let i : alpha := Classical.choice inferInstance
      exact ⟨i, Finset.mem_univ i, mul_pos (ha i) (hupos i)⟩
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  let i0 := positiveTransferTopIndex (alpha := alpha)
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  let eig : Fin (Fintype.card alpha) -> Real :=
    fun i => hHerm.eigenvalues₀ i
  have hbEig (i : Fin (Fintype.card alpha)) :
      T (b i) = eig i • b i := by
    dsimp only [b, eig]
    change T (hT.eigenvectorBasis finrank_euclideanSpace i) =
      hT.eigenvalues finrank_euclideanSpace i •
        hT.eigenvectorBasis finrank_euclideanSpace i
    exact hT.apply_eigenvectorBasis finrank_euclideanSpace i
  have hbu : exists r : Real, r • u = b i0 := by
    apply positiveMatrix_eigenvectors_collinear A hpos hupos hueig
    have hb := congrArg WithLp.ofLp (hbEig i0)
    simpa only [T, Matrix.ofLp_toLpLin, Pi.smul_apply,
      WithLp.ofLp_toLp, lam, eig, i0, smul_eq_mul] using hb
  obtain ⟨r, hru⟩ := hbu
  have hrne : r ≠ 0 := by
    intro hr0
    apply b.orthonormal.ne_zero i0
    rw [← hru, hr0, zero_smul]
  let y : Nat -> EuclideanSpace Real alpha := fun n =>
    WithLp.toLp 2 (fun i => ((A ^ n) *ᵥ a) i)
  have hySucc (n : Nat) : y (n + 1) = T (y n) := by
    apply WithLp.ofLp_injective 2
    change ((A ^ (n + 1)) *ᵥ a) = A *ᵥ ((A ^ n) *ᵥ a)
    rw [pow_succ', Matrix.mulVec_mulVec]
  have hyRepr (n : Nat) (i : Fin (Fintype.card alpha)) :
      b.repr (y n) i = eig i ^ n * b.repr avec i := by
    induction n with
    | zero => simp [y, avec]
    | succ n ih =>
        rw [hySucc]
        have hdiag := hT.eigenvectorBasis_apply_self_apply
          finrank_euclideanSpace (y n) i
        change b.repr (T (y n)) i = _
        change b.repr (T (y n)) i = eig i * b.repr (y n) i at hdiag
        rw [hdiag, ih]
        ring
  let x : Nat -> EuclideanSpace Real alpha := fun n =>
    WithLp.toLp 2 (fun i => ((A ^ n) *ᵥ a) i / lam ^ n)
  have hxEq (n : Nat) : x n = (lam ^ n)⁻¹ • y n := by
    apply WithLp.ofLp_injective 2
    funext i
    simp [x, y, div_eq_inv_mul]
  have hxRepr (n : Nat) (i : Fin (Fintype.card alpha)) :
      b.repr (x n) i = (eig i / lam) ^ n * b.repr avec i := by
    rw [hxEq, map_smul]
    change (lam ^ n)⁻¹ * b.repr (y n) i = _
    rw [hyRepr]
    rw [div_pow]
    field_simp [pow_ne_zero n hlam.ne']
  have htargetTop : b.repr (c • u) i0 = b.repr avec i0 := by
    rw [map_smul]
    change c * b.repr u i0 = b.repr avec i0
    rw [b.repr_apply_apply, b.repr_apply_apply]
    have hinnerBU : @inner Real _ _ (b i0) u = r := by
      rw [← hru, inner_smul_left, real_inner_self_eq_norm_sq, hunorm]
      simp
    have hinnerBA : @inner Real _ _ (b i0) avec = r * c := by
      rw [← hru, inner_smul_left]
      rfl
    rw [hinnerBU, hinnerBA]
    exact mul_comm c r
  have htargetOther (i : Fin (Fintype.card alpha)) (hi : i ≠ i0) :
      b.repr (c • u) i = 0 := by
    rw [map_smul]
    change c * b.repr u i = 0
    rw [b.repr_apply_apply]
    have horth : @inner Real _ _ (b i) (b i0) = 0 :=
      b.orthonormal.inner_eq_zero hi
    have huorth : @inner Real _ _ (b i) u = 0 := by
      have hscaled := congrArg (fun z => @inner Real _ _ (b i) z) hru
      change @inner Real _ _ (b i) (r • u) =
        @inner Real _ _ (b i) (b i0) at hscaled
      rw [inner_smul_right] at hscaled
      rw [horth] at hscaled
      exact (mul_eq_zero.mp hscaled).resolve_left hrne
    rw [huorth, mul_zero]
  have hrepr : Tendsto (fun n => b.repr (x n)) atTop
      (nhds (b.repr (c • u))) := by
    let H := PiLp.homeomorph 2
      (fun _ : Fin (Fintype.card alpha) => Real)
    have hfun : Tendsto (fun n => H (b.repr (x n))) atTop
        (nhds (H (b.repr (c • u)))) := by
      apply tendsto_pi_nhds.2
      intro i
      change Tendsto (fun n => b.repr (x n) i) atTop
        (nhds (b.repr (c • u) i))
      by_cases hi : i = i0
      · subst i
        have heigTop : eig i0 = lam := by rfl
        have hsource : (fun n => b.repr (x n) i0) =
            (fun _ : Nat => b.repr avec i0) := by
          funext n
          rw [hxRepr, heigTop, div_self hlam.ne', one_pow, one_mul]
        rw [hsource, htargetTop]
        exact tendsto_const_nhds
      · have hine : eig i ≠ lam := by
          exact positiveTransfer_eigenvalues₀_ne_top_of_ne
            A hHerm hpos i hi
        have hei : Module.End.HasEigenvalue T (eig i) := by
          simpa [T, eig] using
            hT.hasEigenvalue_eigenvalues finrank_euclideanSpace i
        have hstrict : |eig i| < lam := by
          exact eigenvalue_abs_lt_top A hHerm hpos hei hine
        have hratio : |eig i / lam| < 1 := by
          rw [abs_div, abs_of_pos hlam]
          exact (div_lt_one hlam).mpr hstrict
        have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio
        have hmul := hpow.mul_const (b.repr avec i)
        simpa only [hxRepr, htargetOther i hi, zero_mul] using hmul
    have h := (H.symm.continuous.tendsto _).comp hfun
    simpa only [H, Function.comp_apply, Homeomorph.symm_apply_apply] using h
  have hx : Tendsto x atTop (nhds (c • u)) := by
    have h := (b.repr.symm.continuous.tendsto _).comp hrepr
    rw [b.repr.symm_apply_apply] at h
    exact h.congr' (Filter.Eventually.of_forall fun n =>
      b.repr.symm_apply_apply (x n))
  exact ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, hx⟩


theorem positiveTransfer_normalized_mulVec_tendsto_apply
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a : alpha -> Real) (ha : forall i, 0 < a i) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real alpha,
        (forall i, 0 < u i) ∧ norm u = 1 ∧
        A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧
        exists c : Real, 0 < c ∧ forall i,
          Tendsto (fun n : Nat => ((A ^ n) *ᵥ a) i / lam ^ n)
            atTop (nhds (c * u i)) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, hconv⟩ :=
    positiveTransfer_normalized_mulVec_tendsto A hHerm hpos a ha
  refine ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, ?_⟩
  intro i
  have hi := ((PiLp.continuous_apply 2 (fun _ : alpha => Real) i).tendsto
    (c • u)).comp hconv
  simpa only [Function.comp_apply, WithLp.ofLp_toLp, Pi.smul_apply,
    smul_eq_mul] using hi



theorem positiveTransfer_normalized_mulVec_pair_tendsto
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a b : alpha -> Real) (ha : forall i, 0 < a i)
    (hb : forall i, 0 < b i) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real alpha,
        (forall i, 0 < u i) ∧ norm u = 1 ∧
        A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧
        exists ca cb : Real, 0 < ca ∧ 0 < cb ∧
          Tendsto
            (fun n : Nat => WithLp.toLp 2
              (fun i => ((A ^ n) *ᵥ a) i / lam ^ n))
            atTop (nhds (ca • u)) ∧
          Tendsto
            (fun n : Nat => WithLp.toLp 2
              (fun i => ((A ^ n) *ᵥ b) i / lam ^ n))
            atTop (nhds (cb • u)) := by
  obtain ⟨lamA, hlamA, u, hupos, hunorm, hueig, ca, hca, hconvA⟩ :=
    positiveTransfer_normalized_mulVec_tendsto A hHerm hpos a ha
  obtain ⟨lamB, hlamB, v, hvpos, hvnorm, hveig, cb, hcb, hconvB⟩ :=
    positiveTransfer_normalized_mulVec_tendsto A hHerm hpos b hb
  have hlamATop := positiveTransfer_positive_eigenvalue_eq_top
    A hHerm hpos hupos hueig
  have hlamBTop := positiveTransfer_positive_eigenvalue_eq_top
    A hHerm hpos hvpos hveig
  have hlam : lamB = lamA := hlamBTop.trans hlamATop.symm
  subst lamB
  have huv := positiveTransfer_positive_unit_eigenvector_unique
    A hHerm hpos hupos hvpos hunorm hvnorm hueig hveig
  subst v
  rw [← hlamATop] at hconvB
  exact ⟨lamA, hlamA, u, hupos, hunorm, hueig,
    ca, cb, hca, hcb, hconvA, hconvB⟩



theorem positiveTransfer_normalized_dotProduct_tendsto
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a : alpha -> Real) (ha : forall i, 0 < a i)
    (ell : alpha -> Real) :
    exists lam : Real, 0 < lam ∧
      exists u : EuclideanSpace Real alpha,
        (forall i, 0 < u i) ∧ norm u = 1 ∧
        A *ᵥ (fun i => u i) = lam • (fun i => u i) ∧
        exists c : Real, 0 < c ∧
          Tendsto
            (fun n : Nat => ∑ i,
              ell i * (((A ^ n) *ᵥ a) i / lam ^ n))
            atTop (nhds (c * ∑ i, ell i * u i)) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, hcoord⟩ :=
    positiveTransfer_normalized_mulVec_tendsto_apply A hHerm hpos a ha
  refine ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, ?_⟩
  have hsum : Tendsto
      (fun n : Nat => ∑ i, ell i * (((A ^ n) *ᵥ a) i / lam ^ n))
      atTop (nhds (∑ i, ell i * (c * u i))) := by
    apply tendsto_finsetSum Finset.univ
    intro i hi
    exact (hcoord i).const_mul (ell i)
  have hlimit : (∑ i, ell i * (c * u i)) =
      c * ∑ i, ell i * u i := by
    calc
      (∑ i, ell i * (c * u i)) = ∑ i, c * (ell i * u i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i, ell i * u i := by rw [Finset.mul_sum]
  rw [hlimit] at hsum
  exact hsum



theorem positiveTransfer_log_dotProduct_div_tendsto
    (A : Matrix alpha alpha Real) (hHerm : A.IsHermitian)
    (hpos : forall i j, 0 < A i j)
    (a ell : alpha -> Real) (ha : forall i, 0 < a i)
    (hell : forall i, 0 < ell i) :
    exists lam : Real, 0 < lam ∧
      Tendsto
        (fun n : Nat =>
          Real.log (∑ i, ell i * ((A ^ n) *ᵥ a) i) / (n : Real))
        atTop (nhds (Real.log lam)) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, c, hc, hconv⟩ :=
    positiveTransfer_normalized_dotProduct_tendsto
      A hHerm hpos a ha ell
  let q : Nat -> Real := fun n =>
    ∑ i, ell i * (((A ^ n) *ᵥ a) i / lam ^ n)
  let L : Real := c * ∑ i, ell i * u i
  have hsumpos : 0 < ∑ i, ell i * u i := by
    apply Finset.sum_pos'
    · intro i hi
      exact (mul_pos (hell i) (hupos i)).le
    · let i : alpha := Classical.choice inferInstance
      exact ⟨i, Finset.mem_univ i, mul_pos (hell i) (hupos i)⟩
  have hL : 0 < L := mul_pos hc hsumpos
  have hq : Tendsto q atTop (nhds L) := by
    simpa only [q, L] using hconv
  have hlogq : Tendsto (fun n => Real.log (q n)) atTop
      (nhds (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hq
  have hlogqDiv : Tendsto (fun n => Real.log (q n) / (n : Real))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      hlogq.mul
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : Nat => (1 : Real) / (n : Real)) atTop (nhds 0))
  have htarget : Tendsto
      (fun n => Real.log lam + Real.log (q n) / (n : Real))
      atTop (nhds (Real.log lam)) := by
    simpa using (tendsto_const_nhds (x := Real.log lam)).add hlogqDiv
  refine ⟨lam, hlam, ?_⟩
  apply htarget.congr'
  have hqpos : ∀ᶠ n in atTop, 0 < q n :=
    (tendsto_order.1 hq).1 0 hL
  filter_upwards [hqpos, eventually_ge_atTop 1] with n hqn hn
  have hn0 : (n : Real) ≠ 0 := by positivity
  have hpow : lam ^ n ≠ 0 := pow_ne_zero n hlam.ne'
  have hfactor : (∑ i, ell i * ((A ^ n) *ᵥ a) i) =
      lam ^ n * q n := by
    dsimp only [q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp
  rw [hfactor, Real.log_mul hpow hqn.ne', Real.log_pow]
  field_simp



theorem positiveTransfer_log_dotProduct_sub_div_tendsto
    (A B : Matrix alpha alpha Real)
    (hAHerm : A.IsHermitian) (hBHerm : B.IsHermitian)
    (hApos : forall i j, 0 < A i j) (hBpos : forall i j, 0 < B i j)
    (aA ellA aB ellB : alpha -> Real)
    (haA : forall i, 0 < aA i) (hellA : forall i, 0 < ellA i)
    (haB : forall i, 0 < aB i) (hellB : forall i, 0 < ellB i) :
    exists lamA lamB : Real, 0 < lamA ∧ 0 < lamB ∧
      Tendsto
        (fun n : Nat =>
          (Real.log (∑ i, ellA i * ((A ^ n) *ᵥ aA) i) -
            Real.log (∑ i, ellB i * ((B ^ n) *ᵥ aB) i)) /
              (n : Real))
        atTop (nhds (Real.log lamA - Real.log lamB)) := by
  obtain ⟨lamA, hlamA, hA⟩ :=
    positiveTransfer_log_dotProduct_div_tendsto
      A hAHerm hApos aA ellA haA hellA
  obtain ⟨lamB, hlamB, hB⟩ :=
    positiveTransfer_log_dotProduct_div_tendsto
      B hBHerm hBpos aB ellB haB hellB
  refine ⟨lamA, lamB, hlamA, hlamB, ?_⟩
  simpa only [sub_div] using hA.sub hB

end

end StatMech.Ising
