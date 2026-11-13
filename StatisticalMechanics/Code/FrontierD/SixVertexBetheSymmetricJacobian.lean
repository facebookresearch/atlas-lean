/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricAnalytic
import Code.FrontierD.SixVertexBetheJacobianStability
import Mathlib.LinearAlgebra.Matrix.Gershgorin





open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



def sixVertexBethePositiveHalfJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  let p := sixVertexEvenSymmetricLift m q
  sixVertexBetheJacobianMatrix N (m + m) c p
      (Fin.natAdd m j) (Fin.natAdd m k) -
    sixVertexBetheJacobianMatrix N (m + m) c p
      (Fin.natAdd m j) (Fin.castAdd m k.rev)

theorem sixVertexEvenSymmetricBetheRootJacobian_apply
    {N m : Nat} {c : Real} (hc : 2 < c)
    (q v : Fin m → Real) (j : Fin m) :
    sixVertexEvenSymmetricBetheRootJacobian N m c q v j =
      sixVertexBetheRootJacobian N (m + m) c
        (sixVertexEvenSymmetricLift m q)
        (sixVertexEvenSymmetricLift m v) (Fin.natAdd m j) := by
  let full : (Fin (m + m) → Real) → (Fin (m + m) → Real) := fun p i =>
    sixVertexBetheResidual c N (m + m) p i
  let positive : (Fin (m + m) → Real) →L[Real] (Fin m → Real) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.natAdd m i)
  let J := sixVertexBetheRootJacobian N (m + m) c
    (sixVertexEvenSymmetricLift m q)
  have hfull : HasFDerivAt full J (sixVertexEvenSymmetricLift m q) :=
    (analyticAt_sixVertexBetheResidual_family N (m + m)
      (c, sixVertexEvenSymmetricLift m q) hc)
      |>.comp (x := sixVertexEvenSymmetricLift m q)
        (f := fun p : Fin (m + m) → Real => (c, p))
        (analyticAt_const.prod analyticAt_id)
      |>.hasStrictFDerivAt.hasFDerivAt
  have hlift : HasFDerivAt (sixVertexEvenSymmetricLift m)
      (sixVertexEvenSymmetricLift m) q :=
    (sixVertexEvenSymmetricLift m).hasFDerivAt
  have hcomp : HasFDerivAt
      (fun r : Fin m → Real => positive (full (sixVertexEvenSymmetricLift m r)))
      (positive.comp (J.comp (sixVertexEvenSymmetricLift m))) q :=
    positive.hasFDerivAt.comp q (hfull.comp q hlift)
  have heq : sixVertexEvenSymmetricBetheRootJacobian N m c q =
      positive.comp (J.comp (sixVertexEvenSymmetricLift m)) := by
    apply HasFDerivAt.unique
    · exact (analyticAt_sixVertexEvenSymmetricBetheResidual_family N m (c, q) hc)
        |>.comp (x := q) (f := fun r : Fin m → Real => (c, r))
          (analyticAt_const.prod analyticAt_id)
        |>.hasStrictFDerivAt.hasFDerivAt
    · simpa [full, positive, sixVertexEvenSymmetricBetheResidual,
        Function.comp_def] using hcomp
  rw [heq]
  rfl

private theorem sixVertexEvenSymmetricLift_single
    (m : Nat) (k : Fin m) :
    sixVertexEvenSymmetricLift m (Pi.single k 1) =
      Pi.single (Fin.natAdd m k) 1 -
        Pi.single (Fin.castAdd m k.rev) 1 := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro a
  · have hcross : Fin.castAdd m a ≠ Fin.natAdd m k := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [Fin.castAdd, Fin.natAdd] at hv
      omega
    have hrev : a.rev = k ↔ a = k.rev := by
      constructor
      · intro h
        rw [← h, Fin.rev_rev]
      · intro h
        rw [h, Fin.rev_rev]
    rw [sixVertexEvenSymmetricLift_castAdd]
    simp only [Pi.single_apply, Pi.sub_apply]
    rw [if_neg hcross]
    simp [Fin.castAdd_inj, hrev]
  · have hcross : Fin.natAdd m a ≠ Fin.castAdd m k.rev := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [Fin.castAdd, Fin.natAdd] at hv
      omega
    rw [sixVertexEvenSymmetricLift_natAdd]
    simp only [Pi.single_apply, Pi.sub_apply]
    rw [if_neg hcross]
    simp [Fin.natAdd_inj]

theorem sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply
    {N m : Nat} {c : Real} (hc : 2 < c)
    (q : Fin m → Real) (j k : Fin m) :
    LinearMap.toMatrix'
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap j k =
        sixVertexBethePositiveHalfJacobianMatrix N m c q j k := by
  rw [LinearMap.toMatrix'_apply]
  change sixVertexEvenSymmetricBetheRootJacobian N m c q
      (Pi.single k 1) j = _
  rw [sixVertexEvenSymmetricBetheRootJacobian_apply hc,
    sixVertexEvenSymmetricLift_single, map_sub]
  change
    sixVertexBetheRootJacobian N (m + m) c
        (sixVertexEvenSymmetricLift m q)
        (Pi.single (Fin.natAdd m k) 1) (Fin.natAdd m j) -
      sixVertexBetheRootJacobian N (m + m) c
        (sixVertexEvenSymmetricLift m q)
        (Pi.single (Fin.castAdd m k.rev) 1) (Fin.natAdd m j) = _
  have h₁ := sixVertexBetheRootJacobian_toMatrix'_apply (N := N) hc
    (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j) (Fin.natAdd m k)
  have h₂ := sixVertexBetheRootJacobian_toMatrix'_apply (N := N) hc
    (sixVertexEvenSymmetricLift m q) (Fin.natAdd m j) (Fin.castAdd m k.rev)
  change sixVertexBetheRootJacobian N (m + m) c
      (sixVertexEvenSymmetricLift m q) (Pi.single (Fin.natAdd m k) 1)
        (Fin.natAdd m j) = _ at h₁
  change sixVertexBetheRootJacobian N (m + m) c
      (sixVertexEvenSymmetricLift m q) (Pi.single (Fin.castAdd m k.rev) 1)
        (Fin.natAdd m j) = _ at h₂
  rw [h₁, h₂]
  rfl



theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_diagonalDominance
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m → Real)
    (hdom : ∀ j,
      ∑ k ∈ Finset.univ.erase j,
          ‖sixVertexBethePositiveHalfJacobianMatrix N m c q j k‖ <
        ‖sixVertexBethePositiveHalfJacobianMatrix N m c q j j‖) :
    Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let A := sixVertexBethePositiveHalfJacobianMatrix N m c q
  have hdet : Matrix.det A ≠ 0 := det_ne_zero_of_sum_row_lt_diag hdom
  have hmatrix : LinearMap.toMatrix'
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap = A := by
    ext j k
    exact sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply hc q j k
  have hdetJ : LinearMap.det
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap ≠ 0 := by
    rw [← LinearMap.det_toMatrix', hmatrix]
    exact hdet
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdetJ ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)



theorem sixVertexEvenSymmetricLift_positive_mem_Icc
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (j : Fin m) : q j ∈ Set.Icc 0 Real.pi := by
  let i : Fin (m + m) := Fin.natAdd m j
  let ir : Fin (m + m) := Fin.castAdd m j.rev
  have hir : ir = i.rev := by
    apply Fin.ext
    simp [i, ir, Fin.rev, Fin.natAdd, Fin.castAdd]
    omega
  have hlt : ir < i := by
    rw [Fin.lt_def]
    simp [i, ir, Fin.natAdd, Fin.castAdd, Fin.rev]
    omega
  have horder := hq.1 hlt
  have hir_eval : sixVertexEvenSymmetricLift m q ir = -q j := by
    change sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev) = -q j
    rw [sixVertexEvenSymmetricLift_castAdd]
    simp
  have hi_eval : sixVertexEvenSymmetricLift m q i = q j := by
    exact sixVertexEvenSymmetricLift_natAdd m q j
  rw [hir_eval, hi_eval] at horder
  have hpos : 0 < q j := by linarith
  have hpi := (hq.2.2 i).2.le
  rw [hi_eval] at hpi
  exact ⟨hpos.le, hpi⟩



theorem sixVertexBethePositiveHalfJacobianMatrix_offdiag_nonneg
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    {j k : Fin m} (hjk : j ≠ k) :
    0 ≤ sixVertexBethePositiveHalfJacobianMatrix N m c q j k := by
  let p := sixVertexEvenSymmetricLift m q
  let i : Fin (m + m) := Fin.natAdd m j
  let l : Fin (m + m) := Fin.natAdd m k
  let lr : Fin (m + m) := Fin.castAdd m k.rev
  have hil : i ≠ l := by
    intro h
    apply hjk
    have hval := congrArg Fin.val h
    dsimp [i, l, Fin.natAdd] at hval
    exact Fin.ext (by omega)
  have hilr : i ≠ lr := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [i, lr, Fin.natAdd, Fin.castAdd] at hval
    omega
  have hsymm : p lr = -p l := by
    have hl : p l = q k := by
      exact sixVertexEvenSymmetricLift_natAdd m q k
    have hlr : p lr = -q k := by
      change sixVertexEvenSymmetricLift m q (Fin.castAdd m k.rev) = -q k
      rw [sixVertexEvenSymmetricLift_castAdd]
      simp
    rw [hl, hlr]
  have hiIcc : -p i ∈ Set.Icc (-Real.pi) 0 := by
    have hi := sixVertexEvenSymmetricLift_positive_mem_Icc hq j
    have heval : p i = q j := sixVertexEvenSymmetricLift_natAdd m q j
    rw [heval]
    exact ⟨neg_le_neg hi.2, neg_nonpos.mpr hi.1⟩
  have hlIcc : -p l ∈ Set.Icc (-Real.pi) 0 := by
    have hl := sixVertexEvenSymmetricLift_positive_mem_Icc hq k
    have heval : p l = q k := sixVertexEvenSymmetricLift_natAdd m q k
    rw [heval]
    exact ⟨neg_le_neg hl.2, neg_nonpos.mpr hl.1⟩
  have hsign := sixVertexTheta_right_difference_nonneg hc hiIcc hlIcc
  change 0 ≤
    sixVertexBetheJacobianMatrix N (m + m) c p i l -
      sixVertexBetheJacobianMatrix N (m + m) c p i lr
  rw [sixVertexBetheJacobianMatrix, if_neg hil,
    sixVertexBetheJacobianMatrix, if_neg hilr, hsymm]
  have hden₁ : sixVertexThetaDerivativeDenominator c (-p i) (-p l) =
      sixVertexThetaDerivativeDenominator c (p i) (p l) := by
    unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
    simp only [Real.cos_neg, Real.sin_neg]
    ring
  rw [hden₁] at hsign
  simpa [sixVertexBetheIntegratingFactor, Real.cos_neg] using hsign



theorem sixVertexBethePositiveHalfJacobianMatrix_mul_gap_offdiag_nonneg
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (gap : Fin m → Real) (hgap : ∀ k, 0 ≤ gap k)
    {j k : Fin m} (hjk : j ≠ k) :
    0 ≤ sixVertexBethePositiveHalfJacobianMatrix N m c q j k * gap k :=
  mul_nonneg
    (sixVertexBethePositiveHalfJacobianMatrix_offdiag_nonneg hc hq hjk)
    (hgap k)




def sixVertexPositiveHalfRootGap
    {m : Nat} (q : Fin m → Real) (k : Fin m) : Real :=
  if hk : k.val = 0 then 2 * q k
  else q k - q ⟨k.val - 1, by omega⟩

theorem sixVertexPositiveHalfRootGap_pos
    {m : Nat} {q : Fin m → Real} (hqmono : StrictMono q)
    (hqpos : ∀ k, 0 < q k) (k : Fin m) :
    0 < sixVertexPositiveHalfRootGap q k := by
  unfold sixVertexPositiveHalfRootGap
  split_ifs with hk
  · nlinarith [hqpos k]
  · let kp : Fin m := ⟨k.val - 1, by omega⟩
    have hpred : kp < k := by
      rw [Fin.lt_def]
      dsimp [kp]
      omega
    change 0 < q k - q kp
    linarith [hqmono hpred]

theorem sixVertexEvenSymmetricLift_positive_strictMono
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q)) :
    StrictMono q := by
  intro j k hjk
  have hidx : Fin.natAdd m j < Fin.natAdd m k := by
    rw [Fin.lt_def]
    simp [Fin.natAdd]
    omega
  simpa only [sixVertexEvenSymmetricLift_natAdd] using hq.1 hidx

theorem sixVertexPositiveHalfRootGap_pos_of_open
    {m : Nat} {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (k : Fin m) : 0 < sixVertexPositiveHalfRootGap q k := by
  apply sixVertexPositiveHalfRootGap_pos
    (sixVertexEvenSymmetricLift_positive_strictMono hq)
  intro j
  exact (sixVertexEvenSymmetricLift_positive_mem_Icc hq j).1.lt_of_ne
    (fun h => by
      have hneg : -q j = 0 := by linarith
      let i : Fin (m + m) := Fin.natAdd m j
      let ir : Fin (m + m) := Fin.castAdd m j.rev
      have heq : sixVertexEvenSymmetricLift m q ir =
          sixVertexEvenSymmetricLift m q i := by
        rw [show sixVertexEvenSymmetricLift m q ir = -q j by
          change sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev) = -q j
          rw [sixVertexEvenSymmetricLift_castAdd]
          simp]
        rw [show sixVertexEvenSymmetricLift m q i = q j by
          exact sixVertexEvenSymmetricLift_natAdd m q j]
        linarith
      have hind : ir = i := hq.1.injective heq
      have hne : ir ≠ i := by
        intro hieq
        have hval := congrArg Fin.val hieq
        simp [i, ir, Fin.natAdd, Fin.castAdd] at hval
        omega
      exact hne hind)


def sixVertexBethePositiveHalfScaledJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  sixVertexBethePositiveHalfJacobianMatrix N m c q j k *
    sixVertexPositiveHalfRootGap q k

theorem sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    sixVertexBethePositiveHalfScaledJacobianMatrix N m c q =
      sixVertexBethePositiveHalfJacobianMatrix N m c q *
        Matrix.diagonal (sixVertexPositiveHalfRootGap q) := by
  ext j k
  rw [Matrix.mul_diagonal]
  rfl

theorem sixVertexBethePositiveHalfScaledJacobianMatrix_offdiag_nonneg
    {N m : Nat} {c : Real} (hc : 2 < c) {q : Fin m → Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    {j k : Fin m} (hjk : j ≠ k) :
    0 ≤ sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k := by
  exact sixVertexBethePositiveHalfJacobianMatrix_mul_gap_offdiag_nonneg
    hc hq _ (fun l => (sixVertexPositiveHalfRootGap_pos_of_open hq l).le) hjk


theorem sixVertexBethePositiveHalfJacobianMatrix_diag
    (N m : Nat) (c : Real) (q : Fin m → Real) (j : Fin m) :
    sixVertexBethePositiveHalfJacobianMatrix N m c q j j =
      (N : Real) +
        ∑ l ∈ Finset.univ.erase (Fin.natAdd m j),
          4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q l) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q l) -
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev))) := by
  have hcross : Fin.natAdd m j ≠ Fin.castAdd m j.rev := by
    intro h
    have hval := congrArg Fin.val h
    simp [Fin.natAdd, Fin.castAdd] at hval
    omega
  unfold sixVertexBethePositiveHalfJacobianMatrix
  dsimp only
  rw [sixVertexBetheJacobianMatrix, if_pos rfl,
    sixVertexBetheJacobianMatrix, if_neg hcross]



theorem sixVertexBethePositiveHalfScaledJacobianMatrix_diag
    (N m : Nat) (c : Real) (q : Fin m → Real) (j : Fin m) :
    sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j =
      ((N : Real) +
        ∑ l ∈ Finset.univ.erase (Fin.natAdd m j),
          4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q l) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q l) -
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j)) /
            sixVertexThetaDerivativeDenominator c
              (sixVertexEvenSymmetricLift m q (Fin.natAdd m j))
              (sixVertexEvenSymmetricLift m q (Fin.castAdd m j.rev)))) *
        sixVertexPositiveHalfRootGap q j := by
  rw [sixVertexBethePositiveHalfScaledJacobianMatrix,
    sixVertexBethePositiveHalfJacobianMatrix_diag]



theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m → Real)
    (hgap : ∀ k, sixVertexPositiveHalfRootGap q k ≠ 0)
    (hdom : ∀ j,
      ∑ k ∈ Finset.univ.erase j,
          ‖sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k‖ <
        ‖sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j‖) :
    Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  let A := sixVertexBethePositiveHalfJacobianMatrix N m c q
  let D := Matrix.diagonal (sixVertexPositiveHalfRootGap q)
  let B := sixVertexBethePositiveHalfScaledJacobianMatrix N m c q
  have hdetB : Matrix.det B ≠ 0 := det_ne_zero_of_sum_row_lt_diag hdom
  have hBD : B = A * D := by
    exact sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal
      N m c q
  have hdetD : Matrix.det D ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hgap k)
  have hdetA : Matrix.det A ≠ 0 := by
    intro hzero
    apply hdetB
    rw [hBD, Matrix.det_mul, hzero, zero_mul]
  have hmatrix : LinearMap.toMatrix'
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap = A := by
    ext j k
    exact sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply hc q j k
  have hdetJ : LinearMap.det
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap ≠ 0 := by
    rw [← LinearMap.det_toMatrix', hmatrix]
    exact hdetA
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdetJ ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)

end
end StatMech.FrontierD
