/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddSymmetricCovering
import Code.FrontierD.SixVertexBetheJacobianStability
import Mathlib.LinearAlgebra.Matrix.Gershgorin





open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

def sixVertexOddNegativeCoordinateIndex (m : Nat) (k : Fin m) :
    Fin ((m + 1) + m) := sixVertexOddNegativeIndex m k.rev

def sixVertexBetheOddPositiveHalfJacobianMatrix
    (N m : Nat) (c : Real) (q : Fin m → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  let p := sixVertexOddSymmetricLift m q
  sixVertexBetheJacobianMatrix N ((m + 1) + m) c p
      (sixVertexOddPositiveIndex m j) (sixVertexOddPositiveIndex m k) -
    sixVertexBetheJacobianMatrix N ((m + 1) + m) c p
      (sixVertexOddPositiveIndex m j) (sixVertexOddNegativeCoordinateIndex m k)

theorem sixVertexOddSymmetricBetheRootJacobian_apply
    {N m : Nat} {c : Real} (hc : 2 < c)
    (q v : Fin m → Real) (j : Fin m) :
    sixVertexOddSymmetricBetheRootJacobian N m c q v j =
      sixVertexBetheRootJacobian N ((m + 1) + m) c
        (sixVertexOddSymmetricLift m q) (sixVertexOddSymmetricLift m v)
        (sixVertexOddPositiveIndex m j) := by
  let full : (Fin ((m + 1) + m) → Real) →
      (Fin ((m + 1) + m) → Real) := fun p i =>
    sixVertexBetheResidual c N ((m + 1) + m) p i
  let positive : (Fin ((m + 1) + m) → Real) →L[Real] (Fin m → Real) :=
    ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj (sixVertexOddPositiveIndex m i)
  let J := sixVertexBetheRootJacobian N ((m + 1) + m) c
    (sixVertexOddSymmetricLift m q)
  have hfull : HasFDerivAt full J (sixVertexOddSymmetricLift m q) :=
    (analyticAt_sixVertexBetheResidual_family N ((m + 1) + m)
      (c, sixVertexOddSymmetricLift m q) hc)
      |>.comp (x := sixVertexOddSymmetricLift m q)
        (f := fun p : Fin ((m + 1) + m) → Real => (c, p))
        (analyticAt_const.prod analyticAt_id)
      |>.hasStrictFDerivAt.hasFDerivAt
  have hlift : HasFDerivAt (sixVertexOddSymmetricLift m)
      (sixVertexOddSymmetricLift m) q :=
    (sixVertexOddSymmetricLift m).hasFDerivAt
  have hcomp : HasFDerivAt
      (fun r : Fin m → Real => positive (full (sixVertexOddSymmetricLift m r)))
      (positive.comp (J.comp (sixVertexOddSymmetricLift m))) q :=
    positive.hasFDerivAt.comp q (hfull.comp q hlift)
  have heq : sixVertexOddSymmetricBetheRootJacobian N m c q =
      positive.comp (J.comp (sixVertexOddSymmetricLift m)) := by
    apply HasFDerivAt.unique
    · exact (analyticAt_sixVertexOddSymmetricBetheResidual_family N m (c, q) hc)
        |>.comp (x := q) (f := fun r : Fin m → Real => (c, r))
          (analyticAt_const.prod analyticAt_id)
        |>.hasStrictFDerivAt.hasFDerivAt
    · simpa [full, positive, sixVertexOddSymmetricBetheResidual,
        Function.comp_def] using hcomp
  rw [heq]
  rfl

private theorem sixVertexOddSymmetricLift_single (m : Nat) (k : Fin m) :
    sixVertexOddSymmetricLift m (Pi.single k 1) =
      Pi.single (sixVertexOddPositiveIndex m k) 1 -
        Pi.single (sixVertexOddNegativeCoordinateIndex m k) 1 := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro a
  · refine Fin.lastCases ?_ ?_ a
    · have hcp : sixVertexOddCentralIndex m ≠
          sixVertexOddPositiveIndex m k := by
        intro h
        have hv := congrArg Fin.val h
        simp [sixVertexOddCentralIndex, sixVertexOddPositiveIndex] at hv
        omega
      have hcn : sixVertexOddCentralIndex m ≠
          sixVertexOddNegativeCoordinateIndex m k := by
        intro h
        have hv := congrArg Fin.val h
        simp [sixVertexOddCentralIndex, sixVertexOddNegativeCoordinateIndex,
          sixVertexOddNegativeIndex] at hv
        omega
      rw [show Fin.castAdd m (Fin.last m) = sixVertexOddCentralIndex m by rfl,
        sixVertexOddSymmetricLift_central]
      simp [Pi.single_apply, hcp, hcn]
    · intro j
      have hcross : sixVertexOddNegativeIndex m j ≠
          sixVertexOddPositiveIndex m k := by
        intro h
        have hv := congrArg Fin.val h
        simp [sixVertexOddNegativeIndex, sixVertexOddPositiveIndex] at hv
        omega
      rw [show Fin.castAdd m j.castSucc = sixVertexOddNegativeIndex m j by rfl,
        sixVertexOddSymmetricLift_negative]
      simp only [Pi.single_apply, Pi.sub_apply]
      rw [if_neg hcross]
      have hrev : j.rev = k ↔ j = k.rev := by
        constructor
        · intro h
          rw [← h, Fin.rev_rev]
        · intro h
          rw [h, Fin.rev_rev]
      simp [sixVertexOddNegativeCoordinateIndex, sixVertexOddNegativeIndex,
        Fin.castAdd_inj, hrev]
  · have hcross : sixVertexOddPositiveIndex m a ≠
        sixVertexOddNegativeCoordinateIndex m k := by
      intro h
      have hv := congrArg Fin.val h
      simp [sixVertexOddPositiveIndex, sixVertexOddNegativeCoordinateIndex,
        sixVertexOddNegativeIndex] at hv
      omega
    rw [show Fin.natAdd (m + 1) a = sixVertexOddPositiveIndex m a by rfl,
      sixVertexOddSymmetricLift_positive]
    simp only [Pi.single_apply, Pi.sub_apply]
    rw [if_neg hcross]
    simp [sixVertexOddPositiveIndex]

theorem sixVertexOddSymmetricBetheRootJacobian_toMatrix'_apply
    {N m : Nat} {c : Real} (hc : 2 < c)
    (q : Fin m → Real) (j k : Fin m) :
    LinearMap.toMatrix'
      (sixVertexOddSymmetricBetheRootJacobian N m c q).toLinearMap j k =
        sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k := by
  rw [LinearMap.toMatrix'_apply]
  change sixVertexOddSymmetricBetheRootJacobian N m c q
      (Pi.single k 1) j = _
  rw [sixVertexOddSymmetricBetheRootJacobian_apply hc,
    sixVertexOddSymmetricLift_single, map_sub]
  have h₁ := sixVertexBetheRootJacobian_toMatrix'_apply (N := N) hc
    (sixVertexOddSymmetricLift m q) (sixVertexOddPositiveIndex m j)
      (sixVertexOddPositiveIndex m k)
  have h₂ := sixVertexBetheRootJacobian_toMatrix'_apply (N := N) hc
    (sixVertexOddSymmetricLift m q) (sixVertexOddPositiveIndex m j)
      (sixVertexOddNegativeCoordinateIndex m k)
  change sixVertexBetheRootJacobian N ((m + 1) + m) c
      (sixVertexOddSymmetricLift m q)
      (Pi.single (sixVertexOddPositiveIndex m k) 1)
      (sixVertexOddPositiveIndex m j) = _ at h₁
  change sixVertexBetheRootJacobian N ((m + 1) + m) c
      (sixVertexOddSymmetricLift m q)
      (Pi.single (sixVertexOddNegativeCoordinateIndex m k) 1)
      (sixVertexOddPositiveIndex m j) = _ at h₂
  change sixVertexBetheRootJacobian N ((m + 1) + m) c
        (sixVertexOddSymmetricLift m q)
        (Pi.single (sixVertexOddPositiveIndex m k) 1)
        (sixVertexOddPositiveIndex m j) -
      sixVertexBetheRootJacobian N ((m + 1) + m) c
        (sixVertexOddSymmetricLift m q)
        (Pi.single (sixVertexOddNegativeCoordinateIndex m k) 1)
        (sixVertexOddPositiveIndex m j) = _
  rw [h₁, h₂]
  rfl

theorem sixVertexOddSymmetricBetheRootJacobian_injective_of_diagonalDominance
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m → Real)
    (hdom : ∀ j,
      ∑ k ∈ Finset.univ.erase j,
          ‖sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j k‖ <
        ‖sixVertexBetheOddPositiveHalfJacobianMatrix N m c q j j‖) :
    Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m c q) := by
  let A := sixVertexBetheOddPositiveHalfJacobianMatrix N m c q
  have hdet : Matrix.det A ≠ 0 := det_ne_zero_of_sum_row_lt_diag hdom
  have hmatrix : LinearMap.toMatrix'
      (sixVertexOddSymmetricBetheRootJacobian N m c q).toLinearMap = A := by
    ext j k
    exact sixVertexOddSymmetricBetheRootJacobian_toMatrix'_apply hc q j k
  have hdetJ : LinearMap.det
      (sixVertexOddSymmetricBetheRootJacobian N m c q).toLinearMap ≠ 0 := by
    rw [← LinearMap.det_toMatrix', hmatrix]
    exact hdet
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdetJ ((LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker)

end

end StatMech.FrontierD
