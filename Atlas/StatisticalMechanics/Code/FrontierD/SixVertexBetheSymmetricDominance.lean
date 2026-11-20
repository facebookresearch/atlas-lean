/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricJacobian





open Finset Matrix

namespace StatMech.FrontierD

noncomputable section





theorem sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m → Real)
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (G : Fin m → Real) (eps M : Real)
    (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (hmargin : M + 2 * eps < 2 * Real.pi)
    (hdiag : ∀ j,
      |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| ≤ eps)
    (hoff : ∀ j,
      |(∑ k ∈ Finset.univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) -
        G j| ≤ eps)
    (hG : ∀ j, 0 ≤ G j ∧ G j ≤ M) :
    Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
  apply sixVertexEvenSymmetricBetheRootJacobian_injective_of_scaledDiagonalDominance
    hc q (fun k => (sixVertexPositiveHalfRootGap_pos_of_open hq k).ne')
  intro j
  let B := sixVertexBethePositiveHalfScaledJacobianMatrix N m c q
  have hoffNonneg (k : Fin m) (hkj : k ∈ Finset.univ.erase j) :
      0 ≤ B j k := by
    exact sixVertexBethePositiveHalfScaledJacobianMatrix_offdiag_nonneg
      hc hq (Ne.symm (Finset.mem_erase.mp hkj).1)
  have hsumNorm :
      (∑ k ∈ Finset.univ.erase j, ‖B j k‖) =
        ∑ k ∈ Finset.univ.erase j, B j k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Real.norm_eq_abs, abs_of_nonneg (hoffNonneg k hk)]
  have hsumUpper :
      (∑ k ∈ Finset.univ.erase j, B j k) ≤ G j + eps := by
    have h := hoff j
    rw [abs_le] at h
    linarith
  have hdiagLower : 2 * Real.pi - eps ≤ B j j := by
    have h := hdiag j
    rw [abs_le] at h
    linarith
  have hdiagPos : 0 < B j j := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hepsBound : eps < Real.pi := by
      nlinarith [hmargin, hM]
    linarith
  rw [hsumNorm, Real.norm_eq_abs, abs_of_pos hdiagPos]
  calc
    (∑ k ∈ Finset.univ.erase j, B j k) ≤ G j + eps := hsumUpper
    _ ≤ M + eps := by linarith [(hG j).2]
    _ < 2 * Real.pi - eps := by linarith
    _ ≤ B j j := hdiagLower

end
end StatMech.FrontierD
