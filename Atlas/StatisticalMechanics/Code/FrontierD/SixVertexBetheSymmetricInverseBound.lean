/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheDiagonalDominanceInverse
import Code.FrontierD.SixVertexBetheSymmetricOffDiagonal










open Finset Matrix

namespace StatMech.FrontierD

noncomputable section



theorem exists_abs_le_scaledJacobian_mulVec_of_sourceBounds
    {N m : Nat} {c : Real} (hc : 2 < c) (hm : 0 < m)
    {q : Fin m -> Real}
    (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (G : Fin m -> Real) (eps M : Real)
    (heps : 0 <= eps) (hM : 0 <= M)
    (hmargin : M + 2 * eps < 2 * Real.pi)
    (hdiag : forall j,
      |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j -
        2 * Real.pi| <= eps)
    (hoff : forall j,
      |(∑ k ∈ univ.erase j,
          sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) -
        G j| <= eps)
    (hG : forall j, 0 <= G j /\ G j <= M)
    (v : Fin m -> Real) :
    exists i,
      (forall j, |v j| <= |v i|) /\
      (2 * Real.pi - M - 2 * eps) * |v i| <=
        |(sixVertexBethePositiveHalfScaledJacobianMatrix N m c q).mulVec v i| := by
  classical
  let B := sixVertexBethePositiveHalfScaledJacobianMatrix N m c q
  let delta := 2 * Real.pi - M - 2 * eps
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hrow (j : Fin m) :
      delta + (∑ k ∈ univ.erase j, |B j k|) <= |B j j| := by
    have hoffNonneg (k : Fin m) (hkj : k ∈ univ.erase j) :
        0 <= B j k := by
      exact sixVertexBethePositiveHalfScaledJacobianMatrix_offdiag_nonneg
        hc hq (Ne.symm (mem_erase.mp hkj).1)
    have hsumNorm :
        (∑ k ∈ univ.erase j, |B j k|) =
          ∑ k ∈ univ.erase j, B j k := by
      apply sum_congr rfl
      intro k hk
      rw [abs_of_nonneg (hoffNonneg k hk)]
    have hsumUpper :
        (∑ k ∈ univ.erase j, B j k) <= G j + eps := by
      have h := hoff j
      change |(∑ k ∈ univ.erase j, B j k) - G j| <= eps at h
      rw [abs_le] at h
      linarith
    have hdiagLower : 2 * Real.pi - eps <= B j j := by
      have h := hdiag j
      change |B j j - 2 * Real.pi| <= eps at h
      rw [abs_le] at h
      linarith
    have hdiagPos : 0 < B j j := by
      have hepsBound : eps < Real.pi := by
        nlinarith [hmargin, hM]
      linarith [Real.pi_pos]
    rw [hsumNorm, abs_of_pos hdiagPos]
    dsimp [delta]
    linarith [(hG j).2]
  simpa [B, delta] using
    exists_abs_le_abs_mulVec_of_diagonalMargin B v hrow



theorem exists_abs_le_scaledJacobian_mulVec_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N m : Nat} (hm : 0 < m) (hN : 0 < N)
    (hcount : m + m <= N) {q : Fin m -> Real}
    (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
    (hsol : SixVertexSatisfiesBetheEquations c N (m + m)
      (sixVertexEvenSymmetricLift m q))
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N (m + m)
      (sixVertexEvenSymmetricLift m q) x)
    (hmargin : sixVertexSymmetricScatteringBoundaryBound c +
      2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower <
        2 * Real.pi)
    (v : Fin m -> Real) :
    exists i,
      (forall j, |v j| <= |v i|) /\
      (2 * Real.pi - sixVertexSymmetricScatteringBoundaryBound c -
          2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower) *
          |v i| <=
        |(sixVertexBethePositiveHalfScaledJacobianMatrix N m c q).mulVec v i| := by
  let mesh := 1 / ((N : Real) * lower)
  let G : Fin m -> Real := fun j =>
    ∫ y in -q ⟨m - 1, by omega⟩..q ⟨0, hm⟩,
      sixVertexSymmetricScatteringDerivative c (-q j) y
  let D := sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower
  let O := sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower
  let eps := sixVertexSymmetricJacobianTotalErrorOfLower c N lower
  let M := sixVertexSymmetricScatteringBoundaryBound c
  have hD : 0 <= D := by
    dsimp [D, sixVertexSymmetricJacobianDiagonalErrorOfLower]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hO : 0 <= O := by
    dsimp [O, sixVertexSymmetricJacobianOffDiagonalErrorOfLower]
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have heps : 0 <= eps := by
    dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower]
    exact add_nonneg hD hO
  have hM : 0 <= M := sixVertexSymmetricScatteringBoundaryBound_nonneg hc
  have hmesh (k : Fin m) : sixVertexPositiveHalfRootGap q k <= mesh :=
    sixVertexPositiveHalfRootGap_upper_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity k
  apply exists_abs_le_scaledJacobian_mulVec_of_sourceBounds
    hc hm hopen G eps M heps hM hmargin
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_diag_sub_two_pi_le_of_lower
        hc hN hcount hopen hsol hlower hdensity j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower, D, O] at ⊢
      linarith)
  · intro j
    have hj :=
      abs_sixVertexBethePositiveHalfScaledJacobianMatrix_offdiagSum_sub_integral_le_of_mesh
        (N := N) hc hm hopen hmesh j
    exact hj.trans (by
      dsimp [eps, sixVertexSymmetricJacobianTotalErrorOfLower, O,
        sixVertexSymmetricJacobianOffDiagonalErrorOfLower, mesh] at ⊢
      linarith)
  · intro j
    dsimp [G]
    apply intervalIntegral_sixVertexSymmetricScatteringDerivative_root_bounds
      hc hopen j ⟨0, hm⟩ ⟨m - 1, by omega⟩
    exact (sixVertexEvenSymmetricLift_positive_strictMono hopen).monotone (by
      simp only [Fin.le_def]
      omega)

end

end StatMech.FrontierD
