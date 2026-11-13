/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPerronSpectralIsolation
import Code.FrontierD.SixVertexBetheRootBounds









open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexHalfFilledBetheCandidateNormalized (k : Nat) (c : Real) : Real :=
  if hc : 2 < c then
    sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) /
      (c ^ 2 - 2) ^ ((k + 1) + (k + 1))
  else 0



theorem sixVertexHalfFilledBetheCandidateNormalized_ge
    (k : Nat) {c : Real} (hc : 2 < c) :
    2 / 2 ^ ((k + 1) + (k + 1)) ≤
      sixVertexHalfFilledBetheCandidateNormalized k c := by
  let m := k + 1
  let d := c ^ 2 - 2
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hfactor (j : Fin m) :
      (d / 2) ^ 2 ≤
        ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexPositiveHalfBetheRoots hc k j))‖ ^ 2 := by
    have hj := sixVertexSelectedBetheM_norm_ge hc k j
    dsimp [d, m] at hj ⊢
    nlinarith [sq_nonneg
      (‖sixVertexBetheM c
        (sixVertexBethePhase
          (sixVertexPositiveHalfBetheRoots hc k j))‖ - d / 2)]
  have hprod :
      (d / 2) ^ (2 * m) ≤
        ∏ j : Fin m,
          ‖sixVertexBetheM c
            (sixVertexBethePhase
              (sixVertexPositiveHalfBetheRoots hc k j))‖ ^ 2 := by
    calc
      (d / 2) ^ (2 * m) = ∏ _j : Fin m, (d / 2) ^ 2 := by
        simp [pow_mul]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => sq_nonneg _)
        (fun j _ => hfactor j)
  have hscale : 0 < d ^ (2 * m) := pow_pos hd _
  have hquot :
      2 * (d / 2) ^ (2 * m) / d ^ (2 * m) ≤
        (2 * ∏ j : Fin m,
          ‖sixVertexBetheM c
            (sixVertexBethePhase
              (sixVertexPositiveHalfBetheRoots hc k j))‖ ^ 2) /
          d ^ (2 * m) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by norm_num)) hscale.le
  have hconst :
      2 / 2 ^ (2 * m) = 2 * (d / 2) ^ (2 * m) / d ^ (2 * m) := by
    rw [div_pow]
    field_simp [hd.ne']
  rw [sixVertexHalfFilledBetheCandidateNormalized, dif_pos hc]
  unfold sixVertexSymmetricBetheEigenvalueValue
  change 2 / 2 ^ (m + m) ≤
    (2 * ∏ j : Fin m,
      ‖sixVertexBetheM c
        (sixVertexBethePhase
          (sixVertexPositiveHalfBetheRoots hc k j))‖ ^ 2) / d ^ (m + m)
  rw [show m + m = 2 * m by omega, hconst]
  exact hquot




theorem eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top
    (k : Nat)
    (hnonzero : ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0) :
    ∀ᶠ c : Real in atTop,
      sixVertexHalfFilledBetheCandidateNormalized k c =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega) c /
          (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) := by
  let N := sixVertexFourWidth 0 k
  let n := (k + 1) + (k + 1)
  have hn : 0 < n := by dsimp [n]; omega
  have hhalf : 2 * n = N := by dsimp [n, N, sixVertexFourWidth]; omega
  let δ : Real := 2 / 2 ^ n
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hμlower : ∀ᶠ c : Real in atTop,
      δ ≤ sixVertexHalfFilledBetheCandidateNormalized k c := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    exact sixVertexHalfFilledBetheCandidateNormalized_ge k hc
  have hμeig : ∀ᶠ c : Real in atTop,
      Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (sixVertexSectorTransferNormalized N n c))
        (sixVertexHalfFilledBetheCandidateNormalized k c) := by
    filter_upwards [hnonzero, eventually_gt_atTop (2 : Real)] with c hnon hc
    obtain ⟨a, ha⟩ := hnon hc
    let z : EuclideanSpace Real (SixVertexSector N n) :=
      WithLp.toLp 2 (sixVertexHalfFilledBetheRotatedRealWave hc k a)
    have hz : z ≠ 0 := by
      intro h
      apply ha
      apply WithLp.toLp_injective
      exact h
    have hraw : Module.End.HasEigenvalue
        (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c))
        (sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k)) := by
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := z)
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hz⟩
      · apply WithLp.ofLp_injective 2
        simpa [z, N, n, Matrix.ofLp_toLpLin] using
          sixVertexHalfFilledBetheRotatedRealWave_eigenrelation hc k a
    have hscale : (c ^ 2 - 2) ^ n ≠ 0 :=
      (pow_pos (by nlinarith) n).ne'
    simpa [sixVertexHalfFilledBetheCandidateNormalized, hc, N, n] using
      sixVertexSectorTransferNormalized_hasEigenvalue hscale hraw
  simpa [N, n] using
    eventually_eq_sixVertexSectorTop_normalized_of_positive_eigenvalue_half
      hn hhalf (sixVertexHalfFilledBetheCandidateNormalized k)
      hδ hμeig hμlower

end

end StatMech.FrontierD
