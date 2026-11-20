/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.IsingFK.BetacPc
import Code.IsingFK.PcUpperAllDimensions
import Code.FK.FreePercolationFull

open Real Set

namespace StatMech

namespace FK



theorem fkgq_fkTheta_eq_zero_of_lt_pc
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hpc : p < fkPc d q) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 := by
  have hne : (fkSubcriticalSet d q).Nonempty := by
    rcases (fkSubcriticalSet d q).eq_empty_or_nonempty with hempty | hne
    · exfalso
      rw [fkPc, hempty, Real.sSup_empty] at hpc
      linarith
    · exact hne
  obtain ⟨p', hp'mem, hpp'⟩ := exists_lt_of_lt_csSup hne hpc
  obtain ⟨hp'0, hp'1, _hq', htheta'⟩ := hp'mem
  have hmono :
      fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) ≤
        fkTheta d hp'0 hp'1 (zero_lt_one.trans_le hq) (q := q) :=
    fkgq_fkTheta_monotone_in_p hp hp1 hp'0 hp'1 hpp'.le hq
  refine le_antisymm ?_ (fkTheta_nonneg d hp hp1 (zero_lt_one.trans_le hq) (q := q))
  exact hmono.trans_eq htheta'

end FK

namespace IsingFK



theorem betaC_eq_of_strict_transition (mStar : ℝ → ℝ) (t : ℝ)
    (ht : 0 < t)
    (hbelow : ∀ beta, 0 < beta → beta < t → mStar beta = 0)
    (habove : ∀ beta, t < beta → 0 < mStar beta) :
    betaC mStar = t := by
  let S : Set ℝ := {beta | 0 < beta ∧ mStar beta = 0}
  have hsub : Set.Ioo (0 : ℝ) t ⊆ S := by
    rintro beta ⟨hbeta0, hbetat⟩
    exact ⟨hbeta0, hbelow beta hbeta0 hbetat⟩
  have hSnonempty : S.Nonempty := by
    refine ⟨t / 2, ?_⟩
    have ht2 : 0 < t / 2 := by linarith
    have ht2t : t / 2 < t := by linarith
    exact ⟨ht2, hbelow (t / 2) ht2 ht2t⟩
  have hSle : ∀ beta ∈ S, beta ≤ t := by
    rintro beta ⟨hbeta0, hzero⟩
    by_contra hnot
    have hpos := habove beta (lt_of_not_ge hnot)
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  have hSbdd : BddAbove S := ⟨t, hSle⟩
  unfold betaC
  change sSup S = t
  apply le_antisymm
  · exact csSup_le hSnonempty hSle
  · rw [← csSup_Ioo ht]
    exact csSup_le_csSup hSbdd (Set.nonempty_Ioo.mpr ht) hsub




noncomputable def pottsFKMagnetization (d : ℕ) (q : ℝ) (hq : 1 < q) (beta : ℝ) : ℝ :=
  if hbeta : 0 < beta then
    FK.fkTheta d
      (by
        rw [← betaToP_zero q]
        exact (strictMono_betaToP q hq) hbeta)
      (betaToP_mem q beta hq hbeta.le).2
      (zero_lt_one.trans hq) (q := q)
  else 0


theorem pottsFKMagnetization_nonneg (d : ℕ) (q : ℝ) (hq : 1 < q) (beta : ℝ) :
    0 ≤ pottsFKMagnetization d q hq beta := by
  rw [pottsFKMagnetization]
  split_ifs with hbeta
  · exact FK.fkTheta_nonneg d _ _ _
  · exact le_rfl



theorem pottsFKMagnetization_eq_zero_of_lt_critical
    {d : ℕ} {q beta : ℝ} (hq : 1 < q) (hpc1 : FK.fkPc d q < 1)
    (hbeta : 0 < beta)
    (hbelow : beta < pToBeta q (FK.fkPc d q)) :
    pottsFKMagnetization d q hq beta = 0 := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  have hp : 0 < betaToP q beta := by
    rw [← betaToP_zero q]
    exact (strictMono_betaToP q hq) hbeta
  have hp1 : betaToP q beta < 1 := (betaToP_mem q beta hq hbeta.le).2
  have hparam : betaToP q beta < FK.fkPc d q := by
    have h := (strictMono_betaToP q hq) hbelow
    rwa [betaToP_pToBeta q (FK.fkPc d q) hq0 hq1 hpc1] at h
  rw [pottsFKMagnetization, dif_pos hbeta]
  exact FK.fkgq_fkTheta_eq_zero_of_lt_pc hp hp1 hq.le hparam



theorem pottsFKMagnetization_pos_of_critical_lt
    {d : ℕ} {q beta : ℝ} (hq : 1 < q)
    (hpc0 : 0 ≤ FK.fkPc d q) (hpc1 : FK.fkPc d q < 1)
    (habove : pToBeta q (FK.fkPc d q) < beta) :
    0 < pottsFKMagnetization d q hq beta := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  have hthreshold_nonneg : 0 ≤ pToBeta q (FK.fkPc d q) :=
    pToBeta_mem q (FK.fkPc d q) hq ⟨hpc0, hpc1⟩
  have hbeta : 0 < beta := lt_of_le_of_lt hthreshold_nonneg habove
  have hp : 0 < betaToP q beta := by
    rw [← betaToP_zero q]
    exact (strictMono_betaToP q hq) hbeta
  have hp1 : betaToP q beta < 1 := (betaToP_mem q beta hq hbeta.le).2
  have hparam : FK.fkPc d q < betaToP q beta := by
    have h := (strictMono_betaToP q hq) habove
    rwa [betaToP_pToBeta q (FK.fkPc d q) hq0 hq1 hpc1] at h
  rw [pottsFKMagnetization, dif_pos hbeta]
  exact FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (zero_lt_one.trans hq) hparam





theorem pottsFK_betaC_eq (d : ℕ) {q : ℝ} (hd : 2 ≤ d) (hq : 1 < q) :
    betaC (pottsFKMagnetization d q hq) =
      -((q - 1) / q) * Real.log (1 - FK.fkPc d q) := by
  have hpc0 : 0 < FK.fkPc d q := FK.fkPc_pos_of_two_le hd hq.le
  have hpc1 : FK.fkPc d q < 1 := FK.fkPc_lt_one_of_two_le hd hq.le
  have ht : 0 < pToBeta q (FK.fkPc d q) := by
    rw [← pToBeta_zero q]
    exact (strictMonoOn_pToBeta q hq) (Set.mem_Iio.mpr (by norm_num))
      (Set.mem_Iio.mpr hpc1) hpc0
  exact betaC_eq_of_strict_transition
    (pottsFKMagnetization d q hq) (pToBeta q (FK.fkPc d q))
    ht
    (fun beta hbeta hbelow =>
      pottsFKMagnetization_eq_zero_of_lt_critical hq hpc1 hbeta hbelow)
    (fun beta habove =>
      pottsFKMagnetization_pos_of_critical_lt hq hpc0.le hpc1 habove)

end IsingFK

end StatMech
