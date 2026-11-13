/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.WiredBoxCriticalGeneral
import Code.FK.EdwardsSokalWiredCorrelation

open MeasureTheory Filter
open scoped BigOperators Classical

namespace StatMech
namespace OSSS
namespace PottsSharpnessUnconditional

open Lattice FK
open IsingFK
open WiredBoxLocalized WiredBoxSharpness WiredBoxCritical
  WiredBoxCriticalGeneral

theorem wiredFinite_boxBoundary_mass_eq_conn
    (d m q : Nat) [NeZero q] (hm : 1 <= m)
    (beta : Real) (hbeta : 0 < beta) :
    (wiredFiniteMeasure d m
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d m) =
      wiredConnToBdryProbQ (boxGraph d m) (boxBoundary d m) q
        (1 - Real.exp (-beta)) (boxOrigin d m) := by
  let A : Set (ConfigSpace (Sym2 (boxVerts d m))) :=
    {omega | ConnToBdry (boxGraph d m) (boxBoundary d m) omega (boxOrigin d m)}
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' A) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [show boxBdryConnEvent d m = boxRestrict d m ⁻¹' A from rfl]
  rw [fkgq_wiredFiniteMeasure_real_boxRestrictEvent m
    (by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith : 0 < 1 - Real.exp (-beta))
    (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
    (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q) A hmeas]
  rw [wiredConnToBdryProbQ_eq_wiredFkProb_sum]
  unfold A
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro omega _
  simp only [Set.indicator, Set.mem_setOf_eq]
  split <;> simp_all

theorem exists_supercritical_beta
    (d q : Nat) [NeZero q] (hd : 2 <= d) (hq : 2 <= q) :
    ∃ beta0 : Real, 0 < betaFKThetaQ d q
      (by exact_mod_cast (show (1 : Nat) <= q by omega) : (1 : Real) <= q) beta0 := by
  let qr : Real := q
  let pc := fkPc d qr
  let p := (pc + 1) / 2
  let beta0 := -Real.log (1 - p)
  have hqr : (1 : Real) <= qr := by
    change (1 : Real) <= (q : Real)
    exact_mod_cast (show (1 : Nat) <= q by omega)
  have hpc0 : 0 < pc := fkPc_pos_of_two_le hd hqr
  have hpc1 : pc < 1 := fkPc_lt_one_of_two_le hd hqr
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hpcp : pc < p := by dsimp [p]; linarith
  have hremain : 0 < 1 - p := by linarith
  have hremain1 : 1 - p < 1 := by linarith
  have hbeta0 : 0 < beta0 := by
    dsimp [beta0]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-beta0) = p := by
    dsimp [beta0]
    rw [neg_neg, Real.exp_log hremain]
    ring
  refine ⟨beta0, ?_⟩
  rw [betaFKThetaQ_eq d qr hqr beta0 hbeta0]
  have htheta := frp_fkTheta_pos_of_gt_fkPc d hp hp1
    (zero_lt_one.trans_le hqr) hpcp
  simpa only [qr, hparam] using htheta



theorem potts_boundary_bias_decay_even
    (d q : Nat) [NeZero q] (hd : 2 <= d) (hq : 2 <= q)
    (b : Fin q) (beta : Real) (hbeta : 0 < beta)
    (hcrit : beta < fkBetaCriticalQ d q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n →
      0 <= pottsBoundaryProbWired
          (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q b beta 1
          (boxOrigin d (2 * n)) - 1 / (q : Real) ∧
      pottsBoundaryProbWired
          (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q b beta 1
          (boxOrigin d (2 * n)) - 1 / (q : Real) <=
        Real.exp (-((n : Real) / Q)) := by
  have hqr : (1 : Real) <= (q : Real) := by
    exact_mod_cast (show (1 : Nat) <= q by omega)
  obtain ⟨beta0, hbeta0⟩ := exists_supercritical_beta d q hd hq
  obtain ⟨Q, hQ, hdecay⟩ :=
    wiredOuterInner_subcritical_decay_below_fkBetaCriticalQ
      d q beta0 beta hd hqr hbeta0 hbeta hcrit
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  have htwo : 1 <= 2 * n := by omega
  obtain ⟨v0, hv0⟩ := boxBoundary_nonempty d (2 * n) (by omega) htwo
  have hES := pottsBoundaryProbWired_sub_inv_eq_conn
    (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q b beta 1
      (boxOrigin d (2 * n)) v0 hv0
  simp only [mul_one] at hES
  have hmass := wiredFinite_boxBoundary_mass_eq_conn d (2 * n) q htwo beta hbeta
  have hsubset : boxBdryConnEvent d (2 * n) ⊆ boxBdryConnEvent d n :=
    boxBdryConnEvent_subset_le n (2 * n) hn (n_le_two_mul n)
  have houterLocalized :
      wiredConnToBdryProbQ (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q
          (1 - Real.exp (-beta)) (boxOrigin d (2 * n)) <=
        wiredOuterInnerTheta d q beta n := by
    rw [← hmass, wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
      d n hn q beta hqr hbeta]
    exact measureReal_mono hsubset (measure_ne_top _ _)
  have hconn0 : 0 <= wiredConnToBdryProbQ
      (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q
      (1 - Real.exp (-beta)) (boxOrigin d (2 * n)) := by
    unfold wiredConnToBdryProbQ
    apply Finset.sum_nonneg
    intro omega _
    exact bcProb_nonneg (G := boxGraph d (2 * n))
      (C := boundaryCliqueGraph (boxBoundary d (2 * n)))
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith)
      (by linarith [Real.exp_pos (-beta)])
      (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) omega
  have hcoef0 : 0 <= ((q : Real) - 1) / q := by
    have hq0 : (0 : Real) < q := by positivity
    exact div_nonneg (sub_nonneg.mpr hqr) hq0.le
  have hcoef1 : ((q : Real) - 1) / q <= 1 := by
    have hq0 : (0 : Real) < q := by positivity
    rw [div_le_one hq0]
    linarith
  rw [hES]
  refine ⟨mul_nonneg hcoef0 hconn0, ?_⟩
  calc
    ((q : Real) - 1) / q * wiredConnToBdryProbQ
        (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q
        (1 - Real.exp (-beta)) (boxOrigin d (2 * n)) <=
      wiredConnToBdryProbQ
        (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q
        (1 - Real.exp (-beta)) (boxOrigin d (2 * n)) :=
          mul_le_of_le_one_left hconn0 hcoef1
    _ <= wiredOuterInnerTheta d q beta n := houterLocalized
    _ <= Real.exp (-((n : Real) / Q)) := hdecay n hn

theorem potts_boundary_bias_eq_wired_mass
    (d m q : Nat) [NeZero q] (hd : 1 <= d) (hm : 1 <= m)
    (hq : 2 <= q) (b : Fin q) (beta : Real) (hbeta : 0 < beta) :
    pottsBoundaryProbWired (boxGraph d m) (boxBoundary d m) q b beta 1
        (boxOrigin d m) - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        (wiredFiniteMeasure d m
          (by
            have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
            linarith : 0 < 1 - Real.exp (-beta))
          (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
          Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d m) := by
  obtain ⟨v0, hv0⟩ := boxBoundary_nonempty d m hd hm
  have hES := pottsBoundaryProbWired_sub_inv_eq_conn
    (boxGraph d m) (boxBoundary d m) q b beta 1 (boxOrigin d m) v0 hv0
  simp only [mul_one] at hES
  rw [hES, wiredFinite_boxBoundary_mass_eq_conn d m q hm beta hbeta]



theorem potts_boundary_bias_decay
    (d q : Nat) [NeZero q] (hd : 2 <= d) (hq : 2 <= q)
    (b : Fin q) (beta : Real) (hbeta : 0 < beta)
    (hcrit : beta < fkBetaCriticalQ d q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n →
      0 <= pottsBoundaryProbWired
          (boxGraph d n) (boxBoundary d n) q b beta 1 (boxOrigin d n) -
            1 / (q : Real) ∧
      pottsBoundaryProbWired
          (boxGraph d n) (boxBoundary d n) q b beta 1 (boxOrigin d n) -
            1 / (q : Real) <= Real.exp (-((n : Real) / Q)) := by
  have hqr : (1 : Real) <= (q : Real) := by
    exact_mod_cast (show (1 : Nat) <= q by omega)
  have hq0 : (0 : Real) < q := by positivity
  have hcoef0 : 0 <= ((q : Real) - 1) / q :=
    div_nonneg (sub_nonneg.mpr hqr) hq0.le
  have hcoef1 : ((q : Real) - 1) / q < 1 := by
    rw [div_lt_one hq0]
    linarith
  obtain ⟨beta0, hbeta0⟩ := exists_supercritical_beta d q hd hq
  obtain ⟨Q0, hQ0, hdecay⟩ :=
    wiredOuterInner_subcritical_decay_below_fkBetaCriticalQ
      d q beta0 beta hd hqr hbeta0 hbeta hcrit
  let p : Real := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    dsimp [p]
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by dsimp [p]; linarith [Real.exp_pos (-beta)]
  have hqreal : (1 : Real) <= (q : Real) := hqr
  let a : Nat → Real := fun n =>
    (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hqreal) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
  have ha0 : ∀ n, 0 <= a n := fun n => measureReal_nonneg
  have ha1 : ∀ n, a n <= 1 := fun n => measureReal_le_one
  have hbias1eq :
      pottsBoundaryProbWired (boxGraph d 1) (boxBoundary d 1) q b beta 1
          (boxOrigin d 1) - 1 / (q : Real) = ((q : Real) - 1) / q * a 1 := by
    simpa [a, p] using
      potts_boundary_bias_eq_wired_mass d 1 q (by omega) (by omega)
        hq b beta hbeta
  let bias1 := pottsBoundaryProbWired
      (boxGraph d 1) (boxBoundary d 1) q b beta 1 (boxOrigin d 1) -
        1 / (q : Real)
  have hbias10 : 0 <= bias1 := by
    rw [show bias1 = ((q : Real) - 1) / q * a 1 by
      simpa [bias1] using hbias1eq]
    exact mul_nonneg hcoef0 (ha0 1)
  have hbias11 : bias1 < 1 := by
    rw [show bias1 = ((q : Real) - 1) / q * a 1 by
      simpa [bias1] using hbias1eq]
    exact (mul_le_of_le_one_right hcoef0 (ha1 1)).trans_lt hcoef1
  let r := (bias1 + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  let Q1 := -1 / Real.log r
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hQ1 : 0 < Q1 := by
    dsimp [Q1]
    exact div_pos_of_neg_of_neg (by norm_num) hlogr
  have hexpQ1 : Real.exp (-(1 / Q1)) = r := by
    have hlogne : Real.log r ≠ 0 := ne_of_lt hlogr
    rw [show -(1 / Q1) = Real.log r by
      dsimp [Q1]
      field_simp]
    exact Real.exp_log hr0
  let Q := max (3 * Q0) Q1
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos (by norm_num) hQ0) (le_max_left _ _)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  have hbiasEq := potts_boundary_bias_eq_wired_mass
    d n q (by omega) hn hq b beta hbeta
  have hbias0 : 0 <= pottsBoundaryProbWired
      (boxGraph d n) (boxBoundary d n) q b beta 1 (boxOrigin d n) -
        1 / (q : Real) := by
    rw [hbiasEq]
    exact mul_nonneg hcoef0 measureReal_nonneg
  refine ⟨hbias0, ?_⟩
  by_cases hn1 : n = 1
  · subst n
    have hQ1Q : Q1 <= Q := le_max_right _ _
    have hexpMono : Real.exp (-(1 / Q1)) <= Real.exp (-(1 / Q)) := by
      apply Real.exp_le_exp.mpr
      have := one_div_le_one_div_of_le hQ1 hQ1Q
      linarith
    calc
      pottsBoundaryProbWired (boxGraph d 1) (boxBoundary d 1) q b beta 1
          (boxOrigin d 1) - 1 / (q : Real) = bias1 := rfl
      _ <= r := by dsimp [r]; linarith
      _ = Real.exp (-(1 / Q1)) := hexpQ1.symm
      _ <= Real.exp (-(1 / Q)) := hexpMono
      _ = Real.exp (-(((1 : Nat) : Real) / Q)) := by norm_num
  · have hn2 : 2 <= n := by omega
    let k := n / 2
    have hk : 1 <= k := by dsimp [k]; omega
    have h2k : 2 * k <= n := by dsimp [k]; omega
    have hnk : n <= 3 * k := by dsimp [k]; omega
    have hanti := fkgq_boxBdryConnEvent_diag_antitone
      (d := d) hp hp1 hqreal
    have hind : 2 * k - 1 <= n - 1 := by omega
    have hmassMono : a n <= a (2 * k) := by
      have h := hanti hind
      simpa [a, Nat.sub_add_cancel (by omega : 1 <= n),
        Nat.sub_add_cancel (by omega : 1 <= 2 * k)] using h
    have hbiasEven := potts_boundary_bias_eq_wired_mass
      d (2 * k) q (by omega) (by omega) hq b beta hbeta
    have hbiasMono :
        pottsBoundaryProbWired (boxGraph d n) (boxBoundary d n) q b beta 1
            (boxOrigin d n) - 1 / (q : Real) <=
          pottsBoundaryProbWired (boxGraph d (2 * k)) (boxBoundary d (2 * k))
            q b beta 1 (boxOrigin d (2 * k)) - 1 / (q : Real) := by
      rw [hbiasEq, hbiasEven]
      exact mul_le_mul_of_nonneg_left hmassMono hcoef0
    have houter : a (2 * k) <= wiredOuterInnerTheta d q beta k := by
      rw [show a (2 * k) =
          (wiredFiniteMeasure d (2 * k) hp hp1 (zero_lt_one.trans_le hqreal) :
            Measure _).real (boxBdryConnEvent d (2 * k)) by rfl,
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
          d k hk q beta hqreal hbeta]
      exact measureReal_mono
        (boxBdryConnEvent_subset_le k (2 * k) hk (n_le_two_mul k))
        (measure_ne_top _ _)
    have hQ0Q : 3 * Q0 <= Q := le_max_left _ _
    have hrate1 : (n : Real) / (3 * Q0) <= (k : Real) / Q0 := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hQ0) hQ0]
      have hnkR : (n : Real) <= 3 * (k : Real) := by exact_mod_cast hnk
      nlinarith
    have hrate2 : (n : Real) / Q <= (n : Real) / (3 * Q0) := by
      exact div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) hQ0) hQ0Q
    calc
      pottsBoundaryProbWired (boxGraph d n) (boxBoundary d n) q b beta 1
          (boxOrigin d n) - 1 / (q : Real) <=
        pottsBoundaryProbWired (boxGraph d (2 * k)) (boxBoundary d (2 * k))
          q b beta 1 (boxOrigin d (2 * k)) - 1 / (q : Real) := hbiasMono
      _ = ((q : Real) - 1) / q * a (2 * k) := by simpa [a, p] using hbiasEven
      _ <= a (2 * k) := mul_le_of_le_one_left (ha0 _) hcoef1.le
      _ <= wiredOuterInnerTheta d q beta k := houter
      _ <= Real.exp (-((k : Real) / Q0)) := hdecay k hk
      _ <= Real.exp (-((n : Real) / (3 * Q0))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ <= Real.exp (-((n : Real) / Q)) :=
        Real.exp_le_exp.mpr (by linarith)

end PottsSharpnessUnconditional
end OSSS
end StatMech
