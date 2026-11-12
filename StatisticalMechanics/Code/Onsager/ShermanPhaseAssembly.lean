/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.KWPhaseLemma5
import Code.Onsager.KWSpectral










namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_phaseBucketE
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_phaseBucketN
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)) d

noncomputable def ons_maskPhaseBucketE
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

noncomputable def ons_maskPhaseBucketN
    (L : ℕ) [NeZero L] (x omega : ℂ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)),
    ons_loopWeight
      (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))) d

theorem ons_KWmatPhase_loopSum_two_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)] {n : ℕ}
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L) :
    (∑ d : Fin (n + 1) → ons_Dart L,
      ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d) =
      2 * ons_phaseBucketE L x omega a b e n +
        ons_phaseBucketN L x omega a b e n := by
  let M := ons_KWmatPhase L x omega
    (ons_spinPhase L a) (ons_spinPhase L b)
  let P : (Fin (n + 1) → ons_Dart L) → Prop := fun d => ∃ i, d i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop := fun d =>
    ∃ j, d j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q (fun d => ons_loopWeight M d)
  have hboth := ons_loopSum_spinPhase_both_zero n x omega homega a b e
  have hsymm := ons_loopSum_spinPhase_symm
    (L := L) (n := n + 1) x omega homega a b e
  have hset :
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e) =
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, d i = e) ∧ ∃ j, d j = ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_phaseBucketE ons_phaseBucketN
  linear_combination hsplit + hboth - hsymm

theorem ons_KWmatPhase_mask_loopSum_two_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)] {n : ℕ}
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    (∑ d : Fin (n + 1) → ons_Dart L,
      ons_loopWeight
        (ons_maskMatrix forbidden (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))) d) =
      2 * ons_maskPhaseBucketE L x omega a b forbidden e n +
        ons_maskPhaseBucketN L x omega a b forbidden e n := by
  let M := ons_maskMatrix forbidden (ons_KWmatPhase L x omega
    (ons_spinPhase L a) (ons_spinPhase L b))
  let P : (Fin (n + 1) → ons_Dart L) → Prop := fun d => ∃ i, d i = e
  let Q : (Fin (n + 1) → ons_Dart L) → Prop := fun d =>
    ∃ j, d j = ons_dartRev L e
  have hsplit := ons_sum_split_by_two P Q (fun d => ons_loopWeight M d)
  have hboth := ons_loopSum_spinPhase_mask_both_zero
    n x omega homega a b forbidden hforbidden e
  have hsymm := ons_loopSum_spinPhase_mask_symm
    (L := L) (n := n + 1) x omega homega a b
    forbidden hforbidden e
  have hset :
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e) =
      Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, d i = e) ∧ ∃ j, d j = ons_dartRev L e) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q, M] at hsplit
  unfold ons_maskPhaseBucketE ons_maskPhaseBucketN
  linear_combination hsplit + hboth - hsymm

theorem ons_KWmatPhase_det_eq_two_bucket_exp
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L)
    (hspec : ∀ alpha ∈ (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1) :
    (1 - ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (-∑' n : ℕ,
        (2 * ons_phaseBucketE L x omega a b e n +
          ons_phaseBucketN L x omega a b e n) / ((n : ℂ) + 1)) := by
  rw [ons_det_eq_walk_exp _ hspec]
  refine congrArg Complex.exp (congrArg Neg.neg (tsum_congr (fun n => ?_)))
  exact congrArg (· / ((n : ℂ) + 1))
    (ons_KWmatPhase_loopSum_two_bucket x omega homega a b e)

theorem ons_KWmatPhase_det_eq_A_mul_bucket
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (e : ons_Dart L)
    (hspec : ∀ alpha ∈ (ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1)
    (hB : Summable (fun n : ℕ =>
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)))
    (hN : Summable (fun n : ℕ =>
      ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1))) :
    (1 - ons_KWmatPhase L x omega
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (-∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1)) *
      Complex.exp (-2 * ∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) := by
  have hsplit :
      (∑' n : ℕ, (2 * ons_phaseBucketE L x omega a b e n +
        ons_phaseBucketN L x omega a b e n) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1)) := by
    have heq : (fun n : ℕ =>
        (2 * ons_phaseBucketE L x omega a b e n +
          ons_phaseBucketN L x omega a b e n) / ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) +
          ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  rw [ons_KWmatPhase_det_eq_two_bucket_exp x omega homega a b e hspec,
    hsplit]
  rw [show -(2 * (∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1))) =
      (-(∑' n : ℕ,
        ons_phaseBucketN L x omega a b e n / ((n : ℂ) + 1))) +
      (-2 * ∑' n : ℕ,
        ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) by ring,
    Complex.exp_add]

theorem ons_phaseBucketSeries_eq_geometric
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (a b : Fin 2) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖ < 1) :
    (∑' n : ℕ,
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) =
      ∑' k : ℕ,
        (∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega
          (ons_spinPhase L a) (ons_spinPhase L b))
          e (ons_dartRev L e) s) ^ (k + 1) / (k + 1) := by
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  simpa only [ons_phaseBucketE, not_exists] using
    ons_loopBucketSeries_eq_geometric
      (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
      e (ons_dartRev L e) her hsum hsmall

theorem ons_summable_phaseBucketE_firstReturn
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (a b : Fin 2) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖ < 1) :
    Summable fun n : ℕ =>
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1) := by
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  simpa only [ons_phaseBucketE, not_exists] using
    ons_summable_loopBucketSeries
      (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
      e (ons_dartRev L e) her hsum hsmall

theorem ons_hlam_spinPhase_firstReturn
    {L : ℕ} [NeZero L] [Fact (2 < L)]
    (x omega : ℂ) (a b : Fin 2) (e : ons_Dart L)
    (hsum : Summable fun s =>
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖)
    (hsmall : ∑' s,
      ‖ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s‖ < 1) :
    Complex.exp (-∑' n : ℕ,
      ons_phaseBucketE L x omega a b e n / ((n : ℂ) + 1)) =
      1 - ∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s := by
  let z := ∑' s, ons_firstReturnWeight (ons_KWmatPhase L x omega
    (ons_spinPhase L a) (ons_spinPhase L b))
    e (ons_dartRev L e) s
  have hz : ‖z‖ < 1 :=
    lt_of_le_of_lt (norm_tsum_le_tsum_norm hsum) hsmall
  rw [ons_phaseBucketSeries_eq_geometric x omega a b e hsum hsmall]
  exact ons_lemma4_exp hz

theorem ons_KWmatPhase_spectral_Sherman_small
    (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) :
    ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1 := by
  apply ons_KWmatPhase_spectral_lt_one
  exact ons_Sherman_card_mul_small L hx

noncomputable def ons_spinWalkRoot
    (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2) : ℂ :=
  ons_detWalkRoot (ons_KWmatPhase L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b))

theorem ons_spinWalkRoot_sq
    (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) :
    ons_spinWalkRoot L x a b ^ 2 =
      (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  exact ons_detWalkRoot_sq _
    (ons_KWmatPhase_spectral_Sherman_small L hx a b)

noncomputable def ons_phaseAvoidRoot
    (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2)
    (e : ons_Dart L) : ℂ :=
  Complex.exp (-(∑' n : ℕ,
    ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
      ((n : ℂ) + 1)) / 2)

theorem ons_phaseAvoidRoot_eq_maskRoot
    (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2)
    (e : ons_Dart L) :
    ons_phaseAvoidRoot L x a b e =
      ons_detWalkRoot
        (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) := by
  let M := ons_KWmatPhase L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let S : Finset (ons_Dart L) := {e, ons_dartRev L e}
  have hterm : ∀ n : ℕ,
      (∑ d : Fin (n + 1) → ons_Dart L,
        ∏ k : Fin (n + 1), (ons_maskMatrix S M) (d k) (d (k + 1))) =
      ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n := by
    intro n
    have hsum := ons_loopSum_maskMatrix (n := n + 1) S M
    have hset :
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ ∃ k, d k ∈ S) =
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S,
        Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset] at hsum
    simpa only [M, S, ons_loopWeight, ons_phaseBucketN] using hsum
  unfold ons_phaseAvoidRoot ons_detWalkRoot
  apply congrArg Complex.exp
  congr 1
  apply congrArg Neg.neg
  apply tsum_congr
  intro n
  exact congrArg (· / ((n : ℂ) + 1)) (hterm n).symm


theorem ons_spinWalkRoot_factor_firstReturn_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (e : ons_Dart L) :
    ons_spinWalkRoot L x a b = ons_phaseAvoidRoot L x a b e *
      (1 - ∑' s, ons_firstReturnWeight
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s) := by
  have hfirst := ons_KWmatPhase_firstReturnWeight_small L hx a b e
    (ons_dartRev L e)
  have hB := ons_summable_phaseBucketE_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2
  let Q : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop := fun _ d =>
    ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)
  have hNraw := ons_KWmatPhase_filteredLoopSeries_summable L hx a b Q
  have hN : Summable fun n : ℕ =>
      ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
        ((n : ℂ) + 1) := by
    simpa only [ons_phaseBucketN, Q] using hNraw
  have hseries :
      (∑' n : ℕ,
        (∑ d : Fin (n + 1) → ons_Dart L,
          ∏ k : Fin (n + 1),
            ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)
              (d k) (d (k + 1))) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) := by
    have hterm : ∀ n : ℕ,
        (∑ d : Fin (n + 1) → ons_Dart L,
          ∏ k : Fin (n + 1),
            ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)
              (d k) (d (k + 1))) =
        2 * ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n +
          ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n := by
      intro n
      simpa only [ons_loopWeight] using
        (ons_KWmatPhase_loopSum_two_bucket
          (L := L) (n := n) (x : ℂ) ons_turnRoot
          ons_turnRoot_sq a b e)
    rw [tsum_congr (fun n : ℕ =>
      congrArg (· / ((n : ℂ) + 1)) (hterm n))]
    have heq : (fun n : ℕ =>
        (2 * ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n +
          ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n) /
            ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
            ((n : ℂ) + 1)) +
          ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
            ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  rw [ons_spinWalkRoot, ons_detWalkRoot, hseries]
  rw [show -(2 * (∑' n : ℕ,
        ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1))) / 2 =
      (-(∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) / 2) +
      (-(∑' n : ℕ,
        ons_phaseBucketE L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1))) by ring,
    Complex.exp_add]
  rw [ons_hlam_spinPhase_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2]
  rfl

theorem ons_summable_phaseBucketN_Sherman_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (e : ons_Dart L) :
    Summable fun n : ℕ =>
      ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
        ((n : ℂ) + 1) := by
  let P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop := fun _ d =>
    ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)
  have hs := ons_KWmatPhase_filteredLoopSeries_summable L hx a b P
  simpa only [ons_phaseBucketN, P] using hs


theorem ons_detWalkRoot_mask_delete_pair
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    ons_detWalkRoot
        (ons_maskMatrix forbidden
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) =
      ons_detWalkRoot
          (ons_maskMatrix
            (({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden)
            (ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - ∑' s, ons_firstReturnWeight
          (ons_maskMatrix forbidden
            (ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)))
          e (ons_dartRev L e) s) := by
  let M := ons_KWmatPhase L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let MF := ons_maskMatrix forbidden M
  let pair : Finset (ons_Dart L) := {e, ons_dartRev L e}
  have hentry : ∀ d2 d1 : ons_Dart L, ‖MF d2 d1‖ ≤ ‖(x : ℂ)‖ := by
    intro d2 d1
    simp only [MF, ons_maskMatrix]
    split
    · simp
    · exact norm_ons_KWmatPhase_spin_entry_le L x a b d2 d1
  have hfirst :
      Summable (fun s =>
        ‖ons_firstReturnWeight MF e (ons_dartRev L e) s‖) ∧
      (∑' s, ‖ons_firstReturnWeight MF e (ons_dartRev L e) s‖) < 1 := by
    apply ons_firstReturnWeight_small MF e (ons_dartRev L e)
      ‖(x : ℂ)‖ (norm_nonneg _) hentry
    simpa [ons_ShermanRadius, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx.1] using hx.2
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  have hB : Summable fun n : ℕ =>
      ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
        ((n : ℂ) + 1) := by
    simpa only [ons_maskPhaseBucketE, MF, not_exists] using
      ons_summable_loopBucketSeries MF e (ons_dartRev L e)
        her hfirst.1 hfirst.2
  have hN : Summable fun n : ℕ =>
      ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
        ((n : ℂ) + 1) := by
    let P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop := fun _ d =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)
    have hs := ons_summable_filteredLoopSeries MF ‖(x : ℂ)‖
      (norm_nonneg _) hentry
      (by simpa [Complex.norm_real] using ons_Sherman_card_mul_small L hx) P
    simpa only [ons_maskPhaseBucketN, MF, P] using hs
  have hseries :
      (∑' n : ℕ,
        (∑ d : Fin (n + 1) → ons_Dart L,
          ons_loopWeight MF d) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) := by
    rw [tsum_congr (fun n : ℕ => congrArg (· / ((n : ℂ) + 1))
      (ons_KWmatPhase_mask_loopSum_two_bucket
        (L := L) (n := n) (x : ℂ) ons_turnRoot ons_turnRoot_sq
        a b forbidden hforbidden e))]
    have heq : (fun n : ℕ =>
        (2 * ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n +
          ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n) /
            ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
            ((n : ℂ) + 1)) +
          ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
            ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  have hlam :
      Complex.exp (-(∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1))) =
      1 - ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s := by
    let z := ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s
    have hz : ‖z‖ < 1 :=
      lt_of_le_of_lt (norm_tsum_le_tsum_norm hfirst.1) hfirst.2
    have hgeom := ons_loopBucketSeries_eq_geometric
      MF e (ons_dartRev L e) her hfirst.1 hfirst.2
    rw [show (∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) =
        ∑' k : ℕ, z ^ (k + 1) / (k + 1) by
      simpa only [ons_maskPhaseBucketE, MF, not_exists, z] using hgeom]
    exact ons_lemma4_exp hz
  have hNroot :
      Complex.exp (-(∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) / 2) =
      ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) := by
    have hmask : ons_maskMatrix pair MF =
        ons_maskMatrix (pair ∪ forbidden) M := by
      simp only [MF]
      exact ons_maskMatrix_union pair forbidden M
    rw [← hmask]
    unfold ons_detWalkRoot
    apply congrArg Complex.exp
    congr 1
    apply congrArg Neg.neg
    apply tsum_congr
    intro n
    apply congrArg (· / ((n : ℂ) + 1))
    have hsum := ons_loopSum_maskMatrix (n := n + 1) pair MF
    have hset :
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ ∃ k, d k ∈ pair) =
        Finset.univ.filter (fun d : Fin (n + 1) → ons_Dart L =>
          ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pair,
        Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset] at hsum
    simpa only [ons_loopWeight, ons_maskPhaseBucketN, MF] using hsum.symm
  change ons_detWalkRoot MF =
    ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) *
      (1 - ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s)
  change Complex.exp (-(∑' n : ℕ,
      (∑ d : Fin (n + 1) → ons_Dart L,
        ∏ k : Fin (n + 1), MF (d k) (d (k + 1))) /
          ((n : ℂ) + 1)) / 2) =
    ons_detWalkRoot (ons_maskMatrix (pair ∪ forbidden) M) *
      (1 - ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s)
  simp only [ons_loopWeight] at hseries
  rw [hseries]
  rw [show -(2 * (∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1))) / 2 =
      (-(∑' n : ℕ,
        ons_maskPhaseBucketN L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1)) / 2) +
      (-(∑' n : ℕ,
        ons_maskPhaseBucketE L (x : ℂ) ons_turnRoot a b forbidden e n /
          ((n : ℂ) + 1))) by ring,
    Complex.exp_add, hNroot, hlam]

def ons_addDartPair (L : ℕ) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) : Finset (ons_Dart L) :=
  ({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden

theorem ons_addDartPair_rev_closed (L : ℕ)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e d : ons_Dart L) :
    ons_dartRev L d ∈ ons_addDartPair L forbidden e ↔
      d ∈ ons_addDartPair L forbidden e := by
  have h1 : ons_dartRev L d = e ↔ d = ons_dartRev L e := by
    constructor
    · intro h
      calc
        d = ons_dartRev L (ons_dartRev L d) :=
          (ons_dartRev_involutive L d).symm
        _ = ons_dartRev L e := congrArg (ons_dartRev L) h
    · rintro rfl
      exact ons_dartRev_involutive L e
  have h2 : ons_dartRev L d = ons_dartRev L e ↔ d = e := by
    constructor
    · intro h
      exact (ons_dartRev_involutive L).injective h
    · exact congrArg (ons_dartRev L)
  simp only [ons_addDartPair, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  rw [h1, h2, hforbidden d]
  tauto

def ons_maskAfter (L : ℕ) (forbidden : Finset (ons_Dart L)) :
    List (ons_Dart L) → Finset (ons_Dart L)
  | [] => forbidden
  | e :: es => ons_maskAfter L (ons_addDartPair L forbidden e) es

noncomputable def ons_maskEliminationProduct
    (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2)
    (forbidden : Finset (ons_Dart L)) : List (ons_Dart L) → ℂ
  | [] => 1
  | e :: es =>
      (1 - ∑' s, ons_firstReturnWeight
        (ons_maskMatrix forbidden
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)))
        e (ons_dartRev L e) s) *
      ons_maskEliminationProduct L x a b
        (ons_addDartPair L forbidden e) es

theorem ons_subset_maskAfter (L : ℕ)
    (forbidden : Finset (ons_Dart L)) (es : List (ons_Dart L)) :
    forbidden ⊆ ons_maskAfter L forbidden es := by
  induction es generalizing forbidden with
  | nil => exact Finset.Subset.rfl
  | cons e es ih =>
      intro d hd
      apply ih (forbidden := ons_addDartPair L forbidden e)
      exact Finset.mem_union_right _ hd

theorem ons_mem_maskAfter_of_mem_list (L : ℕ)
    (forbidden : Finset (ons_Dart L)) (es : List (ons_Dart L))
    {d : ons_Dart L} (hd : d ∈ es) :
    d ∈ ons_maskAfter L forbidden es := by
  induction es generalizing forbidden with
  | nil => simp at hd
  | cons e es ih =>
      rw [List.mem_cons] at hd
      rcases hd with hd | hd
      · apply ons_subset_maskAfter L (ons_addDartPair L forbidden e) es
        simp [ons_addDartPair, hd]
      · exact ih (forbidden := ons_addDartPair L forbidden e) hd

theorem ons_detWalkRoot_mask_eliminate_list
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (es : List (ons_Dart L)) :
    ons_detWalkRoot
        (ons_maskMatrix forbidden
          (ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) =
      ons_detWalkRoot
          (ons_maskMatrix (ons_maskAfter L forbidden es)
            (ons_KWmatPhase L (x : ℂ) ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        ons_maskEliminationProduct L x a b forbidden es := by
  induction es generalizing forbidden with
  | nil => simp [ons_maskAfter, ons_maskEliminationProduct]
  | cons e es ih =>
      have hdel := ons_detWalkRoot_mask_delete_pair L hx a b forbidden
        hforbidden e
      have hclosed : ∀ d,
          ons_dartRev L d ∈ ons_addDartPair L forbidden e ↔
            d ∈ ons_addDartPair L forbidden e :=
        ons_addDartPair_rev_closed L forbidden hforbidden e
      have hrest := ih (forbidden := ons_addDartPair L forbidden e) hclosed
      have hrest' := hrest
      simp only [ons_addDartPair] at hrest'
      rw [hdel, hrest']
      simp only [ons_maskAfter, ons_maskEliminationProduct, ons_addDartPair]
      ring


theorem ons_spinWalkRoot_eq_eliminationProduct
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) :
    ons_spinWalkRoot L x a b =
      ons_maskEliminationProduct L x a b ∅
        (Finset.univ : Finset (ons_Dart L)).toList := by
  let es := (Finset.univ : Finset (ons_Dart L)).toList
  have hclosed : ∀ d : ons_Dart L,
      ons_dartRev L d ∈ (∅ : Finset (ons_Dart L)) ↔
        d ∈ (∅ : Finset (ons_Dart L)) := by simp
  have hiter := ons_detWalkRoot_mask_eliminate_list
    L hx a b (∅ : Finset (ons_Dart L)) hclosed es
  have hall : ons_maskAfter L (∅ : Finset (ons_Dart L)) es =
      (Finset.univ : Finset (ons_Dart L)) := by
    apply Finset.eq_univ_of_forall
    intro d
    apply ons_mem_maskAfter_of_mem_list L
      (∅ : Finset (ons_Dart L)) es
    simp [es]
  have hzero :
      ons_maskMatrix (Finset.univ : Finset (ons_Dart L))
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
    ext d2 d1
    simp [ons_maskMatrix]
  rw [hall, hzero, ons_detWalkRoot_zero, one_mul] at hiter
  simpa [ons_spinWalkRoot, ons_maskMatrix, es] using hiter


theorem ons_KWmatPhase_det_eq_A_mul_firstReturn_sq_Sherman_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) (e : ons_Dart L) :
    (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (-∑' n : ℕ,
        ons_phaseBucketN L (x : ℂ) ons_turnRoot a b e n /
          ((n : ℂ) + 1)) *
      (1 - ∑' s, ons_firstReturnWeight
        (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        e (ons_dartRev L e) s) ^ 2 := by
  have hfirst := ons_KWmatPhase_firstReturnWeight_small L hx a b e
    (ons_dartRev L e)
  have hB := ons_summable_phaseBucketE_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2
  have hN := ons_summable_phaseBucketN_Sherman_small L hx a b e
  rw [ons_KWmatPhase_det_eq_A_mul_bucket (x : ℂ) ons_turnRoot
    ons_turnRoot_sq a b e
    (ons_KWmatPhase_spectral_Sherman_small L hx a b) hB hN]
  congr 1
  rw [pow_two, ← ons_hlam_spinPhase_firstReturn
    (x : ℂ) ons_turnRoot a b e hfirst.1 hfirst.2,
    ← Complex.exp_add]
  congr 1
  ring

end StatMech.Onsager
