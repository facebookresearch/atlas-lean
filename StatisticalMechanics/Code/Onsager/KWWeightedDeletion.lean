/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeightedBuckets










namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_detWalkRoot_weighted_mask_delete_pair
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (omega : ℂ) (homega : omega ^ 2 = Complex.I)
    (a b : Fin 2) (q : ℝ) (hq : 0 ≤ q)
    (hentryM : ∀ d2 d1,
      ‖ons_KWmatWeightedPhase L weight omega
        (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1)
    (forbidden : Finset (ons_Dart L))
    (hforbidden : ∀ d,
      ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
    (e : ons_Dart L) :
    ons_detWalkRoot
        (ons_maskMatrix forbidden
          (ons_KWmatWeightedPhase L weight omega
            (ons_spinPhase L a) (ons_spinPhase L b))) =
      ons_detWalkRoot
          (ons_maskMatrix
            (({e, ons_dartRev L e} : Finset (ons_Dart L)) ∪ forbidden)
            (ons_KWmatWeightedPhase L weight omega
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (1 - ∑' s, ons_firstReturnWeight
          (ons_maskMatrix forbidden
            (ons_KWmatWeightedPhase L weight omega
              (ons_spinPhase L a) (ons_spinPhase L b)))
          e (ons_dartRev L e) s) := by
  let M := ons_KWmatWeightedPhase L weight omega
    (ons_spinPhase L a) (ons_spinPhase L b)
  let MF := ons_maskMatrix forbidden M
  let pair : Finset (ons_Dart L) := {e, ons_dartRev L e}
  have hentry : ∀ d2 d1 : ons_Dart L, ‖MF d2 d1‖ ≤ q := by
    intro d2 d1
    simp only [MF, ons_maskMatrix]
    split
    · simpa using hq
    · exact hentryM d2 d1
  have hfirst :
      Summable (fun s =>
        ‖ons_firstReturnWeight MF e (ons_dartRev L e) s‖) ∧
      (∑' s, ‖ons_firstReturnWeight MF e (ons_dartRev L e) s‖) < 1 :=
    ons_firstReturnWeight_small MF e (ons_dartRev L e)
      q hq hentry hsmall
  have her : e ≠ ons_dartRev L e := (ons_dartRev_ne L e).symm
  have hB : Summable fun n : ℕ =>
      ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n /
        ((n : ℂ) + 1) := by
    simpa only [ons_maskWeightedPhaseBucketE, MF, not_exists] using
      ons_summable_loopBucketSeries MF e (ons_dartRev L e)
        her hfirst.1 hfirst.2
  have hN : Summable fun n : ℕ =>
      ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n /
        ((n : ℂ) + 1) := by
    let P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop := fun _ d =>
      ¬ (∃ i, d i = e) ∧ ¬ (∃ j, d j = ons_dartRev L e)
    have hs := ons_summable_filteredLoopSeries MF q hq hentry hcard P
    simpa only [ons_maskWeightedPhaseBucketN, MF, P] using hs
  have hseries :
      (∑' n : ℕ,
        (∑ d : Fin (n + 1) → ons_Dart L,
          ons_loopWeight MF d) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n /
          ((n : ℂ) + 1)) := by
    rw [tsum_congr (fun n : ℕ => congrArg (· / ((n : ℂ) + 1))
      (ons_KWmatWeightedPhase_mask_loopSum_two_bucket
        (L := L) (n := n) weight omega homega
        a b forbidden hforbidden e))]
    have heq : (fun n : ℕ =>
        (2 * ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n +
          ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n) /
            ((n : ℂ) + 1)) =
        (fun n : ℕ => 2 *
          (ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n /
            ((n : ℂ) + 1)) +
          ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n /
            ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  have hlam :
      Complex.exp (-(∑' n : ℕ,
        ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n /
          ((n : ℂ) + 1))) =
      1 - ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s := by
    let z := ∑' s, ons_firstReturnWeight MF e (ons_dartRev L e) s
    have hz : ‖z‖ < 1 :=
      lt_of_le_of_lt (norm_tsum_le_tsum_norm hfirst.1) hfirst.2
    have hgeom := ons_loopBucketSeries_eq_geometric
      MF e (ons_dartRev L e) her hfirst.1 hfirst.2
    rw [show (∑' n : ℕ,
        ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n /
          ((n : ℂ) + 1)) =
        ∑' k : ℕ, z ^ (k + 1) / (k + 1) by
      simpa only [ons_maskWeightedPhaseBucketE, MF, not_exists, z] using hgeom]
    exact ons_lemma4_exp hz
  have hNroot :
      Complex.exp (-(∑' n : ℕ,
        ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n /
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
    simpa only [ons_loopWeight, ons_maskWeightedPhaseBucketN, MF] using hsum.symm
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
        ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n /
          ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n /
          ((n : ℂ) + 1))) / 2 =
      (-(∑' n : ℕ,
        ons_maskWeightedPhaseBucketN L weight omega a b forbidden e n /
          ((n : ℂ) + 1)) / 2) +
      (-(∑' n : ℕ,
        ons_maskWeightedPhaseBucketE L weight omega a b forbidden e n /
          ((n : ℂ) + 1))) by ring,
    Complex.exp_add, hNroot, hlam]

end StatMech.Onsager
