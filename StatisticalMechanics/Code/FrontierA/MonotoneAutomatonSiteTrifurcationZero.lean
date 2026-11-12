/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.MonotoneAutomatonTrifurcation
import Code.FrontierA.MonotoneAutomatonSiteBond
import Code.Percolation.CanonBurtonKeane

open MeasureTheory

namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation
open Finset Filter Topology
open scoped ENNReal

variable {d : ℕ}

def SiteCanonicalTrifurcationEvent (x : Site d) :
    Set (ConfigSpace (Site d)) :=
  {eta | IsCanonicalTrifurcation d (siteToBond eta) x}

theorem measurableSet_siteCanonicalTrifurcationEvent (x : Site d) :
    MeasurableSet (SiteCanonicalTrifurcationEvent x) := by
  change MeasurableSet (siteToBond ⁻¹'
    {omega | IsCanonicalTrifurcation d omega x})
  exact measurable_siteToBond (ctp_measurableSet_isCanonicalTrifurcation x)

theorem siteCanonicalTrifurcation_shift (g : Multiplicative (Site d))
    (eta : ConfigSpace (Site d)) (x : Site d) :
    IsCanonicalTrifurcation d (siteToBond (shift g eta)) (g • x) ↔
      IsCanonicalTrifurcation d (siteToBond eta) x := by
  rw [siteToBond_shift, ctp_isCanonicalTrifurcation_shift]

theorem siteCanonicalTrifurcationProb_const
    (mu : Measure (ConfigSpace (Site d)))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (x : Site d) :
    mu (SiteCanonicalTrifurcationEvent x) =
      mu (SiteCanonicalTrifurcationEvent 0) := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hgx : g • (0 : Site d) = x := by
    show Multiplicative.toAdd g + (0 : Site d) = x
    simp [g]
  have hpre : (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹'
      SiteCanonicalTrifurcationEvent x =
        SiteCanonicalTrifurcationEvent 0 := by
    ext eta
    simp only [Set.mem_preimage, SiteCanonicalTrifurcationEvent, Set.mem_setOf_eq]
    rw [← hgx, siteCanonicalTrifurcation_shift]
  calc
    mu (SiteCanonicalTrifurcationEvent x) =
        mu ((shift g) ⁻¹' SiteCanonicalTrifurcationEvent x) :=
      (hinv.measure_preimage g
        (measurableSet_siteCanonicalTrifurcationEvent x)).symm
    _ = mu (SiteCanonicalTrifurcationEvent 0) := by rw [hpre]

noncomputable def siteCanonicalTrifurcationCount
    (eta : ConfigSpace (Site d)) (n : ℕ) : ℕ :=
  (canonicalTrifurcationsInBox (siteToBond eta) (n + 1)).card

theorem siteCanonicalTrifurcationCount_le_boundary
    (eta : ConfigSpace (Site d)) (n : ℕ) :
    siteCanonicalTrifurcationCount eta n ≤ boxSV_boundaryCard d (n + 1) := by
  unfold siteCanonicalTrifurcationCount boxSV_boundaryCard
  exact finite_canonical_trifurcation_count (siteToBond eta) (n + 1) (by omega)

lemma siteCanonicalTrifurcationCount_eq_sum_indicator
    (eta : ConfigSpace (Site d)) (n : ℕ) :
    (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) =
      ∑ x ∈ boxFinsetBK d n,
        (SiteCanonicalTrifurcationEvent x).indicator
          (fun _ ↦ (1 : ℝ≥0∞)) eta := by
  classical
  unfold siteCanonicalTrifurcationCount canonicalTrifurcationsInBox boxFinsetBK
  simp only [Nat.add_sub_cancel, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : IsCanonicalTrifurcation d (siteToBond eta) x
  · rw [if_pos h, Set.indicator_of_mem]
    exact h
  · rw [if_neg h, Set.indicator_of_notMem]
    exact h

theorem expected_siteCanonicalTrifurcationCount
    (mu : Measure (ConfigSpace (Site d)))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (n : ℕ) :
    ∫⁻ eta, (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) ∂mu =
      (boxFinsetBK d n).card • mu (SiteCanonicalTrifurcationEvent 0) := by
  classical
  have hmeas : ∀ x : Site d, Measurable (fun eta ↦
      (SiteCanonicalTrifurcationEvent x).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) eta) := fun x ↦
    Measurable.indicator measurable_const
      (measurableSet_siteCanonicalTrifurcationEvent x)
  calc
    ∫⁻ eta, (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) ∂mu =
        ∫⁻ eta, ∑ x ∈ boxFinsetBK d n,
          (SiteCanonicalTrifurcationEvent x).indicator
            (fun _ ↦ (1 : ℝ≥0∞)) eta ∂mu := by
      apply lintegral_congr
      intro eta
      exact siteCanonicalTrifurcationCount_eq_sum_indicator eta n
    _ = ∑ x ∈ boxFinsetBK d n, ∫⁻ eta,
          (SiteCanonicalTrifurcationEvent x).indicator
            (fun _ ↦ (1 : ℝ≥0∞)) eta ∂mu := by
      rw [lintegral_finsetSum]
      intro x hx
      exact hmeas x
    _ = ∑ x ∈ boxFinsetBK d n,
          mu (SiteCanonicalTrifurcationEvent x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [lintegral_indicator (measurableSet_siteCanonicalTrifurcationEvent x)]
      simp
    _ = ∑ _x ∈ boxFinsetBK d n,
          mu (SiteCanonicalTrifurcationEvent 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact siteCanonicalTrifurcationProb_const mu hinv x
    _ = (boxFinsetBK d n).card •
          mu (SiteCanonicalTrifurcationEvent 0) := by
      rw [Finset.sum_const]

theorem siteCanonicalTrifurcation_prob_eq_zero_of_one_le
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    mu (SiteCanonicalTrifurcationEvent 0) = 0 := by
  classical
  let p : ℝ≥0∞ := mu (SiteCanonicalTrifurcationEvent 0)
  have hkey : ∀ n,
      ((boxFinsetBK d n).card : ℝ≥0∞) * p ≤
        (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by
    intro n
    have hexp := expected_siteCanonicalTrifurcationCount mu hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ eta, (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) ∂mu ≤
        (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by
      calc
        ∫⁻ eta, (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) ∂mu ≤
            ∫⁻ _eta, (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) ∂mu := by
          apply lintegral_mono
          intro eta
          change (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) ≤
            (boxSV_boundaryCard d (n + 1) : ℝ≥0∞)
          exact_mod_cast siteCanonicalTrifurcationCount_le_boundary eta n
        _ = (boxSV_boundaryCard d (n + 1) : ℝ≥0∞) := by
          rw [lintegral_const]
          simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := measure_ne_top mu _
  let pr : ℝ := p.toReal
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ n,
      ((boxFinsetBK d n).card : ℝ) * pr ≤
        (boxSV_boundaryCard d (n + 1) : ℝ) := by
    intro n
    have h := hkey n
    have h' : (((boxFinsetBK d n).card : ℝ≥0∞) * p).toReal ≤
        (boxSV_boundaryCard d (n + 1) : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, pr] using h'
  have hvolr : ∀ n, (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := fun n ↦ by
    exact_mod_cast bkc_boxFinsetBK_card_pos d n
  have hle : ∀ n, pr ≤
      (boxSV_boundaryCard d (n + 1) : ℝ) /
        ((boxFinsetBK d n).card : ℝ) := by
    intro n
    rw [le_div_iff₀ (hvolr n)]
    linarith [hkeyr n]
  have hpr0 : pr ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds
      (cbk_boundary_succ_vol_tendsto d hd) hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := hpreq
  have hpzero : p = 0 :=
    (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  exact hpzero

theorem siteCanonicalTrifurcation_prob_eq_zero
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
    mu {eta | IsCanonicalTrifurcation d (siteToBond eta) 0} = 0 := by
  by_cases hd : 1 ≤ d
  · exact siteCanonicalTrifurcation_prob_eq_zero_of_one_le mu hd hinv
  · have hd0 : d = 0 := by omega
    subst d
    have hempty : {eta : ConfigSpace (Site 0) |
        IsCanonicalTrifurcation 0 (siteToBond eta) 0} = ∅ := by
      ext eta
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a1, a2, a3, hne, hadj, hinf, hsep⟩
      exact hne.1 (Subsingleton.elim a1 a2)
    rw [hempty, measure_empty]

end StatMech.FrontierA

