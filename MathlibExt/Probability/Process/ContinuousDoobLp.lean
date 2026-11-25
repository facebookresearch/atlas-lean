/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Data.Finset.Sort

/-!
# Doob's maximal inequality in continuous time

For a nonnegative submartingale with continuous paths and any real exponent `p > 1`,
`Submartingale.lintegral_iSup_rpow_le` bounds the moment of its running maximum by
`(p / (p - 1)) ^ p` times the terminal moment.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MathlibExt.Probability.ContinuousDoobWanted.Submartingale

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- Apply the discrete weak maximal inequality on a finite set of observation times. -/
private lemma finite_tail [IsFiniteMeasure μ] {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}
    (hX : Submartingale X ℱ μ) (h0 : ∀ s ω, 0 ≤ X s ω) {t : ℝ≥0}
    (s : Finset ℝ≥0) (ht : t ∈ s) (hs : ∀ u ∈ s, u ≤ t) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * μ {ω | a ≤ s.sup' ⟨t, ht⟩ X ω} ≤
      μ.withDensity (fun ω ↦ ENNReal.ofReal (X t ω)) {ω | a ≤ s.sup' ⟨t, ht⟩ X ω} := by
  classical
  let e := s.orderEmbOfFin rfl
  let τ : ℕ → ℝ≥0 := fun k ↦ if hk : k < s.card then e ⟨k, hk⟩ else t
  have hτ : Monotone τ := by
    intro i j hij
    dsimp [τ]
    split_ifs with hi hj hj
    · exact e.monotone hij
    · exact hs _ (s.orderEmbOfFin_mem rfl _)
    · omega
    · rfl
  let Fs : Filtration ℕ m :=
    ⟨fun k ↦ ℱ (τ k), fun _ _ h ↦ ℱ.mono (hτ h), fun k ↦ ℱ.le (τ k)⟩
  have hdisc : Submartingale (fun k ↦ X (τ k)) Fs μ :=
    ⟨fun k ↦ hX.stronglyMeasurable _, fun _ _ hij ↦ hX.ae_le_condExp (hτ hij),
      fun k ↦ hX.integrable _⟩
  have hmax (ω : Ω) : (Finset.range (s.card + 1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ X (τ k) ω) = s.sup' ⟨t, ht⟩ X ω := by
    rw [Finset.sup'_apply (⟨t, ht⟩ : s.Nonempty) X ω]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun k _ ↦ Finset.le_sup' (fun u ↦ X u ω) ?_
      dsimp [τ]
      split_ifs
      · exact s.orderEmbOfFin_mem rfl _
      · exact ht
    · refine Finset.sup'_le _ _ fun u hu ↦ ?_
      let k := (s.orderIsoOfFin rfl).symm ⟨u, hu⟩
      have hku : τ k = u := by
        simp [τ, k.isLt, e, ← Finset.coe_orderIsoOfFin_apply, k]
      rw [← hku]
      exact Finset.le_sup' (fun j ↦ X (τ j) ω)
        (Finset.mem_range.mpr (Nat.lt_succ_of_lt k.isLt))
  let ε : ℝ≥0 := ⟨a, ha.le⟩
  have hw := maximal_ineq hdisc (fun k ω ↦ h0 _ _) (ε := ε) s.card
  simp only [hmax, τ, lt_irrefl, dite_false] at hw
  have hmeas := Finset.measurable_sup' (f := X) ⟨t, ht⟩
    (fun u _ ↦ ((hX.stronglyMeasurable u).mono (ℱ.le u)).measurable)
  rw [withDensity_apply _ (measurableSet_le measurable_const hmeas),
    ← ofReal_integral_eq_lintegral_ofReal (hX.integrable t).integrableOn
      (Filter.Eventually.of_forall (h0 t))]
  rw [← ENNReal.ofReal_coe_nnreal (p := ε)] at hw
  exact hw

/-- Integrate the tail bound against the powers for `p` and `p - 1`, using the
terminal value as the density of the measure in the second layer-cake formula. -/
private lemma moment_le_mixed {M : Ω → ℝ} {Y : Ω → ℝ≥0∞}
    (hM : Measurable M) (h0 : ∀ ω, 0 ≤ M ω) (hY : Measurable Y) {p : ℝ} (hp : 1 < p)
    (htail : ∀ a : ℝ, 0 < a → ENNReal.ofReal a * μ {ω | a ≤ M ω} ≤
      μ.withDensity Y {ω | a ≤ M ω}) :
    ∫⁻ ω, ENNReal.ofReal (M ω) ^ p ∂μ ≤ ENNReal.ofReal (p / (p - 1)) *
      ∫⁻ ω, Y ω * ENNReal.ofReal (M ω) ^ (p - 1) ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp1 := sub_pos.mpr hp
  let ν := μ.withDensity Y
  have layer (ρ : Measure Ω) (r : ℝ) (hr : 0 < r) :
      ∫⁻ ω, ENNReal.ofReal (M ω) ^ r ∂ρ = ENNReal.ofReal r *
        ∫⁻ a in Ioi 0, ρ {ω | a ≤ M ω} * ENNReal.ofReal (a ^ (r - 1)) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (h0 _) hr.le]
    exact lintegral_rpow_eq_lintegral_meas_le_mul ρ (Filter.Eventually.of_forall h0)
      hM.aemeasurable hr
  have hstep (a : ℝ) (ha : 0 < a) :
      μ {ω | a ≤ M ω} * ENNReal.ofReal (a ^ (p - 1)) ≤
        ν {ω | a ≤ M ω} * ENNReal.ofReal (a ^ (p - 1 - 1)) := by
    have heq : a ^ (p - 1) = a * a ^ (p - 1 - 1) := by
      nth_rw 1 [← sub_add_cancel (p - 1) 1, Real.rpow_add ha, Real.rpow_one, mul_comm]
    rw [heq, ENNReal.ofReal_mul ha.le, ← mul_assoc, mul_comm (μ _)]
    exact mul_le_mul_left (htail a ha) _
  have hcoeff : ENNReal.ofReal p =
      ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hp0.le hp1.le), div_mul_cancel₀ _ hp1.ne']
  rw [layer μ p hp0]
  calc
    _ ≤ ENNReal.ofReal p *
        ∫⁻ a in Ioi 0, ν {ω | a ≤ M ω} * ENNReal.ofReal (a ^ (p - 1 - 1)) :=
      mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hstep) _
    _ = _ := by
      rw [hcoeff, mul_assoc, ← layer ν (p - 1) hp1,
        lintegral_withDensity_eq_lintegral_mul μ hY (hM.ennreal_ofReal.pow_const _)]
      rfl

/-- For a bounded maximum the moment is finite, so the factor from Hölder can be cancelled. -/
private lemma bounded_moment_le [IsFiniteMeasure μ] {M : Ω → ℝ} {Y : Ω → ℝ≥0∞}
    (hM : Measurable M) (h0 : ∀ ω, 0 ≤ M ω) {K : ℝ} (hK : ∀ ω, M ω ≤ K)
    (hY : Measurable Y) {p : ℝ} (hp : 1 < p)
    (htail : ∀ a : ℝ, 0 < a → ENNReal.ofReal a * μ {ω | a ≤ M ω} ≤
      μ.withDensity Y {ω | a ≤ M ω}) :
    ∫⁻ ω, ENNReal.ofReal (M ω) ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, Y ω ^ p ∂μ := by
  let q := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  let S := ∫⁻ ω, ENNReal.ofReal (M ω) ^ p ∂μ
  let T := ∫⁻ ω, Y ω ^ p ∂μ
  change S ≤ ENNReal.ofReal (q ^ p) * T
  rcases eq_or_ne S 0 with hS | hS
  · simp [hS]
  have hfin : S ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (μ := μ) (fun ω ↦
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hK ω)) hpq.nonneg))
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpq.nonneg ENNReal.ofReal_ne_top)
      (measure_ne_top _ _)
  have hpow (ω : Ω) : (ENNReal.ofReal (M ω) ^ (p - 1)) ^ q = ENNReal.ofReal (M ω) ^ p := by
    rw [← ENNReal.rpow_mul]
    congr 1
    dsimp [q]
    field_simp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hY.aemeasurable
    (hM.ennreal_ofReal.pow_const (p - 1)).aemeasurable
  simp only [Pi.mul_apply, hpow] at hh
  have hmain : S ≤ ENNReal.ofReal q * (T ^ (1 / p) * S ^ (1 / q)) :=
    (moment_le_mixed hM h0 hY hp htail).trans (mul_le_mul_right hh _)
  have hroot : S ^ (1 / p) ≤ ENNReal.ofReal q * T ^ (1 / p) := by
    have hq : 0 < 1 / q := one_div_pos.mpr hpq.symm.pos
    apply (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 hS) hfin).ne'
      (ENNReal.rpow_ne_top_of_nonneg hq.le hfin)).mp
    rw [← ENNReal.rpow_add _ _ hS hfin, one_div, one_div, hpq.inv_add_inv_eq_one,
      ENNReal.rpow_one, mul_assoc]
    simpa only [one_div] using hmain
  have h := ENNReal.rpow_le_rpow hroot hpq.nonneg
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hpq.pos.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul,
    one_div_mul_cancel hpq.pos.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hpq.symm.nonneg hpq.nonneg] at h

end MathlibExt.Probability.ContinuousDoobWanted.Submartingale

namespace MathlibExt.Probability.ContinuousDoobWanted

/-- **Doob's `L^p` maximal inequality in continuous time.** Let `X` be a nonnegative
submartingale indexed by `ℝ≥0` with continuous paths, and `p > 1`. For every `t ≥ 0`,
`E[(sup_{0 ≤ s ≤ t} X s)^p] ≤ (p / (p - 1))^p E[X_t^p]` (Le Gall, *Brownian Motion, Martingales,
and Stochastic Calculus*, Chapter 3, section "Continuous time martingales and supermartingales";
the discrete-time inequality is Proposition 12.4.3 of his ENS notes). The integrals are lower
Lebesgue integrals, so the statement needs no integrability assumption on `X_t^p`. -/
public theorem Submartingale.lintegral_iSup_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → ℝ} (hX : Submartingale X ℱ μ) (hnonneg : ∀ t ω, 0 ≤ X t ω)
    (hcont : ∀ ω, Continuous fun t ↦ X t ω) {p : ℝ} (hp : 1 < p) (t : ℝ≥0) :
    ∫⁻ ω, (⨆ s : Set.Icc (0 : ℝ≥0) t, ENNReal.ofReal (X s ω)) ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ENNReal.ofReal (X t ω) ^ p ∂μ := by
  classical
  have hp0 : 0 < p := by linarith
  have hm (u : ℝ≥0) := ((hX.stronglyMeasurable u).mono (ℱ.le u)).measurable
  let I := Set.Icc (0 : ℝ≥0) t
  have : Nonempty I := ⟨⟨t, zero_le, le_rfl⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq I
  -- Include the terminal time on every grid. Cap the maximum at n so that its moment is finite.
  let grid (n : ℕ) := insert t ((Finset.range n).image fun k ↦ (d k : ℝ≥0))
  have ht (n : ℕ) : t ∈ grid n := Finset.mem_insert_self _ _
  have hne (n : ℕ) : (grid n).Nonempty := ⟨t, ht n⟩
  let M (n : ℕ) := (grid n).sup' (hne n) X
  let B (n : ℕ) (ω : Ω) := min (M n ω) (n : ℝ)
  have hmB (n : ℕ) : Measurable (B n) :=
    (Finset.measurable_sup' (hne n) (fun u _ ↦ hm u)).min measurable_const
  have hmono : Monotone B := by
    intro i j hij ω
    have hg : grid i ⊆ grid j :=
      Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.range_mono hij))
    exact min_le_min (Finset.sup'_mono X hg (hne i) ω) (Nat.cast_le.mpr hij)
  have hbound (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (B n ω) ^ p ∂μ ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ENNReal.ofReal (X t ω) ^ p ∂μ := by
    apply Submartingale.bounded_moment_le (hmB n) (fun ω ↦ le_min
      ((hnonneg t ω).trans (Finset.le_sup' X (ht n) ω)) (Nat.cast_nonneg n))
      (fun ω ↦ min_le_right _ (n : ℝ)) (hm t).ennreal_ofReal hp
    intro a ha
    by_cases han : a ≤ n
    · simp only [B, le_min_iff, han, and_true]
      apply Submartingale.finite_tail hX hnonneg (grid n) (ht n) _ ha
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rfl
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
        exact (d k).property.2
    · simp [B, le_min_iff, han]
  -- Every dense sample is below a capped maximum once both its index and its value fit.
  have hsup (ω : Ω) : (⨆ s : I, ENNReal.ofReal (X s ω)) ≤
      ⨆ n, ENNReal.ofReal (B n ω) := by
    refine iSup_le fun s ↦ hd.induction_on s
      (isClosed_le (ENNReal.continuous_ofReal.comp ((hcont ω).comp continuous_subtype_val))
        continuous_const) ?_
    intro k
    obtain ⟨j, hj⟩ := exists_nat_ge (X (d k) ω)
    let n := max (k + 1) j
    have hk : (d k : ℝ≥0) ∈ grid n := Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (lt_of_lt_of_le k.lt_succ_self
        (le_max_left _ _)), rfl⟩)
    exact le_iSup_of_le n (ENNReal.ofReal_le_ofReal (le_min (Finset.le_sup' X hk ω)
      (hj.trans (Nat.cast_le.mpr (le_max_right _ _)))))
  calc
    _ ≤ ∫⁻ ω, (⨆ n, ENNReal.ofReal (B n ω)) ^ p ∂μ :=
      lintegral_mono fun ω ↦ ENNReal.rpow_le_rpow (hsup ω) hp0.le
    _ = ⨆ n, ∫⁻ ω, ENNReal.ofReal (B n ω) ^ p ∂μ := by
      simp_rw [ENNReal.iSup_rpow_of_pos hp0]
      exact lintegral_iSup (fun n ↦ (hmB n).ennreal_ofReal.pow_const p)
        (fun i j hij ω ↦ ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hmono hij ω)) hp0.le)
    _ ≤ _ := iSup_le hbound

end MathlibExt.Probability.ContinuousDoobWanted
