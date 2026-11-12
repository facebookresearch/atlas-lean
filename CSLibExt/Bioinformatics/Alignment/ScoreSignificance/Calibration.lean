/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.GumbelTail

/-!
# Calibration of the Karlin–Altschul p-value in the null model

Karlin and Altschul (1990) assess a maximal segment score `s` of a sequence of length `n` by the
Gumbel tail approximation `P(Mₙ ≥ s) ≈ 1 - exp (-K n e^{-λ s})`. This file proves that the
resulting p-value is calibrated in the null model, in the sense that the Gumbel limit of
`GumbelTail` supports, and in no stronger sense.

## Setting

* **Null model.** The scores `X 0, X 1, …` are i.i.d. with negative mean and Cramér root
  `θ > 0` (`E e^{θ X} = 1`), packaged with the renewal input of `GumbelTail`:
  `NonlatticeRenewalInput P X` (nonlattice scores) or `LatticeRenewalInput P X` (scores on a
  lattice `hℤ`). The ladder decomposition and the renewal tail `P(Y > t) ~ C e^{-θ t}` are
  hypotheses there, not derived from the scores; the same holds here. `K = C / A` is the
  constant of those structures, and the results need `C > 0` (equivalently `K > 0`).
* **Score statistic.** The maximal segment score `Mₙ = maxSegmentScoreRV X n` of the first `n`
  scores (empty segment allowed).
* **p-value.** `gumbelPValue K θ n s = 1 - exp (-K n e^{-θ s})`, evaluated at `s = Mₙ`; this is
  the Karlin–Altschul formula with `λ = θ`.

## Main results

* `gumbelPValue_le_iff`: `gumbelPValue K θ n s ≤ α ↔ log n / θ + gumbelLevel K θ α ≤ s` for
  `0 < α < 1`, where `exp (-K e^{-θ x_α}) = 1 - α` at `x_α = gumbelLevel K θ α`
  (`exp_neg_mul_exp_gumbelLevel`).
* `eventually_real_gumbelPValue_le_le`, `tendsto_real_gumbelPValue_le`: the calibration
  statements for any statistic satisfying the Gumbel lower bound (resp. Gumbel limit).
* `NonlatticeRenewalInput.tendsto_real_gumbelPValue_le`: **exact asymptotic calibration**,
  `P(pₙ ≤ α) → α` for every `α ∈ [0, 1]`.
* `NonlatticeRenewalInput.eventually_real_gumbelPValue_le_le`,
  `LatticeRenewalInput.eventually_real_gumbelPValue_le_le`: **asymptotic validity**, for every
  `α ∈ [0, 1]` and `ε > 0`, eventually `P(pₙ ≤ α) ≤ α + ε`, i.e. `limsup P(pₙ ≤ α) ≤ α`. In the
  lattice case this is all that holds in general: `P(Mₙ ≤ log n / θ + x)` has no limit
  (`LatticeRenewalInput.not_tendsto`), and the p-value built from the lower Gumbel bound is
  conservative.

## Scope

* The validity is **asymptotic** (`n → ∞`). Finite-`n` validity in the sense of
  `IsValidPValue` (`μ {p ≤ t} ≤ t` for each `n`) is **false** in general, not merely unproved.
  Example: let `Mₙ` be the maximum of `n + 1` i.i.d. `Exp(1)` variables (`θ = K = 1`, the model
  in the test file). Then `p₁ ≤ 1 / 2 ↔ M₁ ≥ log (1 / log 2)`, so
  `P(p₁ ≤ 1 / 2) = 1 - (1 - log 2)² ≈ 0.906 > 1 / 2`.
* This is single-sequence significance. The BLAST E-value `K m n e^{-λ S}` for two-sequence
  local alignment is not covered (see the scope note in `GumbelTail`).
* The constant `K` is the one of the renewal input; its renewal-theoretic formula is not
  formalized.

## Reuse search

Pinned Mathlib v4.35.0, CSLib and the Atlas libraries (searched 2026-11-12): the Gumbel limit
theorems and `maxSegmentScoreRV` are in `GumbelTail` and reused here; there is no existing
Karlin–Altschul p-value or asymptotic p-value calibration statement. `IsValidPValue`
(`MathlibExt.Probability.Statistics.MultipleTesting.Basic`) is the finite-sample notion and is
not what is proved here.

## References

* S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of molecular
  sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268, eq. (1)–(2).
* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140, Theorem 1.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance

open MeasureTheory ProbabilityTheory Filter Topology

/-- The **Karlin–Altschul p-value** `1 - exp (-K n e^{-θ s})` of a maximal segment score `s` of a
sequence of length `n`: the Gumbel approximation of `P(Mₙ ≥ s)` with constant `K` and Cramér root
`θ` (the `λ` of Karlin–Altschul). -/
noncomputable def gumbelPValue (K θ : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  1 - Real.exp (-(K * n * Real.exp (-(θ * s))))

/-- The **Gumbel level** `x_α = log (K / (-log (1 - α))) / θ`: the centered threshold at which the
Gumbel distribution function `exp (-K e^{-θ x})` equals `1 - α`. The p-value `gumbelPValue K θ n s`
is at most `α` exactly when `s ≥ log n / θ + x_α`. -/
noncomputable def gumbelLevel (K θ α : ℝ) : ℝ :=
  Real.log (K / -Real.log (1 - α)) / θ

variable {K θ α : ℝ} {n : ℕ}

/-- The p-value is positive once `K > 0` and `n ≥ 1`. -/
theorem gumbelPValue_pos (hK : 0 < K) (hn : 0 < n) (s : ℝ) : 0 < gumbelPValue K θ n s := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h : 0 < K * n * Real.exp (-(θ * s)) := by positivity
  have := Real.exp_lt_one_iff.2 (neg_lt_zero.2 h)
  unfold gumbelPValue; linarith

/-- The p-value is at most `1`. -/
theorem gumbelPValue_le_one (s : ℝ) : gumbelPValue K θ n s ≤ 1 := by
  unfold gumbelPValue; linarith [Real.exp_pos (-(K * n * Real.exp (-(θ * s))))]

/-- **Rejection region.** For `0 < α < 1`, the p-value is at most `α` exactly when the score
exceeds the Gumbel threshold `log n / θ + x_α`. -/
theorem gumbelPValue_le_iff (hK : 0 < K) (hθ : 0 < θ) (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    (s : ℝ) : gumbelPValue K θ n s ≤ α ↔ Real.log n / θ + gumbelLevel K θ α ≤ s := by
  have hL : 0 < -Real.log (1 - α) := neg_pos.2 (Real.log_neg (by linarith) (by linarith))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hKn : 0 < K * n := mul_pos hK hn'
  unfold gumbelPValue gumbelLevel
  rw [Real.log_div hK.ne' hL.ne', ← add_div, div_le_iff₀ hθ]
  calc 1 - Real.exp (-(K * n * Real.exp (-(θ * s)))) ≤ α
      ↔ Real.log (1 - α) ≤ -(K * n * Real.exp (-(θ * s))) := by
        rw [Real.log_le_iff_le_exp (by linarith)]; constructor <;> intro h <;> linarith
    _ ↔ Real.exp (-(θ * s)) ≤ -Real.log (1 - α) / (K * n) := by
        rw [le_div_iff₀ hKn]; constructor <;> intro h <;> linarith
    _ ↔ -(θ * s) ≤ Real.log (-Real.log (1 - α) / (K * n)) :=
        (Real.le_log_iff_exp_le (div_pos hL hKn)).symm
    _ ↔ Real.log n + (Real.log K - Real.log (-Real.log (1 - α))) ≤ s * θ := by
        rw [Real.log_div hL.ne' hKn.ne', Real.log_mul hK.ne' hn'.ne']
        constructor <;> intro h <;> linarith

/-- At the Gumbel level, the Gumbel distribution function equals `1 - α`:
`exp (-K e^{-θ x_α}) = 1 - α`. -/
theorem exp_neg_mul_exp_gumbelLevel (hK : 0 < K) (hθ : 0 < θ) (hα0 : 0 < α) (hα1 : α < 1) :
    Real.exp (-(K * Real.exp (-(θ * gumbelLevel K θ α)))) = 1 - α := by
  have hL : 0 < -Real.log (1 - α) := neg_pos.2 (Real.log_neg (by linarith) (by linarith))
  unfold gumbelLevel
  rw [mul_div_cancel₀ _ hθ.ne', Real.exp_neg (Real.log _), Real.exp_log (div_pos hK hL),
    show K * (K / -Real.log (1 - α))⁻¹ = -Real.log (1 - α) by field_simp, neg_neg,
    Real.exp_log (by linarith)]

/-- The maximal segment score of measurable scores is measurable. -/
theorem measurable_maxSegmentScoreRV {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (n : ℕ) : Measurable (maxSegmentScoreRV X n) := by
  convert Finset.measurable_sup' (⟨(0, 0), by simp⟩ :
      (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).Nonempty)
    (f := fun p ω => segmentScore (fun k => X k ω) p.1 p.2)
    (fun p _ => Finset.measurable_sum _ fun k _ => hX k) using 1
  ext ω
  simp only [maxSegmentScoreRV, maxSegmentScore]
  refine le_antisymm (Finset.sup'_le _ _ fun p hp => Finset.le_sup'
    (fun p ω => segmentScore (fun k => X k ω) p.1 p.2) hp ω) ?_
  exact Finset.sup'_le _ _ (a := fun ω' => (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).sup'
    ⟨(0, 0), by simp⟩ fun p => segmentScore (fun k => X k ω') p.1 p.2)
    (fun p hp ω' => Finset.le_sup' (fun p => segmentScore (fun k => X k ω') p.1 p.2) hp) ω

section Calibration

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : ℕ → Ω → ℝ}

/-- **Asymptotic validity from the Gumbel lower bound.** If a measurable statistic `Mₙ`
satisfies `liminf P(Mₙ ≤ log n / θ + x) ≥ exp (-K e^{-θ x})` for every `x`, then for every level
`α ∈ [0, 1]`, `limsup P(gumbelPValue K θ n Mₙ ≤ α) ≤ α`. -/
theorem eventually_real_gumbelPValue_le_le (hM : ∀ n, Measurable (M n)) (hK : 0 < K)
    (hθ : 0 < θ)
    (hlow : ∀ x : ℝ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      Real.exp (-(K * Real.exp (-(θ * x)))) - ε ≤ P.real {ω | M n ω ≤ Real.log n / θ + x})
    (hα : α ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, P.real {ω | gumbelPValue K θ n (M n ω) ≤ α} ≤ α + ε := by
  obtain ⟨h0, h1⟩ := hα
  rcases h0.eq_or_lt with rfl | h0
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hset : {ω | gumbelPValue K θ n (M n ω) ≤ 0} = ∅ := by
      ext ω; simpa using gumbelPValue_pos hK hn (M n ω)
    rw [hset, measureReal_empty]; linarith
  rcases h1.eq_or_lt with rfl | h1
  · exact Eventually.of_forall fun n => measureReal_le_one.trans (by linarith)
  set x := gumbelLevel K θ α
  set G : ℝ → ℝ := fun y => Real.exp (-(K * Real.exp (-(θ * y)))) with hG_def
  have hGx : G x = 1 - α := exp_neg_mul_exp_gumbelLevel hK hθ h0 h1
  have hlim : Tendsto (fun δ => G (x - δ)) (𝓝[>] 0) (𝓝 (1 - α)) := by
    have hc : Continuous fun δ => G (x - δ) := by rw [hG_def]; fun_prop
    simpa [hGx] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hδpos⟩ := ((hlim.eventually (lt_mem_nhds
    (by linarith : 1 - α - ε / 2 < 1 - α))).and eventually_mem_nhdsWithin).exists
  filter_upwards [hlow (x - δ) (ε / 2) hε2, eventually_ge_atTop 1] with n hn hn1
  have hsub : {ω | gumbelPValue K θ n (M n ω) ≤ α} ⊆
      {ω | M n ω ≤ Real.log n / θ + (x - δ)}ᶜ := by
    intro ω hω hle
    rw [Set.mem_ofPred_eq, gumbelPValue_le_iff hK hθ hn1 h0 h1] at hω
    have hδ' : (0 : ℝ) < δ := hδpos
    simp only [Set.mem_ofPred_eq] at hle
    linarith
  have hmeas : MeasurableSet {ω | M n ω ≤ Real.log n / θ + (x - δ)} :=
    measurableSet_le (hM n) measurable_const
  calc P.real {ω | gumbelPValue K θ n (M n ω) ≤ α}
      ≤ P.real {ω | M n ω ≤ Real.log n / θ + (x - δ)}ᶜ := measureReal_mono hsub
    _ = 1 - P.real {ω | M n ω ≤ Real.log n / θ + (x - δ)} := by
        rw [measureReal_compl hmeas, probReal_univ]
    _ ≤ α + ε := by simp only [hG_def] at hδ; linarith

/-- **Exact asymptotic calibration from the Gumbel limit.** If a measurable statistic `Mₙ`
satisfies `P(Mₙ ≤ log n / θ + x) → exp (-K e^{-θ x})` for every `x`, then for every level
`α ∈ [0, 1]`, `P(gumbelPValue K θ n Mₙ ≤ α) → α`. -/
theorem tendsto_real_gumbelPValue_le (hM : ∀ n, Measurable (M n)) (hK : 0 < K) (hθ : 0 < θ)
    (hlim : ∀ x : ℝ, Tendsto (fun n : ℕ => P.real {ω | M n ω ≤ Real.log n / θ + x}) atTop
      (𝓝 (Real.exp (-(K * Real.exp (-(θ * x)))))))
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => P.real {ω | gumbelPValue K θ n (M n ω) ≤ α}) atTop (𝓝 α) := by
  have hlow : ∀ x : ℝ, ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      Real.exp (-(K * Real.exp (-(θ * x)))) - ε ≤ P.real {ω | M n ω ≤ Real.log n / θ + x} :=
    fun x ε hε => ((hlim x).eventually (lt_mem_nhds (sub_lt_self _ hε))).mono fun _ h => h.le
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨h0, h1⟩ := hα
    rcases h1.eq_or_lt with rfl | h1
    · refine Eventually.of_forall fun n => ?_
      have hset : {ω | gumbelPValue K θ n (M n ω) ≤ 1} = Set.univ := by
        ext ω; simpa using gumbelPValue_le_one (K := K) (θ := θ) (n := n) (M n ω)
      rw [hset, probReal_univ]; exact ha
    rcases h0.eq_or_lt with rfl | h0
    · exact Eventually.of_forall fun n => lt_of_lt_of_le ha measureReal_nonneg
    have hGx := exp_neg_mul_exp_gumbelLevel hK hθ h0 h1
    have hε : 0 < (α - a) / 2 := by linarith
    filter_upwards [(hlim (gumbelLevel K θ α)).eventually
      (gt_mem_nhds (lt_add_of_pos_right _ hε)), eventually_ge_atTop 1] with n hn hn1
    rw [hGx] at hn
    have hsub : {ω | M n ω ≤ Real.log n / θ + gumbelLevel K θ α}ᶜ ⊆
        {ω | gumbelPValue K θ n (M n ω) ≤ α} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
      rw [Set.mem_ofPred_eq, gumbelPValue_le_iff hK hθ hn1 h0 h1]
      exact hω.le
    have hmeas : MeasurableSet {ω | M n ω ≤ Real.log n / θ + gumbelLevel K θ α} :=
      measurableSet_le (hM n) measurable_const
    have := measureReal_mono (μ := P) hsub
    rw [measureReal_compl hmeas, probReal_univ] at this
    linarith
  · filter_upwards [eventually_real_gumbelPValue_le_le hM hK hθ hlow hα
      (half_pos (sub_pos.2 ha))] with n hn
    linarith

end Calibration

/-! ### The null model: maximal segment scores of i.i.d. Cramér scores -/

section NullModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- **Exact asymptotic calibration, nonlattice scores** (Karlin–Altschul 1990 with the
Iglehart / Karlin–Dembo limit). In the null model of i.i.d. nonlattice Cramér scores with renewal
input `R` and `C > 0`, the Karlin–Altschul p-value `pₙ = 1 - exp (-K n e^{-θ Mₙ})` of the maximal
segment score satisfies `P(pₙ ≤ α) → α` for every `α ∈ [0, 1]`. -/
theorem NonlatticeRenewalInput.tendsto_real_gumbelPValue_le (R : NonlatticeRenewalInput P X)
    (hC : 0 < R.C) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ =>
        P.real {ω | gumbelPValue R.K R.θ n (maxSegmentScoreRV X n ω) ≤ α}) atTop (𝓝 α) :=
  ScoreSignificance.tendsto_real_gumbelPValue_le (measurable_maxSegmentScoreRV R.cramer.measurable)
    (div_pos hC R.ladder.A_pos) R.cramer.pos R.tendsto_gumbel hα

/-- **Asymptotic validity, nonlattice scores.** In the nonlattice null model with `C > 0`, for
every `α ∈ [0, 1]` and `ε > 0`, eventually `P(pₙ ≤ α) ≤ α + ε`. -/
theorem NonlatticeRenewalInput.eventually_real_gumbelPValue_le_le
    (R : NonlatticeRenewalInput P X) (hC : 0 < R.C) (hα : α ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      P.real {ω | gumbelPValue R.K R.θ n (maxSegmentScoreRV X n ω) ≤ α} ≤ α + ε :=
  ((R.tendsto_real_gumbelPValue_le hC hα).eventually
    (gt_mem_nhds (lt_add_of_pos_right α hε))).mono fun _ h => h.le

/-- **Asymptotic validity, lattice scores.** In the null model of i.i.d. lattice Cramér scores
with renewal input `R` and `C > 0`, the Karlin–Altschul p-value `pₙ = 1 - exp (-K n e^{-θ Mₙ})`
(built from the lower lattice bound) is asymptotically conservative: for every `α ∈ [0, 1]` and
`ε > 0`, eventually `P(pₙ ≤ α) ≤ α + ε`. Exact calibration is not claimed: the underlying
probabilities have no limit (`LatticeRenewalInput.not_tendsto`). -/
theorem LatticeRenewalInput.eventually_real_gumbelPValue_le_le (R : LatticeRenewalInput P X)
    (hC : 0 < R.C) (hα : α ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      P.real {ω | gumbelPValue R.K R.θ n (maxSegmentScoreRV X n ω) ≤ α} ≤ α + ε :=
  ScoreSignificance.eventually_real_gumbelPValue_le_le
    (measurable_maxSegmentScoreRV R.cramer.measurable) (div_pos hC R.ladder.A_pos) R.cramer.pos
    (fun x _ hδ => (R.eventually_bounds x hδ).mono fun _ h => h.1) hα hε

end NullModel

end Cslib.Bioinformatics.Alignment.ScoreSignificance
