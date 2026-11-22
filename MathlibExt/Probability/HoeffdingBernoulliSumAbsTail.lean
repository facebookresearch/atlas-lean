/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

open scoped BigOperators MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]

namespace ProbabilityTheory

@[expose] public section

/-- **Two-sided Hoeffding inequality for Bernoulli sums.** Let $X_0, \dots, X_{n-1}$ be
independent real random variables on a probability space, each almost everywhere measurable,
almost surely equal to $0$ or $1$, and with expectation $p$, and let $\varepsilon > 0$. Then the
probability that $\lvert X_0 + \dots + X_{n-1} - np \rvert > \varepsilon n$ is at most
$2 e^{-2 \varepsilon^2 n}$.

Source: JIS concept `jis_grounded_4cd778f9d6394cee44270586`.

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL28/Jackson/jackson5.tex`
(Proposition, Hoeffding's Inequality, Thm. 2 of Hoe63).
Proves `Wanted` entry `hoeffding_bernoulli_sum_abs_tail`.
-/
theorem hoeffding_bernoulli_sum_abs_tail {n : ℕ} (X : Fin n → Ω → ℝ)
    (p ε : ℝ) (h_indep : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hBernoulli : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
    (hexp : ∀ i, ∫ x, X i x ∂μ = p) (hε : 0 < ε) :
    μ.real {ω | ε * (n : ℝ) < |(∑ i, X i ω) - (n : ℝ) * p|} ≤
      2 * Real.exp (-2 * ε ^ 2 * (n : ℝ)) := by
  -- Centered variables `Y i ω = X i ω - p`.
  set Y : Fin n → Ω → ℝ := fun i ω => X i ω - p with hYdef
  -- Each `X i` takes values in `Set.Icc 0 1`.
  have hIcc : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards [hBernoulli i] with ω hω
    rcases hω with h0 | h1
    · rw [h0]
      exact ⟨le_rfl, zero_le_one⟩
    · rw [h1]
      exact ⟨zero_le_one, le_rfl⟩
  -- Variance proxy `(‖1 - 0‖₊ / 2) ^ 2` equals `1 / 4`.
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    have h1 : ‖(1 : ℝ) - 0‖₊ = 1 := by simp
    rw [h1]
    norm_num
  -- Each centered variable is subgaussian with proxy `1 / 4` (Hoeffding's lemma).
  have hsub : ∀ i, HasSubgaussianMGF (Y i) (1 / 4 : NNReal) μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (hmeas i) (hIcc i)
    rw [hexp i, hc] at h
    exact h
  -- Independence is preserved by centering.
  have hYindep : iIndepFun Y μ :=
    h_indep.comp (fun _ x => x - p) (fun _ => measurable_id.sub_const p)
  -- The threshold `ε * n` is nonnegative.
  have hεn : (0 : ℝ) ≤ ε * n := mul_nonneg hε.le (Nat.cast_nonneg _)
  -- Sum of the proxies over `Finset.univ`.
  have hcsum : ↑(∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 / 4 : NNReal))
      = (n : ℝ) / 4 := by
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- The one-sided exponent simplifies to `-2 * ε ^ 2 * n`.
  have hexp_eq : -(ε * (n : ℝ)) ^ 2
        / (2 * ↑(∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 / 4 : NNReal)))
      = -2 * ε ^ 2 * (n : ℝ) := by
    rw [hcsum]
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · field_simp
      ring
  -- Upper tail.
  have hup : μ.real {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, Y i ω} ≤
      Real.exp (-2 * ε ^ 2 * (n : ℝ)) := by
    have h : μ.real {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, Y i ω} ≤
        Real.exp (-(ε * (n : ℝ)) ^ 2
          / (2 * ↑(∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 / 4 : NNReal)))) :=
      HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (X := Y)
        (c := fun _ => (1 / 4 : NNReal)) (s := Finset.univ) hYindep
        (fun i _ => hsub i) (ε := ε * (n : ℝ)) hεn
    rwa [hexp_eq] at h
  -- Lower tail, via the negated family.
  have hneg : ∀ i, HasSubgaussianMGF (-Y i) (1 / 4 : NNReal) μ :=
    fun i => (hsub i).neg
  have hZindep : iIndepFun (fun i => -Y i) μ :=
    hYindep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hlow : μ.real {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, (-Y i) ω} ≤
      Real.exp (-2 * ε ^ 2 * (n : ℝ)) := by
    have h : μ.real {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, (-Y i) ω} ≤
        Real.exp (-(ε * (n : ℝ)) ^ 2
          / (2 * ↑(∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 / 4 : NNReal)))) :=
      HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
        (X := fun i => -Y i) (c := fun _ => (1 / 4 : NNReal)) (s := Finset.univ)
        hZindep (fun i _ => hneg i) (ε := ε * (n : ℝ)) hεn
    rwa [hexp_eq] at h
  -- The centered sum equals the expression in the goal.
  have hsum : ∀ ω, ∑ i ∈ Finset.univ, Y i ω
      = (∑ i, X i ω) - (n : ℝ) * p := by
    intro ω
    simp only [hYdef]
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Negated sums, for the lower-tail covering argument.
  have hneg_sum : ∀ ω, ∑ i ∈ Finset.univ, (-Y i) ω
      = -(∑ i ∈ Finset.univ, Y i ω) := by
    intro ω
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
  -- The two-sided event is covered by the two one-sided events.
  have hsub_set : {ω | ε * (n : ℝ) < |(∑ i, X i ω) - (n : ℝ) * p|} ⊆
      {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, Y i ω} ∪
        {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, (-Y i) ω} := by
    intro ω hω
    have hω' : ε * (n : ℝ) < |(∑ i, X i ω) - (n : ℝ) * p| := hω
    rw [← hsum ω] at hω'
    by_cases ha : 0 ≤ ∑ i ∈ Finset.univ, Y i ω
    · left
      rw [abs_of_nonneg ha] at hω'
      exact le_of_lt hω'
    · right
      have ha' : ∑ i ∈ Finset.univ, Y i ω < 0 := lt_of_not_ge ha
      rw [abs_of_neg ha'] at hω'
      show ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, (-Y i) ω
      rw [hneg_sum ω]
      exact le_of_lt hω'
  have hfin : μ ({ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, Y i ω} ∪
      {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, (-Y i) ω}) ≠ ⊤ :=
    MeasureTheory.measure_ne_top μ _
  calc μ.real {ω | ε * (n : ℝ) < |(∑ i, X i ω) - (n : ℝ) * p|}
        ≤ μ.real ({ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, Y i ω} ∪
            {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, (-Y i) ω}) :=
          MeasureTheory.measureReal_mono hsub_set hfin
      _ ≤ μ.real {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, Y i ω} +
            μ.real {ω | ε * (n : ℝ) ≤ ∑ i ∈ Finset.univ, (-Y i) ω} :=
          MeasureTheory.measureReal_union_le _ _
      _ ≤ Real.exp (-2 * ε ^ 2 * (n : ℝ)) + Real.exp (-2 * ε ^ 2 * (n : ℝ)) :=
          add_le_add hup hlow
      _ = 2 * Real.exp (-2 * ε ^ 2 * (n : ℝ)) := by ring

end

end ProbabilityTheory
