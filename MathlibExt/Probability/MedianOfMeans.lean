/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.HoeffdingBounded

/-!
# Median amplification of independent estimates

The "median trick" of Alon, Matias and Szegedy: if each of `s` independent estimates lands in a
target interval with probability at least `7 / 8`, then their median misses the interval only
if at least half of the estimates do, which by Hoeffding's inequality has probability at most
`exp (-9 s / 32)`. So `O(log (1 / ε))` independent repetitions push the failure probability of a
constant-probability estimator below `ε` (N. Alon, Y. Matias and M. Szegedy, "The space
complexity of approximating the frequency moments", J. Comput. System Sci. 58 (1999) 137–147,
proofs of Theorems 2.1 and 2.2, which output the median of `s₂ = 2 log (1 / ε)` means and invoke
"the standard estimate of Chernoff"; we use Hoeffding's inequality instead, hence the constant
`9 / 32`).

## Main results

- `sampleMedian`: a median of finitely many reals.
- `sampleMedian_mem_Icc`: the median lies in any closed interval that contains more than half
  of the values.
- `measureReal_two_mul_card_bad_ge_le`: at least half of `s` independent estimates, each bad with
  probability at most `1 / 8`, are bad with probability at most `exp (-9 s / 32)`.
- `measureReal_sampleMedian_notMem_Icc_le`: the median of `s` such estimates misses the interval
  with probability at most `exp (-9 s / 32)`.

## Relation to `MathlibExt.Probability.MedianTrick`

That module proves the same amplification, also with Hoeffding's inequality, as
`ProbabilityTheory.median_trick`, for an odd number `r` of estimates each within `ε` of `μ` with
probability at least `3 / 4` (failure bound `exp (-r / 8)`). This module allows any number of
estimates and any interval, each estimate being bad with probability at most `1 / 8`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real

namespace MathlibExt.Probability.MedianOfMeans

/-- **Sample median.** For `y : Fin s → ℝ`, the least value `y j` such that more than half of the
values are at most `y j`. For odd `s` this is the usual median; for even `s` it is the upper of
the two middle values; for `s = 0` it is `0` by the convention `sInf ∅ = 0`. -/
noncomputable def sampleMedian {s : ℕ} (y : Fin s → ℝ) : ℝ :=
  sInf {t | t ∈ Set.range y ∧ s < 2 * (univ.filter fun i => y i ≤ t).card}

/-- **The median lies in an interval holding a strict majority.** If fewer than half of the
values `y i` lie outside `[a, b]` (that is, `2 · #{i | y i ∉ [a, b]} < s`), then the sample median
lies in `[a, b]`. This is the deterministic step of the median trick (N. Alon, Y. Matias and
M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.1: "In case this does not happen,
the median Yᵢ supplies a good estimate"). -/
theorem sampleMedian_mem_Icc {s : ℕ} (y : Fin s → ℝ) {a b : ℝ}
    (h : 2 * (univ.filter fun i => y i ∉ Set.Icc a b).card < s) :
    sampleMedian y ∈ Set.Icc a b := by
  set T : Set ℝ := {t | t ∈ Set.range y ∧ s < 2 * (univ.filter fun i => y i ≤ t).card}
    with hT
  have hs : 0 < s := by omega
  have hfin : T.Finite := (Set.finite_range y).subset fun t ht => ht.1
  have hne : T.Nonempty := by
    have : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ y univ_nonempty
    refine ⟨y j, ⟨j, rfl⟩, ?_⟩
    have : (univ.filter fun i => y i ≤ y j) = univ :=
      Finset.filter_true_of_mem fun i _ => hj i (mem_univ i)
    rw [this, card_univ, Fintype.card_fin]
    omega
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin s))) (fun i => y i ∈ Set.Icc a b)
  rw [card_univ, Fintype.card_fin] at hcard
  constructor
  · -- Lower bound: the infimum is attained at some `y j₀`.
    obtain ⟨⟨j₀, hj₀⟩, hcnt⟩ := Set.Nonempty.csInf_mem hne hfin
    change a ≤ sInf T
    rw [← hj₀]
    by_contra hlt
    push Not at hlt
    have hsub : (univ.filter fun i => y i ≤ y j₀) ⊆ univ.filter fun i => y i ∉ Set.Icc a b := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and, Set.mem_Icc, not_and, not_le] at hi ⊢
      intro hai
      linarith
    rw [← hj₀] at hcnt
    have := card_le_card hsub
    omega
  · -- Upper bound: the largest value at most `b` belongs to `T`.
    set G := univ.filter fun i => y i ≤ b with hG
    have hgood : (univ.filter fun i => y i ∈ Set.Icc a b) ⊆ G := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and, Set.mem_Icc, hG] at hi ⊢
      exact hi.2
    have hGcard : s < 2 * G.card := by
      have := card_le_card hgood
      omega
    have hGne : G.Nonempty := by
      rw [← card_pos]; omega
    obtain ⟨i₀, hi₀G, hi₀⟩ := Finset.exists_max_image G y hGne
    have hi₀b : y i₀ ≤ b := by simpa [hG] using hi₀G
    have hmem : y i₀ ∈ T := by
      refine ⟨⟨i₀, rfl⟩, ?_⟩
      have : G ⊆ univ.filter fun i => y i ≤ y i₀ := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and]
        exact hi₀ i hi
      have := card_le_card this
      omega
    exact (csInf_le hfin.bddBelow hmem).trans hi₀b

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **At least half of independent estimates are rarely bad.** Let `Y₁, …, Y_s` be independent
real random variables, each outside `[a, b]` with probability at most `1 / 8`. Then the
probability that at least half of them lie outside `[a, b]` is at most `exp (-9 s / 32)`. The
proof applies Hoeffding's inequality to the indicators of the bad events (N. Alon, Y. Matias and
M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.1, where "the standard estimate
of Chernoff" plays this role with `s = 2 log (1 / ε)`). -/
theorem measureReal_two_mul_card_bad_ge_le {s : ℕ} {Y : Fin s → Ω → ℝ}
    (h_indep : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i)) {a b : ℝ}
    (hbad : ∀ i, μ.real {ω | Y i ω ∉ Set.Icc a b} ≤ 1 / 8) :
    μ.real {ω | s ≤ 2 * (univ.filter fun i => Y i ω ∉ Set.Icc a b).card} ≤
      exp (-9 * s / 32) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  set B : Set ℝ := (Set.Icc a b)ᶜ with hB
  have hBm : MeasurableSet B := measurableSet_Icc.compl
  set Z : Fin s → Ω → ℝ := fun i ω => B.indicator 1 (Y i ω) with hZ
  have hZind : iIndepFun Z μ :=
    h_indep.comp (fun _ => B.indicator 1) fun _ => measurable_one.indicator hBm
  have hZmeas : ∀ i, AEMeasurable (Z i) μ := fun i =>
    ((measurable_one.indicator hBm).comp (hmeas i)).aemeasurable
  have hZrange : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    Filter.Eventually.of_forall fun ω => by
      simp only [hZ, Set.indicator, Pi.one_apply]
      split_ifs <;> norm_num
  have hhoef := MathlibExt.Probability.HoeffdingBounded.measureReal_avg_sub_ge_le hZind hZmeas
    hZrange (t := 3 / 8) (by norm_num)
  have hexp : exp (-2 * (s : ℝ) * (3 / 8) ^ 2 / (1 - 0) ^ 2) = exp (-9 * s / 32) := by
    congr 1; ring
  rw [hexp] at hhoef
  refine le_trans (measureReal_mono (fun ω hω => ?_)) hhoef
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  -- The empirical average of the indicators is at least `1 / 2`.
  have hsum : ∑ i, Z i ω = ((univ.filter fun i => Y i ω ∉ Set.Icc a b).card : ℝ) := by
    simp only [hZ, Set.indicator, Pi.one_apply, hB, Set.mem_compl_iff]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one]
  -- Each mean is at most `1 / 8`.
  have hmean : ∀ i, μ[Z i] ≤ 1 / 8 := by
    intro i
    have : μ[Z i] = μ.real {ω | Y i ω ∉ Set.Icc a b} := by
      simp only [hZ]
      rw [show (fun ω => B.indicator 1 (Y i ω)) = (Y i ⁻¹' B).indicator (1 : Ω → ℝ) from by
        funext ω; simp [Set.indicator]]
      rw [integral_indicator_one ((hmeas i) hBm)]
      rfl
    rw [this]; exact hbad i
  have hmeansum : (1 / s : ℝ) * ∑ i, μ[Z i] ≤ 1 / 8 := by
    calc (1 / s : ℝ) * ∑ i, μ[Z i] ≤ (1 / s : ℝ) * ∑ _i : Fin s, (1 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hmean i) (by positivity)
      _ = 1 / 8 := by
          rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hcast : (s : ℝ) ≤ 2 * ((univ.filter fun i => Y i ω ∉ Set.Icc a b).card : ℝ) := by
    exact_mod_cast hω
  rw [hsum]
  have : (1 / 2 : ℝ) ≤ (1 / s : ℝ) * ((univ.filter fun i => Y i ω ∉ Set.Icc a b).card : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hsR]
    linarith
  linarith

/-- **Median amplification.** Let `Y₁, …, Y_s` be independent real random variables, each
outside `[a, b]` with probability at most `1 / 8`. Then their sample median lies outside `[a, b]`
with probability at most `exp (-9 s / 32)`; in particular at most `ε` once
`s ≥ (32 / 9) log (1 / ε)`. This is the amplification step of N. Alon, Y. Matias and M. Szegedy,
J. Comput. System Sci. 58 (1999), proofs of Theorems 2.1 and 2.2, where each `Yⱼ` is a mean of
independent copies of a basic estimator and Chebyshev's inequality supplies the `1 / 8`; the
source takes `s = 2 log (1 / ε)` with a Chernoff bound, while this statement uses Hoeffding's
inequality and so has the explicit constant `9 / 32`. -/
theorem measureReal_sampleMedian_notMem_Icc_le {s : ℕ} {Y : Fin s → Ω → ℝ}
    (h_indep : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i)) {a b : ℝ}
    (hbad : ∀ i, μ.real {ω | Y i ω ∉ Set.Icc a b} ≤ 1 / 8) :
    μ.real {ω | sampleMedian (fun i => Y i ω) ∉ Set.Icc a b} ≤ exp (-9 * s / 32) := by
  refine le_trans (measureReal_mono fun ω hω => ?_)
    (measureReal_two_mul_card_bad_ge_le h_indep hmeas hbad)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hlt
  push Not at hlt
  exact hω (sampleMedian_mem_Icc (fun i => Y i ω) hlt)

end MathlibExt.Probability.MedianOfMeans
