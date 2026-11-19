/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching
public import MathlibExt.Biology.PopulationGenetics.Haldane
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open scoped ENNReal NNReal
open MathlibExt.Probability MathlibExt.Probability.GaltonWatson
open MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching
open MathlibExt.Biology.PopulationGenetics.Haldane (pgf_poissonMeasure mean_poissonMeasure)

namespace MathlibExtTest.Biology.Epidemiology.EarlyEpidemicBranching

/-! ### Definitions unfold as expected -/

example (ξ : ℕ → ℕ → ℕ) : bpSize ξ 0 = 1 := rfl

example (ξ : ℕ → ℕ → ℕ) (n : ℕ) : bpSize ξ (n + 1) = ∑ i ∈ range (bpSize ξ n), ξ n i := rfl

example {α : Type*} [DecidableEq α] (ξ : ℕ → ℕ → ℕ) (U : ℕ → α) (S₀ : Finset α) :
    epiSize ξ U S₀ 0 = 1 := rfl

example {α : Type*} [DecidableEq α] (U : ℕ → α) (S₀ : Finset α) (j : ℕ) :
    epiHit U S₀ j ↔ U j ∈ S₀ ∧ ∀ j' < j, U j' ≠ U j := Iff.rfl

/-! ### Deterministic coupling on concrete data

Every individual makes two contacts (`ξ = 2`), so `Z n = 2 ^ n`. All values below are computed
by evaluating the definitions. -/

/-- Fresh targets: contact `j` goes to individual `j + 1` of the susceptibles `{1, …, 99}`. The
first 14 contacts all hit, so the epidemic is the branching process up to generation 3. -/
example : epiSize (fun _ _ => 2) (fun j => j + 1) ((range 100).erase 0) 3 = 8 := by decide
example : bpSize (fun _ _ => 2) 3 = 8 := by decide
example : bpContacts (fun _ _ => 2) 3 = 14 := by decide

/-- The coupling theorem gives the same conclusion without evaluating the epidemic. -/
example : epiSize (fun _ _ => 2) (fun j => j + 1) ((range 100).erase 0) 3 =
    bpSize (fun _ _ => 2) 3 :=
  epiSize_eq_bpSize_of_forall_hit _ _ _ (M := 14) (by decide) (by decide)

/-- Repeated targets: every contact goes to individual `1`. Only the first contact infects; the
epidemic dies out at generation 2 while the branching process has 4 individuals. -/
example : epiSize (fun _ _ => 2) (fun _ => 1) ((range 100).erase 0) 1 = 1 := by decide
example : epiSize (fun _ _ => 2) (fun _ => 1) ((range 100).erase 0) 2 = 0 := by decide
example : bpSize (fun _ _ => 2) 2 = 4 := by decide

/-- Depletion: only three susceptibles `{1, 2, 3}`. Generation sizes `1, 2, 1, 0`, extinct by
generation `#S₀ + 1 = 4` as `epiSize_card_add_one_eq_zero` predicts. -/
example : epiSize (fun _ _ => 2) (fun j => j + 1) {1, 2, 3} 1 = 2 := by decide
example : epiSize (fun _ _ => 2) (fun j => j + 1) {1, 2, 3} 2 = 1 := by decide
example : epiSize (fun _ _ => 2) (fun j => j + 1) {1, 2, 3} 3 = 0 := by decide
example : epiSize (fun _ _ => 2) (fun j => j + 1) ({1, 2, 3} : Finset ℕ) 4 = 0 :=
  epiSize_card_add_one_eq_zero _ _ _

/-! ### The index case

In the one-individual population `Fin 1`, one contact per infective, always to the individual
`0`. -/

/-- An index case outside the population infects the individual `0` when it is susceptible. -/
example : epiSize (fun _ _ => 1) (fun _ => (0 : Fin 1)) univ 1 = 1 := by decide

/-- If the index case is the individual `0` itself, it is left out of `S₀ = ∅`, and its contact
infects nobody. -/
example : epiSize (fun _ _ => 1) (fun _ => (0 : Fin 1)) ∅ 1 = 0 := by decide

/-- With the index case `0 ∉ S₀` inside `Fin 3`, the infectives of generations `0, …, n` never
outnumber the population, whatever the offspring numbers and the contact targets. -/
example (ξ : ℕ → ℕ → ℕ) (U : ℕ → Fin 3) (n : ℕ) :
    ∑ m ∈ range (n + 1), epiSize ξ U ((univ : Finset (Fin 3)).erase 0) m ≤ 3 :=
  (sum_epiSize_le_card ξ U _ (notMem_erase 0 univ) n).trans_eq (Fintype.card_fin 3)

/-! ### Exponential bounds used below -/

private lemma exp_eight_fifths_lt_five : exp (8 / 5) < 5 := by
  have h1 : exp (8 / 5) ^ 5 = exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 : exp 1 ^ 8 < 5 ^ 5 :=
    calc exp 1 ^ 8 < 2.7182818286 ^ 8 := by gcongr; exact Real.exp_one_lt_d9
      _ < 5 ^ 5 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) (h1 ▸ h2)

private lemma four_lt_exp_three_halves : 4 < exp (3 / 2) := by
  have h1 : exp (3 / 2) ^ 2 = exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 : (4 : ℝ) ^ 2 < exp 1 ^ 3 :=
    calc (4 : ℝ) ^ 2 < 2.7182818283 ^ 3 := by norm_num
      _ < exp 1 ^ 3 := by gcongr; exact Real.exp_one_gt_d9
  exact lt_of_pow_lt_pow_left₀ 2 (exp_pos _).le (h1 ▸ h2)

/-! ### Supercritical case: Poisson(2) offspring, `R₀ = 2`

The extinction probability `q` is the least root of `q = e^{2(q - 1)}` in `[0, 1]`. We bracket it
from the generating function alone: `q ∈ (1/5, 1/4)` (numerically `q ≈ 0.2032`). -/

theorem pgf_poisson_two (s : ℝ) : pgf id (poissonMeasure 2) s = exp (2 * (s - 1)) := by
  rw [pgf_poissonMeasure]; norm_num

theorem extinctionProb_poisson_two_mem :
    extinctionProb (poissonMeasure 2) ∈ Set.Ioo (1 / 5 : ℝ) (1 / 4) := by
  have hq := isLeast_extinctionProb (poissonMeasure 2)
  set q := extinctionProb (poissonMeasure 2)
  have he : 1 / 5 < exp (-(8 / 5)) := by
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (exp_pos _) exp_eight_fifths_lt_five
  have he2 : exp (-(8 / 5)) < 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (by norm_num) (by linarith [add_one_le_exp (8 / 5 : ℝ)])
  constructor
  · -- No fixed point in `[0, 1/5]`: there `e^{2(s-1)} ≥ e^{-8/5} (1 + 2 (s - 1/5)) > s`.
    by_contra hle
    rw [not_lt] at hle
    have hfix : exp (2 * (q - 1)) = q := by rw [← pgf_poisson_two]; exact hq.1.2
    have hexp : exp (-(8 / 5)) * (1 + 2 * (q - 1 / 5)) ≤ exp (2 * (q - 1)) := by
      rw [show 2 * (q - 1) = -(8 / 5) + 2 * (q - 1 / 5) by ring, Real.exp_add]
      exact mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp (2 * (q - 1 / 5))])
        (exp_pos _).le
    nlinarith [mul_nonneg (sub_nonneg.2 hle) (by linarith : (0 : ℝ) ≤ 1 - 2 * exp (-(8 / 5)))]
  · -- A fixed point in `[1/5, 1/4)` by the intermediate value theorem.
    set g : ℝ → ℝ := fun s => exp (2 * (s - 1)) - s
    have hg5 : 0 < g (1 / 5) := by
      simp only [g]; rw [show 2 * ((1 : ℝ) / 5 - 1) = -(8 / 5) by norm_num]; linarith
    have hg4 : g (1 / 4) < 0 := by
      simp only [g]
      rw [show 2 * ((1 : ℝ) / 4 - 1) = -(3 / 2) by norm_num, Real.exp_neg]
      have := inv_strictAnti₀ (by norm_num) four_lt_exp_three_halves
      linarith
    have hcont : ContinuousOn g (Set.Icc (1 / 5) (1 / 4)) := by fun_prop
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨hg4.le, hg5.le⟩
    have htq : q ≤ t := hq.2 ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      by rw [pgf_poisson_two]; simp only [g] at hgt; linarith⟩
    have ht4 : t ≠ 1 / 4 := fun h => by rw [h] at hgt; linarith
    exact lt_of_le_of_lt htq (lt_of_le_of_ne ht.2 ht4)

/-- A major outbreak has probability `1 - q ∈ (3/4, 4/5)`. -/
example : 1 - extinctionProb (poissonMeasure 2) ∈ Set.Ioo (3 / 4 : ℝ) (4 / 5) := by
  have := extinctionProb_poisson_two_mem
  constructor <;> linarith [this.1, this.2]

/-- The threshold theorem agrees: `R₀ = 2 > 1` gives a positive major-outbreak probability. -/
example : 0 < 1 - extinctionProb (poissonMeasure 2) :=
  one_sub_extinctionProb_pos (by rw [mean_poissonMeasure]; norm_num)

/-- The canonical model with Poisson(2) offspring in the population `Fin (k + 1)`, whose
individual `0` is the index case (left out of `S₀`), with everybody else susceptible: as
`k → ∞`, the probability that the epidemic reaches generation `1` converges to
`1 - P(Z₁ = 0) = 1 - e^{-2}`. -/
example : Tendsto (fun k : ℕ => (canonicalMeasure (poissonMeasure 2) (k + 1)).real
      {ω | epiSize (fun n i => ω.1 (n, i)) (fun j => ω.2 j)
        ((univ : Finset (Fin (k + 1))).erase 0) 1 ≠ 0}) atTop (𝓝 (1 - exp (-2))) := by
  have hS : Tendsto (fun k : ℕ => (((k + 1) - ((univ : Finset (Fin (k + 1))).erase 0).card : ℕ)
      : ℝ) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simp only [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, Nat.add_sub_cancel,
      Nat.add_sub_cancel_left, Nat.cast_one, Nat.cast_add]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h := tendsto_measureReal_epiSize_ne_zero (ν := poissonMeasure 2)
    (P := fun k => canonicalMeasure (poissonMeasure 2) (k + 1)) (N := fun k => k + 1)
    (ξ := fun k n i ω => ω.1 (n, i)) (U := fun k j ω => ω.2 j)
    (S₀ := fun k => (univ : Finset (Fin (k + 1))).erase 0)
    (fun k => isEarlyEpidemic_canonical _ _) (tendsto_add_atTop_nat 1) hS 1
  rwa [law_real_zero, Function.iterate_one, pgf_poisson_two,
    show (2 : ℝ) * (0 - 1) = -2 by norm_num] at h

/-! ### Subcritical (Poisson(1/2), `R₀ = 1/2`) and critical (Poisson(1), `R₀ = 1`) cases -/

/-- Independent check from the generating function: for `r ≤ 1` the only fixed point of
`s ↦ e^{r(s-1)}` in `[0, 1]` is `1` (`e^{r(s-1)} > 1 + r(s-1) ≥ s` for `s < 1`), so `q = 1`. -/
theorem extinctionProb_poisson_eq_one {r : ℝ≥0} (hr : r ≤ 1) :
    extinctionProb (poissonMeasure r) = 1 := by
  have hq := (isLeast_extinctionProb (poissonMeasure r)).1
  rw [Set.mem_ofPred_eq, pgf_poissonMeasure] at hq
  set q := extinctionProb (poissonMeasure r)
  by_contra hne
  have hlt : q < 1 := lt_of_le_of_ne hq.1.2 hne
  have hr' : (r : ℝ) ≤ 1 := by exact_mod_cast hr
  rcases eq_or_lt_of_le r.coe_nonneg with h0 | hpos
  · rw [← h0, zero_mul, Real.exp_zero] at hq
    exact hne hq.2.symm
  · have hx : (r : ℝ) * (q - 1) ≠ 0 := mul_ne_zero hpos.ne' (by linarith)
    have := Real.add_one_lt_exp hx
    nlinarith [mul_nonneg (sub_nonneg.2 hr') (by linarith : (0 : ℝ) ≤ 1 - q)]

private lemma poissonMeasure_one_ne_one {r : ℝ≥0} (hr : r ≤ 1) : poissonMeasure r {1} ≠ 1 := by
  rw [poissonMeasure_singleton]
  refine (ENNReal.ofReal_lt_one.2 ?_).ne
  have hr' : (r : ℝ) ≤ 1 := by exact_mod_cast hr
  have : exp (-(r : ℝ)) < 1 ∨ (r : ℝ) = 0 := by
    rcases eq_or_lt_of_le r.coe_nonneg with h0 | hpos
    · exact Or.inr h0.symm
    · exact Or.inl (Real.exp_lt_one_iff.2 (by linarith))
  rcases this with h | h
  · simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    nlinarith [exp_pos (-(r : ℝ)), r.coe_nonneg]
  · simp [h]

/-- Subcritical: `R₀ = 1/2`. -/
example : mean (poissonMeasure (1 / 2)) ≤ 1 := by
  rw [mean_poissonMeasure]; norm_num

/-- The threshold theorem and the direct computation agree: `q = 1` for `R₀ = 1/2`. -/
example : extinctionProb (poissonMeasure (1 / 2)) = 1 :=
  (extinctionProb_eq_one_iff _ (poissonMeasure_one_ne_one (by norm_num))).2
    (by rw [mean_poissonMeasure]; norm_num)

example : extinctionProb (poissonMeasure (1 / 2)) = 1 :=
  extinctionProb_poisson_eq_one (by norm_num)

/-- In a finite population eventual extinction is certain whatever `R₀`, even for the
supercritical Poisson(2) law: it is finiteness, not `R₀`, that decides this. -/
example (N : ℕ) [NeZero N] (S₀ : Finset (Fin N)) :
    (canonicalMeasure (poissonMeasure 2) N).real
      {ω | ∃ n, epiSize (fun n i => ω.1 (n, i)) (fun j => ω.2 j) S₀ n = 0} = 1 :=
  have := (isEarlyEpidemic_canonical (poissonMeasure 2) N).isProbabilityMeasure
  measureReal_exists_epiSize_eq_zero _ _ _ S₀

/-- What `R₀ ≤ 1` decides: the subcritical epidemic is extinct within a number of generations
that does not depend on the population. -/
example : ∃ n₀, ∀ n ≥ n₀, ∀ (N : ℕ) [NeZero N] (S₀ : Finset (Fin N)),
    1 - 1 / 100 < (canonicalMeasure (poissonMeasure (1 / 2)) N).real
      {ω | epiSize (fun n i => ω.1 (n, i)) (fun j => ω.2 j) S₀ n = 0} := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_measureReal_epiSize_eq_zero_gt.{0, 0}
    (poissonMeasure_one_ne_one (by norm_num : (1 / 2 : ℝ≥0) ≤ 1))
    (by rw [mean_poissonMeasure]; norm_num) (by norm_num : (0 : ℝ) < 1 / 100)
  exact ⟨n₀, fun n hn N _ S₀ =>
    hn₀ n hn _ S₀ (isEarlyEpidemic_canonical (poissonMeasure (1 / 2)) N).toIsOffspringFamily⟩

/-- Critical: `R₀ = 1` exactly. -/
example : mean (poissonMeasure 1) = 1 := by
  rw [mean_poissonMeasure]; norm_num

/-- At `R₀ = 1` extinction is still certain (threshold theorem and direct computation). -/
example : extinctionProb (poissonMeasure 1) = 1 :=
  (extinctionProb_eq_one_iff _ (poissonMeasure_one_ne_one le_rfl)).2
    (by rw [mean_poissonMeasure]; norm_num)

example : extinctionProb (poissonMeasure 1) = 1 :=
  extinctionProb_poisson_eq_one le_rfl

/-- ... but not in finite time: `P(Z₁ = 0) = e^{-1} < 1`, so the critical epidemic survives its
first generation with probability `1 - e^{-1}` in the large-population limit. -/
example : (law (poissonMeasure 1) 1).real {0} = exp (-1) := by
  rw [law_real_zero, Function.iterate_one, pgf_poissonMeasure]; norm_num

/-! ### The birthday bound on a concrete population -/

/-- In `Fin 10` with nine susceptibles, some of the first three contacts is wasted with
probability at most `(3 · 1 + C(3, 2)) / 10 = 6 / 10`. -/
example (S₀ : Finset (Fin 10)) (hS : S₀.card = 9) :
    canonicalMeasure (poissonMeasure 2) 10
      {ω | ∃ j < 3, ¬ epiHit (fun j => ω.2 j) S₀ j} ≤ 6 * (10 : ℝ≥0∞)⁻¹ := by
  have h := (isEarlyEpidemic_canonical (poissonMeasure 2) 10).measure_exists_not_epiHit_le S₀ 3
  rw [hS] at h
  exact_mod_cast h

end MathlibExtTest.Biology.Epidemiology.EarlyEpidemicBranching
