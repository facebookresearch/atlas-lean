/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Field

/-!
# Causal identification with potential outcomes

Potential outcomes `Y₀, Y₁` (the outcome a unit would show untreated and treated) are the
vocabulary of this file. An *identification* result expresses a causal quantity, defined through
the potential outcomes, by the law of observed quantities alone.

## Main definitions

* `popMean`, `popVar`, `ate`: mean, variance (divisor `N - 1`) and average treatment effect of a
  finite population of `N` units with fixed potential outcomes.
* `randExp n₁ f`: the expectation of a statistic `f` of the treated set under *complete
  randomization*, the uniform law on treated sets of size `n₁`.
* `diffInMeans`, `neymanVar`: the difference of the treated and control sample means, and
  Neyman's variance estimator `s₁² / n₁ + s₀² / n₀`.
* `observed T Y₀ Y₁`: the observed outcome `Y₁` on the treated event `T` and `Y₀` off it.
* `propensity μ T W w`: the conditional probability of `T` given `W = w`, for a discrete `W`.
* `CondIndepDiscrete μ T V W`: the event `T` is conditionally independent of `V` given the
  discrete variable `W`. `StronglyIgnorable μ T V W` adds overlap, `0 < P(T | W) < 1`.

## Main results

* Neyman (1923), complete randomization: `randExp_diffInMeans` (the difference in means is
  unbiased for the finite-population ATE), `randExp_sq_diffInMeans_sub_ate` (its exact
  variance `S₁²/n₁ + S₀²/n₀ - S_τ²/N`), `randExp_neymanVar` (the expectation of Neyman's
  estimator is `S₁²/n₁ + S₀²/n₀`), and `randVar_le_randExp_neymanVar` (the estimator is
  conservative, with equality exactly for a constant treatment effect).
* Rosenbaum & Rubin (1983), for a covariate with finitely many values:
  `condIndepDiscrete_propensity` (Theorem 1: the propensity score is a balancing score,
  `T ⊥ X | e(X)`), `condIndepDiscrete_comp_iff` (Theorem 2: `b(X)` is a balancing score if and
  only if it is finer than `e(X)`), `StronglyIgnorable.comp_of_balancing` and
  `stronglyIgnorable_propensity` (Theorem 3: strong ignorability given `X` implies it given any
  balancing score, in particular given `e(X)`), and `propensity_propensity` (the score is
  calibrated, `P(T | e(X) = c) = c`).
* Inverse probability weighting by the propensity score (the weighting of Horvitz & Thompson
  1952; Rosenbaum 1987): `integral_ipw_treated`, `integral_ipw_control`, `integral_ipw_ate`:
  `E[1_T Y / e(X)] = E[Y₁]` and `E[1_{Tᶜ} Y / (1 - e(X))] = E[Y₀]` under strong ignorability
  (finite covariate space); `integral_ipw_treated_condExp`: the same identity for a general
  covariate σ-algebra, with `e = P(T | m)` a conditional expectation, under conditional mean
  independence and the strong overlap `e ≥ ε > 0` (the control arm is the case `T ↦ Tᶜ`).

## Not covered

Validity of permutation p-values under a group-invariant null (Fisher 1935); Theorems 1–3 of
Rosenbaum & Rubin for covariates with infinitely many values (stated with conditional
independence given a σ-algebra); the asymptotic
(superpopulation) versions of Neyman's results; instrumental variables (the Wald ratio and the
LATE theorem), which belong with Mendelian randomization. Graphical identification (the
do-operator, adjustment) is in `CSLibExt/MachineLearning/GraphicalModels/CausalBayesNet.lean`.

## References

* J. Neyman, *On the application of probability theory to agricultural experiments* (1923);
  translated by D. M. Dabrowska and T. P. Speed, Statistical Science 5(4) (1990), 465–472.
* R. A. Fisher, *The Design of Experiments*, Oliver and Boyd (1935).
* G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
  Sciences*, Cambridge University Press (2015), Chapter 6.
* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70(1) (1983), 41–55.
* D. G. Horvitz and D. J. Thompson, *A generalization of sampling without replacement from a
  finite universe*, JASA 47(260) (1952), 663–685.
* P. R. Rosenbaum, *Model-based direct adjustment*, JASA 82(398) (1987), 387–394.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality

open MeasureTheory ProbabilityTheory Finset

/-! ### Finite-population randomization inference (Neyman 1923) -/

section Neyman

variable {ι : Type*}

/-- The mean of `y` over a set of units `S`, `(1/|S|) ∑_{i ∈ S} yᵢ` (the junk value `0` for
`S = ∅`). -/
noncomputable def sampleMean (y : ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ i ∈ S, y i) / S.card

/-- The sample variance of `y` over `S` with divisor `|S| - 1`; meaningful for `|S| ≥ 2` (for
`|S| ≤ 1` it is the junk value `0`). -/
noncomputable def sampleVar (y : ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ i ∈ S, (y i - sampleMean y S) ^ 2) / ((S.card : ℝ) - 1)

variable [Fintype ι]

/-- The mean of a finite population of `N = Fintype.card ι` units, `(1/N) ∑ᵢ yᵢ`. -/
noncomputable def popMean (y : ι → ℝ) : ℝ :=
  (∑ i, y i) / Fintype.card ι

/-- The variance of a finite population with divisor `N - 1`, `S² = ∑ᵢ (yᵢ - ȳ)² / (N - 1)`;
meaningful for `N ≥ 2`. -/
noncomputable def popVar (y : ι → ℝ) : ℝ :=
  (∑ i, (y i - popMean y) ^ 2) / ((Fintype.card ι : ℝ) - 1)

/-- The finite-population average treatment effect `(1/N) ∑ᵢ (y₁ᵢ - y₀ᵢ)`. -/
noncomputable def ate (y₀ y₁ : ι → ℝ) : ℝ :=
  popMean fun i => y₁ i - y₀ i

/-- The difference in means for the treated set `S`: the mean of the treated outcomes `y₁` over
`S` minus the mean of the control outcomes `y₀` over the complement. -/
noncomputable def diffInMeans [DecidableEq ι] (y₀ y₁ : ι → ℝ) (S : Finset ι) : ℝ :=
  sampleMean y₁ S - sampleMean y₀ Sᶜ

/-- Neyman's variance estimator `s₁² / n₁ + s₀² / n₀` for the treated set `S`. -/
noncomputable def neymanVar [DecidableEq ι] (y₀ y₁ : ι → ℝ) (S : Finset ι) : ℝ :=
  sampleVar y₁ S / S.card + sampleVar y₀ Sᶜ / (Sᶜ).card

/-- The expectation of a statistic `f` of the treated set under complete randomization: the
treated set is uniform among the `(N choose n₁)` sets of `n₁` units (`n₁ ≤ N`; for `n₁ > N`
there is no such set and the value is `0`). -/
noncomputable def randExp (n₁ : ℕ) (f : Finset ι → ℝ) : ℝ :=
  (∑ S ∈ univ.powersetCard n₁, f S) / (Fintype.card ι).choose n₁

private lemma choose_ne_zero {n₁ : ℕ} (h : n₁ ≤ Fintype.card ι) :
    ((Fintype.card ι).choose n₁ : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos h).ne'

/-- Number of treated sets containing a given unit. -/
private lemma sum_powersetCard_ite_mem [DecidableEq ι] (n₁ : ℕ) (i : ι) :
    (∑ S ∈ univ.powersetCard n₁, (if i ∈ S then (1 : ℝ) else 0)) * (Fintype.card ι) =
      (Fintype.card ι).choose n₁ * n₁ := by
  rw [sum_boole]
  rcases Nat.eq_zero_or_pos n₁ with rfl | hn
  · simp
  have hcard := card_filter_powersetCard_subset {i} univ n₁ (by simp) (by simp; omega)
  simp only [singleton_subset_iff, card_singleton, card_univ] at hcard
  rw [hcard]
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card ι = N + 1 :=
    ⟨Fintype.card ι - 1, (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.2 ⟨i⟩)).symm⟩
  obtain ⟨k, rfl⟩ : ∃ k, n₁ = k + 1 := ⟨n₁ - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  rw [hN]
  simp only [Nat.add_sub_cancel]
  have := Nat.add_one_mul_choose_eq N k
  rw [mul_comm]
  exact_mod_cast this

/-- Number of treated sets containing two given distinct units. -/
private lemma sum_powersetCard_ite_mem_mem [DecidableEq ι] (n₁ : ℕ) {i j : ι} (hij : i ≠ j) :
    (∑ S ∈ univ.powersetCard n₁, (if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0)) *
        ((Fintype.card ι) * ((Fintype.card ι : ℝ) - 1)) =
      (Fintype.card ι).choose n₁ * (n₁ * ((n₁ : ℝ) - 1)) := by
  rw [sum_boole]
  by_cases hn : 2 ≤ n₁
  · have hs : ({i, j} : Finset ι).card = 2 := card_pair hij
    have hcard := card_filter_powersetCard_subset {i, j} univ n₁ (by simp) (by omega)
    rw [hs, card_univ] at hcard
    have hfilt : (univ.powersetCard n₁).filter (fun S => i ∈ S ∧ j ∈ S) =
        (univ.powersetCard n₁).filter (fun S => {i, j} ⊆ S) := by
      ext S; simp [insert_subset_iff]
    rw [hfilt, hcard]
    have hN : 2 ≤ Fintype.card ι := by
      rw [← card_univ]
      exact le_trans (by rw [hs]) (card_le_univ {i, j})
    obtain ⟨N, hN'⟩ : ∃ N, Fintype.card ι = N + 2 := ⟨Fintype.card ι - 2, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n₁ = k + 2 := ⟨n₁ - 2, by omega⟩
    rw [hN']
    simp only [Nat.add_sub_cancel]
    have h1 := Nat.add_one_mul_choose_eq (N + 1) (k + 1)
    have h2 := Nat.add_one_mul_choose_eq N k
    push_cast
    have e1 : ((N + 1 + 1 : ℕ) : ℝ) * ((N + 1).choose (k + 1) : ℕ) =
        ((N + 1 + 1).choose (k + 1 + 1) : ℕ) * ((k + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    have e2 : ((N + 1 : ℕ) : ℝ) * (N.choose k : ℕ) =
        ((N + 1).choose (k + 1) : ℕ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast h2
    push_cast at e1 e2
    linear_combination ((N : ℝ) + 2) * e2 + ((k : ℝ) + 1) * e1
  · have hempty : (univ.powersetCard n₁).filter (fun S => i ∈ S ∧ j ∈ S) = ∅ := by
      refine filter_eq_empty_iff.2 fun S hS h => ?_
      have h2 : ({i, j} : Finset ι) ⊆ S := by simp [insert_subset_iff, h.1, h.2]
      have := card_le_card h2
      rw [card_pair hij, (mem_powersetCard.1 hS).2] at this
      exact hn this
    rw [hempty, card_empty, Nat.cast_zero, zero_mul]
    interval_cases n₁ <;> simp

/-- The expected sample total: `E[∑_{i ∈ S} aᵢ] = (n₁/N) ∑ᵢ aᵢ`. -/
private lemma randExp_sum_mem {n₁ : ℕ} (hn : n₁ ≤ Fintype.card ι) (hN : 0 < Fintype.card ι)
    (a : ι → ℝ) :
    randExp n₁ (fun S => ∑ i ∈ S, a i) = n₁ / Fintype.card ι * ∑ i, a i := by
  classical
  have hC := choose_ne_zero (ι := ι) hn
  have hN' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcount : ∀ i : ι, ∑ S ∈ univ.powersetCard n₁, (if i ∈ S then (1 : ℝ) else 0) =
      (Fintype.card ι).choose n₁ * n₁ / Fintype.card ι := fun i => by
    rw [eq_div_iff hN', sum_powersetCard_ite_mem]
  have hsum : ∑ S ∈ univ.powersetCard n₁, ∑ i ∈ S, a i =
      ∑ i, a i * ∑ S ∈ univ.powersetCard n₁, (if i ∈ S then (1 : ℝ) else 0) := by
    calc ∑ S ∈ univ.powersetCard n₁, ∑ i ∈ S, a i =
          ∑ S ∈ univ.powersetCard n₁, ∑ i, (if i ∈ S then a i else 0) := by
          refine sum_congr rfl fun S _ => ?_
          rw [sum_ite_mem, univ_inter]
      _ = ∑ i, ∑ S ∈ univ.powersetCard n₁, (if i ∈ S then a i else 0) := sum_comm
      _ = _ := by
          refine sum_congr rfl fun i _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun S _ => ?_
          split_ifs <;> simp
  rw [randExp, hsum]
  simp_rw [hcount]
  rw [← sum_mul, div_eq_iff hC]
  field_simp

/-- The expected squared sample total:
`E[(∑_{i ∈ S} aᵢ)²] = (n₁/N) ∑ aᵢ² + n₁(n₁-1)/(N(N-1)) ((∑ aᵢ)² - ∑ aᵢ²)`. -/
private lemma randExp_sq_sum_mem {n₁ : ℕ} (hn : n₁ ≤ Fintype.card ι) (hN : 2 ≤ Fintype.card ι)
    (a : ι → ℝ) :
    randExp n₁ (fun S => (∑ i ∈ S, a i) ^ 2) =
      n₁ / Fintype.card ι * ∑ i, a i ^ 2 +
        n₁ * ((n₁ : ℝ) - 1) / (Fintype.card ι * ((Fintype.card ι : ℝ) - 1)) *
          ((∑ i, a i) ^ 2 - ∑ i, a i ^ 2) := by
  classical
  have hC := choose_ne_zero (ι := ι) hn
  have hN0 : (Fintype.card ι : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
  have hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
  set C : ℝ := ((Fintype.card ι).choose n₁ : ℝ)
  set c₁ : ℝ := C * n₁ / Fintype.card ι
  set c₂ : ℝ := C * (n₁ * ((n₁ : ℝ) - 1)) / (Fintype.card ι * ((Fintype.card ι : ℝ) - 1))
  have hcount : ∀ i j : ι, ∑ S ∈ univ.powersetCard n₁, (if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) =
      c₂ + (c₁ - c₂) * (if i = j then 1 else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [and_self, ite_true, mul_one, add_sub_cancel]
      rw [eq_div_iff hN0, sum_powersetCard_ite_mem]
    · simp only [hij, ite_false, mul_zero, add_zero]
      rw [eq_div_iff (mul_ne_zero hN0 hN1), sum_powersetCard_ite_mem_mem n₁ hij]
  have hsum : ∑ S ∈ univ.powersetCard n₁, (∑ i ∈ S, a i) ^ 2 =
      ∑ i, ∑ j, a i * a j *
        ∑ S ∈ univ.powersetCard n₁, (if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) := by
    have hpt : ∀ S : Finset ι, (∑ i ∈ S, a i) ^ 2 =
        ∑ i, ∑ j, a i * a j * (if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) := by
      intro S
      rw [← univ_inter S, ← sum_ite_mem, sq, sum_mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [hi, hj]
    simp_rw [hpt]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
  rw [randExp, hsum]
  simp_rw [hcount]
  have hsq : ∑ i, ∑ j, a i * a j * (c₂ + (c₁ - c₂) * (if i = j then 1 else 0)) =
      c₂ * (∑ i, a i) ^ 2 + (c₁ - c₂) * ∑ i, a i ^ 2 := by
    simp_rw [mul_add, sum_add_distrib, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ,
      ite_true, sq, sum_mul_sum]
    rw [mul_sum, mul_sum]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    · exact sum_congr rfl fun i _ => by ring
  rw [hsq, div_eq_iff hC]
  simp only [c₁, c₂]
  field_simp
  ring

private lemma randExp_congr {n₁ : ℕ} {f g : Finset ι → ℝ}
    (h : ∀ S : Finset ι, S.card = n₁ → f S = g S) : randExp n₁ f = randExp n₁ g := by
  unfold randExp
  congr 1
  exact sum_congr rfl fun S hS => h S (mem_powersetCard_univ.1 hS)

private lemma randExp_const {n₁ : ℕ} (hn : n₁ ≤ Fintype.card ι) (c : ℝ) :
    randExp n₁ (fun _ : Finset ι => c) = c := by
  rw [randExp, sum_const, card_powersetCard, card_univ, nsmul_eq_mul]
  field_simp [choose_ne_zero (ι := ι) hn]

private lemma randExp_add {n₁ : ℕ} (f g : Finset ι → ℝ) :
    randExp n₁ (fun S => f S + g S) = randExp n₁ f + randExp n₁ g := by
  simp only [randExp, sum_add_distrib, add_div]

private lemma randExp_smul {n₁ : ℕ} (c : ℝ) (f : Finset ι → ℝ) :
    randExp n₁ (fun S => c * f S) = c * randExp n₁ f := by
  simp only [randExp, ← mul_sum, mul_div_assoc]

/-- The control set of a completely randomized design is itself completely randomized. -/
private lemma randExp_compl [DecidableEq ι] {n₁ : ℕ} (hn : n₁ ≤ Fintype.card ι) (f : Finset ι → ℝ) :
    randExp n₁ (fun S => f Sᶜ) = randExp (Fintype.card ι - n₁) f := by
  unfold randExp
  rw [Nat.choose_symm hn]
  congr 1
  refine sum_nbij' (fun S => Sᶜ) (fun S => Sᶜ) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_powersetCard_univ] at hS ⊢
    rw [card_compl, hS]
  · intro S hS
    simp only [mem_powersetCard_univ] at hS ⊢
    rw [card_compl, hS]
    omega
  · intro S _; simp
  · intro S _; simp
  · intro S _; rfl

omit [Fintype ι] in
private lemma sum_sq_sub_const (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    ∑ i ∈ s, (f i - c) ^ 2 = ∑ i ∈ s, f i ^ 2 - 2 * c * ∑ i ∈ s, f i + s.card * c ^ 2 := by
  have : ∀ i ∈ s, (f i - c) ^ 2 = f i ^ 2 - 2 * c * f i + c ^ 2 := fun i _ => by ring
  rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
    nsmul_eq_mul]

omit [Fintype ι] in
private lemma sum_sq_sub_mean (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, (f i - (∑ j ∈ s, f j) / s.card) ^ 2 =
      ∑ i ∈ s, f i ^ 2 - (∑ i ∈ s, f i) ^ 2 / s.card := by
  rw [sum_sq_sub_const]
  rcases eq_or_ne (s.card : ℝ) 0 with h | h
  · rw [h]; simp
  · field_simp; ring

private lemma popVar_eq (y : ι → ℝ) :
    popVar y = (∑ i, y i ^ 2 - (∑ i, y i) ^ 2 / Fintype.card ι) /
      ((Fintype.card ι : ℝ) - 1) := by
  rw [popVar, popMean, ← card_univ, sum_sq_sub_mean]

omit [Fintype ι] in
private lemma sampleVar_eq (y : ι → ℝ) (S : Finset ι) :
    sampleVar y S = (∑ i ∈ S, y i ^ 2 - (∑ i ∈ S, y i) ^ 2 / S.card) / ((S.card : ℝ) - 1) := by
  rw [sampleVar, sampleMean, sum_sq_sub_mean]

/-- The sample variance is unbiased for the population variance under sampling without
replacement of `m ≥ 2` units. -/
private lemma randExp_sampleVar {m : ℕ} (hm : 2 ≤ m) (hmN : m ≤ Fintype.card ι) (y : ι → ℝ) :
    randExp m (sampleVar y) = popVar y := by
  have hN : 2 ≤ Fintype.card ι := hm.trans hmN
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have h1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (m : ℝ) ≠ 0 := by linarith
  rw [randExp_congr (g := fun S => (1 / ((m : ℝ) - 1)) * (∑ i ∈ S, y i ^ 2) +
      (-(1 / ((m : ℝ) - 1) / m)) * (∑ i ∈ S, y i) ^ 2) fun S hS => by
        rw [sampleVar_eq, hS]; field_simp; ring]
  rw [randExp_add, randExp_smul, randExp_smul, randExp_sum_mem hmN (by omega),
    randExp_sq_sum_mem hmN hN, popVar_eq]
  have h3 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have h4 : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-- On a treated set of size `n₁`, the difference in means is a sample total minus a constant. -/
private lemma diffInMeans_eq [DecidableEq ι] {n₁ : ℕ} (y₀ y₁ : ι → ℝ) {S : Finset ι}
    (hS : S.card = n₁) :
    diffInMeans y₀ y₁ S = ∑ i ∈ S, (y₁ i / n₁ + y₀ i / ((Fintype.card ι : ℝ) - n₁)) -
      (∑ i, y₀ i) / ((Fintype.card ι : ℝ) - n₁) := by
  have hc : ((Sᶜ).card : ℝ) = (Fintype.card ι : ℝ) - n₁ := by
    rw [card_compl, ← hS, Nat.cast_sub (card_le_univ S)]
  rw [diffInMeans, sampleMean, sampleMean, hc, hS, sum_add_distrib, ← sum_div, ← sum_div,
    ← sum_compl_add_sum S y₀]
  ring

/-- The population variance is nonnegative, and zero exactly for a constant population
(at least two units). -/
private lemma popVar_nonneg_and_eq_zero_iff (hN : 2 ≤ Fintype.card ι) (y : ι → ℝ) :
    0 ≤ popVar y ∧ (popVar y = 0 ↔ ∃ c, ∀ i, y i = c) := by
  have hN' : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
  have hsq : 0 ≤ ∑ i, (y i - popMean y) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  refine ⟨div_nonneg hsq hN'.le, ?_⟩
  rw [popVar, div_eq_zero_iff, or_iff_left hN'.ne',
    sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _]
  constructor
  · intro h
    exact ⟨popMean y, fun i => by simpa [sub_eq_zero] using h i (mem_univ i)⟩
  · rintro ⟨c, hc⟩ i _
    have hmean : popMean y = c := by
      have hN0 : (Fintype.card ι : ℝ) ≠ 0 := by linarith
      rw [popMean, sum_congr rfl fun i _ => hc i, sum_const, card_univ, nsmul_eq_mul]
      field_simp
    rw [hc i, hmean, sub_self]
    ring

/-- **Neyman (1923)**: under complete randomization with `n₁ ≥ 1` treated and `n₀ ≥ 1` control
units, the difference in means is unbiased for the finite-population average treatment
effect. -/
theorem randExp_diffInMeans [DecidableEq ι] (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 1 ≤ n₁)
    (h₀ : n₁ + 1 ≤ Fintype.card ι) :
    randExp n₁ (diffInMeans y₀ y₁) = ate y₀ y₁ := by
  have hn₁ : (1 : ℝ) ≤ n₁ := by exact_mod_cast h₁
  have hn₀ : (n₁ : ℝ) + 1 ≤ Fintype.card ι := by exact_mod_cast h₀
  rw [randExp_congr fun S hS => diffInMeans_eq y₀ y₁ hS]
  simp_rw [sub_eq_add_neg]
  rw [randExp_add, randExp_const (by omega), randExp_sum_mem (by omega) (by omega), ate,
    popMean, sum_add_distrib, ← sum_div, ← sum_div, sum_sub_distrib]
  obtain ⟨n₀, hn₀def⟩ : ∃ n₀ : ℝ, n₀ = (Fintype.card ι : ℝ) - n₁ := ⟨_, rfl⟩
  have hN : (Fintype.card ι : ℝ) = n₀ + n₁ := by rw [hn₀def]; ring
  have : n₀ ≠ 0 := by rw [hn₀def]; linarith
  have : n₀ + n₁ ≠ 0 := by rw [hn₀def]; linarith
  have : (n₁ : ℝ) ≠ 0 := by linarith
  rw [hN, add_neg_cancel_right]
  field_simp
  ring

/-- **Neyman (1923)**: the variance of the difference in means under complete randomization is
`S₁²/n₁ + S₀²/n₀ - S_τ²/N`, where `S_τ²` is the population variance of the unit-level effects
`τᵢ = y₁ᵢ - y₀ᵢ` and `n₀ = N - n₁`. -/
theorem randExp_sq_diffInMeans_sub_ate [DecidableEq ι] (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 1 ≤ n₁)
    (h₀ : n₁ + 1 ≤ Fintype.card ι) :
    randExp n₁ (fun S => (diffInMeans y₀ y₁ S - ate y₀ y₁) ^ 2) =
      popVar y₁ / n₁ + popVar y₀ / ((Fintype.card ι : ℝ) - n₁) -
        popVar (fun i => y₁ i - y₀ i) / Fintype.card ι := by
  have hn₁ : (1 : ℝ) ≤ n₁ := by exact_mod_cast h₁
  have hn₀ : (n₁ : ℝ) + 1 ≤ Fintype.card ι := by exact_mod_cast h₀
  set n₀ : ℝ := (Fintype.card ι : ℝ) - n₁ with hn₀def
  set a : ι → ℝ := fun i => y₁ i / n₁ + y₀ i / n₀
  set K : ℝ := (∑ i, y₀ i) / n₀ + ate y₀ y₁
  rw [randExp_congr (g := fun S => (∑ i ∈ S, a i) ^ 2 + (-2 * K) * ∑ i ∈ S, a i + K ^ 2)
    fun S hS => by rw [diffInMeans_eq y₀ y₁ hS]; ring]
  rw [randExp_add, randExp_add, randExp_smul, randExp_const (by omega),
    randExp_sq_sum_mem (by omega) (by omega), randExp_sum_mem (by omega) (by omega),
    popVar_eq, popVar_eq, popVar_eq]
  have hsa : ∑ i, a i = (∑ i, y₁ i) / n₁ + (∑ i, y₀ i) / n₀ := by
    simp only [a, sum_add_distrib, sum_div]
  have hsa2 : ∑ i, a i ^ 2 = (∑ i, y₁ i ^ 2) / n₁ ^ 2 + 2 * (∑ i, y₁ i * y₀ i) / (n₁ * n₀) +
      (∑ i, y₀ i ^ 2) / n₀ ^ 2 := by
    simp only [a, add_sq, sum_add_distrib, div_pow, sum_div, mul_sum]
    congr 1; congr 1
    refine sum_congr rfl fun i _ => by ring_nf
  have hd2 : ∑ i, (y₁ i - y₀ i) ^ 2 = ∑ i, y₁ i ^ 2 - 2 * ∑ i, y₁ i * y₀ i + ∑ i, y₀ i ^ 2 := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_sum]
    congr 2; refine sum_congr rfl fun i _ => by ring
  have hd : ∑ i, (y₁ i - y₀ i) = ∑ i, y₁ i - ∑ i, y₀ i := sum_sub_distrib _ _
  have hate : ate y₀ y₁ = (∑ i, y₁ i - ∑ i, y₀ i) / Fintype.card ι := by
    rw [ate, popMean, hd]
  simp only [K, hate, hsa, hsa2, hd2, hd]
  have : n₀ ≠ 0 := by rw [hn₀def]; linarith
  have : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have : (n₁ : ℝ) ≠ 0 := by linarith
  have hN : (Fintype.card ι : ℝ) = n₀ + n₁ := by rw [hn₀def]; ring
  have : n₀ + n₁ ≠ 0 := by rw [← hN]; linarith
  have : n₀ + n₁ - 1 ≠ 0 := by rw [← hN]; linarith
  rw [hN]
  field_simp
  ring

/-- The expectation of Neyman's variance estimator under complete randomization with at least
two treated and two control units is `S₁²/n₁ + S₀²/n₀` (the sample variances are unbiased for
the population variances under sampling without replacement). -/
theorem randExp_neymanVar [DecidableEq ι] (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 2 ≤ n₁)
    (h₀ : n₁ + 2 ≤ Fintype.card ι) :
    randExp n₁ (neymanVar y₀ y₁) =
      popVar y₁ / n₁ + popVar y₀ / ((Fintype.card ι : ℝ) - n₁) := by
  rw [randExp_congr (g := fun S => (1 / (n₁ : ℝ)) * sampleVar y₁ S +
      (1 / ((Fintype.card ι : ℝ) - n₁)) * sampleVar y₀ Sᶜ) fun S hS => by
        rw [neymanVar, card_compl, hS, Nat.cast_sub (by omega)]; ring]
  rw [randExp_add, randExp_smul, randExp_smul, randExp_compl (by omega),
    randExp_sampleVar h₁ (by omega), randExp_sampleVar (by omega) (by omega)]
  ring

/-- **Neyman's variance estimator is conservative**: its expectation under complete
randomization is at least the variance of the difference in means, with equality exactly when
the treatment effect `y₁ᵢ - y₀ᵢ` is the same for all units. -/
theorem randVar_le_randExp_neymanVar [DecidableEq ι] (y₀ y₁ : ι → ℝ) {n₁ : ℕ} (h₁ : 2 ≤ n₁)
    (h₀ : n₁ + 2 ≤ Fintype.card ι) :
    randExp n₁ (fun S => (diffInMeans y₀ y₁ S - ate y₀ y₁) ^ 2) ≤
        randExp n₁ (neymanVar y₀ y₁) ∧
      (randExp n₁ (fun S => (diffInMeans y₀ y₁ S - ate y₀ y₁) ^ 2) =
          randExp n₁ (neymanVar y₀ y₁) ↔ ∃ c, ∀ i, y₁ i - y₀ i = c) := by
  rw [randExp_sq_diffInMeans_sub_ate y₀ y₁ (by omega) (by omega), randExp_neymanVar y₀ y₁ h₁ h₀]
  obtain ⟨hnn, hiff⟩ := popVar_nonneg_and_eq_zero_iff (by omega) fun i => y₁ i - y₀ i
  have hN : (0 : ℝ) < Fintype.card ι := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast (show 2 ≤ Fintype.card ι by omega)
    linarith
  refine ⟨by linarith [div_nonneg hnn hN.le], ?_⟩
  rw [← hiff]
  constructor
  · intro h
    have : popVar (fun i => y₁ i - y₀ i) / Fintype.card ι = 0 := by linarith
    rcases div_eq_zero_iff.1 this with h' | h'
    · exact h'
    · exact absurd h' hN.ne'
  · intro h; rw [h, zero_div, sub_zero]

end Neyman

/-! ### Observed outcomes, propensity score and strong ignorability -/

section Propensity

variable {Ω β γ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The observed outcome: `Y₁` on the treated event `T`, `Y₀` off it (consistency). -/
noncomputable def observed (T : Set Ω) (Y₀ Y₁ : Ω → ℝ) : Ω → ℝ :=
  T.indicator Y₁ + Tᶜ.indicator Y₀

/-- The propensity of the event `T` given `W = w`, `P(T ∩ {W = w}) / P(W = w)`. Meaningful for
`P(W = w) > 0`; it is `0` (a junk value) when `P(W = w) = 0`. -/
noncomputable def propensity (μ : Measure Ω) (T : Set Ω) (W : Ω → β) (w : β) : ℝ :=
  μ.real (T ∩ W ⁻¹' {w}) / μ.real (W ⁻¹' {w})

/-- The event `T` is conditionally independent of `V` given `W`, stated through the values of
`W`: `P(T, V ∈ B, W = w) P(W = w) = P(T, W = w) P(V ∈ B, W = w)` for all measurable `B` and all
`w`. For a `W` with countably many values this is the conditional independence of the indicator
of `T` and `V` given `W`. -/
def CondIndepDiscrete [MeasurableSpace β] (μ : Measure Ω) (T : Set Ω) (V : Ω → β) (W : Ω → γ) :
    Prop :=
  ∀ B : Set β, MeasurableSet B → ∀ w : γ,
    μ.real (T ∩ V ⁻¹' B ∩ W ⁻¹' {w}) * μ.real (W ⁻¹' {w}) =
      μ.real (T ∩ W ⁻¹' {w}) * μ.real (V ⁻¹' B ∩ W ⁻¹' {w})

/-- **Strong ignorability** of the treatment `T` given `W` for the potential outcomes `V`
(Rosenbaum & Rubin 1983): `T ⊥ V | W` and overlap, `0 < P(T | W = w) < 1` for every value `w`
of positive probability. -/
def StronglyIgnorable [MeasurableSpace β] (μ : Measure Ω) (T : Set Ω) (V : Ω → β) (W : Ω → γ) :
    Prop :=
  CondIndepDiscrete μ T V W ∧
    ∀ w, μ (W ⁻¹' {w}) ≠ 0 → 0 < propensity μ T W w ∧ propensity μ T W w < 1

/-- Strong ignorability is inherited by measurable functions of the potential outcomes. -/
theorem StronglyIgnorable.comp [MeasurableSpace β] [MeasurableSpace γ] {T : Set Ω}
    {V : Ω → β} {δ : Type*} {W : Ω → δ} (h : StronglyIgnorable μ T V W) {g : β → γ}
    (hg : Measurable g) :
    StronglyIgnorable μ T (g ∘ V) W :=
  ⟨fun B hB w => h.1 (g ⁻¹' B) (hg hB) w, h.2⟩

variable {𝒳 : Type*} [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]

omit [Finite 𝒳] in
/-- Splitting an event along the finitely many values of `X` inside a level set of `f ∘ X`. -/
private lemma measureReal_inter_comp_preimage [IsFiniteMeasure μ] [Fintype 𝒳] [DecidableEq γ]
    {X : Ω → 𝒳} (hX : Measurable X) {A : Set Ω} (hA : MeasurableSet A) (f : 𝒳 → γ) (c : γ) :
    μ.real (A ∩ (fun ω => f (X ω)) ⁻¹' {c}) =
      ∑ x ∈ univ.filter (fun x => f x = c), μ.real (A ∩ X ⁻¹' {x}) := by
  have hset : A ∩ (fun ω => f (X ω)) ⁻¹' {c} =
      ⋃ x ∈ univ.filter (fun x => f x = c), A ∩ X ⁻¹' {x} := by
    ext ω; simp [eq_comm]
  rw [hset, measureReal_biUnion_finset]
  · intro x _ y _ hxy
    exact Set.disjoint_left.2 fun ω h1 h2 => hxy (h1.2.symm.trans h2.2)
  · exact fun x _ => hA.inter (hX (measurableSet_singleton x))

omit [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] in
private lemma measureReal_inter_preimage_eq_propensity_mul [IsFiniteMeasure μ] {T : Set Ω}
    {X : Ω → 𝒳} (x : 𝒳) :
    μ.real (T ∩ X ⁻¹' {x}) = propensity μ T X x * μ.real (X ⁻¹' {x}) := by
  by_cases h : μ.real (X ⁻¹' {x}) = 0
  · rw [h, mul_zero]
    exact le_antisymm (h ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
  · rw [propensity, div_mul_cancel₀ _ h]

/-- Summing a per-value proportionality over a level set of the propensity score. -/
private lemma measureReal_inter_level [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {S : Set Ω} (hS : MeasurableSet S)
    (h : ∀ x, μ.real (T ∩ S ∩ X ⁻¹' {x}) = propensity μ T X x * μ.real (S ∩ X ⁻¹' {x}))
    (c : ℝ) :
    μ.real (T ∩ S ∩ (fun ω => propensity μ T X (X ω)) ⁻¹' {c}) =
      c * μ.real (S ∩ (fun ω => propensity μ T X (X ω)) ⁻¹' {c}) := by
  have := Fintype.ofFinite 𝒳
  classical
  rw [measureReal_inter_comp_preimage hX (hT.inter hS),
    measureReal_inter_comp_preimage hX hS, mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [h x, (mem_filter.1 hx).2]

omit [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] in
private lemma setIntegral_inter_eq_propensity_mul [IsFiniteMeasure μ] {T : Set Ω}
    {X : Ω → 𝒳} {Y : Ω → ℝ} (hY : Measurable Y)
    (h : CondIndepDiscrete μ T Y X) (x : 𝒳) :
    ∫ ω in T ∩ X ⁻¹' {x}, Y ω ∂μ = propensity μ T X x * ∫ ω in X ⁻¹' {x}, Y ω ∂μ := by
  set A := X ⁻¹' {x}
  by_cases h0 : μ.real A = 0
  · have hA0 : μ A = 0 := (measureReal_eq_zero_iff).1 h0
    rw [Measure.restrict_eq_zero.2 hA0,
      Measure.restrict_eq_zero.2 (measure_mono_null Set.inter_subset_right hA0)]
    simp
  have he : 0 ≤ propensity μ T X x := div_nonneg measureReal_nonneg measureReal_nonneg
  have hmeas : (μ.restrict (T ∩ A)).map Y =
      ENNReal.ofReal (propensity μ T X x) • (μ.restrict A).map Y := by
    ext B hB
    rw [Measure.map_apply hY hB, Measure.smul_apply, Measure.map_apply hY hB,
      Measure.restrict_apply (hY hB), Measure.restrict_apply (hY hB), smul_eq_mul,
      ← ofReal_measureReal, ← ofReal_measureReal, ← ENNReal.ofReal_mul he]
    congr 1
    have key := h B hB x
    have hs1 : Y ⁻¹' B ∩ (T ∩ A) = T ∩ Y ⁻¹' B ∩ A := by
      ext; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
    rw [hs1, propensity, div_mul_eq_mul_div, eq_div_iff h0, key]
  calc ∫ ω in T ∩ A, Y ω ∂μ = ∫ y, y ∂((μ.restrict (T ∩ A)).map Y) :=
        (integral_map hY.aemeasurable aestronglyMeasurable_id).symm
    _ = propensity μ T X x * ∫ ω in A, Y ω ∂μ := by
        rw [hmeas, integral_smul_measure, ENNReal.toReal_ofReal he, smul_eq_mul]
        congr 1
        exact integral_map hY.aemeasurable aestronglyMeasurable_id

/-- Reweighting: if `∫_{S ∩ {X = x}} Y = p x ∫_{X = x} Y` for every `x`, and `p x ≠ 0` on
values of positive probability, then `1_S Y / p(X)` is integrable with integral `∫ Y`. -/
private lemma integral_indicator_div_eq {S : Set Ω} (hS : MeasurableSet S)
    {X : Ω → 𝒳} (hX : Measurable X) {Y : Ω → ℝ} (hYi : Integrable Y μ) (p : 𝒳 → ℝ)
    (hp : ∀ x, μ (X ⁻¹' {x}) ≠ 0 → p x ≠ 0)
    (hrel : ∀ x, ∫ ω in S ∩ X ⁻¹' {x}, Y ω ∂μ = p x * ∫ ω in X ⁻¹' {x}, Y ω ∂μ) :
    Integrable (S.indicator fun ω => Y ω / p (X ω)) μ ∧
      ∫ ω, S.indicator (fun ω => Y ω / p (X ω)) ω ∂μ = ∫ ω, Y ω ∂μ := by
  have := Fintype.ofFinite 𝒳
  have hU : (⋃ x, X ⁻¹' {x}) = Set.univ := by ext ω; simp
  have hA : ∀ x : 𝒳, MeasurableSet (X ⁻¹' {x}) := fun x => hX (measurableSet_singleton x)
  have hdisj : Pairwise (Function.onFun Disjoint fun x : 𝒳 => X ⁻¹' {x}) := fun x y hxy =>
    Set.disjoint_left.2 fun ω h1 h2 => hxy (h1.symm.trans h2)
  have heq : ∀ x, Set.EqOn (S.indicator fun ω => Y ω / p (X ω))
      (fun ω => S.indicator Y ω * (p x)⁻¹) (X ⁻¹' {x}) := by
    intro x ω hω
    have hω' : X ω = x := hω
    by_cases hS' : ω ∈ S <;> simp [hS', hω', div_eq_mul_inv]
  have hon : ∀ x, IntegrableOn (S.indicator fun ω => Y ω / p (X ω)) (X ⁻¹' {x}) μ := fun x =>
    (((hYi.indicator hS).mul_const (p x)⁻¹).integrableOn).congr_fun (heq x).symm (hA x)
  have hint : Integrable (S.indicator fun ω => Y ω / p (X ω)) μ := by
    rw [← integrableOn_univ, ← hU]
    exact integrableOn_finite_iUnion.2 hon
  refine ⟨hint, ?_⟩
  have hsplit : ∀ g : Ω → ℝ, (∀ x, IntegrableOn g (X ⁻¹' {x}) μ) →
      ∫ ω, g ω ∂μ = ∑ x, ∫ ω in X ⁻¹' {x}, g ω ∂μ := by
    intro g hg
    rw [← setIntegral_univ, ← hU, integral_iUnion_fintype hA hdisj hg]
  rw [hsplit _ hon, hsplit _ fun x => hYi.integrableOn]
  refine sum_congr rfl fun x _ => ?_
  rw [setIntegral_congr_fun (hA x) (heq x), integral_mul_const, setIntegral_indicator hS,
    Set.inter_comm, hrel x]
  by_cases h0 : μ (X ⁻¹' {x}) = 0
  · rw [Measure.restrict_eq_zero.2 h0]; simp
  · field_simp [hp x h0]

/-- **Rosenbaum & Rubin (1983), Theorem 1**: the propensity score `e(X) = P(T | X)` is a
balancing score: given `e(X)`, the treatment is conditionally independent of the covariate
`X`. -/
theorem condIndepDiscrete_propensity [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) :
    CondIndepDiscrete μ T X (fun ω => propensity μ T X (X ω)) := by
  intro B hB c
  have hper : ∀ x, μ.real (T ∩ X ⁻¹' B ∩ X ⁻¹' {x}) =
      propensity μ T X x * μ.real (X ⁻¹' B ∩ X ⁻¹' {x}) := by
    intro x
    by_cases hx : x ∈ B
    · have hs : X ⁻¹' B ∩ X ⁻¹' {x} = X ⁻¹' {x} :=
        Set.inter_eq_right.2 fun ω hω => by simpa [show X ω = x from hω] using hx
      rw [Set.inter_assoc, hs, measureReal_inter_preimage_eq_propensity_mul]
    · have hs : X ⁻¹' B ∩ X ⁻¹' {x} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω hω => hx (by simpa [show X ω = x from hω.2] using hω.1)
      rw [Set.inter_assoc, hs]; simp
  have huniv : ∀ x, μ.real (T ∩ Set.univ ∩ X ⁻¹' {x}) =
      propensity μ T X x * μ.real (Set.univ ∩ X ⁻¹' {x}) := by
    intro x; simpa using measureReal_inter_preimage_eq_propensity_mul x
  have h1 := measureReal_inter_level hT hX (hX hB) hper c
  have h2 := measureReal_inter_level hT hX MeasurableSet.univ huniv c
  simp only [Set.inter_univ, Set.univ_inter] at h2
  rw [h1, h2]; ring

/-- The propensity score is calibrated: among units with score `c` (an event of positive
probability), the proportion treated is `c`. -/
theorem propensity_propensity [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {c : ℝ}
    (hc : μ ((fun ω => propensity μ T X (X ω)) ⁻¹' {c}) ≠ 0) :
    propensity μ T (fun ω => propensity μ T X (X ω)) c = c := by
  have huniv : ∀ x, μ.real (T ∩ Set.univ ∩ X ⁻¹' {x}) =
      propensity μ T X x * μ.real (Set.univ ∩ X ⁻¹' {x}) := by
    intro x; simpa using measureReal_inter_preimage_eq_propensity_mul x
  have h2 := measureReal_inter_level hT hX MeasurableSet.univ huniv c
  simp only [Set.inter_univ, Set.univ_inter] at h2
  have hne : μ.real ((fun ω => propensity μ T X (X ω)) ⁻¹' {c}) ≠ 0 :=
    (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hc
  rw [propensity, h2, mul_div_cancel_right₀ _ hne]

/-- Summing a per-value proportionality over a level set of a function of the covariate. -/
private lemma measureReal_inter_comp_level [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {S : Set Ω} (hS : MeasurableSet S) {δ : Type*} (f : 𝒳 → δ)
    (w : δ) (c : ℝ) (h : ∀ x, f x = w → μ.real (T ∩ S ∩ X ⁻¹' {x}) = c * μ.real (S ∩ X ⁻¹' {x})) :
    μ.real (T ∩ S ∩ (fun ω => f (X ω)) ⁻¹' {w}) = c * μ.real (S ∩ (fun ω => f (X ω)) ⁻¹' {w}) := by
  have := Fintype.ofFinite 𝒳
  classical
  rw [measureReal_inter_comp_preimage hX (hT.inter hS),
    measureReal_inter_comp_preimage hX hS, mul_sum]
  exact sum_congr rfl fun x hx => h x (mem_filter.1 hx).2

omit [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] in
/-- A proportionality `P(T, X = x) = c P(X = x)` restricts to the events `{X ∈ B}`. -/
private lemma measureReal_inter_preimage_of [IsFiniteMeasure μ] {T : Set Ω} {X : Ω → 𝒳}
    {B : Set 𝒳} {x : 𝒳} {c : ℝ} (h : μ.real (T ∩ X ⁻¹' {x}) = c * μ.real (X ⁻¹' {x})) :
    μ.real (T ∩ X ⁻¹' B ∩ X ⁻¹' {x}) = c * μ.real (X ⁻¹' B ∩ X ⁻¹' {x}) := by
  by_cases hx : x ∈ B
  · have hs : X ⁻¹' B ∩ X ⁻¹' {x} = X ⁻¹' {x} :=
      Set.inter_eq_right.2 fun ω hω => by simpa [show X ω = x from hω] using hx
    rw [Set.inter_assoc, hs, h]
  · have hs : X ⁻¹' B ∩ X ⁻¹' {x} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω => hx (by simpa [show X ω = x from hω.2] using hω.1)
    rw [Set.inter_assoc, hs]; simp

/-- **Rosenbaum & Rubin (1983), Theorem 2**: a function `b(X)` of the covariate is a balancing
score (`T ⊥ X | b(X)`) if and only if it is finer than the propensity score: covariate values
of positive probability with the same `b` have the same propensity. (Theorem 1 is the case
`b = e`.) -/
theorem condIndepDiscrete_comp_iff [IsFiniteMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {δ : Type*} (b : 𝒳 → δ) :
    CondIndepDiscrete μ T X (fun ω => b (X ω)) ↔
      ∀ x x', μ (X ⁻¹' {x}) ≠ 0 → μ (X ⁻¹' {x'}) ≠ 0 → b x = b x' →
        propensity μ T X x = propensity μ T X x' := by
  have := Fintype.ofFinite 𝒳
  classical
  have hlev : ∀ w, MeasurableSet ((fun ω => b (X ω)) ⁻¹' {w}) := fun w =>
    hX (Set.toFinite (b ⁻¹' {w})).measurableSet
  constructor
  · intro h
    -- every covariate value of positive probability has the propensity of its `b`-level set
    have key : ∀ z, μ (X ⁻¹' {z}) ≠ 0 →
        propensity μ T X z = μ.real (T ∩ (fun ω => b (X ω)) ⁻¹' {b z}) /
          μ.real ((fun ω => b (X ω)) ⁻¹' {b z}) := by
      intro z hz
      have hsub : X ⁻¹' {z} ⊆ (fun ω => b (X ω)) ⁻¹' {b z} := fun ω hω => by
        simp [show X ω = z from hω]
      have hk := h {z} (measurableSet_singleton z) (b z)
      rw [Set.inter_assoc, Set.inter_eq_left.2 hsub] at hk
      have hz' : μ.real (X ⁻¹' {z}) ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hz
      have hW : μ.real ((fun ω => b (X ω)) ⁻¹' {b z}) ≠ 0 :=
        (measureReal_ne_zero_iff (measure_ne_top _ _)).2 fun h0 => hz (measure_mono_null hsub h0)
      rw [propensity, div_eq_div_iff hz' hW, hk]
    intro x x' hx hx' hb
    rw [key x hx, key x' hx', hb]
  · intro h B hB w
    by_cases hex : ∃ x₀, b x₀ = w ∧ μ (X ⁻¹' {x₀}) ≠ 0
    · obtain ⟨x₀, hbx₀, hx₀⟩ := hex
      have hper : ∀ x, b x = w →
          μ.real (T ∩ X ⁻¹' {x}) = propensity μ T X x₀ * μ.real (X ⁻¹' {x}) := by
        intro x hbx
        by_cases hx : μ (X ⁻¹' {x}) = 0
        · have h0 : μ.real (X ⁻¹' {x}) = 0 := by simp [measureReal_def, hx]
          rw [measureReal_inter_preimage_eq_propensity_mul, h0, mul_zero, mul_zero]
        · rw [measureReal_inter_preimage_eq_propensity_mul,
            h x x₀ hx hx₀ (hbx.trans hbx₀.symm)]
      have h1 := measureReal_inter_comp_level hT hX (hX hB) b w (propensity μ T X x₀)
        fun x hbx => measureReal_inter_preimage_of (hper x hbx)
      have h2 := measureReal_inter_comp_level hT hX MeasurableSet.univ b w (propensity μ T X x₀)
        fun x hbx => by simpa using hper x hbx
      simp only [Set.inter_univ, Set.univ_inter] at h2
      rw [h1, h2]
      ring
    · push Not at hex
      have hW : μ.real ((fun ω => b (X ω)) ⁻¹' {w}) = 0 := by
        have hsum := measureReal_inter_comp_preimage (μ := μ) hX MeasurableSet.univ b w
        simp only [Set.univ_inter] at hsum
        rw [hsum]
        exact sum_eq_zero fun x hx => by
          simp [measureReal_def, hex x (mem_filter.1 hx).2]
      have hsub : μ.real (X ⁻¹' B ∩ (fun ω => b (X ω)) ⁻¹' {w}) = 0 :=
        le_antisymm (hW ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
      rw [hW, hsub, mul_zero, mul_zero]

omit [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] in
/-- Conditional independence given `X`, value by value:
`P(T, V ∈ B, X = x) = e(x) P(V ∈ B, X = x)`. -/
private lemma measureReal_inter_eq_propensity_mul_of_condIndep [IsFiniteMeasure μ]
    [MeasurableSpace β] {T : Set Ω} {V : Ω → β} {X : Ω → 𝒳} (h : CondIndepDiscrete μ T V X)
    {B : Set β} (hB : MeasurableSet B) (x : 𝒳) :
    μ.real (T ∩ V ⁻¹' B ∩ X ⁻¹' {x}) = propensity μ T X x * μ.real (V ⁻¹' B ∩ X ⁻¹' {x}) := by
  by_cases h0 : μ.real (X ⁻¹' {x}) = 0
  · have h1 : μ.real (T ∩ V ⁻¹' B ∩ X ⁻¹' {x}) = 0 :=
      le_antisymm (h0 ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
    have h2 : μ.real (V ⁻¹' B ∩ X ⁻¹' {x}) = 0 :=
      le_antisymm (h0 ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
    rw [h1, h2, mul_zero]
  · rw [propensity, div_mul_eq_mul_div, eq_div_iff h0, h B hB x]

/-- **Rosenbaum & Rubin (1983), Theorem 3**: if treatment assignment is strongly ignorable given
the covariate `X`, it is strongly ignorable given any balancing score `b(X)`. -/
theorem StronglyIgnorable.comp_of_balancing [IsFiniteMeasure μ] [MeasurableSpace β] {T : Set Ω}
    (hT : MeasurableSet T) {V : Ω → β} (hV : Measurable V) {X : Ω → 𝒳} (hX : Measurable X)
    {δ : Type*} (b : 𝒳 → δ) (hb : CondIndepDiscrete μ T X (fun ω => b (X ω)))
    (h : StronglyIgnorable μ T V X) :
    StronglyIgnorable μ T V (fun ω => b (X ω)) := by
  have := Fintype.ofFinite 𝒳
  classical
  have hfine := (condIndepDiscrete_comp_iff hT hX b).1 hb
  -- the total mass of a `b`-level set
  have hWsum : ∀ w, μ.real ((fun ω => b (X ω)) ⁻¹' {w}) =
      ∑ x ∈ univ.filter (fun x => b x = w), μ.real (X ⁻¹' {x}) := fun w => by
    simpa using measureReal_inter_comp_preimage (μ := μ) hX MeasurableSet.univ b w
  -- on a level set of positive mass, the propensity takes a single value `c`
  have hlevel : ∀ w, μ ((fun ω => b (X ω)) ⁻¹' {w}) ≠ 0 → ∃ x₀, b x₀ = w ∧
      μ (X ⁻¹' {x₀}) ≠ 0 ∧ ∀ (S : Set Ω), MeasurableSet S →
        (∀ x, μ.real (T ∩ S ∩ X ⁻¹' {x}) = propensity μ T X x * μ.real (S ∩ X ⁻¹' {x})) →
        μ.real (T ∩ S ∩ (fun ω => b (X ω)) ⁻¹' {w}) =
          propensity μ T X x₀ * μ.real (S ∩ (fun ω => b (X ω)) ⁻¹' {w}) := by
    intro w hw
    have hne : μ.real ((fun ω => b (X ω)) ⁻¹' {w}) ≠ 0 :=
      (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hw
    rw [hWsum] at hne
    obtain ⟨x₀, hx₀, hx₀0⟩ := exists_ne_zero_of_sum_ne_zero hne
    have hx₀μ : μ (X ⁻¹' {x₀}) ≠ 0 := fun h0 => hx₀0 (by simp [measureReal_def, h0])
    refine ⟨x₀, (mem_filter.1 hx₀).2, hx₀μ, fun S hS hS' => ?_⟩
    refine measureReal_inter_comp_level hT hX hS b w _ fun x hbx => ?_
    rw [hS' x]
    by_cases hx : μ (X ⁻¹' {x}) = 0
    · have h0 : μ.real (S ∩ X ⁻¹' {x}) = 0 :=
        le_antisymm ((show μ.real (X ⁻¹' {x}) = 0 by simp [measureReal_def, hx]) ▸
          measureReal_mono Set.inter_subset_right) measureReal_nonneg
      rw [h0, mul_zero, mul_zero]
    · rw [hfine x x₀ hx hx₀μ (hbx.trans (mem_filter.1 hx₀).2.symm)]
  have huniv : ∀ x, μ.real (T ∩ Set.univ ∩ X ⁻¹' {x}) =
      propensity μ T X x * μ.real (Set.univ ∩ X ⁻¹' {x}) := fun x => by
    simpa using measureReal_inter_preimage_eq_propensity_mul x
  refine ⟨fun B hB w => ?_, fun w hw => ?_⟩
  · by_cases hw : μ ((fun ω => b (X ω)) ⁻¹' {w}) = 0
    · have hW : μ.real ((fun ω => b (X ω)) ⁻¹' {w}) = 0 := by simp [measureReal_def, hw]
      have hsub : μ.real (V ⁻¹' B ∩ (fun ω => b (X ω)) ⁻¹' {w}) = 0 :=
        le_antisymm (hW ▸ measureReal_mono Set.inter_subset_right) measureReal_nonneg
      rw [hW, hsub, mul_zero, mul_zero]
    · obtain ⟨x₀, -, -, hc⟩ := hlevel w hw
      have h1 := hc _ (hV hB) (measureReal_inter_eq_propensity_mul_of_condIndep h.1 hB)
      have h2 := hc _ MeasurableSet.univ huniv
      simp only [Set.inter_univ, Set.univ_inter] at h2
      rw [h1, h2]; ring
  · obtain ⟨x₀, -, hx₀μ, hc⟩ := hlevel w hw
    have h2 := hc _ MeasurableSet.univ huniv
    simp only [Set.inter_univ, Set.univ_inter] at h2
    have hne : μ.real ((fun ω => b (X ω)) ⁻¹' {w}) ≠ 0 :=
      (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hw
    rw [propensity, h2, mul_div_cancel_right₀ _ hne]
    exact h.2 x₀ hx₀μ

/-- **Rosenbaum & Rubin (1983), Theorem 3** for the propensity score: if treatment assignment
is strongly ignorable given the covariate `X`, it is strongly ignorable given `e(X)`. -/
theorem stronglyIgnorable_propensity [IsFiniteMeasure μ] [MeasurableSpace β] {T : Set Ω}
    (hT : MeasurableSet T) {V : Ω → β} (hV : Measurable V) {X : Ω → 𝒳} (hX : Measurable X)
    (h : StronglyIgnorable μ T V X) :
    StronglyIgnorable μ T V (fun ω => propensity μ T X (X ω)) :=
  h.comp_of_balancing hT hV hX (propensity μ T X) (condIndepDiscrete_propensity hT hX)

private lemma ipw_treated [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₁ : Measurable Y₁) (hY₁i : Integrable Y₁ μ) (h : StronglyIgnorable μ T Y₁ X) :
    Integrable (T.indicator fun ω => observed T Y₀ Y₁ ω / propensity μ T X (X ω)) μ ∧
    ∫ ω, T.indicator (fun ω => observed T Y₀ Y₁ ω / propensity μ T X (X ω)) ω ∂μ =
      ∫ ω, Y₁ ω ∂μ := by
  have hobs : T.indicator (fun ω => observed T Y₀ Y₁ ω / propensity μ T X (X ω)) =
      T.indicator (fun ω => Y₁ ω / propensity μ T X (X ω)) := by
    refine Set.indicator_congr fun ω hω => ?_
    simp [observed, hω]
  rw [hobs]
  exact integral_indicator_div_eq hT hX hY₁i _ (fun x hx => (h.2 x hx).1.ne')
    (setIntegral_inter_eq_propensity_mul hY₁ h.1)

private lemma ipw_control [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Measurable Y₀) (hY₀i : Integrable Y₀ μ) (h : StronglyIgnorable μ T Y₀ X) :
    Integrable (Tᶜ.indicator fun ω => observed T Y₀ Y₁ ω / (1 - propensity μ T X (X ω))) μ ∧
    ∫ ω, Tᶜ.indicator (fun ω => observed T Y₀ Y₁ ω / (1 - propensity μ T X (X ω))) ω ∂μ =
      ∫ ω, Y₀ ω ∂μ := by
  have hobs : Tᶜ.indicator (fun ω => observed T Y₀ Y₁ ω / (1 - propensity μ T X (X ω))) =
      Tᶜ.indicator (fun ω => Y₀ ω / (1 - propensity μ T X (X ω))) := by
    refine Set.indicator_congr fun ω hω => ?_
    simp [observed, Set.notMem_of_mem_compl hω, hω]
  rw [hobs]
  refine integral_indicator_div_eq hT.compl hX hY₀i (fun x => 1 - propensity μ T X x)
    (fun x hx => (sub_pos.2 (h.2 x hx).2).ne') fun x => ?_
  have hsplit := integral_inter_add_sdiff (μ := μ) (f := Y₀) (s := X ⁻¹' {x}) hT
    hY₀i.integrableOn
  have hc : Tᶜ ∩ X ⁻¹' {x} = X ⁻¹' {x} \ T := by ext; simp [and_comm]
  rw [Set.inter_comm, setIntegral_inter_eq_propensity_mul hY₀ h.1] at hsplit
  rw [hc]
  linear_combination hsplit

/-- **Inverse probability weighting** (Horvitz & Thompson 1952; Rosenbaum 1987): under
strong ignorability of `T` given a finitely-valued covariate `X` for the treated potential
outcome `Y₁`, `E[1_T Y / e(X)] = E[Y₁]`, where `Y` is the observed outcome. -/
theorem integral_ipw_treated [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₁ : Measurable Y₁)
    (hY₁i : Integrable Y₁ μ) (h : StronglyIgnorable μ T Y₁ X) :
    ∫ ω, T.indicator (fun ω => observed T Y₀ Y₁ ω / propensity μ T X (X ω)) ω ∂μ =
      ∫ ω, Y₁ ω ∂μ :=
  (ipw_treated hT hX hY₁ hY₁i h).2

/-- **Inverse probability weighting**, control arm: under strong ignorability of `T` given `X`
for `Y₀`, `E[1_{Tᶜ} Y / (1 - e(X))] = E[Y₀]`. -/
theorem integral_ipw_control [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀)
    (hY₀i : Integrable Y₀ μ) (h : StronglyIgnorable μ T Y₀ X) :
    ∫ ω, Tᶜ.indicator (fun ω => observed T Y₀ Y₁ ω / (1 - propensity μ T X (X ω))) ω ∂μ =
      ∫ ω, Y₀ ω ∂μ :=
  (ipw_control hT hX hY₀ hY₀i h).2

/-- **Identification of the average treatment effect by inverse probability weighting**: under
strong ignorability of `T` given a finitely-valued `X` for the pair `(Y₀, Y₁)`,
`E[1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X))] = E[Y₁ - Y₀]`. -/
theorem integral_ipw_ate [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T)
    {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ} (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁)
    (hY₀i : Integrable Y₀ μ) (hY₁i : Integrable Y₁ μ)
    (h : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) X) :
    ∫ ω, (T.indicator (fun ω => observed T Y₀ Y₁ ω / propensity μ T X (X ω)) ω -
        Tᶜ.indicator (fun ω => observed T Y₀ Y₁ ω / (1 - propensity μ T X (X ω))) ω) ∂μ =
      ∫ ω, (Y₁ ω - Y₀ ω) ∂μ := by
  obtain ⟨h1i, h1⟩ := ipw_treated (Y₀ := Y₀) hT hX hY₁ hY₁i (h.comp measurable_snd)
  obtain ⟨h0i, h0⟩ := ipw_control (Y₁ := Y₁) hT hX hY₀ hY₀i (h.comp measurable_fst)
  rw [integral_sub h1i h0i, h1, h0, integral_sub hY₁i hY₀i]

end Propensity

/-! ### Inverse probability weighting with a general covariate -/

section IPWGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Inverse probability weighting with a general covariate**: let the covariate information be
a sub-σ-algebra `m` (for example the one generated by `X`), and `e = P(T | m)` the propensity
score. If `Y₁` is integrable, the treatment is mean-ignorable for `Y₁`,
`E[1_T Y₁ | m] = e E[Y₁ | m]` (implied by `Y₁ ⊥ T | m`), and overlap holds in the strong form
`e ≥ ε > 0`, then `E[1_T Y / e] = E[Y₁]` for the observed outcome `Y`. -/
theorem integral_ipw_treated_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet[mΩ] T) {Y₀ Y₁ : Ω → ℝ}
    (hY₁ : Integrable Y₁ μ)
    (hign : μ[T.indicator Y₁ | m] =ᵐ[μ] fun ω => μ[T.indicator 1 | m] ω * μ[Y₁ | m] ω)
    {ε : ℝ} (hε : 0 < ε) (hov : ∀ᵐ ω ∂μ, ε ≤ μ[T.indicator 1 | m] ω) :
    ∫ ω, T.indicator (fun ω => observed T Y₀ Y₁ ω / μ[T.indicator 1 | m] ω) ω ∂μ =
      ∫ ω, Y₁ ω ∂μ := by
  set e : Ω → ℝ := μ[T.indicator 1 | m]
  have he : StronglyMeasurable[m] (fun ω => (e ω)⁻¹) :=
    (stronglyMeasurable_condExp.measurable.inv).stronglyMeasurable
  have hg : Integrable (T.indicator Y₁) μ := hY₁.indicator hT
  have hpt : T.indicator (fun ω => observed T Y₀ Y₁ ω / e ω) =
      (fun ω => (e ω)⁻¹) * T.indicator Y₁ := by
    funext ω
    by_cases hω : ω ∈ T <;> simp [observed, hω, div_eq_inv_mul]
  have hbdd : ∀ᵐ ω ∂μ, ‖(e ω)⁻¹‖ ≤ ε⁻¹ := hov.mono fun ω hω => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hε.trans_le hω)]
    exact inv_anti₀ hε hω
  have hint : Integrable ((fun ω => (e ω)⁻¹) * T.indicator Y₁) μ :=
    hg.bdd_mul (he.mono hm).aestronglyMeasurable hbdd
  rw [hpt, ← integral_condExp hm]
  calc ∫ ω, (μ[(fun ω => (e ω)⁻¹) * T.indicator Y₁ | m]) ω ∂μ
      = ∫ ω, μ[Y₁ | m] ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [condExp_mul_of_stronglyMeasurable_left he hint hg, hign, hov]
          with ω h1 h2 h3
        rw [h1, Pi.mul_apply, h2, ← mul_assoc, inv_mul_cancel₀ (hε.trans_le h3).ne', one_mul]
    _ = ∫ ω, Y₁ ω ∂μ := integral_condExp hm

end IPWGeneral

end MathlibExt.Probability.Causality
