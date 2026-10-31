/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The multinomial distribution

Throw `N` balls independently into the cells of a finite type `ι`, a ball landing in cell `i`
with probability `p i`. The vector of cell counts `x : ι → ℕ` has the multinomial law

`P(x) = N! / ∏ᵢ xᵢ! · ∏ᵢ p i ^ xᵢ` for `∑ᵢ xᵢ = N` (and `0` otherwise).

## Main definitions

* `ProbabilityTheory.multinomialReal N p x`: the real-valued mass function.
* `ProbabilityTheory.multinomial N p hp₀ hp₁`: the multinomial law as a `PMF (ι → ℕ)`, for a
  probability vector `p`.

## Main results

* `sum_multinomialReal`: normalization (the multinomial theorem).
* `sum_mul_multinomialReal`: the mean `E Xᵢ = N pᵢ`.
* `sum_mul_mul_multinomialReal_of_ne`, `sum_mul_sub_one_multinomialReal`: the second factorial
  moments `E[Xᵢ Xⱼ] = N (N - 1) pᵢ pⱼ` (`i ≠ j`) and `E[Xᵢ (Xᵢ - 1)] = N (N - 1) pᵢ²`.
* `sum_covariance_multinomialReal`: the covariance `Cov(Xᵢ, Xⱼ) = N (δᵢⱼ pᵢ - pᵢ pⱼ)`.
* `cond_measureReal_eq_multinomialReal`: **Poisson conditioning**. Independent Poisson counts
  `Xᵢ ~ Po(λᵢ)` conditioned on their total `∑ᵢ Xᵢ = N` are multinomial with
  `pᵢ = λᵢ / ∑ⱼ λⱼ`.
* `cond_measureReal_eq_binomial`: the two-cell case: for independent `X ~ Po(a)`,
  `Y ~ Po(b)`, the law of `X` given `X + Y = N` is `Bin(N, a / (a + b))`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
  Wiley (1968), §VI.9.
* N. L. Johnson, S. Kotz and N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley
  (1997), ch. 35 (multinomial distributions, including Poisson conditioning).
* F. W. Townes, S. C. Hicks, M. J. Aryee and R. A. Irizarry, *Feature selection and dimension
  reduction for single-cell RNA-Seq based on a multinomial model*, Genome Biol. 20 (2019), 295.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal unitInterval

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The multinomial mass function: the probability `N! / ∏ᵢ xᵢ! · ∏ᵢ pᵢ ^ xᵢ` that `N`
independent throws, landing in cell `i` with probability `pᵢ`, produce the cell counts `x`; it is
`0` unless `∑ᵢ xᵢ = N`. The formula is a polynomial in `p` and is defined for every real vector
`p`; it is a probability mass function exactly when `p` is a probability vector
(`0 ≤ pᵢ`, `∑ᵢ pᵢ = 1`), which the normalization theorems assume. -/
noncomputable def multinomialReal (N : ℕ) (p : ι → ℝ) (x : ι → ℕ) : ℝ :=
  if ∑ i, x i = N then (Nat.multinomial univ x : ℝ) * ∏ i, p i ^ x i else 0

/-- The multinomial mass function is nonnegative for a nonnegative vector `p`. -/
theorem multinomialReal_nonneg {N : ℕ} {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (x : ι → ℕ) :
    0 ≤ multinomialReal N p x := by
  unfold multinomialReal
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun i _ => pow_nonneg (hp i) _)
  · exact le_rfl

/-- The multinomial mass function vanishes off the simplex `∑ᵢ xᵢ = N`. -/
theorem multinomialReal_of_sum_ne {N : ℕ} {p : ι → ℝ} {x : ι → ℕ} (h : ∑ i, x i ≠ N) :
    multinomialReal N p x = 0 := by
  simp [multinomialReal, h]

/-- On the simplex the multinomial mass is `N! / ∏ᵢ xᵢ! · ∏ᵢ pᵢ ^ xᵢ`. -/
theorem multinomialReal_eq_factorial_div {N : ℕ} {p : ι → ℝ} {x : ι → ℕ}
    (h : ∑ i, x i = N) :
    multinomialReal N p x = (N.factorial : ℝ) / (∏ i, ((x i).factorial : ℝ)) * ∏ i, p i ^ x i := by
  have hspec : (∏ i, ((x i).factorial : ℝ)) * Nat.multinomial univ x = N.factorial := by
    rw [← h]
    exact_mod_cast Nat.multinomial_spec univ x
  have hne : (∏ i, ((x i).factorial : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [multinomialReal, ite_eq_left h, ← hspec, mul_div_cancel_left₀ _ hne]

section Support

variable [DecidableEq ι]

/-- The support of the multinomial mass function is the finite set `piAntidiag univ N` of count
vectors with total `N`. -/
theorem multinomialReal_of_notMem {N : ℕ} {p : ι → ℝ} {x : ι → ℕ}
    (h : x ∉ piAntidiag univ N) : multinomialReal N p x = 0 :=
  multinomialReal_of_sum_ne (by simpa using h)

/-- **Multinomial theorem.** `∑ₓ P(x) = (∑ᵢ pᵢ) ^ N` for every real vector `p`. -/
theorem sum_multinomialReal_eq_pow (N : ℕ) (p : ι → ℝ) :
    ∑ x ∈ piAntidiag univ N, multinomialReal N p x = (∑ i, p i) ^ N := by
  rw [sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun x hx => ?_
  rw [multinomialReal, ite_eq_left (mem_piAntidiag.1 hx).1]

/-- **Normalization.** For `∑ᵢ pᵢ = 1` the multinomial masses sum to one. -/
theorem sum_multinomialReal {N : ℕ} {p : ι → ℝ} (hp : ∑ i, p i = 1) :
    ∑ x ∈ piAntidiag univ N, multinomialReal N p x = 1 := by
  rw [sum_multinomialReal_eq_pow, hp, one_pow]

/-- The multinomial law of `N` throws with cell probabilities `p` (a probability vector), as a
probability mass function on count vectors `ι → ℕ`. -/
noncomputable def multinomial (N : ℕ) (p : ι → ℝ) (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) :
    PMF (ι → ℕ) :=
  PMF.ofFinset (fun x => ENNReal.ofReal (multinomialReal N p x)) (piAntidiag univ N)
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => multinomialReal_nonneg hp₀ x,
        sum_multinomialReal hp₁, ENNReal.ofReal_one])
    (fun x hx => by rw [multinomialReal_of_notMem hx, ENNReal.ofReal_zero])

/-- The mass of the multinomial PMF at `x` is `multinomialReal N p x`. -/
theorem multinomial_apply {N : ℕ} {p : ι → ℝ} (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    (x : ι → ℕ) : multinomial N p hp₀ hp₁ x = ENNReal.ofReal (multinomialReal N p x) :=
  rfl

/-- Adding one ball to cell `i`: `(yᵢ + 1) · multinomial(y + eᵢ) = (∑ⱼ yⱼ + 1) · multinomial(y)`. -/
private lemma mul_multinomial_add_single (y : ι → ℕ) (i : ι) :
    (y i + 1) * Nat.multinomial univ (y + Pi.single i 1) =
      (∑ j, y j + 1) * Nat.multinomial univ y := by
  have h1 := Nat.multinomial_spec univ (y + Pi.single i 1)
  have h2 := Nat.multinomial_spec univ y
  have hprod : ∏ j, ((y + Pi.single i 1 : ι → ℕ) j).factorial =
      (y i + 1) * ∏ j, (y j).factorial := by
    rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i, ← mul_assoc]
    congr 1
    · simp [Nat.factorial_succ]
    · refine prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := by simpa using hj
      simp [hji]
  have hsum : ∑ j, (y + Pi.single i 1 : ι → ℕ) j = ∑ j, y j + 1 := by
    simp [sum_add_distrib]
  rw [hprod, hsum, Nat.factorial_succ, ← h2] at h1
  have hP : 0 < ∏ j, (y j).factorial := prod_pos fun j _ => Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hP
  linarith [h1]

/-- **Shift identity.** Weighting by the count of cell `i` removes one throw:
`∑_{x : ∑ x = N + 1} xᵢ g(x) P_{N+1}(x) = (N + 1) pᵢ ∑_{y : ∑ y = N} g(y + eᵢ) P_N(y)`. -/
private lemma sum_mul_multinomialReal_succ (N : ℕ) (p : ι → ℝ) (i : ι) (g : (ι → ℕ) → ℝ) :
    ∑ x ∈ piAntidiag univ (N + 1), (x i : ℝ) * g x * multinomialReal (N + 1) p x =
      (N + 1) * p i * ∑ y ∈ piAntidiag univ N, g (y + Pi.single i 1) * multinomialReal N p y := by
  have hterm : ∀ y ∈ piAntidiag univ N,
      (N + 1) * p i * (g (y + Pi.single i 1) * multinomialReal N p y) =
        ((y + Pi.single i 1 : ι → ℕ) i : ℝ) * g (y + Pi.single i 1) *
          multinomialReal (N + 1) p (y + Pi.single i 1) := by
    intro y hy
    have hy' := (mem_piAntidiag.1 hy).1
    have hy1 : ∑ j, (y + Pi.single i 1 : ι → ℕ) j = N + 1 := by simp [sum_add_distrib, hy']
    rw [multinomialReal, ite_eq_left hy', multinomialReal, ite_eq_left hy1]
    have hm : ((y i + 1 : ℕ) : ℝ) * Nat.multinomial univ (y + Pi.single i 1) =
        ((N + 1 : ℕ) : ℝ) * Nat.multinomial univ y := by
      rw [← hy']
      exact_mod_cast mul_multinomial_add_single y i
    have hp : ∏ j, p j ^ (y + Pi.single i 1 : ι → ℕ) j = p i * ∏ j, p j ^ y j := by
      rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j => p j ^ y j)]
      have : ∏ j ∈ {i}ᶜ, p j ^ (y + Pi.single i 1 : ι → ℕ) j = ∏ j ∈ {i}ᶜ, p j ^ y j :=
        prod_congr rfl fun j hj => by
          have hji : j ≠ i := by simpa using hj
          simp [hji]
      rw [this]
      simp [pow_succ]
      ring
    rw [hp]
    simp only [Pi.add_apply, Pi.single_eq_same]
    push_cast at hm ⊢
    linear_combination (-(g (y + Pi.single i 1) * (p i * ∏ j, p j ^ y j))) * hm
  rw [mul_sum]
  symm
  refine sum_bij_ne_zero (fun y _ _ => y + Pi.single i 1) ?_ ?_ ?_ (fun y hy _ => hterm y hy)
  · intro y hy _
    simp only [mem_piAntidiag] at hy ⊢
    refine ⟨?_, fun j _ => mem_univ j⟩
    simp [sum_add_distrib, hy.1]
  · intro y _ _ z _ _ h
    funext j
    have := congrFun h j
    simpa using this
  · intro x hx hne
    have hxi : x i ≠ 0 := by
      intro h0
      apply hne
      simp [h0]
    set y : ι → ℕ := fun j => x j - (Pi.single i 1 : ι → ℕ) j with hy_def
    have hadd : y + Pi.single i 1 = x := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [y]; omega
      · simp [y, Pi.single_apply, hj]
    have hyN : y ∈ piAntidiag univ N := by
      simp only [mem_piAntidiag] at hx ⊢
      refine ⟨?_, fun j _ => mem_univ j⟩
      have hs : univ.sum y + 1 = univ.sum x := by
        conv_rhs => rw [← hadd]
        simp [sum_add_distrib]
      have hx1 : univ.sum x = N + 1 := hx.1
      omega
    refine ⟨y, hyN, ?_, hadd⟩
    rw [hterm y hyN, hadd]
    exact hne

/-- **Mean, polynomial form.** `∑ₓ xᵢ P(x) = N pᵢ (∑ⱼ pⱼ) ^ (N - 1)` for every real vector `p`. -/
theorem sum_mul_multinomialReal_eq (N : ℕ) (p : ι → ℝ) (i : ι) :
    ∑ x ∈ piAntidiag univ N, (x i : ℝ) * multinomialReal N p x =
      N * p i * (∑ j, p j) ^ (N - 1) := by
  rcases N with _ | N
  · simp
  · have h := sum_mul_multinomialReal_succ N p i (fun _ => 1)
    simp only [mul_one, one_mul] at h
    rw [h, sum_multinomialReal_eq_pow]
    push_cast
    simp

/-- **Second factorial moment, polynomial form.** For `i ≠ j`,
`∑ₓ xᵢ xⱼ P(x) = N (N - 1) pᵢ pⱼ (∑ₗ pₗ) ^ (N - 2)` for every real vector `p`. -/
theorem sum_mul_mul_multinomialReal_of_ne_eq (N : ℕ) (p : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    ∑ x ∈ piAntidiag univ N, (x i : ℝ) * x j * multinomialReal N p x =
      N * (N - 1) * p i * p j * (∑ l, p l) ^ (N - 2) := by
  rcases N with _ | N
  · simp
  · rw [sum_mul_multinomialReal_succ N p i (fun x => (x j : ℝ))]
    have hji : j ≠ i := Ne.symm hij
    simp only [Pi.add_apply, Pi.single_apply, hji, ite_false, add_zero]
    rw [sum_mul_multinomialReal_eq N p j]
    push_cast
    ring

/-- **Second factorial moment, polynomial form.**
`∑ₓ xᵢ (xᵢ - 1) P(x) = N (N - 1) pᵢ² (∑ₗ pₗ) ^ (N - 2)` for every real vector `p`. -/
theorem sum_mul_sub_one_multinomialReal_eq (N : ℕ) (p : ι → ℝ) (i : ι) :
    ∑ x ∈ piAntidiag univ N, (x i : ℝ) * ((x i : ℝ) - 1) * multinomialReal N p x =
      N * (N - 1) * p i ^ 2 * (∑ l, p l) ^ (N - 2) := by
  rcases N with _ | N
  · simp
  · rw [sum_mul_multinomialReal_succ N p i (fun x => (x i : ℝ) - 1)]
    simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [sum_mul_multinomialReal_eq N p i]
    push_cast
    ring

/-- **Mean.** For `∑ⱼ pⱼ = 1`, `E Xᵢ = N pᵢ`. -/
theorem sum_mul_multinomialReal {N : ℕ} {p : ι → ℝ} (hp : ∑ i, p i = 1) (i : ι) :
    ∑ x ∈ piAntidiag univ N, (x i : ℝ) * multinomialReal N p x = N * p i := by
  rw [sum_mul_multinomialReal_eq, hp, one_pow, mul_one]

/-- **Mixed second moment.** For `∑ₗ pₗ = 1` and `i ≠ j`, `E[Xᵢ Xⱼ] = N (N - 1) pᵢ pⱼ`. -/
theorem sum_mul_mul_multinomialReal_of_ne {N : ℕ} {p : ι → ℝ} (hp : ∑ i, p i = 1) {i j : ι}
    (hij : i ≠ j) :
    ∑ x ∈ piAntidiag univ N, (x i : ℝ) * x j * multinomialReal N p x =
      N * (N - 1) * p i * p j := by
  rw [sum_mul_mul_multinomialReal_of_ne_eq N p hij, hp, one_pow, mul_one]

/-- **Second factorial moment.** For `∑ₗ pₗ = 1`, `E[Xᵢ (Xᵢ - 1)] = N (N - 1) pᵢ²`. -/
theorem sum_mul_sub_one_multinomialReal {N : ℕ} {p : ι → ℝ} (hp : ∑ i, p i = 1) (i : ι) :
    ∑ x ∈ piAntidiag univ N, (x i : ℝ) * ((x i : ℝ) - 1) * multinomialReal N p x =
      N * (N - 1) * p i ^ 2 := by
  rw [sum_mul_sub_one_multinomialReal_eq, hp, one_pow, mul_one]

/-- **Covariance.** For `∑ₗ pₗ = 1`,
`Cov(Xᵢ, Xⱼ) = ∑ₓ (xᵢ - N pᵢ) (xⱼ - N pⱼ) P(x) = N (δᵢⱼ pᵢ - pᵢ pⱼ)`; in particular
`Var Xᵢ = N pᵢ (1 - pᵢ)` and `Cov(Xᵢ, Xⱼ) = -N pᵢ pⱼ` for `i ≠ j`. -/
theorem sum_covariance_multinomialReal {N : ℕ} {p : ι → ℝ} (hp : ∑ i, p i = 1) (i j : ι) :
    ∑ x ∈ piAntidiag univ N,
        ((x i : ℝ) - N * p i) * ((x j : ℝ) - N * p j) * multinomialReal N p x =
      N * ((if i = j then p i else 0) - p i * p j) := by
  have h1 := sum_multinomialReal (N := N) hp
  have hi := sum_mul_multinomialReal (N := N) hp i
  have hj := sum_mul_multinomialReal (N := N) hp j
  by_cases hij : i = j
  · subst hij
    have h2 := sum_mul_sub_one_multinomialReal (N := N) hp i
    have e : ∀ x : ι → ℕ, ((x i : ℝ) - N * p i) * ((x i : ℝ) - N * p i) * multinomialReal N p x =
        (x i : ℝ) * ((x i : ℝ) - 1) * multinomialReal N p x +
          (1 - 2 * N * p i) * ((x i : ℝ) * multinomialReal N p x) +
          (N * p i) ^ 2 * multinomialReal N p x := fun x => by ring
    rw [sum_congr rfl fun x _ => e x, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
      h2, hi, h1, ite_eq_left rfl]
    ring
  · have h2 := sum_mul_mul_multinomialReal_of_ne (N := N) hp hij
    have e : ∀ x : ι → ℕ, ((x i : ℝ) - N * p i) * ((x j : ℝ) - N * p j) * multinomialReal N p x =
        (x i : ℝ) * x j * multinomialReal N p x - N * p j * ((x i : ℝ) * multinomialReal N p x) -
          N * p i * ((x j : ℝ) * multinomialReal N p x) +
          N * p i * (N * p j) * multinomialReal N p x := fun x => by ring
    rw [sum_congr rfl fun x _ => e x, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
      ← mul_sum, ← mul_sum, ← mul_sum, h2, hi, hj, h1, ite_eq_right hij]
    ring

end Support

section PoissonConditioning

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [Fintype ι] in
/-- The mass of a random variable with law `Po(r)` at `k`. -/
private lemma measureReal_eq_poisson {Z : Ω → ℕ} {r : ℝ≥0} (hZ : HasLaw Z (poissonMeasure r) μ)
    (k : ℕ) : μ.real {ω | Z ω = k} = Real.exp (-r) * r ^ k / k.factorial := by
  rw [hZ.measureReal_eq (p := (· = k)) (measurableSet_singleton k), Set.ofPred_eq_eq_singleton,
    poissonMeasure_real_singleton]

/-- A product of Poisson masses on the simplex `∑ᵢ yᵢ = N` is
`e^{-∑ r} / N! · multinomialReal N r y`. -/
private lemma prod_poisson_eq {r : ι → ℝ} {N : ℕ} {y : ι → ℕ} (hy : ∑ i, y i = N) :
    ∏ i, Real.exp (-r i) * r i ^ y i / (y i).factorial =
      Real.exp (-∑ i, r i) / N.factorial * multinomialReal N r y := by
  rw [multinomialReal_eq_factorial_div hy, prod_div_distrib, prod_mul_distrib, ← Real.exp_sum,
    sum_neg_distrib]
  have hN : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp

/-- **Poisson conditioning.** Let `Xᵢ ~ Po(λᵢ)`, `i ∈ ι`, be independent Poisson counts with
`∑ᵢ λᵢ > 0`. Given their total `∑ᵢ Xᵢ = N`, the count vector is multinomial with
`N` throws and cell probabilities `λᵢ / ∑ⱼ λⱼ`:
`P(X = x | ∑ᵢ Xᵢ = N) = multinomialReal N (λ / ∑ λ) x`. -/
theorem cond_measureReal_eq_multinomialReal {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hXm : ∀ i, Measurable (X i)) (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) μ)
    (hind : iIndepFun X μ) (hr : 0 < ∑ i, r i) (N : ℕ) (x : ι → ℕ) :
    (μ[|{ω | ∑ i, X i ω = N}]).real {ω | ∀ i, X i ω = x i} =
      multinomialReal N (fun i => (r i : ℝ) / ∑ j, (r j : ℝ)) x := by
  classical
  have hfin : IsFiniteMeasure μ := by
    cases isEmpty_or_nonempty ι with
    | inl h => simp at hr
    | inr h => exact (hX (Classical.arbitrary ι)).isFiniteMeasure
  set Λ : ℝ := ∑ j, (r j : ℝ) with hΛ
  have hΛpos : 0 < Λ := by rw [hΛ]; exact_mod_cast hr
  have hS : MeasurableSet {ω | ∑ i, X i ω = N} :=
    (Finset.measurable_sum univ fun i _ => hXm i) (measurableSet_singleton N)
  have hmeasA : ∀ y : ι → ℕ, MeasurableSet {ω | ∀ i, X i ω = y i} := fun y => by
    have : {ω | ∀ i, X i ω = y i} = ⋂ i, X i ⁻¹' {y i} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun i => hXm i (measurableSet_singleton _)
  -- joint mass of the count vector
  have hjoint : ∀ y : ι → ℕ, μ.real {ω | ∀ i, X i ω = y i} =
      ∏ i, Real.exp (-(r i : ℝ)) * (r i : ℝ) ^ y i / (y i).factorial := by
    intro y
    have h := hind.measure_inter_preimage_eq_mul univ (sets := fun i => {y i})
      (fun i _ => measurableSet_singleton _)
    have hset : (⋂ i ∈ (univ : Finset ι), X i ⁻¹' {y i}) = {ω | ∀ i, X i ω = y i} := by
      ext; simp
    rw [hset] at h
    rw [measureReal_def, h, ENNReal.toReal_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [← measureReal_eq_poisson (hX i) (y i)]
    rfl
  -- the event `∑ᵢ Xᵢ = N` as a disjoint union over the simplex
  have hSeq : {ω | ∑ i, X i ω = N} =
      ⋃ y ∈ piAntidiag (univ : Finset ι) N, {ω | ∀ i, X i ω = y i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_piAntidiag, exists_prop]
    constructor
    · intro h
      exact ⟨fun i => X i ω, ⟨h, fun i _ => mem_univ i⟩, fun i => rfl⟩
    · rintro ⟨y, ⟨hy, -⟩, hω⟩
      rw [← hy]
      exact sum_congr rfl fun i _ => hω i
  have hSreal : μ.real {ω | ∑ i, X i ω = N} =
      Real.exp (-Λ) / N.factorial * Λ ^ N := by
    rw [hSeq, measureReal_biUnion_finset]
    · rw [sum_congr rfl fun y hy => (hjoint y).trans (prod_poisson_eq (mem_piAntidiag.1 hy).1),
        ← mul_sum, sum_multinomialReal_eq_pow]
    · intro y _ z _ hyz
      exact Set.disjoint_left.2 fun ω hy hz => hyz (funext fun i => (hy i).symm.trans (hz i))
    · exact fun y _ => hmeasA y
  have hcond : (μ[|{ω | ∑ i, X i ω = N}]).real {ω | ∀ i, X i ω = x i} =
      (μ.real {ω | ∑ i, X i ω = N})⁻¹ *
        μ.real ({ω | ∑ i, X i ω = N} ∩ {ω | ∀ i, X i ω = x i}) := by
    simp only [measureReal_def, cond_apply hS, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [hcond, hSreal]
  by_cases hx : ∑ i, x i = N
  · have hset : {ω | ∑ i, X i ω = N} ∩ {ω | ∀ i, X i ω = x i} = {ω | ∀ i, X i ω = x i} := by
      refine Set.inter_eq_right.2 fun ω hω => ?_
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [← hx]
      exact sum_congr rfl fun i _ => hω i
    rw [hset, hjoint, prod_poisson_eq hx, multinomialReal_eq_factorial_div hx,
      multinomialReal_eq_factorial_div hx, ← hΛ]
    simp_rw [div_pow]
    rw [prod_div_distrib, prod_pow_eq_pow_sum, hx]
    have hN : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hE : Real.exp (-Λ) ≠ 0 := (Real.exp_pos _).ne'
    have hP : (∏ i, ((x i).factorial : ℝ)) ≠ 0 :=
      prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hΛN : Λ ^ N ≠ 0 := pow_ne_zero _ hΛpos.ne'
    field_simp
  · have hset : {ω | ∑ i, X i ω = N} ∩ {ω | ∀ i, X i ω = x i} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h hω
      exact hx (by rw [← h]; exact sum_congr rfl fun i _ => (hω i).symm)
    rw [hset, measureReal_empty, mul_zero, multinomialReal_of_sum_ne hx]

/-- **Poisson conditioning, two cells.** For independent `X ~ Po(a)` and `Y ~ Po(b)` with
`a + b > 0`, the law of `X` given `X + Y = N` is binomial `Bin(N, a / (a + b))`. -/
theorem cond_measureReal_eq_binomial {X Y : Ω → ℕ} {a b : ℝ≥0} (hab : 0 < a + b)
    (hXm : Measurable X) (hYm : Measurable Y) (hX : HasLaw X (poissonMeasure a) μ)
    (hY : HasLaw Y (poissonMeasure b) μ) (hXY : IndepFun X Y μ) (N k : ℕ) :
    (μ[|{ω | X ω + Y ω = N}]).real {ω | X ω = k} =
      (binomial N ⟨(a : ℝ) / (a + b), div_nonneg a.2 (add_nonneg a.2 b.2),
        div_le_one_of_le₀ (le_add_of_nonneg_right b.2) (add_nonneg a.2 b.2)⟩).real {k} := by
  have hab' : (0 : ℝ) < a + b := by exact_mod_cast hab
  have hS : MeasurableSet {ω | X ω + Y ω = N} := (hXm.add hYm) (measurableSet_singleton N)
  have hcond : (μ[|{ω | X ω + Y ω = N}]).real {ω | X ω = k} =
      (μ.real {ω | X ω + Y ω = N})⁻¹ * μ.real ({ω | X ω + Y ω = N} ∩ {ω | X ω = k}) := by
    simp only [measureReal_def, cond_apply hS, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hsum : μ.real {ω | X ω + Y ω = N} = Real.exp (-(a + b : ℝ)) * (a + b : ℝ) ^ N /
      N.factorial := by
    have h := measureReal_eq_poisson (hXY.hasLaw_add_poissonMeasure hX hY) N
    push_cast at h
    exact h
  rw [hcond, hsum, binomial_real_singleton]
  rcases le_or_gt k N with hk | hk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hset : {ω | X ω + Y ω = k + j} ∩ {ω | X ω = k} = {ω | X ω = k} ∩ {ω | Y ω = j} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      omega
    have hind : μ.real ({ω | X ω = k} ∩ {ω | Y ω = j}) =
        μ.real {ω | X ω = k} * μ.real {ω | Y ω = j} := by
      have := hXY.measure_inter_preimage_eq_mul {k} {j} (measurableSet_singleton k)
        (measurableSet_singleton j)
      simp only [measureReal_def]
      rw [← ENNReal.toReal_mul]
      exact congrArg ENNReal.toReal this
    rw [hset, hind, measureReal_eq_poisson hX, measureReal_eq_poisson hY,
      Nat.cast_choose ℝ (Nat.le_add_right k j), Nat.add_sub_cancel_left]
    have h1 : 1 - (a : ℝ) / (a + b) = b / (a + b) := by field_simp; ring
    rw [h1, Real.exp_neg (a + b : ℝ), Real.exp_add, Real.exp_neg, Real.exp_neg]
    have hk! : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hj! : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hN! : ((k + j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have ha : Real.exp a ≠ 0 := (Real.exp_pos _).ne'
    have hb : Real.exp b ≠ 0 := (Real.exp_pos _).ne'
    have hab0 : (a : ℝ) + b ≠ 0 := hab'.ne'
    field_simp
    rw [div_pow, div_pow, pow_add]
    field_simp
  · have hset : {ω | X ω + Y ω = N} ∩ {ω | X ω = k} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [hset, measureReal_empty, mul_zero, Nat.choose_eq_zero_of_lt hk]
    simp

end PoissonConditioning

end ProbabilityTheory
