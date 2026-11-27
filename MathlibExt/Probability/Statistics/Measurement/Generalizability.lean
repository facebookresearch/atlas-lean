/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Crossed person-by-item moment model: absolute and relative errors

For the balanced crossed decomposition `X p i = mu + P p + I i + e p i`
with the stated covariance structure, the absolute error of a person
mean has variance `(sigmaI2 + sigmae2) / m` and the relative error
(against the same sampled items) has variance `sigmae2 / m`, where
`m` is the number of items.

These are the absolute and relative error variances of
generalizability theory for a crossed person-by-item design with a
single observation per cell: in the notation of Brennan (2001),
*Generalizability Theory* (Springer), the relative error variance for
mean scores over `m = n_i` items is `sigma^2(delta) = sigma^2_e / n_i`
and the absolute error variance is
`sigma^2(Delta) = sigma^2_i / n_i + sigma^2_e / n_i`; see also
Cronbach, Gleser, Nanda, and Rajaratnam (1972), *The Dependability of
Behavioral Measurements* (Wiley). Here `Delta_p` (resp. `delta_p`) is
the realized absolute (resp. relative) error of person `p`'s mean: the
person mean minus the universe-score mean (resp. minus the mean
including the realized item main effects over the same sampled items),
so `Var[Delta_p]` and `Var[delta_p]` are the two error variances
above.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.Measurement

/-- Absolute error of a person in the crossed person-by-item model.

`Delta_p grandMean X P p` is the random variable
`fun ω => (1 / m) * ∑ i, X p i ω - (grandMean + P p ω)`, where
`m = Fintype.card Item`.  Under the decomposition
`X p i = grandMean + P p + I i + e p i` this equals the item mean plus
the residual mean for `p`; that equality is a consequence of the
model, not part of this definition. -/
noncomputable def Delta_p {Ω : Type*} {Person Item : Type*} [Fintype Item] [Nonempty Item]
    (grandMean : ℝ) (X : Person → Item → Ω → ℝ) (P : Person → Ω → ℝ)
    (p : Person) : Ω → ℝ :=
  fun ω => (1 / (Fintype.card Item : ℝ)) * ∑ i, X p i ω
    - (grandMean + P p ω)

/-- Relative error of a person in the crossed person-by-item model.

`delta_p grandMean X P I p` is the random variable
`fun ω => (1 / m) * ∑ i, X p i ω
  - (grandMean + P p ω + (1 / m) * ∑ i, I i ω)`,
where `m = Fintype.card Item`.  The subtracted item mean is the mean
over the same items that `p` saw.  Under the decomposition of `X`
this equals the residual mean for `p`; that equality is a
consequence of the model, not part of this definition. -/
noncomputable def delta_p {Ω : Type*} {Person Item : Type*} [Fintype Item] [Nonempty Item]
    (grandMean : ℝ) (X : Person → Item → Ω → ℝ) (P : Person → Ω → ℝ)
    (I : Item → Ω → ℝ) (p : Person) : Ω → ℝ :=
  fun ω => (1 / (Fintype.card Item : ℝ)) * ∑ i, X p i ω
    - (grandMean + P p ω
      + (1 / (Fintype.card Item : ℝ)) * ∑ i, I i ω)

/-- Variances of the absolute and relative errors for a fixed person.

This is the minimal core of `variance_absolute_relative_errors` for
a fixed `p`: only the decomposition of `X p i`, the item and residual
square-integrability facts, the item-item, residual-residual (at `p`),
and item-residual (at `p`) covariance hypotheses, and the positive
item count are needed.  In particular no person finiteness or
nonemptiness, person variance component, moments, reverse
cross-covariances, or nonnegativity hypotheses are used. -/
theorem variance_absolute_relative_errors_selected
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Person Item : Type*} [Fintype Item] [Nonempty Item] [DecidableEq Item]
    (grandMean : ℝ)
    (X : Person → Item → Ω → ℝ) (P : Person → Ω → ℝ)
    (I : Item → Ω → ℝ) (e : Person → Item → Ω → ℝ)
    (sigmaI2 sigmae2 : ℝ) (p : Person)
    (hX : ∀ i, X p i
      = fun ω => grandMean + P p ω + I i ω + e p i ω)
    (hI_mem : ∀ i, MemLp (I i) 2 μ)
    (he_mem : ∀ i, MemLp (e p i) 2 μ)
    (hI_cov : ∀ i j, cov[I i, I j; μ]
      = if i = j then sigmaI2 else 0)
    (he_cov : ∀ i j, cov[e p i, e p j; μ]
      = if i = j then sigmae2 else 0)
    (hIe_cov : ∀ i j, cov[I i, e p j; μ] = 0)
    (hm_pos : 0 < (Fintype.card Item : ℝ)) :
    Var[Delta_p grandMean X P p; μ]
        = (sigmaI2 + sigmae2) / (Fintype.card Item : ℝ)
      ∧ Var[delta_p grandMean X P I p; μ]
        = sigmae2 / (Fintype.card Item : ℝ) := by
  have hm_ne : (Fintype.card Item : ℝ) ≠ 0 := ne_of_gt hm_pos
  have hXw : ∀ (i : Item) (ω : Ω), X p i ω = grandMean + P p ω + I i ω + e p i ω := by
    intro i ω
    have h := hX i
    rw [h]
  have hDelta : Delta_p grandMean X P p
      = fun ω => (1 / (Fintype.card Item : ℝ)) * (∑ i, I i ω + ∑ i, e p i ω) := by
    funext ω
    unfold Delta_p
    simp_rw [hXw _ ω]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hdelta : delta_p grandMean X P I p
      = fun ω => (1 / (Fintype.card Item : ℝ)) * (∑ i, e p i ω) := by
    funext ω
    unfold delta_p
    simp_rw [hXw _ ω]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hA : MemLp (fun ω => ∑ i, I i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hI_mem i)
  have hB : MemLp (fun ω => ∑ i, e p i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => he_mem i)
  constructor
  · rw [hDelta, variance_const_mul, variance_fun_add hA hB]
    rw [variance_fun_sum (fun i => hI_mem i)]
    rw [variance_fun_sum (fun i => he_mem i)]
    rw [covariance_fun_sum_fun_sum (fun i => hI_mem i) (fun i => he_mem i)]
    simp_rw [hIe_cov]
    simp only [Finset.sum_const_zero]
    simp_rw [hI_cov]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp_rw [he_cov]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  · rw [hdelta, variance_const_mul, variance_fun_sum (fun i => he_mem i)]
    simp_rw [he_cov]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- Variances of the absolute and relative errors in the crossed
person-by-item moment model.

Persons and items are finite and nonempty; `m = Fintype.card Item`
is the common number of items per person, with `(m : ℝ) > 0`.
The score decomposition, centered square-integrable effects, the
three covariance kernels, all zero cross-block covariances (in both
orders), nonnegative variance components, and the positive item-count
denominator are all hypotheses.  The conclusions are

  `Var[Delta_p grandMean X P p; μ] = (sigmaI2 + sigmae2) / m` and
  `Var[delta_p grandMean X P I p; μ] = sigmae2 / m`. -/
theorem variance_absolute_relative_errors
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {Person Item : Type*} [Fintype Person] [Nonempty Person]
    [Fintype Item] [Nonempty Item] [DecidableEq Person] [DecidableEq Item]
    (grandMean : ℝ)
    (X : Person → Item → Ω → ℝ) (P : Person → Ω → ℝ)
    (I : Item → Ω → ℝ) (e : Person → Item → Ω → ℝ)
    (sigmaP2 sigmaI2 sigmae2 : ℝ) (p : Person)
    (hX : ∀ p i, X p i
      = fun ω => grandMean + P p ω + I i ω + e p i ω)
    (hP_mem : ∀ p, MemLp (P p) 2 μ)
    (hI_mem : ∀ i, MemLp (I i) 2 μ)
    (he_mem : ∀ p i, MemLp (e p i) 2 μ)
    (hP_mean : ∀ p, μ[P p] = 0)
    (hI_mean : ∀ i, μ[I i] = 0)
    (he_mean : ∀ p i, μ[e p i] = 0)
    (hP_cov : ∀ p q, cov[P p, P q; μ]
      = if p = q then sigmaP2 else 0)
    (hI_cov : ∀ i j, cov[I i, I j; μ]
      = if i = j then sigmaI2 else 0)
    (he_cov : ∀ p i q j, cov[e p i, e q j; μ]
      = if (p, i) = (q, j) then sigmae2 else 0)
    (hPI_cov : ∀ p i, cov[P p, I i; μ] = 0)
    (hIP_cov : ∀ i p, cov[I i, P p; μ] = 0)
    (hPe_cov : ∀ p q i, cov[P p, e q i; μ] = 0)
    (heP_cov : ∀ p i q, cov[e p i, P q; μ] = 0)
    (hIe_cov : ∀ i p j, cov[I i, e p j; μ] = 0)
    (heI_cov : ∀ p i j, cov[e p i, I j; μ] = 0)
    (hsigmaP2 : 0 ≤ sigmaP2) (hsigmaI2 : 0 ≤ sigmaI2)
    (hsigmae2 : 0 ≤ sigmae2)
    (hm_pos : 0 < (Fintype.card Item : ℝ)) :
    Var[Delta_p grandMean X P p; μ]
        = (sigmaI2 + sigmae2) / (Fintype.card Item : ℝ)
      ∧ Var[delta_p grandMean X P I p; μ]
        = sigmae2 / (Fintype.card Item : ℝ) := by
  have he_cov_p : ∀ i j : Item, cov[e p i, e p j; μ] = if i = j then sigmae2 else 0 := by
    intro i j
    rw [he_cov]
    simp
  exact variance_absolute_relative_errors_selected grandMean X P I e sigmaI2 sigmae2 p
    (fun i => hX p i) hI_mem (fun i => he_mem p i) hI_cov he_cov_p
    (fun i j => hIe_cov i p j) hm_pos
end MathlibExt.Probability.Statistics.Measurement
