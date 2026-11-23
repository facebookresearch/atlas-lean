/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.StdSimplexWeights

/-!
# Categorical distributions: maximum likelihood and Dirichlet MAP estimates

A categorical distribution on a finite set `α` is a point `θ` of Mathlib's standard simplex
`Convexity.StdSimplex ℝ α`, with probabilities `θ.weights a`. For observed counts `n : α → ℕ` the
likelihood of the observations is `∏ a, θ.weights a ^ n a`.

* **Maximum likelihood.** When the total count `N = ∑ b, n b` is positive, the likelihood is
  maximized by the normalized counts `n a / N` (`likelihood_le_mle`, `mle_apply`). When `N = 0`
  the likelihood is constant, every distribution maximizes it, and `mle` chooses the uniform
  distribution (`mle_of_sum_eq_zero`).
* **MAP under a Dirichlet prior.** For concentrations `conc ≥ 1`, the posterior kernel is
  maximized by `mapEstimate`, the normalization of the nonnegative pseudo-counts
  `n a + conc a - 1` (`posterior_le_mapEstimate`). When their sum is positive this is
  `(n a + conc a - 1) / ∑ b, (n b + conc b - 1)`; when all pseudo-counts are zero (no observations
  and all concentrations `1`) the posterior kernel is constant, every distribution is optimal, and
  `mapEstimate` chooses the uniform distribution. Without observations and with some
  concentration above `1`, the estimate is the normalized `conc - 1`, a mode of the prior kernel;
  for equal concentrations it is uniform.
* **Laplace smoothing.** With all concentrations `2` the MAP estimate is add-one smoothing
  `(n a + 1) / (N + K)`, where `K` is the number of categories (`laplace_apply`).

Mathlib has no Dirichlet distribution; MAP estimation only needs its density up to the
normalizing constant, `∏ θ a ^ (conc a - 1)` on the simplex (`dirichletKernel`).

Both optimality results follow from `Convexity.StdSimplex.prod_rpow_le_prod_rpow_normalizeWeights`
in `MathlibExt/Analysis/Convex/StdSimplexWeights.lean`: for real weights `a ≥ 0`,
`∏ θ i ^ a i ≤ ∏ (a i / ∑ a) ^ a i` for every probability vector `θ` (Gibbs' inequality in product
form, derived there from MathlibExt's log-sum inequality). The estimates are built with
`Convexity.StdSimplex.normalize` from the same file.

## Main definitions and results

* `mle`, `likelihood_le_mle`, `isMaxOn_likelihood`: the maximum likelihood estimate. For two
  categories and a positive number of trials this is the Bernoulli estimate `y / N` (Casella and
  Berger, *Statistical Inference*, Example 7.2.7; formalized as `bernoulli_isMLE` in
  `FormalizedTextbooks/CasellaBergerStatisticalInference`).
* `dirichletKernel conc θ = ∏ θ i ^ (conc i - 1)`: for positive concentrations, the Dirichlet
  density in the interior of the simplex up to its normalizing constant.
* `mapEstimate`, `isMaxOn_posterior`: for concentrations `conc ≥ 1`, the MAP estimate.
* `laplace`, `isMaxOn_posterior_laplace`: Laplace smoothing is the MAP estimate under the prior
  with all concentrations `2`.
-/

@[expose] public section

namespace Cslib.MachineLearning.Categorical

open Finset Convexity

variable {α : Type*} [Fintype α]

/-! ## Maximum likelihood -/

/-- The likelihood of observations with counts `n` under the categorical distribution `θ`. -/
noncomputable def likelihood (θ : StdSimplex ℝ α) (n : α → ℕ) : ℝ :=
  ∏ a, θ.weights a ^ n a

theorem likelihood_nonneg (θ : StdSimplex ℝ α) (n : α → ℕ) : 0 ≤ likelihood θ n :=
  prod_nonneg fun a _ => pow_nonneg (θ.nonneg a) _

/-- The maximum likelihood estimate: the normalized counts `n a / ∑ b, n b` when there is at least
one observation (`mle_apply`), and the uniform distribution otherwise (`mle_of_sum_eq_zero`). -/
noncomputable def mle [Nonempty α] (n : α → ℕ) : StdSimplex ℝ α :=
  StdSimplex.normalize (fun a => (n a : ℝ)) fun _ => Nat.cast_nonneg _

/-- Without observations the estimate is uniform. -/
theorem mle_of_sum_eq_zero [Nonempty α] {n : α → ℕ} (hn : ∑ a, n a = 0) (a : α) :
    (mle n).weights a = (Fintype.card α : ℝ)⁻¹ := by
  simp [mle, StdSimplex.normalizeWeights, ← Nat.cast_sum, hn]

theorem mle_apply [Nonempty α] {n : α → ℕ} (hn : 0 < ∑ a, n a) (a : α) :
    (mle n).weights a = n a / ∑ b, n b := by
  rw [mle, StdSimplex.normalize_weights, StdSimplex.normalizeWeights_of_pos (by exact_mod_cast hn),
    Nat.cast_sum]

/-- **Maximum likelihood**: `mle n` maximizes the categorical likelihood over the simplex. -/
theorem likelihood_le_mle [Nonempty α] (n : α → ℕ) (θ : StdSimplex ℝ α) :
    likelihood θ n ≤ likelihood (mle n) n := by
  have h := StdSimplex.prod_rpow_le_prod_rpow_normalizeWeights (a := fun a => (n a : ℝ))
    (fun _ => Nat.cast_nonneg _) θ.nonneg θ.total_of_fintype
  simpa only [Real.rpow_natCast, likelihood, mle, StdSimplex.normalize_weights] using h

theorem isMaxOn_likelihood [Nonempty α] (n : α → ℕ) :
    IsMaxOn (likelihood · n) Set.univ (mle n) :=
  fun θ _ => likelihood_le_mle n θ

/-! ## Dirichlet prior and MAP estimation -/

/-- The unnormalized Dirichlet kernel `∏ θ a ^ (conc a - 1)`. For strictly positive
concentrations it is the Dirichlet density in the interior of the simplex up to its normalizing
constant (which does not depend on `θ` and so does not affect maximizers). For concentrations at
least `1`, the case used below, it also has the intended boundary values; concentrations in
`(0, 1)` have boundary singularities that `Real.rpow` does not represent, and no density
interpretation is claimed for nonpositive concentrations. -/
noncomputable def dirichletKernel (conc : α → ℝ) (θ : StdSimplex ℝ α) : ℝ :=
  ∏ a, θ.weights a ^ (conc a - 1)

omit [Fintype α] in
theorem pseudoCount_nonneg {conc : α → ℝ} (hconc : ∀ a, 1 ≤ conc a) (n : α → ℕ) (a : α) :
    0 ≤ (n a : ℝ) + conc a - 1 := by
  linarith [hconc a, (Nat.cast_nonneg (n a) : (0 : ℝ) ≤ n a)]

/-- The MAP estimate under a Dirichlet prior with concentrations `conc ≥ 1`: the normalization of
the pseudo-counts `n a + conc a - 1`, uniform when they are all zero. -/
noncomputable def mapEstimate [Nonempty α] (conc : α → ℝ) (hconc : ∀ a, 1 ≤ conc a)
    (n : α → ℕ) : StdSimplex ℝ α :=
  StdSimplex.normalize (fun a => n a + conc a - 1) (pseudoCount_nonneg hconc n)

/-- The posterior kernel is a product of powers with the pseudo-counts as exponents. -/
theorem likelihood_mul_dirichletKernel {conc : α → ℝ} (hconc : ∀ a, 1 ≤ conc a)
    (θ : StdSimplex ℝ α) (n : α → ℕ) :
    likelihood θ n * dirichletKernel conc θ = ∏ a, θ.weights a ^ ((n a : ℝ) + conc a - 1) := by
  rw [likelihood, dirichletKernel, ← prod_mul_distrib]
  refine prod_congr rfl fun a _ => ?_
  rw [← Real.rpow_natCast, add_sub_assoc]
  by_cases h : (n a : ℝ) + (conc a - 1) = 0
  · have h1 : (n a : ℝ) = 0 := le_antisymm (by linarith [hconc a]) (Nat.cast_nonneg _)
    have h2 : conc a - 1 = 0 := by linarith
    rw [h, h1, h2, Real.rpow_zero, mul_one]
  · rw [Real.rpow_add' (θ.nonneg a) h]

/-- **MAP estimation under a Dirichlet prior**: with concentrations `conc ≥ 1`, `mapEstimate`
maximizes the posterior kernel over the simplex. -/
theorem posterior_le_mapEstimate [Nonempty α] {conc : α → ℝ} (hconc : ∀ a, 1 ≤ conc a)
    (n : α → ℕ) (θ : StdSimplex ℝ α) :
    likelihood θ n * dirichletKernel conc θ ≤
      likelihood (mapEstimate conc hconc n) n *
        dirichletKernel conc (mapEstimate conc hconc n) := by
  rw [likelihood_mul_dirichletKernel hconc, likelihood_mul_dirichletKernel hconc]
  simpa only [mapEstimate, StdSimplex.normalize_weights] using
    StdSimplex.prod_rpow_le_prod_rpow_normalizeWeights (pseudoCount_nonneg hconc n) θ.nonneg
      θ.total_of_fintype

theorem isMaxOn_posterior [Nonempty α] {conc : α → ℝ} (hconc : ∀ a, 1 ≤ conc a) (n : α → ℕ) :
    IsMaxOn (fun θ => likelihood θ n * dirichletKernel conc θ) Set.univ
      (mapEstimate conc hconc n) :=
  fun θ _ => posterior_le_mapEstimate hconc n θ

/-- Laplace (add-one) smoothing `(n a + 1) / (N + K)` with `K` categories. -/
noncomputable def laplace [Nonempty α] (n : α → ℕ) : StdSimplex ℝ α :=
  mapEstimate (fun _ => 2) (fun _ => by norm_num) n

theorem laplace_apply [Nonempty α] (n : α → ℕ) (a : α) :
    (laplace n).weights a = (n a + 1) / ((∑ b, n b : ℕ) + Fintype.card α) := by
  have hpos : 0 < ∑ b, ((n b : ℝ) + 2 - 1) :=
    sum_pos (fun b _ => by linarith [(Nat.cast_nonneg (n b) : (0 : ℝ) ≤ n b)]) univ_nonempty
  rw [laplace, mapEstimate, StdSimplex.normalize_weights, StdSimplex.normalizeWeights_of_pos hpos]
  congr 1
  · ring
  · rw [Nat.cast_sum, Finset.card_univ.symm, Finset.cast_card, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring

/-- **Laplace smoothing is a MAP estimate**: under the Dirichlet prior with all concentrations
`2`, add-one smoothing maximizes the posterior kernel. -/
theorem isMaxOn_posterior_laplace [Nonempty α] (n : α → ℕ) :
    IsMaxOn (fun θ => likelihood θ n * dirichletKernel (fun _ => 2) θ) Set.univ (laplace n) :=
  isMaxOn_posterior (fun _ => by norm_num) n

end Cslib.MachineLearning.Categorical
