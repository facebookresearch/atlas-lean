/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ChineseRestaurant
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The finite-mixture partition formula tends to the Chinese restaurant process law

Griffiths and Ghahramani (*The Indian buffet process: an introduction and review*, JMLR 12
(2011), Section 2) derive the prior on partitions of an infinite mixture model by taking the
number of classes `K` to infinity in a finite Bayesian mixture. With mixing weights
`θ ~ Dirichlet(α/K, …, α/K)` and class assignments `cᵢ | θ ~ Discrete(θ)`, they compute that a
partition of `N` objects into `K₊` blocks of sizes `m₁, …, m_{K₊}` has probability (their
Equation 4 summed over the `K! / K₀!` labelings of the blocks, `K₀ = K - K₊`)

  `P_K([c]) = K! / K₀! · (α/K)^{K₊} · ∏ₖ ∏_{j=1}^{mₖ-1} (j + α/K) · Γ(α) / Γ(N + α)`,

and their Equation 5 is the limit

  `lim_{K → ∞} P_K([c]) = α^{K₊} · ∏ₖ (mₖ - 1)! · Γ(α) / Γ(N + α)`,

the law of the Chinese restaurant process. We write `Γ(N + α) / Γ(α)` as the rising factorial
`α^{(N)}` (`ascPochhammer`), as in `crpProb`.

This file records the closed form `P_K([c])` as a definition (`finitePartitionProb`); it does
not derive it from the Dirichlet–multinomial model. What is proved is the limit of that closed
form, Equation 5.

Main results:

* `tendsto_descFactorial_div_pow`: `K! / ((K - r)! K^r) → 1`.
* `tendsto_prod_range_add_div`: `∏_{j=1}^{n} (j + α/K) → n!`.
* `finitePartitionProb`: the closed form `P_K([c])` above, taken as a definition.
* `tendsto_finitePartitionProb`: **the closed-form finite-mixture partition probability tends to
  the Chinese restaurant process law** (Equation 5).

`tendsto_descFactorial_div_pow` is also proved, with the same statement, as a private theorem of
`MathlibExt.Probability.DeFinetti` and as a private lemma of
`MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry16Corollary1JensenSeries`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.InfiniteMixtureLimit

open Filter Topology Finset MathlibExt.Biology.PopulationGenetics.ChineseRestaurant

/-- **Falling factorial over a power tends to one.** For every fixed `r`,
`K! / ((K - r)! K^r) = K (K - 1) ⋯ (K - r + 1) / K^r → 1` as `K → ∞`; this is the factor `1` in
Griffiths and Ghahramani (2011), Equations 5 and 14. -/
theorem tendsto_descFactorial_div_pow (r : ℕ) :
    Tendsto (fun K : ℕ => (K.descFactorial r : ℝ) / (K : ℝ) ^ r) atTop (𝓝 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hlin : Tendsto (fun K : ℕ => 1 - (r : ℝ) / K) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (r : ℝ))
    refine (by simpa using ih.mul hlin : Tendsto _ atTop (𝓝 (1 : ℝ))).congr' ?_
    filter_upwards [eventually_ge_atTop (r + 1)] with K hK
    have hK0 : (K : ℝ) ≠ 0 := by
      have : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
      exact this.ne'
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega), pow_succ]
    field_simp

/-- **Shifted products tend to factorials.** For every real `α` and natural `n`,
`∏_{j=1}^{n} (j + α/K) → n!` as `K → ∞` (Griffiths and Ghahramani 2011, Equations 5 and 14). -/
theorem tendsto_prod_range_add_div (α : ℝ) (n : ℕ) :
    Tendsto (fun K : ℕ => ∏ j ∈ range n, ((j + 1 : ℝ) + α / K)) atTop (𝓝 (n.factorial : ℝ)) := by
  have h : Tendsto (fun K : ℕ => ∏ j ∈ range n, ((j + 1 : ℝ) + α / K)) atTop
      (𝓝 (∏ j ∈ range n, ((j + 1 : ℝ) + 0))) :=
    tendsto_finsetProd _ fun j _ =>
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat α)
  simpa [← Finset.prod_range_add_one_eq_factorial] using h

/-- **Closed-form partition probability of a finite symmetric Dirichlet mixture.** The expression
`K!/(K - |π|)! · (α/K)^{|π|} · ∏_{B ∈ π} ∏_{j=1}^{|B|-1} (j + α/K) / α^{(n)}`, where
`α^{(n)} = Γ(n + α) / Γ(α)` is the rising factorial. Griffiths and Ghahramani (2011, Section 2.2:
Equation 4 times the `K! / K₀!` labelings) give it as the probability that, for `K` classes with
weights `θ ~ Dirichlet(α/K, …, α/K)`, the class assignments of `n` objects induce the partition
`π`. It is the paper's closed form, taken here as a definition for every `α` and `K`; it is not
derived from the Dirichlet–multinomial model. It vanishes when `K < |π|`. It is that probability
only for `α > 0` and `K ≥ 1`: for `α < 0` the formula can be negative, at `α = 0` the rising
factorial vanishes and every partition of `n ≥ 1` objects gets `0`, and for `K = 0` (no classes)
every partition of `n ≥ 1` objects gets `0`. The limit `tendsto_finitePartitionProb` is an identity
of formulas that holds for every `α`. -/
noncomputable def finitePartitionProb (α : ℝ) (K : ℕ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) : ℝ :=
  (K.descFactorial #π.parts : ℝ) * (α / K) ^ #π.parts *
    π.cardProd (fun m ↦ ∏ j ∈ range (m - 1), ((j + 1 : ℝ) + α / K)) /
      (ascPochhammer ℝ n).eval α

/-- **The closed-form finite-mixture partition probability tends to the Chinese restaurant
process law** (Griffiths and Ghahramani 2011, Equation 5). For every `α` and every partition `π`
of `n` objects, the closed form `finitePartitionProb α K π` (Equation 4 times `K! / K₀!`,
recorded from the paper, not derived from the model here) converges, as `K → ∞`, to the law of
the Chinese restaurant process `α^{|π|} ∏_{B ∈ π} (|B| - 1)! / α^{(n)}` (`crpProb`). -/
theorem tendsto_finitePartitionProb (α : ℝ) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) :
    Tendsto (fun K : ℕ => finitePartitionProb α K π) atTop (𝓝 (crpProb α π)) := by
  have hprod : Tendsto (fun K : ℕ => π.cardProd fun m ↦ ∏ j ∈ range (m - 1), ((j + 1 : ℝ) + α / K))
      atTop (𝓝 (π.cardProd fun m ↦ ((m - 1).factorial : ℝ))) :=
    tendsto_finsetProd _ fun B _ => tendsto_prod_range_add_div α (B.card - 1)
  have h := ((tendsto_descFactorial_div_pow #π.parts).const_mul (α ^ #π.parts)).mul hprod
  have h' := h.div_const ((ascPochhammer ℝ n).eval α)
  rw [mul_one] at h'
  refine h'.congr' ?_
  filter_upwards with K
  simp only [finitePartitionProb, div_pow]
  ring

end MathlibExt.Probability.InfiniteMixtureLimit
