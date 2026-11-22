/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Kim–Vu polynomial concentration

Let `t₁, …, tₙ` be independent `{0, 1}` random variables with `E tᵢ = pᵢ` and let
`Y = ∑_{e ∈ E} w(e) ∏_{i ∈ e} tᵢ` be a polynomial with positive coefficients whose supporting
hypergraph `E` has edges of size at most `k`. For a set `A` of variables, the partial derivative
of `Y` with respect to `A` is `Y_A = ∑_{e ⊇ A} w(e) ∏_{i ∈ e \ A} tᵢ`. Let
`E_j = max_{|A| = j} E(Y_A)`, `E = max_{j ≥ 0} E_j` and `E' = max_{j ≥ 1} E_j`. Kim and Vu proved

`P(|Y - E Y| > a_k (E E')^{1/2} λ^k) = O(exp(-λ + (k - 1) log n))` for `λ > 1`,
`a_k = 8^k (k!)^{1/2}`.

The point is that only the *average* effects `E_j` of groups of variables enter, not their
worst-case effects as in Azuma's or McDiarmid's inequality. The model application is the number
of triangles in `G(n, p)` for `p` below `n^{-2/3}`, where the worst-case effect of an edge exceeds
the mean.

Reference: J. H. Kim and V. H. Vu, "Concentration of multivariate polynomials and its
applications", *Combinatorica* 20 (2000), 417–434, Section 1.2, Main Theorem.
-/

@[expose] public section

open MeasureTheory unitInterval MathlibExt.Probability.Combinatorics.RandomSubset

namespace MathlibExt.Probability.KimVuConcentrationWanted

variable {n : ℕ}

/-- **Partial derivative of a positive polynomial.** For a weighted hypergraph on `Fin n` with
edge set `E` and weights `w`, and a set `A` of variables, the value at `ω` of
`Y_{H_A} = ∑_{e ∈ E, A ⊆ e} w(e) ∏_{i ∈ e \ A} tᵢ`, where `tᵢ = 1` if `ω i` and `0` otherwise.
For `A = ∅` this is the polynomial `Y_H` itself (J. H. Kim and V. H. Vu, "Concentration of
multivariate polynomials and its applications", *Combinatorica* 20 (2000), Section 1.2, the
truncated subhypergraph `H_A`). -/
noncomputable def truncatedPoly (E : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℝ)
    (A : Finset (Fin n)) (ω : Fin n → Bool) : ℝ :=
  ∑ e ∈ E with A ⊆ e, w e * ∏ i ∈ e \ A, (if ω i then (1 : ℝ) else 0)

/-- **Maximal average effect of `j` variables.** `E_j(H) = max_{|A| = j} E(Y_{H_A})`, the
expectation taken for independent `{0, 1}` variables `tᵢ` with means `p i`; it is `0` when
`j > n` (J. H. Kim and V. H. Vu, *Combinatorica* 20 (2000), Section 1.2). -/
noncomputable def maxAverageEffect (p : Fin n → I) (E : Finset (Finset (Fin n)))
    (w : Finset (Fin n) → ℝ) (j : ℕ) : ℝ :=
  ⨆ A : {A : Finset (Fin n) // A.card = j},
    ∫ ω, truncatedPoly E w A.1 ω ∂(randomSubsetLaw p)

/-- **Kim–Vu concentration of positive polynomials (Main Theorem).** For every `k` there is a
constant `C > 0` such that the following holds. Let `t₁, …, tₙ` be independent `{0, 1}` random
variables with `E tᵢ = pᵢ`, let `Y = ∑_{e ∈ E} w(e) ∏_{i ∈ e} tᵢ` with positive weights and
edges of size at most `k`, and let `E_j` be the maximal average effect of `j` variables,
`E = max_{j ≥ 0} E_j` and `E' = max_{j ≥ 1} E_j`. Then for every `λ > 1`,
`P(|Y - E Y| > 8^k (k!)^{1/2} (E E')^{1/2} λ^k) ≤ C exp(-λ + (k - 1) log n)`.

(J. H. Kim and V. H. Vu, "Concentration of multivariate polynomials and its applications",
*Combinatorica* 20 (2000), 417–434, Section 1.2, Main Theorem, where the bound is written
`O(exp(-λ + (k - 1) log n))`. The theorem there also allows some `tᵢ` to be the constants
`pᵢ`; this entry states the case, singled out there, in which every `tᵢ` is a `{0, 1}`
variable. `E'` is the maximum over `1 ≤ j ≤ n`, which equals the maximum over all `j ≥ 1`
because `E_j = 0` for `j > n`.) -/
theorem_wanted kim_vu_concentration (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : Fin n → I) (E : Finset (Finset (Fin n)))
      (w : Finset (Fin n) → ℝ), (∀ e ∈ E, 0 < w e) → (∀ e ∈ E, e.card ≤ k) →
      ∀ lam : ℝ, 1 < lam →
        (randomSubsetLaw p).real
          {ω | (8 : ℝ) ^ k * Real.sqrt (k.factorial : ℝ) *
              Real.sqrt ((max (maxAverageEffect p E w 0)
                  (⨆ j : Fin n, maxAverageEffect p E w (j + 1))) *
                (⨆ j : Fin n, maxAverageEffect p E w (j + 1))) * lam ^ k <
            |truncatedPoly E w ∅ ω - ∫ ω', truncatedPoly E w ∅ ω' ∂(randomSubsetLaw p)|} ≤
          C * Real.exp (-lam + ((k : ℝ) - 1) * Real.log n)

end MathlibExt.Probability.KimVuConcentrationWanted
