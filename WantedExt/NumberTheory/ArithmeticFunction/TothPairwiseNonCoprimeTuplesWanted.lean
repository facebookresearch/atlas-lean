/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Fintype.Pi
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Tóth, k-tuples with pairwise non-coprime components — wishlist

Statement-only records for László Tóth's JIS 27 (2024) paper. A coprimality
graph on the vertex set `Fin k` is encoded by its edge set
`E : Finset (Fin k × Fin k)` with `e.1 < e.2` for every `e ∈ E`, matching the
paper's `E ⊆ V^{(2)} = {{i, j} : 1 ≤ i < j ≤ k}`. Sums over
`n₁, …, n_k ≤ x` are taken over `Fintype.piFinset (fun _ => Finset.Icc 1 N)`
for natural `N ≥ 2`; since `⌊x⌋^k = x^k + O(x^{k-1})`, this is equivalent to
the real-`x` statements.

Theorem 2 of the paper (Ushiroya's mean-value theorem) is already in
`MathlibExt/NumberTheory/ArithmeticFunction/WintnerMeanValueMultivariable.lean`.
`MathlibExt/NumberTheory/ArithmeticFunction/EulerProductMeanValue.lean` proves Theorem 3
only under coordinatewise multiplicativity, which is stronger than the source's; the
source-strength Theorem 3 is `euler_product_mean_value_of_coprime_prod` below.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- The characteristic function `δ_G` of the coprimality graph with edge set
`E`: `1` if `gcd(n_i, n_j) = 1` for every edge `(i, j) ∈ E`, and `0` otherwise.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, display (def_delta_G). -/
public def coprimalityIndicator {k : ℕ} (E : Finset (Fin k × Fin k))
    (n : Fin k → ℕ) : ℕ :=
  if ∀ e ∈ E, Nat.Coprime (n e.1) (n e.2) then 1 else 0

/-- With no edges, `δ_G = 1`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, remark after display (def_delta_G). -/
public theorem coprimalityIndicator_empty {k : ℕ} (n : Fin k → ℕ) :
    coprimalityIndicator (∅ : Finset (Fin k × Fin k)) n = 1 := by
  simp [coprimalityIndicator]

/-- Small values: for the single edge `(0, 1)`, `δ_G(2, 3) = 1` and
`δ_G(2, 4) = 0`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, display (def_delta_G). -/
public theorem coprimalityIndicator_small_values :
    coprimalityIndicator ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) ![2, 3] = 1 ∧
      coprimalityIndicator ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2))
        ![2, 4] = 0 := by
  decide

/-- The number of pairs `i < j` with `gcd(n_i, n_j) = 1`; the paper's
`β_r(n) = 1` exactly when this count is `r`, `β'_r(n) = 1` exactly when it is at
least `r`, and `β = β_0`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, displays (def_beta), (def_beta_exact), (def_beta_least). -/
public def coprimePairCount {k : ℕ} (n : Fin k → ℕ) : ℕ :=
  ((univ.filter fun e : Fin k × Fin k => e.1 < e.2).filter
    fun e => Nat.Coprime (n e.1) (n e.2)).card

/-- Small values: `(2, 3, 4)` has two coprime pairs and `(6, 10, 15)` is
pairwise non-coprime.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, displays (def_beta) and (def_beta_exact). -/
public theorem coprimePairCount_small_values :
    coprimePairCount ![2, 3, 4] = 2 ∧ coprimePairCount ![6, 10, 15] = 0 := by
  decide

/-- The asymptotic density `A_G = ∏_p ∑_{F ⊆ E} (-1)^{|F|} / p^{v(F)}` of the
coprimality graph with edge set `E`, where `v(F)` is the number of distinct
vertices appearing in `F` (Arias de Reyna–Heyman form of the constant).

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1, display (A_G_version). -/
public noncomputable def coprimalityDensity {k : ℕ} (E : Finset (Fin k × Fin k)) : ℝ :=
  ∏' p : Nat.Primes, ∑ F ∈ E.powerset,
    (-1 : ℝ) ^ F.card /
      ((p : ℕ) : ℝ) ^ (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card

/-- With no edges, `A_G = 1`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1, display (A_G_version). -/
public theorem coprimalityDensity_empty (k : ℕ) :
    coprimalityDensity (∅ : Finset (Fin k × Fin k)) = 1 := by
  simp [coprimalityDensity]

/-- Theorem 1: for a coprimality graph with edge set `E` and maximum degree
`d_G`, `∑_{n₁, …, n_k ≤ x} δ_G(n) = A_G x^k + O(x^{k-1} (log x)^{d_G})`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1 (`jis-2024-24.8.5-thm-1`). -/
public theorem_wanted coprimality_graph_count_asymp {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |(∑ n ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 N),
          (coprimalityIndicator E n : ℝ)) - coprimalityDensity E * (N : ℝ) ^ k|
        ≤ C * (N : ℝ) ^ (k - 1) *
          Real.log N ^ (univ.sup fun i : Fin k => (E.filter fun e => e.1 = i ∨ e.2 = i).card)

/-- Theorem 1, display (A_G): Hu's form of the constant,
`A_G = ∏_p ∑_{m=0}^{k} i_m(G) p^{-m} (1 - 1/p)^{k-m}`, where `i_m(G)` is the
number of independent vertex sets of size `m`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1 (`jis-2024-24.8.5-thm-1`). -/
public theorem_wanted coprimalityDensity_eq_independent_set_product {k : ℕ}
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, ∑ m ∈ range (k + 1),
        ((univ.filter fun S : Finset (Fin k) =>
            S.card = m ∧ ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)).card : ℝ) /
          ((p : ℕ) : ℝ) ^ m * (1 - 1 / ((p : ℕ) : ℝ)) ^ (k - m)

/-- Lemma 4: `δ_G` is multiplicative as a function of `k` variables:
`δ_G(m₁n₁, …, m_kn_k) = δ_G(m) δ_G(n)` whenever
`gcd(m₁ ⋯ m_k, n₁ ⋯ n_k) = 1`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 4 (`jis-2024-24.8.5-lem-4`). -/
public theorem_wanted coprimalityIndicator_mul {k : ℕ} (E : Finset (Fin k × Fin k))
    (m n : Fin k → ℕ)
    (hmn : Nat.Coprime (∏ i, m i) (∏ i, n i)) :
    coprimalityIndicator E (fun i => m i * n i) =
      coprimalityIndicator E m * coprimalityIndicator E n

/-- Lemma 5: inclusion–exclusion for `β_r`:
`β_r(n) = ∑_{j=r}^{k(k-1)/2} (-1)^{j-r} binom(j, r) ∑_{|E| = j} δ_G(n)`;
the case `r = 0` is the paper's identity for `β`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 5 (`jis-2024-24.8.5-lem-5`). -/
public theorem_wanted exactly_coprime_pairs_inclusion_exclusion {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (n : Fin k → ℕ) :
    (if coprimePairCount n = r then 1 else 0 : ℤ) =
      ∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℤ) ^ (j - r) * (j.choose r : ℤ) *
        ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
          (coprimalityIndicator E n : ℤ)

/-- Lemma 6: inclusion–exclusion for `β'_r`, `r ≥ 1`:
`β'_r(n) = ∑_{j=r}^{k(k-1)/2} (-1)^{j-r} binom(j-1, r-1) ∑_{|E| = j} δ_G(n)`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 6 (`jis-2024-24.8.5-lem-6`). -/
public theorem_wanted at_least_coprime_pairs_inclusion_exclusion {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (hr : 1 ≤ r) (n : Fin k → ℕ) :
    (if r ≤ coprimePairCount n then 1 else 0 : ℤ) =
      ∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℤ) ^ (j - r) * ((j - 1).choose (r - 1) : ℤ) *
        ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
          (coprimalityIndicator E n : ℤ)

/-- Theorem 7, first display: for `Re s_i > 1` and any vertex cover `J` of the
coprimality graph,
`∑ δ_G(n) / (n₁^{s₁} ⋯ n_k^{s_k}) = ζ(s₁) ⋯ ζ(s_k) D'_G(s)`, where
`D'_G(s) = ∏_p ∑'_{L ⊆ J} ∏_{ℓ ∈ L} p^{-s_ℓ} ∏_{i ∈ (J \ L) ∪ (N(L) \ J)} (1 - p^{-s_i})`,
the primed sum running over independent subsets `L` of `J` and `N(L)` being the
neighbourhood of `L`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 7 (`jis-2024-24.8.5-thm-7`). -/
public theorem_wanted coprimality_dirichlet_series_eq {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2)
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J)
    (s : Fin k → ℂ) (hs : ∀ i, 1 < (s i).re) :
    ∑' n : Fin k → ℕ, (coprimalityIndicator E (fun i => n i + 1) : ℂ) /
        ∏ i, ((n i + 1 : ℕ) : ℂ) ^ s i =
      (∏ i, riemannZeta (s i)) *
        ∏' p : Nat.Primes, ∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬ (e.1 ∈ L ∧ e.2 ∈ L)),
          (∏ l ∈ L, ((p : ℕ) : ℂ) ^ (-s l)) *
            ∏ i ∈ (J \ L) ∪ ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J),
              (1 - ((p : ℕ) : ℂ) ^ (-s i))

/-- Theorem 7, convergence clause: the Euler product `D'_G(s)` is absolutely
convergent, i.e. `∑_p |D'_{G,p}(s) - 1| < ∞`, whenever
`Re (s_{i₁} + ⋯ + s_{i_j}) > 1` for every set of `j ≥ 2` non-isolated vertices.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 7 (`jis-2024-24.8.5-thm-7`). -/
public theorem_wanted coprimality_euler_factor_summable {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2)
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J) (s : Fin k → ℂ)
    (hs : ∀ T : Finset (Fin k), (∀ i ∈ T, ∃ e ∈ E, e.1 = i ∨ e.2 = i) → 2 ≤ T.card →
      1 < (∑ i ∈ T, s i).re) :
    Summable fun p : Nat.Primes =>
      ‖(∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬ (e.1 ∈ L ∧ e.2 ∈ L)),
          (∏ l ∈ L, ((p : ℕ) : ℂ) ^ (-s l)) *
            ∏ i ∈ (J \ L) ∪ ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J),
              (1 - ((p : ℕ) : ℂ) ^ (-s i))) - 1‖

/-- Theorem 9, first representation: `A_G = ∑ (μ * δ_G)(n) / (n₁ ⋯ n_k)`,
with `(μ * f)(n) = ∑_{d_i ∣ n_i} μ(d₁) ⋯ μ(d_k) f(n₁/d₁, …, n_k/d_k)`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`). -/
public theorem_wanted coprimalityDensity_eq_tsum_moebius_conv {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    coprimalityDensity E =
      ∑' n : Fin k → ℕ,
        (∑ d ∈ Fintype.piFinset (fun i => Nat.divisors (n i + 1)),
            (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
              (coprimalityIndicator E (fun i => (n i + 1) / d i) : ℝ)) /
          ∏ i, ((n i : ℝ) + 1)

/-- Theorem 9, second representation:
`A_G = ∏_p (1 - 1/p)^k ∑_{ν} δ_G(p^{ν₁}, …, p^{ν_k}) / p^{ν₁ + ⋯ + ν_k}`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`). -/
public theorem_wanted coprimalityDensity_eq_prime_power_product {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ)) ^ k *
        ∑' ν : Fin k → ℕ, (coprimalityIndicator E (fun i => (p : ℕ) ^ ν i) : ℝ) /
          ((p : ℕ) : ℝ) ^ (∑ i, ν i)

/-- Theorem 9, display (A_G_version_new): for any vertex cover `J`,
`A_G = ∏_p ∑'_{L ⊆ J} p^{-|L|} (1 - 1/p)^{|J \ L| + |N(L) \ J|}`, the primed sum
running over independent subsets `L` of `J`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`). -/
public theorem_wanted coprimalityDensity_eq_vertex_cover_product {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2)
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, ∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬ (e.1 ∈ L ∧ e.2 ∈ L)),
        (1 / ((p : ℕ) : ℝ)) ^ L.card * (1 - 1 / ((p : ℕ) : ℝ)) ^
          ((J \ L).card + ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card)

/-- Theorem 11, equation (asympt_form_exact): the number of `n ∈ [1, x]^k` with
exactly `r` coprime pairs is `C_{k,r} x^k + O(x^{k-1} (log x)^{k-1})`, where
`C_{k,r} = ∑_{j=r}^{k(k-1)/2} (-1)^{j-r} binom(j, r) ∑_{|E| = j} A_G`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 11 (`jis-2024-24.8.5-thm-11`). -/
public theorem_wanted exactly_coprime_pairs_count_asymp {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((Fintype.piFinset (fun _ : Fin k => Icc 1 N)).filter
            fun n => coprimePairCount n = r).card -
          (∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℝ) ^ (j - r) * (j.choose r : ℝ) *
            ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
              coprimalityDensity E) * (N : ℝ) ^ k|
        ≤ C * (N : ℝ) ^ (k - 1) * Real.log N ^ (k - 1)

/-- Theorem 11, equation (asympt_form_least): for `r ≥ 1`, the number of
`n ∈ [1, x]^k` with at least `r` coprime pairs is
`C'_{k,r} x^k + O(x^{k-1} (log x)^{k-1})`, where
`C'_{k,r} = ∑_{j=r}^{k(k-1)/2} (-1)^{j-r} binom(j-1, r-1) ∑_{|E| = j} A_G`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 11 (`jis-2024-24.8.5-thm-11`). -/
public theorem_wanted at_least_coprime_pairs_count_asymp {k : ℕ} (hk : 2 ≤ k) (r : ℕ)
    (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((Fintype.piFinset (fun _ : Fin k => Icc 1 N)).filter
            fun n => r ≤ coprimePairCount n).card -
          (∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℝ) ^ (j - r) * ((j - 1).choose (r - 1) : ℝ) *
            ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
              coprimalityDensity E) * (N : ℝ) ^ k|
        ≤ C * (N : ℝ) ^ (k - 1) * Real.log N ^ (k - 1)

/-- Corollary 12: the density `C_k` of pairwise non-coprime `k`-tuples equals
`∑ (μ * β)(n) / (n₁ ⋯ n_k)` and `∑_{j=0}^{k(k-1)/2} (-1)^j ∑_{|E| = j} A_G`; the
asymptotic formula for `∑ β(n)` is the case `r = 0` of
`exactly_coprime_pairs_count_asymp`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Corollary 12 (`jis-2024-24.8.5-cor-12`). -/
public theorem_wanted pairwise_non_coprime_density_eq_tsum_moebius_conv {k : ℕ}
    (hk : 2 ≤ k) :
    ∑' n : Fin k → ℕ,
        (∑ d ∈ Fintype.piFinset (fun i => Nat.divisors (n i + 1)),
            (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
              (if coprimePairCount (fun i => (n i + 1) / d i) = 0 then 1 else 0)) /
          ∏ i, ((n i : ℝ) + 1) =
      ∑ j ∈ range (k * (k - 1) / 2 + 1), (-1 : ℝ) ^ j *
        ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
          coprimalityDensity E

/-- Theorem 3 (Ushiroya), source strength: if `f : ℕ^k → ℂ` is multiplicative in the
multivariable sense (`f(a b) = f(a) f(b)` whenever `gcd(a₁⋯a_k, b₁⋯b_k) = 1`) and
`∑_p ∑_{ν ≠ 0} |(μ * f)(p^{ν₁}, …, p^{ν_k})| / p^{ν₁+⋯+ν_k} < ∞`, then the mean value of `f`
exists and equals `∏_p (1 - 1/p)^k ∑_ν f(p^{ν₁}, …, p^{ν_k}) / p^{ν₁+⋯+ν_k}`. The mean value
is the source's joint limit of the box averages `(x₁⋯x_k)^{-1} ∑_{n_i ≤ x_i} f(n)` as all
`x_i → ∞` (integer `x_i`, equivalent to real ones since only `⌊x_i⌋` enters the sum and
`⌊x_i⌋/x_i → 1`), and `(μ * f)` is written as
the divisor-tuple sum against `ArithmeticFunction.moebius`, as in
`MetaMathlibExt.euler_product_mean_value` (which assumes coordinatewise multiplicativity).

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with
Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5,
Theorem 3 (`jis-2024-24.8.5-thm-3`). -/
public theorem_wanted euler_product_mean_value_of_coprime_prod
    {k : ℕ} (f : (Fin k → ℕ) → ℂ)
    (hmult : ∀ a b : Fin k → ℕ, Nat.Coprime (∏ i, a i) (∏ i, b i) →
      f (fun i => a i * b i) = f a * f b)
    (hsumm : Summable (fun q : { q : { p : ℕ // p.Prime } × (Fin k → ℕ) // q.2 ≠ 0 } =>
      ‖(∑ d ∈ Fintype.piFinset (fun i => Nat.divisors ((q.1.1 : ℕ) ^ (q.1.2 i))),
          (∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℂ)) *
          f (fun i => (q.1.1 : ℕ) ^ (q.1.2 i) / d i)) /
        (((q.1.1 : ℕ) : ℂ) ^ (∑ i, q.1.2 i))‖)) :
    ∃ M : ℂ, Filter.Tendsto (fun x : Fin k → ℕ =>
      (∑ n ∈ Fintype.piFinset (fun i => Finset.Icc 1 (x i)), f n) / ∏ i, (x i : ℂ))
      Filter.atTop (nhds M) ∧
      M = ∏' (p : { p : ℕ // p.Prime }),
        ((1 - 1 / ((p : ℕ) : ℂ)) ^ k *
        (∑' (ν : Fin k → ℕ),
          f (fun i => (p : ℕ) ^ (ν i)) / (((p : ℕ) : ℂ) ^ (∑ i, ν i))))

end

end MetaMathlibExt
