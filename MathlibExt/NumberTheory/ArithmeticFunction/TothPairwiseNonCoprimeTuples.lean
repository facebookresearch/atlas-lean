/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Tuples coprime along the edges of a graph

For a fixed tuple, a graph contributes to the coprimality indicator sum precisely when
all its edges belong to the set of coprime pairs. Counting subgraphs by their number of
edges then gives the inclusion–exclusion formula for exactly `r` coprime pairs.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Coprimality indicator of a graph.** Let $E$ be a set of ordered pairs $(i, j)$ of indices in
$\{0, \dots, k-1\}$, the edge set of a graph $G$ on these $k$ vertices. For
$n = (n_0, \dots, n_{k-1}) \in \mathbb{N}^k$, the coprimality indicator $\delta_G(n)$ is the
natural number $1$ if $\gcd(n_i, n_j) = 1$ for every $(i, j) \in E$, and $0$ otherwise.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, display (def_delta_G). -/
public def coprimalityIndicator {k : ℕ} (E : Finset (Fin k × Fin k))
    (n : Fin k → ℕ) : ℕ :=
  if ∀ e ∈ E, Nat.Coprime (n e.1) (n e.2) then 1 else 0

/-- **Coprimality indicator of the empty graph.** Let $k \in \mathbb{N}$ and let $G$ be the graph
on $k$ vertices with no edges, and let $\delta_G$ be its coprimality indicator. Then
$\delta_G(n) = 1$ for every $n = (n_0, \dots, n_{k-1}) \in \mathbb{N}^k$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, remark after display (def_delta_G). -/
public theorem coprimalityIndicator_empty {k : ℕ} (n : Fin k → ℕ) :
    coprimalityIndicator (∅ : Finset (Fin k × Fin k)) n = 1 := by
  simp [coprimalityIndicator]

/-- **Coprimality indicator of a single edge: examples.** Let $G$ be the graph on the two
vertices $0, 1$ with the single edge $(0, 1)$, with coprimality indicator $\delta_G$. Then
$\delta_G(2, 3) = 1$ and $\delta_G(2, 4) = 0$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, display (def_delta_G). -/
public theorem coprimalityIndicator_small_values :
    coprimalityIndicator ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) ![2, 3] = 1 ∧
      coprimalityIndicator ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2))
        ![2, 4] = 0 := by
  decide

/-- **Number of coprime pairs.** For $n = (n_0, \dots, n_{k-1}) \in \mathbb{N}^k$, the number of
coprime pairs of $n$ is the number of index pairs $(i, j)$ with $0 \le i < j < k$ and
$\gcd(n_i, n_j) = 1$.

In the paper's notation, $\beta_r(n) = 1$ exactly when this count is $r$, $\beta'_r(n) = 1$
exactly when it is at least $r$, and $\beta = \beta_0$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, displays (def_beta), (def_beta_exact), (def_beta_least). -/
public def coprimePairCount {k : ℕ} (n : Fin k → ℕ) : ℕ :=
  ((univ.filter fun e : Fin k × Fin k => e.1 < e.2).filter
    fun e => Nat.Coprime (n e.1) (n e.2)).card

/-- **Number of coprime pairs: examples.** The triple $(2, 3, 4)$ has exactly two coprime pairs
of components, and the triple $(6, 10, 15)$ has none, that is, its components are pairwise
non-coprime.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, displays (def_beta) and (def_beta_exact). -/
public theorem coprimePairCount_small_values :
    coprimePairCount ![2, 3, 4] = 2 ∧ coprimePairCount ![6, 10, 15] = 0 := by
  decide

/-- **Coprimality density of a graph.** Let $k$ be a natural number and let $E$ be a set of ordered
pairs $(a, b)$ of vertices in $\{1, \dots, k\}$, the edge set of a graph $G$. For $F \subseteq E$
let $v(F)$ be the number of distinct vertices that occur in some pair of $F$. The coprimality
density of $G$ is the real number
$$A_G = \prod_p \sum_{F \subseteq E} \frac{(-1)^{|F|}}{p^{v(F)}},$$
the product running over all primes $p$.

When every edge $(a, b)$ has $a < b$, this is the Arias de Reyna–Heyman form of the asymptotic
density of the $k$-tuples $(n_1, \dots, n_k)$ of positive integers with $\gcd(n_a, n_b) = 1$ for
every edge $(a, b)$ of $G$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1, display (A_G_version). -/
public noncomputable def coprimalityDensity {k : ℕ} (E : Finset (Fin k × Fin k)) : ℝ :=
  ∏' p : Nat.Primes, ∑ F ∈ E.powerset,
    (-1 : ℝ) ^ F.card /
      ((p : ℕ) : ℝ) ^ (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card

/-- **The coprimality density of the empty graph is $1$.** For every natural number $k$, the
coprimality density of the graph on $\{1, \dots, k\}$ with no edges equals $1$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 1, display (A_G_version). -/
public theorem coprimalityDensity_empty (k : ℕ) :
    coprimalityDensity (∅ : Finset (Fin k × Fin k)) = 1 := by
  simp [coprimalityDensity]

namespace CoprimePairs

private lemma sum_coprimalityIndicator_powersetCard {k : ℕ} (n : Fin k → ℕ)
    (edges : Finset (Fin k × Fin k)) (j : ℕ) :
    ∑ E ∈ edges.powersetCard j, (coprimalityIndicator E n : ℤ) =
      ((edges.filter fun e => Nat.Coprime (n e.1) (n e.2)).card.choose j : ℤ) := by
  let good (e : Fin k × Fin k) := Nat.Coprime (n e.1) (n e.2)
  have hsets : (edges.powersetCard j).filter (fun E => ∀ e ∈ E, good e) =
      (edges.filter good).powersetCard j := by
    ext E
    simp only [mem_filter, mem_powersetCard, subset_iff]
    grind
  simp only [coprimalityIndicator, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_boole]
  rw [← card_powersetCard, ← hsets]

private lemma alternating_choose_sum {t m : ℕ} (ht : t ≤ m) (r : ℕ) :
    (∑ j ∈ Icc r m, (-1 : ℤ) ^ (j - r) * (j.choose r : ℤ) * (t.choose j : ℤ)) =
      if t = r then 1 else 0 := by
  -- Terms above the actual number of coprime pairs vanish.
  rw [← sum_subset (Icc_subset_Icc_right ht) (fun j hj hout => by
    have hjr := (mem_Icc.mp hj).1
    have htj : t < j := by simpa [mem_Icc, hjr] using hout
    simp [Nat.choose_eq_zero_of_lt htj])]
  by_cases hr : r ≤ t
  · rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, show t + 1 - r = t - r + 1 by omega]
    simp only [Nat.add_sub_cancel_left]
    calc
      _ = (t.choose r : ℤ) * ∑ i ∈ range (t - r + 1),
            (-1 : ℤ) ^ i * ((t - r).choose i : ℤ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [mul_right_comm, mul_assoc, ← Nat.cast_mul, Nat.choose_mul (Nat.le_add_right r i),
          Nat.add_sub_cancel_left, Nat.cast_mul]
        ac_rfl
      _ = _ := by
        rw [Int.alternating_sum_range_choose]
        obtain rfl | hlt := eq_or_lt_of_le hr
        · simp
        · simp [Nat.sub_ne_zero_of_lt hlt, hlt.ne']
  · simp [Icc_eq_empty_of_lt (Nat.lt_of_not_ge hr), ne_of_lt (Nat.lt_of_not_ge hr)]

end CoprimePairs

-- The finite counting argument also applies to tuples of length zero or one.
set_option linter.unusedVariables false in
/-- **Inclusion–exclusion for tuples with exactly $r$ coprime pairs.** Let $k \ge 2$, $r \ge 0$
and $n \in \mathbb{N}^k$, and let $\beta_r(n)$ be $1$ if $n$ has exactly $r$ coprime pairs and $0$
otherwise. For a set $E$ of pairs $(a, b)$ with $0 \le a < b < k$, let $\delta_E$ be the
coprimality indicator of the graph with edge set $E$. Then, as integers,
$$\beta_r(n) = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j}{r} \sum_{|E| = j} \delta_E(n),$$
where the inner sum runs over the $j$-element sets $E$ of such pairs.

For $r = 0$ this is the paper's identity for $\beta = \beta_0$, the indicator of pairwise
non-coprime tuples.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Lemma 5 (`jis-2024-24.8.5-lem-5`). -/
public theorem exactly_coprime_pairs_inclusion_exclusion {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (n : Fin k → ℕ) :
    (if coprimePairCount n = r then 1 else 0 : ℤ) =
      ∑ j ∈ Icc r (k * (k - 1) / 2), (-1 : ℤ) ^ (j - r) * (j.choose r : ℤ) *
        ∑ E ∈ (univ.filter fun e : Fin k × Fin k => e.1 < e.2).powersetCard j,
          (coprimalityIndicator E n : ℤ) := by
  let edges := univ.filter fun e : Fin k × Fin k => e.1 < e.2
  have hbound : coprimePairCount n ≤ k * (k - 1) / 2 := by
    calc
      coprimePairCount n ≤ edges.card := card_filter_le _ _
      _ = k * (k - 1) / 2 := by
        simp [edges, Fintype.card_product_filter_lt, Nat.choose_two_right]
  simp_rw [CoprimePairs.sum_coprimalityIndicator_powersetCard]
  exact (CoprimePairs.alternating_choose_sum hbound r).symm

end

end MetaMathlibExt
