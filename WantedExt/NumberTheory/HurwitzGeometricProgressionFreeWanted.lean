/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient

/-!
# Avoiding 3-term geometric progressions in Hurwitz quaternions: wishlist

Source: Megumi Asada, Bruce Fang, Eva Fourakis, Sarah Manski, Nathan McNew, Steven J. Miller,
Gwyneth Moreland, Ajmain Yamin, and Sindy Xin Zhang, *Avoiding 3-Term Geometric Progressions
in Hurwitz Quaternions*, Journal of Integer Sequences 27 (2024), Article 24.7.7
(arXiv:1807.07605).

No new definition is introduced; the paper's notions are written inline (local notation),
following Section 1, Section 2 and Section 5 of the paper:

* `Q_Hur` is the set of quaternions in `ℍ[ℚ]` whose four coordinates are all in `ℤ` or all
  in `ℤ + 1/2`; the norm `Nm` is `Quaternion.normSq`.
* `S(N)` is the set of nonzero Hurwitz quaternions of norm at most `N`, and `S(G)` for
  `G ⊆ ℕ` is the set of Hurwitz quaternions whose norm lies in `G`. The (upper, lower) density
  of `A ⊆ Q_Hur` is the (lim sup, lim inf) limit of `|A ∩ S(N)| / |S(N)|`.
* A 3-term geometric progression is a triple `(a, ar, ar²)` with `a, r ∈ Q_Hur ∖ {0}` and `r`
  a non-unit, i.e. `Nm r ≠ 1`.
* Rankin's greedy set `G₃*(ℕ₊)` is the set of positive integers all of whose `p`-adic
  valuations have no digit `2` in base `3` (the paper's description via Brown and Gordon).
* The quaternion greedy set `G₃*(Q_Hur ∖ {0})` adds Hurwitz quaternions by increasing norm
  unless they complete a progression with smaller-norm members. Since `Nm r ≥ 2`, the new
  element must be the third term; the set is therefore the unique `Gq` with
  `q ∈ Gq ↔ q ∈ Q_Hur, q ≠ 0, and q ≠ a r²` for all `a, ar ∈ Gq` and non-unit `r ≠ 0`
  (unique by strong induction on the norm). Statements about it take such a `Gq` as a
  hypothesis.
-/

namespace MetaMathlibExt

@[expose] public section

set_option quotPrecheck false in
/-- The Hurwitz order: quaternions with all coordinates in `ℤ` or all in `ℤ + 1/2`. -/
local notation "𝐇" => Set.ofPred fun q : Quaternion ℚ =>
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)
set_option quotPrecheck false in
/-- `S(N)`: nonzero Hurwitz quaternions of norm at most `N`. -/
local notation "𝐒" N:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ q ≠ 0 ∧ Quaternion.normSq q ≤ ((N : ℕ) : ℚ)
set_option quotPrecheck false in
/-- `S(G)`: Hurwitz quaternions whose norm lies in `G ⊆ ℕ`. -/
local notation "𝐒ᴳ" G:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ ∃ n ∈ G, Quaternion.normSq q = ((n : ℕ) : ℚ)
set_option quotPrecheck false in
/-- The density ratio `|A ∩ S(N)| / |S(N)|`. -/
local notation "ρ" A:max N:max =>
  ((Set.ncard (A ∩ 𝐒 N) : ℝ) / (Set.ncard (𝐒 N) : ℝ))
set_option quotPrecheck false in
/-- `A ⊆ Q_Hur` contains no triple `(a, ar, ar²)` with `a, r ≠ 0` and `r` a non-unit. -/
local notation "GPFree" A:max => A ⊆ 𝐇 ∧ ∀ a ∈ 𝐇, ∀ r ∈ 𝐇, a ≠ 0 → r ≠ 0 →
  Quaternion.normSq r ≠ 1 → ¬ (a ∈ A ∧ a * r ∈ A ∧ a * r ^ 2 ∈ A)
set_option quotPrecheck false in
/-- Rankin's greedy set `G₃*(ℕ₊)`: positive integers whose prime valuations have no
ternary digit `2`. -/
local notation "𝐆ʳ" => Set.ofPred fun n : ℕ =>
  0 < n ∧ ∀ p : ℕ, p.Prime → 2 ∉ Nat.digits 3 (n.factorization p)
set_option quotPrecheck false in
/-- `Gq` is the quaternion greedy set `G₃*(Q_Hur ∖ {0})`, pinned by its defining recursion. -/
local notation "IsQuaternionGreedy" Gq:max => ∀ q : Quaternion ℚ, q ∈ Gq ↔
  (q ∈ 𝐇 ∧ q ≠ 0 ∧ ¬ ∃ a ∈ Gq, ∃ r ∈ 𝐇, r ≠ 0 ∧ Quaternion.normSq r ≠ 1 ∧
    a * r ∈ Gq ∧ q = a * r ^ 2)
set_option quotPrecheck false in
/-- `Q = U R²` for a unit `U ∈ Q_Hur` and some `R ∈ Q_Hur` of norm `r`. -/
local notation "IsUnitMulSq" Q:max r:max => ∃ U ∈ 𝐇, Quaternion.normSq U = 1 ∧
  ∃ R ∈ 𝐇, Quaternion.normSq R = ((r : ℕ) : ℚ) ∧ Q = U * R ^ 2

/-- **Number of Hurwitz quaternions of a given norm.** A Hurwitz quaternion is a quaternion
$q = x_0 + x_1 i + x_2 j + x_3 k$ whose rational coordinates $x_0, x_1, x_2, x_3$ are either all
integers or all halves of odd integers, and its norm is
$\mathrm{Nm}(q) = x_0^2 + x_1^2 + x_2^2 + x_3^2$. For every positive integer $N$, the number of
Hurwitz quaternions of norm $N$ is $24 \sum_{d \mid N,\ d \text{ odd}} d$, that is, $24$ times
the sum of the odd divisors of $N$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 1. -/
public theorem_wanted card_hurwitz_norm_eq (N : ℕ) (hN : 0 < N) :
    (Set.ofPred fun q : Quaternion ℚ => q ∈ 𝐇 ∧ Quaternion.normSq q = (N : ℚ)).ncard =
      24 * ∑ d ∈ N.divisors with Odd d, d

/-- **Counting Hurwitz quaternions of bounded norm.** A Hurwitz quaternion is a quaternion whose
four rational coordinates are either all integers or all halves of odd integers; its norm is the
sum of the squares of its coordinates. For a natural number $N$ let $S(N)$ be the set of nonzero
Hurwitz quaternions of norm at most $N$.

(a) There is a real constant $C$ such that $\bigl| |S(N)| - \pi^2 N^2 \bigr| \le C N \log N$ for
every natural number $N \ge 2$.

(b) For every positive integer $M$ there is a real constant $C$ such that, for every natural
number $N \ge 2$, the number $c_M(N)$ of Hurwitz quaternions whose norm is a positive integer
$n \le N$ coprime to $M$ satisfies
$$\Bigl| c_M(N) - \pi^2 N^2 \cdot \frac{\varphi(2M)}{M}
\prod_{p \mid M} \Bigl(1 - \frac{1}{p^2}\Bigr) \Bigr| \le C N \log N,$$
where $\varphi$ is Euler's totient function and the product runs over the primes $p$ dividing $M$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 2. -/
public theorem_wanted card_hurwitz_norm_le_asymptotic :
    (∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((𝐒 N).ncard : ℝ) - Real.pi ^ 2 * (N : ℝ) ^ 2| ≤ C * N * Real.log N) ∧
    ∀ M : ℕ, 0 < M → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((Set.ofPred fun q : Quaternion ℚ => q ∈ 𝐇 ∧
            ∃ n : ℕ, Quaternion.normSq q = (n : ℚ) ∧ 0 < n ∧ n ≤ N ∧ n.Coprime M).ncard : ℝ) -
          Real.pi ^ 2 * (N : ℝ) ^ 2 * ((Nat.totient (2 * M) : ℝ) / M) *
            ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ) ^ 2)| ≤ C * N * Real.log N

/-- **Density of Hurwitz quaternions whose norm has prescribed prime exponents.** A Hurwitz
quaternion is a quaternion whose four rational coordinates are either all integers or all halves
of odd integers; its norm is the sum of the squares of its coordinates. For a natural number $N$
let $S(N)$ be the set of nonzero Hurwitz quaternions of norm at most $N$. Let $A$ be a set of
natural numbers, let $G$ be the set of positive integers $n$ such that for every prime $p$ the
exponent $\nu_p(n)$ of $p$ in $n$ lies in $A$, and let $H_G$ be the set of Hurwitz quaternions
whose norm lies in $G$. Then the ratio $|H_G \cap S(N)| / |S(N)|$ tends, as $N \to \infty$, to
$$\frac{6}{\pi^2} \Bigl( \sum_{k \in A} 2^{-2k} \Bigr)
\prod_{p > 2} \Bigl( \sum_{k \in A} p^{-k} - \frac{1}{p} \sum_{k \in A} p^{-2k} \Bigr),$$
the product running over the odd primes $p$. Here $6/\pi^2 = 1/\zeta(2)$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Theorem 5. -/
public theorem_wanted density_hurwitz_norm_valuations_in (A : Set ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ρ (𝐒ᴳ (Set.ofPred fun n : ℕ =>
        0 < n ∧ ∀ p : ℕ, p.Prime → n.factorization p ∈ A)) N)
      Filter.atTop
      (nhds (6 / Real.pi ^ 2 * (∑' k : A, 1 / (2 : ℝ) ^ (2 * (k : ℕ))) *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
          (∑' k : A, 1 / ((p : ℕ) : ℝ) ^ (k : ℕ) -
            1 / ((p : ℕ) : ℝ) * ∑' k : A, 1 / ((p : ℕ) : ℝ) ^ (2 * (k : ℕ)))))

/-- **Density of Hurwitz quaternions with norm in Rankin's greedy set.** A Hurwitz quaternion is a
quaternion whose four rational coordinates are either all integers or all halves of odd integers;
its norm is the sum of the squares of its coordinates. For a natural number $N$ let $S(N)$ be the
set of nonzero Hurwitz quaternions of norm at most $N$. Let $G$ be the set of positive integers
$n$ such that, for every prime $p$, the base-$3$ digits of the exponent $\nu_p(n)$ of $p$ in $n$
include no $2$ (this is Rankin's greedy set of positive integers avoiding 3-term geometric
progressions), and let $H_G$ be the set of Hurwitz quaternions whose norm lies in $G$. With
$f(x) = \prod_{i \ge 0} \bigl(1 + x^{-3^i}\bigr)$, the ratio $|H_G \cap S(N)| / |S(N)|$ tends,
as $N \to \infty$, to
$$\frac{6}{\pi^2} \, f(4) \prod_{p > 2} \Bigl( f(p) - \frac{f(p^2)}{p} \Bigr),$$
the product running over the odd primes $p$.

The paper writes this constant as $(f(2^2)/\zeta(2)) \prod_{p > 2} (f(p) - f(p^2)/p)$, using
$1/\zeta(2) = 6/\pi^2$, and gives its value as approximately $0.782643$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Theorem 7 (restated as the unnumbered theorem of the introduction). -/
public theorem_wanted density_hurwitz_norm_in_rankin_greedy :
    Filter.Tendsto (fun N : ℕ => ρ (𝐒ᴳ 𝐆ʳ) N) Filter.atTop
      (nhds ((∏' i : ℕ, (1 + 1 / (4 : ℝ) ^ (3 ^ i))) * (6 / Real.pi ^ 2) *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
          ((∏' i : ℕ, (1 + 1 / ((p : ℕ) : ℝ) ^ (3 ^ i))) -
            (∏' i : ℕ, (1 + 1 / (((p : ℕ) : ℝ) ^ 2) ^ (3 ^ i))) / ((p : ℕ) : ℝ))))

/-- **Upper density of Hurwitz quaternions with norms in a lacunary union of intervals.** Let
$Q_{\mathrm{Hur}}$ be the set of Hurwitz quaternions, the rational quaternions whose four
coordinates are all integers or all lie in $\mathbb{Z} + \tfrac12$, and let $\mathrm{Nm}(q)$ be
the sum of the squares of the coordinates of $q$. For $N \in \mathbb{N}$ let $S(N)$ be the set of
nonzero $q \in Q_{\mathrm{Hur}}$ with $\mathrm{Nm}(q) \le N$, and define the upper density of a
set $A$ of quaternions as $\limsup_{N \to \infty} |A \cap S(N)| / |S(N)|$. For a natural number
$M$ let $T_M$ be the set of positive integers in $(M/48, M/45] \cup (M/40, M/36] \cup
(M/32, M/27] \cup (M/24, M/12] \cup (M/9, M/8] \cup (M/4, M]$, and let
$\mathcal{S} = \bigcup_{i \ge 1} T_{N_i}$ with $N_i = 48^{2^i}$. Then the set of
$q \in Q_{\mathrm{Hur}}$ with $\mathrm{Nm}(q) \in \mathcal{S}$ has upper density
$17665627/18662400$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 10 (the set `𝒮` from Section 4.1). -/
public theorem_wanted upperDensity_hurwitz_norm_in_interval_union :
    Filter.limsup (fun N : ℕ => ρ (𝐒ᴳ (Set.ofPred fun n : ℕ => 0 < n ∧
        ∃ i : ℕ, 1 ≤ i ∧
          let M : ℚ := ((48 ^ (2 ^ i) : ℕ) : ℚ)
          (M / 48 < n ∧ (n : ℚ) ≤ M / 45) ∨ (M / 40 < n ∧ (n : ℚ) ≤ M / 36) ∨
            (M / 32 < n ∧ (n : ℚ) ≤ M / 27) ∨ (M / 24 < n ∧ (n : ℚ) ≤ M / 12) ∨
            (M / 9 < n ∧ (n : ℚ) ≤ M / 8) ∨ (M / 4 < n ∧ (n : ℚ) ≤ M))) N) Filter.atTop =
      17665627 / 18662400

/-- **Many disjoint geometric progressions among Hurwitz quaternions.** A Hurwitz quaternion is a
quaternion whose four rational coordinates are either all integers or all halves of odd integers;
its norm is the sum of the squares of its coordinates. For a natural number $N$ let $S(N)$ be the
set of nonzero Hurwitz quaternions of norm at most $N$. Fix a Hurwitz quaternion $R$ of norm $2$,
and for a natural number $N$ let $E(N)$ be the set of triples $(bR^{3n}, bR^{3n+1}, bR^{3n+2})$,
where $n$ is a natural number and $b$ is a Hurwitz quaternion whose norm is an odd integer at
most $N / 2^{3n+2}$. Then for every $N$, every triple in $E(N)$ has the form $(a, aR, aR^2)$ with
all three entries in $S(N)$, and two distinct triples in $E(N)$ have no entry in common.
Moreover there is a real constant $C$ such that
$$\Bigl| |E(N)| - \frac{\pi^2 N^2}{21} \Bigr| \le C N (\log N)^2$$
for every natural number $N \ge 2$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 12. -/
public theorem_wanted disjoint_progressions_hurwitz_card (R : Quaternion ℚ) (hR : R ∈ 𝐇)
    (hR2 : Quaternion.normSq R = 2) :
    let E : ℕ → Set (Quaternion ℚ × Quaternion ℚ × Quaternion ℚ) := fun N =>
      Set.ofPred fun t => ∃ n : ℕ, ∃ b ∈ 𝐇, ∃ m : ℕ, Odd m ∧
        Quaternion.normSq b = (m : ℚ) ∧ (m : ℚ) ≤ (N : ℚ) / 2 ^ (3 * n + 2) ∧
        t = (b * R ^ (3 * n), b * R ^ (3 * n + 1), b * R ^ (3 * n + 2))
    (∀ N : ℕ, ∀ t ∈ E N,
      (t.1 ∈ 𝐒 N ∧ t.2.1 ∈ 𝐒 N ∧ t.2.2 ∈ 𝐒 N ∧ t.2.1 = t.1 * R ∧ t.2.2 = t.1 * R ^ 2) ∧
      ∀ t' ∈ E N, t ≠ t' →
        Disjoint ({t.1, t.2.1, t.2.2} : Set (Quaternion ℚ)) {t'.1, t'.2.1, t'.2.2}) ∧
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      |((E N).ncard : ℝ) - Real.pi ^ 2 * (N : ℝ) ^ 2 / 21| ≤ C * N * Real.log N ^ 2

/-- **Upper bound for geometric-progression-free Hurwitz sets.** Let $Q_{\mathrm{Hur}}$ be the
set of Hurwitz quaternions, the rational quaternions whose four coordinates are all integers or
all lie in $\mathbb{Z} + \tfrac12$, and let $\mathrm{Nm}(q)$ be the sum of the squares of the
coordinates of $q$. For $N \in \mathbb{N}$ let $S(N)$ be the set of nonzero
$q \in Q_{\mathrm{Hur}}$ with $\mathrm{Nm}(q) \le N$. Let $A \subseteq Q_{\mathrm{Hur}}$ be free
of 3-term geometric progressions: there are no $a, r \in Q_{\mathrm{Hur}}$ with $a \ne 0$,
$r \ne 0$ and $\mathrm{Nm}(r) \ne 1$ such that $a$, $ar$ and $ar^2$ all lie in $A$. Then the
upper density $\limsup_{N \to \infty} |A \cap S(N)| / |S(N)|$ of $A$ is at most $20/21$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 13. -/
public theorem_wanted upperDensity_le_of_hurwitz_gpFree (A : Set (Quaternion ℚ))
    (hA : GPFree A) :
    Filter.limsup (fun N : ℕ => ρ A N) Filter.atTop ≤ 20 / 21

/-- **Bounds on the supremum of upper densities of geometric-progression-free Hurwitz sets.** Let
$Q_{\mathrm{Hur}}$ be the set of Hurwitz quaternions, the rational quaternions whose four
coordinates are all integers or all lie in $\mathbb{Z} + \tfrac12$, and let $\mathrm{Nm}(q)$ be
the sum of the squares of the coordinates of $q$. For $N \in \mathbb{N}$ let $S(N)$ be the set of
nonzero $q \in Q_{\mathrm{Hur}}$ with $\mathrm{Nm}(q) \le N$, and define the upper density of a
set $A$ of quaternions as $\limsup_{N \to \infty} |A \cap S(N)| / |S(N)|$. Call
$A \subseteq Q_{\mathrm{Hur}}$ free of 3-term geometric progressions if there are no
$a, r \in Q_{\mathrm{Hur}}$ with $a \ne 0$, $r \ne 0$ and $\mathrm{Nm}(r) \ne 1$ such that $a$,
$ar$ and $ar^2$ all lie in $A$. Let $\bar m_{\mathrm{Hur}}$ be the supremum of the upper
densities of such sets. Then $17665627/18662400 \le \bar m_{\mathrm{Hur}} \le 20/21$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Theorem 14 (restated as the unnumbered theorem of the introduction). -/
public theorem_wanted sSup_upperDensity_hurwitz_gpFree_bounds :
    let m : ℝ := sSup (Set.ofPred fun x : ℝ => ∃ A : Set (Quaternion ℚ), (GPFree A) ∧
      Filter.limsup (fun N : ℕ => ρ A N) Filter.atTop = x)
    17665627 / 18662400 ≤ m ∧ m ≤ 20 / 21

/-- **Squarefree norms and the lower density of the quaternion greedy set.** A Hurwitz quaternion is
a quaternion whose four rational coordinates are either all integers or all halves of odd integers;
the norm $\mathrm{Nm}(q)$ of a quaternion $q$ is the sum of the squares of its coordinates. For a
natural number $N$ let $S(N)$ be the set of nonzero Hurwitz quaternions of norm at most $N$. Let
$\mathcal{G}$ be a set of quaternions such that a quaternion $q$ lies in $\mathcal{G}$ if and only
if $q$ is a nonzero Hurwitz quaternion and there are no $a \in \mathcal{G}$ and Hurwitz quaternion
$r \ne 0$ with norm $\mathrm{Nm}(r) \ne 1$, $ar \in \mathcal{G}$ and $q = ar^2$ (this recursion on
the norm characterizes the quaternion greedy set). Then $\mathcal{G}$ contains every Hurwitz
quaternion whose norm is a squarefree natural number, and
$$\liminf_{N \to \infty} \frac{|\mathcal{G} \cap S(N)|}{|S(N)|} \ge \frac{60}{7 \pi^2 \zeta(3)},$$
where $\zeta(3) = \sum_{n \ge 1} n^{-3}$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 17. -/
public theorem_wanted quaternionGreedy_squarefree_norm_and_lowerDensity
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    (∀ q ∈ 𝐇, (∃ n : ℕ, Squarefree n ∧ Quaternion.normSq q = (n : ℚ)) → q ∈ Gq) ∧
      60 / (7 * Real.pi ^ 2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) ≤
        Filter.liminf (fun N : ℕ => ρ Gq N) Filter.atTop

/-- **The quaternion greedy set is not determined by norms.** A Hurwitz quaternion is a quaternion
whose four rational coordinates are either all integers or all halves of odd integers; the norm
$\mathrm{Nm}(q)$ of a quaternion $q$ is the sum of the squares of its coordinates. Let
$\mathcal{G}$ be a set of quaternions such that a quaternion $q$ lies in $\mathcal{G}$ if and only
if $q$ is a nonzero Hurwitz quaternion and there are no $a \in \mathcal{G}$ and Hurwitz quaternion
$r \ne 0$ with norm $\mathrm{Nm}(r) \ne 1$, $ar \in \mathcal{G}$ and $q = ar^2$ (this recursion on
the norm characterizes the quaternion greedy set). Then for every set $G$ of positive integers,
$\mathcal{G}$ is not the set of Hurwitz quaternions whose norm lies in $G$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 18. -/
public theorem_wanted quaternionGreedy_ne_norm_preimage
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) (G : Set ℕ)
    (hG : ∀ n ∈ G, 0 < n) :
    Gq ≠ 𝐒ᴳ G

/-- **The quaternion greedy set and the norm preimage of Rankin's set differ infinitely.** A
Hurwitz quaternion is a quaternion whose four rational coordinates are either all integers or all
halves of odd integers; the norm $\mathrm{Nm}(q)$ of a quaternion $q$ is the sum of the squares of
its coordinates. Let $\mathcal{G}$ be a set of quaternions such that a quaternion $q$ lies in
$\mathcal{G}$ if and only if $q$ is a nonzero Hurwitz quaternion and there are no
$a \in \mathcal{G}$ and Hurwitz quaternion $r \ne 0$ with norm $\mathrm{Nm}(r) \ne 1$,
$ar \in \mathcal{G}$ and $q = ar^2$ (this recursion on the norm characterizes the quaternion
greedy set). Let $G^*_3$ be Rankin's greedy set, the set of positive integers $n$ such that for
every prime $p$ the base-$3$ digits of the exponent of $p$ in $n$ include no digit $2$, and let
$S(G^*_3)$ be the set of Hurwitz quaternions whose norm lies in $G^*_3$. Then both
$\mathcal{G} \setminus S(G^*_3)$ and $S(G^*_3) \setminus \mathcal{G}$ are infinite.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 19. -/
public theorem_wanted quaternionGreedy_diff_rankin_infinite
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    (Gq \ 𝐒ᴳ 𝐆ʳ).Infinite ∧ (𝐒ᴳ 𝐆ʳ \ Gq).Infinite

/-- **Hurwitz quaternions of square norm that are not a unit times a square.** A Hurwitz
quaternion is a quaternion whose four rational coordinates are either all integers or all halves
of odd integers; its norm is the sum of the squares of its coordinates, and a Hurwitz unit is a
Hurwitz quaternion of norm $1$. Let $r$ be a positive integer that is not a sum of three squares
of integers, or that is divisible by an odd integer greater than $24$. Then some Hurwitz
quaternion $Q$ of norm $r^2$ cannot be written as $Q = UR^2$ with $U$ a Hurwitz unit and $R$ a
Hurwitz quaternion of norm $r$. If $r$ is not a sum of three squares of integers, then $Q = r$,
viewed as a quaternion with zero imaginary part, is such a quaternion.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 20. -/
public theorem_wanted exists_hurwitz_norm_sq_not_unit_mul_sq (r : ℕ) (hr : 0 < r)
    (h : (¬ ∃ a b c : ℕ, r = a ^ 2 + b ^ 2 + c ^ 2) ∨ ∃ m : ℕ, Odd m ∧ 24 < m ∧ m ∣ r) :
    (∃ Q ∈ 𝐇, Quaternion.normSq Q = ((r ^ 2 : ℕ) : ℚ) ∧ ¬ IsUnitMulSq Q r) ∧
      ((¬ ∃ a b c : ℕ, r = a ^ 2 + b ^ 2 + c ^ 2) →
        ¬ IsUnitMulSq ((r : ℚ) : Quaternion ℚ) r)

/-- **Quaternions of prime-square norm separating the greedy set from Rankin's set.** A Hurwitz
quaternion is a quaternion whose four rational coordinates are either all integers or all halves
of odd integers; its norm $\mathrm{Nm}(q)$ is the sum of the squares of its coordinates, and a
Hurwitz unit is a Hurwitz quaternion of norm $1$. Let $\mathcal{G}$ be a set of quaternions such
that a quaternion $q$ lies in $\mathcal{G}$ if and only if $q$ is a nonzero Hurwitz quaternion
and there are no $a \in \mathcal{G}$ and Hurwitz quaternion $r \ne 0$ with $\mathrm{Nm}(r) \ne 1$,
$ar \in \mathcal{G}$ and $q = ar^2$ (this recursion on the norm characterizes the quaternion
greedy set). Let $G^*_3$ be Rankin's greedy set, the set of positive integers $n$ such that for
every prime $\ell$ the base-$3$ digits of the exponent of $\ell$ in $n$ include no digit $2$, and
let $S(G^*_3)$ be the set of Hurwitz quaternions whose norm lies in $G^*_3$. Let $p$ be a prime
and $Q$ a Hurwitz quaternion of norm $p^2$ that cannot be written as $Q = UR^2$ with $U$ a
Hurwitz unit and $R$ a Hurwitz quaternion of norm $p$. Then
$Q \in \mathcal{G} \setminus S(G^*_3)$ and $Q^2 \in S(G^*_3) \setminus \mathcal{G}$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 21. -/
public theorem_wanted quaternionGreedy_mem_of_not_unit_mul_sq
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) (p : ℕ) (hp : p.Prime)
    (Q : Quaternion ℚ) (hQ : Q ∈ 𝐇) (hQn : Quaternion.normSq Q = ((p ^ 2 : ℕ) : ℚ))
    (hQU : ¬ IsUnitMulSq Q p) :
    Q ∈ Gq \ 𝐒ᴳ 𝐆ʳ ∧ Q ^ 2 ∈ 𝐒ᴳ 𝐆ʳ \ Gq

end

end MetaMathlibExt
