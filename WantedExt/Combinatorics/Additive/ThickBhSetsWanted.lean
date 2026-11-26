/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Combinatorics.Additive.BhSet
public import MathlibExt.Combinatorics.Additive.SingerSet
public import MathlibExt.Combinatorics.Additive.ThickBhSets

/-!
# Constructing thick `B_h`-sets

Statements from Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer
Sequences 27 (2024), Article 24.1.2 (arXiv:2308.12406): the generalized Bose and Singer
constructions of `B_h`-sets in cyclic groups (both proved in
`MathlibExt.Combinatorics.Additive.ThickBhSets`), sufficient conditions for two such sets to be
affinely equivalent, the prime-gap results the paper quotes, and the resulting bounds on
`R_h(n)` and `R_h⁻¹(k)`.

The paper fixes the generator `θ` to be a root of a Conway polynomial; the statements here
are made for every generator `θ` of `K^×`, which is what the paper's proofs use. Residues
`b ∈ ℤ/Mℤ` are represented by natural numbers `b`, since `θ ^ b` depends only on `b mod M`.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- **Membership in a Bose set.** Let $F$ be a finite field with $q$ elements, let $K$ be a field
extension of $F$, let $\theta \in K$, and let $h$ and $b$ be natural numbers. A residue
$a \in \mathbb{Z}/(q^h - 1)\mathbb{Z}$ lies in the Bose set $\mathrm{Bose}_h(q, b)$ built from
$F$, $K$ and $\theta$ if and only if $\theta^a = \theta^b + v$ for some $v \in F$, where
$\theta^a$ means $\theta$ raised to the least nonnegative representative of $a$ (or to $|a|$
when $h = 0$, since then $\mathbb{Z}/(q^h - 1)\mathbb{Z} = \mathbb{Z}$).

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 1. -/
public theorem mem_boseSet {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ) (a : ZMod (Fintype.card F ^ h - 1)) :
    a ∈ boseSet F h θ b ↔ ∃ v : F, θ ^ a.val = θ ^ b + algebraMap F K v :=
  Iff.rfl

/-- **Maximum size of a $B_h$-set in $\{1, \dots, n\}$.** For natural numbers $h$ and $n$, $R_h(n)$
is the largest number of elements of a $B_h$-set of natural numbers contained in
$\{1, \dots, n\}$. If no $B_h$-set is contained in $\{1, \dots, n\}$ (for example when $n = 0$),
then $R_h(n) = 0$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the paragraph before Theorem 5. -/
public noncomputable def bhMaxCard (h n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧
    AdditiveCombinatorics.IsBhSet (A : Set ℕ) h ∧ A.card = k}

/-- **Shortest interval containing a $B_h$-set of given size.** For natural numbers $h$ and $k$,
$R_h^{-1}(k)$ is the smallest natural number $n$ such that some $B_h$-set of natural numbers with
exactly $k$ elements is contained in $\{1, \dots, n\}$; it is $0$ when no such $n$ exists, for
example when $k = 0$, since a $B_h$-set is nonempty.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the paragraph before Theorem 5. -/
public noncomputable def bhMinLength (h k : ℕ) : ℕ :=
  sInf {n | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧
    AdditiveCombinatorics.IsBhSet (A : Set ℕ) h ∧ A.card = k}

private theorem isBhSet_singleton {h : ℕ} (hh : 0 < h) (a : ℕ) :
    AdditiveCombinatorics.IsBhSet ({a} : Set ℕ) h := by
  refine ⟨Set.singleton_nonempty a, hh, ?_⟩
  intro l₁ l₂ h₁ h₂ len₁ len₂ _ _ _
  rw [List.eq_replicate_iff.2 ⟨len₁, fun x hx => h₁ x hx⟩,
    List.eq_replicate_iff.2 ⟨len₂, fun x hx => h₂ x hx⟩]

/-- **$R_h(n)$ is at most $n$.** For all natural numbers $h$ and $n$, let $R_h(n)$ be the largest
size of a $B_h$-set contained in $\{1, \dots, n\}$, or $0$ if there is no such set (for example
when $h = 0$ or $n = 0$). Then $R_h(n) \le n$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition of `R_h(n)` before Theorem 5. -/
public theorem bhMaxCard_le (h n : ℕ) : bhMaxCard h n ≤ n := by
  refine csSup_le' ?_
  rintro k ⟨A, hA, -, rfl⟩
  simpa using Finset.card_le_card hA

/-- **$R_h(1) = 1$.** For every natural number $h \ge 1$, the largest size $R_h(1)$ of a $B_h$-set
contained in $\{1\}$ equals $1$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition of `R_h(n)` before Theorem 5. -/
public theorem bhMaxCard_one {h : ℕ} (hh : 0 < h) : bhMaxCard h 1 = 1 := by
  refine le_antisymm (bhMaxCard_le h 1) ?_
  refine le_csSup ⟨1, ?_⟩ ⟨{1}, by simp, by simpa using isBhSet_singleton hh 1, rfl⟩
  rintro k ⟨A, hA, -, rfl⟩
  simpa using Finset.card_le_card hA

/-- **The shortest interval holding a one-element $B_h$-set.** For every natural number
$h \ge 1$, the smallest natural number $n$ such that $\{1, \dots, n\}$ contains a $B_h$-set with
exactly one element is $1$; that is, $R_h^{-1}(1) = 1$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the paragraph before Theorem 7 ("Clearly, `R_h⁻¹(1) = 1`"). -/
public theorem bhMinLength_one {h : ℕ} (hh : 0 < h) : bhMinLength h 1 = 1 := by
  refine le_antisymm
    (Nat.sInf_le ⟨{1}, by simp, by simpa using isBhSet_singleton hh 1, rfl⟩) ?_
  rw [Nat.one_le_iff_ne_zero, Ne, bhMinLength, Nat.sInf_eq_zero, not_or]
  refine ⟨?_, Set.nonempty_iff_ne_empty.1
    ⟨1, {1}, by simp, by simpa using isBhSet_singleton hh 1, rfl⟩⟩
  rintro ⟨A, hA, -, hcard⟩
  have : A = ∅ := by simpa using hA
  simp [this] at hcard

/-- **Affine equivalences between Bose sets.** Let $F$ be a finite field with $q$ elements and
characteristic $p$, let $h \ge 2$, let $K$ be a field extension of $F$ of degree $h$, and let
$\theta \in K$ have order $|K| - 1$, that is, generate $K^\times$. Let $b$ and $e$ be natural
numbers such that the minimal polynomials of $\theta^b$ and $\theta^e$ over $F$ both have
degree $h$. Suppose that (i) $b \equiv e \pmod{(q^h - 1)/(q - 1)}$, or
(ii) $\theta^b - \theta^e \in F$, or (iii) $b \equiv p^i e \pmod{q^h - 1}$ for some natural
number $i$. Then the Bose sets $\mathrm{Bose}_h(q, b)$ and $\mathrm{Bose}_h(q, e)$ built from
$F$, $K$ and $\theta$ are affinely equivalent.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 4 (items (i)–(iii)) (`jis-2024-24.1.2-thm-4`). -/
public theorem_wanted zModAffinelyEquivalent_boseSet {F K : Type*} [Field F] [Fintype F]
    [Field K] [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h)
    {θ : K} (hθ : orderOf θ = Fintype.card K - 1) {b e : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (he : (minpoly F (θ ^ e)).natDegree = h)
    (hbe : b ≡ e [MOD (Fintype.card F ^ h - 1) / (Fintype.card F - 1)] ∨
      θ ^ b - θ ^ e ∈ Set.range (algebraMap F K) ∨
      ∃ i : ℕ, b ≡ ringChar F ^ i * e [MOD Fintype.card F ^ h - 1]) :
    ZModAffinelyEquivalent (boseSet F h θ b) (boseSet F h θ e)

/-- **Unconditional bounds for $R_h(n)$ and $R_h^{-1}(k)$.** Let $h \ge 2$. Write $R_h(n)$ for the
largest size of a $B_h$-set contained in $\{1, \dots, n\}$, with $R_h(0) = 0$, and $R_h^{-1}(k)$
for the least $n$ such that $\{1, \dots, n\}$ contains a $B_h$-set with $k$ elements, with
$R_h^{-1}(0) = 0$ (a $B_h$-set is nonempty). Then every natural number $n$ satisfies
$R_h(n) \ge n^{1/h} - 2^{44} n^{154/(155h)}$, and every natural number $k$ satisfies
$R_h^{-1}(k) \le k^h + 3^{155h} k^{h - 1/155}$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(a) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_unconditional {h : ℕ} (hh : 2 ≤ h) :
    (∀ n : ℕ, (n : ℝ) ^ (1 / (h : ℝ)) - 2 ^ 44 * (n : ℝ) ^ ((154 : ℝ) / (155 * h)) ≤
      bhMaxCard h n) ∧
    ∀ k : ℕ, (bhMinLength h k : ℝ) ≤
      (k : ℝ) ^ h + 3 ^ (155 * h) * (k : ℝ) ^ ((h : ℝ) - 1 / 155)

/-- **Bounds for $R_h(n)$ and $R_h^{-1}(k)$ beyond $e^{e^{34}}$.** Let $h \ge 2$. Write $R_h(n)$ for
the largest size of a $B_h$-set contained in $\{1, \dots, n\}$ and $R_h^{-1}(k)$ for the least
$n$ such that $\{1, \dots, n\}$ contains a $B_h$-set with $k$ elements. Then every natural number
$n \ge e^{e^{34}}$ satisfies $R_h(n) \ge n^{1/h} - 7 n^{2/(3h)}$, and every natural number
$k \ge e^{e^{34}}$ satisfies $R_h^{-1}(k) \le k^h + (3k)^{h - 1/3}$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(b) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_large {h : ℕ} (hh : 2 ≤ h) :
    (∀ n : ℕ, Real.exp (Real.exp 34) ≤ n →
      (n : ℝ) ^ (1 / (h : ℝ)) - 7 * (n : ℝ) ^ ((2 : ℝ) / (3 * h)) ≤ bhMaxCard h n) ∧
    ∀ k : ℕ, Real.exp (Real.exp 34) ≤ k →
      (bhMinLength h k : ℝ) ≤ (k : ℝ) ^ h + (3 * k : ℝ) ^ ((h : ℝ) - 1 / 3)

/-- **Eventual bounds for $R_h(n)$ and $R_h^{-1}(k)$.** Let $h \ge 2$. Write $R_h(n)$ for the
largest size of a $B_h$-set contained in $\{1, \dots, n\}$ and $R_h^{-1}(k)$ for the least $n$
such that $\{1, \dots, n\}$ contains a $B_h$-set with $k$ elements. Then
$R_h(n) \ge n^{1/h} - n^{21/(40h)}$ for all sufficiently large natural numbers $n$, and
$R_h^{-1}(k) \le k^h + 2^h k^{h - 19/40}$ for all sufficiently large natural numbers $k$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(c) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_eventually {h : ℕ} (hh : 2 ≤ h) :
    (∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / (h : ℝ)) - (n : ℝ) ^ ((21 : ℝ) / (40 * h)) ≤ bhMaxCard h n) ∧
    ∀ᶠ k : ℕ in atTop,
      (bhMinLength h k : ℝ) ≤ (k : ℝ) ^ h + 2 ^ h * (k : ℝ) ^ ((h : ℝ) - 19 / 40)

/-- **Riemann Hypothesis bounds for $R_h(n)$ and $R_h^{-1}(k)$.** Assume the Riemann Hypothesis
and let $h \ge 2$. Write $R_h(n)$ for the largest size of a $B_h$-set contained in
$\{1, \dots, n\}$, with $R_h(0) = 0$ (a $B_h$-set is nonempty), and $R_h^{-1}(k)$ for the least
$n$ such that $\{1, \dots, n\}$ contains a $B_h$-set with $k$ elements, and let $\log$ be the
natural logarithm, with the convention $\log 0 = 0$. Then every natural number $k \ge 1$
satisfies $R_h^{-1}(k) < k^h + \log(20k)\, k^{h - 1/2} + 2 k^{h - 1} (\log(20k))^{2h}$, and
every natural number $n$ satisfies $R_h(n) \ge n^{1/h} - (7 + (\log n)/h)\, n^{1/(2h)}$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(d) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_of_RH (hRH : RiemannHypothesis) {h : ℕ}
    (hh : 2 ≤ h) :
    (∀ k : ℕ, 1 ≤ k → (bhMinLength h k : ℝ) <
      (k : ℝ) ^ h + Real.log (20 * k) * (k : ℝ) ^ ((h : ℝ) - 1 / 2) +
        2 * (k : ℝ) ^ (h - 1) * Real.log (20 * k) ^ (2 * h)) ∧
    ∀ n : ℕ, (n : ℝ) ^ (1 / (h : ℝ)) - (7 + Real.log n / h) * (n : ℝ) ^ (1 / (2 * (h : ℝ))) ≤
      bhMaxCard h n

/-- **Cully-Hugill's theorem for 155th powers.** For every natural number $n \ge 1$ there is a
prime $p$ with $n^{155} < p < (n + 1)^{155}$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 6 (Cully-Hugill) (`jis-2024-24.1.2-thm-6`). -/
public theorem_wanted exists_prime_between_pow_155 (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 155 < p ∧ p < (n + 1) ^ 155

/-- **Unconditional bounds for $R_h^{-1}(k)$, $k \ge 4$, and $R_h(n)$, $n \ge h + 3$.** Let
$h \ge 2$. Write $R_h(n)$ for the largest size of a $B_h$-set contained in $\{1, \dots, n\}$ and
$R_h^{-1}(k)$ for the least $n$ such that $\{1, \dots, n\}$ contains a $B_h$-set with $k$
elements. Then every natural number $k \ge 4$ satisfies
$R_h^{-1}(k) < k^h + 3^{155h} k^{h - 1/155}$, and every natural number $n \ge h + 3$ satisfies
$R_h(n) \ge n^{1/h} - 2^{44} n^{154/(155h)}$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 7 (`jis-2024-24.1.2-thm-7`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_ge_explicit {h : ℕ} (hh : 2 ≤ h) :
    (∀ k : ℕ, 4 ≤ k → (bhMinLength h k : ℝ) <
      (k : ℝ) ^ h + 3 ^ (155 * h) * (k : ℝ) ^ ((h : ℝ) - 1 / 155)) ∧
    ∀ n : ℕ, h + 3 ≤ n →
      (n : ℝ) ^ (1 / (h : ℝ)) - 2 ^ 44 * (n : ℝ) ^ ((154 : ℝ) / (155 * h)) ≤ bhMaxCard h n

/-- **Cully-Hugill's theorem for cubes.** For every natural number $n > \exp(\exp(32.537))$ there
is a prime $p$ with $n^3 < p < (n + 1)^3$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 8 (Cully-Hugill) (`jis-2024-24.1.2-thm-8`). -/
public theorem_wanted exists_prime_between_cubes_of_large (n : ℕ)
    (hn : Real.exp (Real.exp 32.537) < n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3

/-- **Strict bounds for thick $B_h$-sets beyond $e^{e^{34}}$.** Let $h \ge 2$. For natural
numbers $n$ and $k$, let $R_h(n)$ be the largest size of a $B_h$-set of natural numbers contained
in $\{1, \dots, n\}$, and let $R_h^{-1}(k)$ be the smallest $n$ such that $\{1, \dots, n\}$
contains a $B_h$-set with exactly $k$ elements. Then every natural number $k > e^{e^{34}}$
satisfies $R_h^{-1}(k) < k^h + (3k)^{h - 1/3}$, and every natural number $n > e^{e^{34}}$
satisfies $R_h(n) > n^{1/h} - 7 n^{2/(3h)}$.

The printed theorem leaves $n$ unquantified; the hypothesis on $n$ is taken from Theorem 5(b).

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 9 (`jis-2024-24.1.2-thm-9`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_gt_large {h : ℕ} (hh : 2 ≤ h) :
    (∀ k : ℕ, Real.exp (Real.exp 34) < k →
      (bhMinLength h k : ℝ) < (k : ℝ) ^ h + (3 * k : ℝ) ^ ((h : ℝ) - 1 / 3)) ∧
    ∀ n : ℕ, Real.exp (Real.exp 34) < n →
      (n : ℝ) ^ (1 / (h : ℝ)) - 7 * (n : ℝ) ^ ((2 : ℝ) / (3 * h)) < bhMaxCard h n

/-- **Baker–Harman–Pintz theorem.** There is a real number $x_0$ such that for every real
$x \ge x_0$ there is a prime $p$ with $x - x^{21/40} \le p \le x$ and a prime $p'$ with
$x \le p' \le x + x^{21/40}$.

This is the form quoted in the paper, which prints the first interval as $[x - x^{21/40}, n]$
with $n$ undefined; the right endpoint is read as $x$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 10 (Baker, Harman and Pintz) (`jis-2024-24.1.2-thm-10`). -/
public theorem_wanted eventually_exists_prime_short_intervals :
    ∀ᶠ x : ℝ in atTop,
      (∃ p : ℕ, p.Prime ∧ x - x ^ ((21 : ℝ) / 40) ≤ p ∧ (p : ℝ) ≤ x) ∧
      ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + x ^ ((21 : ℝ) / 40)

/-- **Eventual strict upper bound for $R_h^{-1}(k)$ and lower bound for $R_h(n)$.** Let $h \ge 2$.
Write $R_h(n)$ for the largest size of a $B_h$-set contained in $\{1, \dots, n\}$ and
$R_h^{-1}(k)$ for the least $n$ such that $\{1, \dots, n\}$ contains a $B_h$-set with $k$
elements. Then $R_h^{-1}(k) < k^h + 2^h k^{h - 19/40}$ for all sufficiently large natural
numbers $k$, and $R_h(n) \ge n^{1/h} - n^{21/(40h)}$ for all sufficiently large natural
numbers $n$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 11 (`jis-2024-24.1.2-thm-11`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_ge_eventually {h : ℕ} (hh : 2 ≤ h) :
    (∀ᶠ k : ℕ in atTop,
      (bhMinLength h k : ℝ) < (k : ℝ) ^ h + 2 ^ h * (k : ℝ) ^ ((h : ℝ) - 19 / 40)) ∧
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / (h : ℝ)) - (n : ℝ) ^ ((21 : ℝ) / (40 * h)) ≤ bhMaxCard h n

/-- **Dudek–Grenié–Molteni theorem.** Assume the Riemann Hypothesis. Then for every natural
number $n \ge 2$ there is a prime $p$ with
$n^2 < p < \bigl(n + (1 + 1/\log n)^2 \log n\bigr)^2$, where $\log$ is the natural logarithm.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 12 (`jis-2024-24.1.2-thm-12`). -/
public theorem_wanted exists_prime_between_sq_of_RH (hRH : RiemannHypothesis) (n : ℕ)
    (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ ((n : ℝ) ^ 2 < p) ∧
      (p : ℝ) < ((n : ℝ) + (1 + 1 / Real.log n) ^ 2 * Real.log n) ^ 2

/-- **Riemann Hypothesis bounds for $R_h^{-1}(k)$, $k \ge 4$, and $R_h(n)$, $n \ge h + 3$.** Assume
the Riemann Hypothesis and let $h \ge 2$. Write $R_h(n)$ for the largest size of a $B_h$-set
contained in $\{1, \dots, n\}$ and $R_h^{-1}(k)$ for the least $n$ such that $\{1, \dots, n\}$
contains a $B_h$-set with $k$ elements, and let $\log$ be the natural logarithm. Then every
natural number $k \ge 4$ satisfies
$R_h^{-1}(k) < k^h + \log(20k)\, k^{h - 1/2} + 2 k^{h - 1} (\log(20k))^{2h}$, and every natural
number $n \ge h + 3$ satisfies $R_h(n) \ge n^{1/h} - (7 + (\log n)/h)\, n^{1/(2h)}$.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 13 (`jis-2024-24.1.2-thm-13`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_ge_of_RH (hRH : RiemannHypothesis) {h : ℕ}
    (hh : 2 ≤ h) :
    (∀ k : ℕ, 4 ≤ k → (bhMinLength h k : ℝ) <
      (k : ℝ) ^ h + Real.log (20 * k) * (k : ℝ) ^ ((h : ℝ) - 1 / 2) +
        2 * (k : ℝ) ^ (h - 1) * Real.log (20 * k) ^ (2 * h)) ∧
    ∀ n : ℕ, h + 3 ≤ n →
      (n : ℝ) ^ (1 / (h : ℝ)) - (7 + Real.log n / h) * (n : ℝ) ^ (1 / (2 * (h : ℝ))) ≤
        bhMaxCard h n

end

end MetaMathlibExt
