/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# A minimal excludant over overpartitions (statements)

Statement-only targets from Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over
Overpartitions*, Journal of Integer Sequences 27 (2024), Article 24.7.1. `σ_r mex̄(n)` sums, over
the repo's `Nat.Overpartition n`,
the least positive integer occurring fewer than `r` times among the non-overlined parts;
`σmex̄ = σ_1 mex̄`. q-series are over ℂ with `‖q‖ < 1` and the repo `qPochhammerInfRaw`.
The quoted modular-form results (Theorems 14, 15, 18 and Proposition 17) are not stated.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of overpartitions.** For a natural number $n$, $\overline{p}(n)$ is the number of
overpartitions of $n$, that is, of pairs consisting of a partition $p$ of $n$ and a set of
overlined part sizes, each of which occurs as a part of $p$. For example, $\overline{p}(3) = 8$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Section 1. -/
public noncomputable def overpartitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Overpartition n)


open Filter
open QPochhammer

/--
**Number of non-overlined copies of a part size.** For an overpartition $O$ of $n$ and a natural
number $a$, the number of non-overlined parts of size $a$ in $O$ is the multiplicity of $a$ in the
underlying partition of $O$, minus $1$ if $a$ is overlined in $O$ and minus $0$ otherwise.

This matches the convention that only the first occurrence of a part size may be overlined: an
overpartition records each overlined size once.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `mex̄_r`.
-/
public def nonOverlinedCount {n : ℕ} (O : Nat.Overpartition n) (a : ℕ) : ℕ :=
  O.toPartition.parts.count a - if a ∈ O.overlines then 1 else 0

/--
**Minimal excludant of an overpartition with a multiplicity bound.** For natural numbers $r \ge 1$
and $n$ and an overpartition $O$ of $n$, $\overline{\mathrm{mex}}_r(O)$ is the least positive
integer $k$ that occurs fewer than $r$ times among the non-overlined parts of $O$. Such a $k$
exists, since $n + 1$ is not a part of $O$. For $r = 0$, which the paper does not use, the value
is $0$ by convention.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `mex̄_r`.
-/
public def leastGapOverpartition (r : ℕ) {n : ℕ} (O : Nat.Overpartition n) : ℕ :=
  if hr : r = 0 then 0
  else
    Nat.find (show ∃ k : ℕ,
        1 ≤ k ∧ nonOverlinedCount O k < r from by
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hnotmem : n + 1 ∉ O.toPartition.parts := by
        intro hmem
        have hle : n + 1 ≤ O.toPartition.parts.sum :=
          Multiset.le_sum_of_mem hmem
        rw [O.toPartition.parts_sum] at hle
        omega
      have hcount : O.toPartition.parts.count (n + 1) = 0 :=
        Multiset.count_eq_zero.mpr hnotmem
      exact ⟨n + 1, Nat.zero_lt_succ n, by
        simp [nonOverlinedCount, hcount, hrpos]⟩)

/--
**Three-colored distinct-part partitions.** For a natural number $n$, $D_3(n)$ is the number of
triples $(A, B, C)$ of subsets of $\{1, \dots, n\}$ such that the sum of the elements of $A$, the
sum of the elements of $B$ and the sum of the elements of $C$ add up to $n$. Here $A$, $B$, $C$
are the parts of the three colors of a partition of $n$ whose parts of each color are distinct.

A size may occur in several colors but at most once in each, as in the product
$\prod_{m \ge 1} (1 + q^m)^3$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public def D3 (n : ℕ) : ℕ :=
  ((((Finset.Icc 1 n).powerset.product (Finset.Icc 1 n).powerset).product
    (Finset.Icc 1 n).powerset).filter fun p =>
      p.1.1.sum id + p.1.2.sum id + p.2.sum id = n).card

/-- **Sums of minimal excludants over overpartitions.** For natural numbers $r$ and $n$,
$\sigma_r\overline{\mathrm{mex}}(n)$ is the sum, over all overpartitions $\pi$ of $n$, of
$\overline{\mathrm{mex}}_r(\pi)$, the least positive integer occurring fewer than $r$ times
among the non-overlined parts of $\pi$; for $r = 0$ the value $\overline{\mathrm{mex}}_0(\pi)$
is $0$ by convention, so $\sigma_0\overline{\mathrm{mex}}(n) = 0$. We write
$\sigma\overline{\mathrm{mex}}(n) = \sigma_1\overline{\mathrm{mex}}(n)$.

By direct enumeration, $\sigma\overline{\mathrm{mex}}(n) = 1, 3, 6, 13, 24$ for $n = 0, \dots, 4$,
and $\sigma_2\overline{\mathrm{mex}}(2) = 5$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definitions of `σmex̄` and `σ_r mex̄`. -/
public noncomputable def sigmaMexOverpartition (r n : ℕ) : ℕ :=
  ∑ O : Nat.Overpartition n, leastGapOverpartition r O

/-- **The number of overpartitions of zero.** The number $\overline{p}(0)$ of overpartitions of
$0$ equals $1$: the empty overpartition is the only one.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Section 1 (`p̄(0) = 1`). -/
public theorem overpartitionCount_zero : overpartitionCount 0 = 1 :=
  Fintype.card_eq_one_iff.mpr ⟨Nat.Overpartition.ofPartition default, fun _ =>
    Nat.Overpartition.eq_of_zero _ _⟩

/--
**Three-colored distinct-part partitions of $0$.** The number $D_3(0)$ of partitions of $0$ into
parts of three colors, with the parts of each color distinct, equals $1$: the empty partition is
the only one.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_zero : D3 0 = 1 := by
  decide

/--
**Three-colored distinct-part partitions of $1$.** The number $D_3(1)$ of partitions of $1$ into
parts of three colors, with the parts of each color distinct, equals $3$: the single part $1$
takes one of the three colors.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_one : D3 1 = 3 := by
  decide

/--
**Three-colored distinct-part partitions of $2$.** The number $D_3(2)$ of partitions of $2$ into
parts of three colors, with the parts of each color distinct, equals $6$: the single part $2$ in
one of three colors, or two parts $1$ in two different colors.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_two : D3 2 = 6 := by
  decide

/--
**The overpartition mex sum counts three-colored distinct-part partitions.** For an
overpartition $\pi$, let $\overline{\mathrm{mex}}(\pi)$ be the least positive integer that does
not occur among the non-overlined parts of $\pi$, and let $\sigma\overline{\mathrm{mex}}(n)$ be
the sum of $\overline{\mathrm{mex}}(\pi)$ over all overpartitions $\pi$ of $n$. For every
positive integer $n$, $\sigma\overline{\mathrm{mex}}(n) = D_3(n)$, the number of partitions of
$n$ into distinct parts in three colors: the number of triples $(A, B, C)$ of subsets of
$\{1, \dots, n\}$ whose three element sums add up to $n$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 2.
-/
public theorem_wanted sigmaMexOverpartition_eq_D3 (n : ℕ) (hn : 0 < n) :
    sigmaMexOverpartition 1 n = D3 n

/--
**Asymptotic formula for the overpartition mex sum.** Let $\sigma\overline{\mathrm{mex}}(n)$ be
the sum, over all overpartitions $\pi$ of $n$, of $\overline{\mathrm{mex}}(\pi)$, the least
positive integer that does not occur among the non-overlined parts of $\pi$. Then
$\sigma\overline{\mathrm{mex}}(n) \sim e^{\pi\sqrt{n}} / (8 n^{3/4})$ as $n \to \infty$, that is,
the ratio of the two sides tends to $1$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 3.
-/
public theorem_wanted sigmaMexOverpartition_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (sigmaMexOverpartition 1 n : ℝ))
      (fun n => Real.exp (Real.pi * Real.sqrt n) /
        (8 * (n : ℝ) ^ ((3 : ℝ) / 4)))

/--
**Parity of the overpartition mex sum.** For an overpartition $\pi$, let
$\overline{\mathrm{mex}}(\pi)$ be the least positive integer that does not occur among the
non-overlined parts of $\pi$, and let $\sigma\overline{\mathrm{mex}}(n)$ be the sum of
$\overline{\mathrm{mex}}(\pi)$ over all overpartitions $\pi$ of $n$. For every positive integer
$n$, $\sigma\overline{\mathrm{mex}}(n)$ is odd if $n = j(j+1)/2$ is a triangular number for some
natural number $j$, and even otherwise.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 4.
-/
public theorem_wanted sigmaMexOverpartition_parity (n : ℕ) (hn : 0 < n) :
    ((∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 1) ∧
    ((¬∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 0)

/--
**Generating function of the overpartition r-mex sums.** Let $r$ be a positive integer and $q$
a complex number with $|q| < 1$. Write $(a;q)_\infty = \prod_{j \ge 0} (1 - a q^j)$, and let
$\sigma_r\overline{\mathrm{mex}}(n)$ be the sum over all overpartitions $\pi$ of $n$ of
$\overline{\mathrm{mex}}_r(\pi)$, the least positive integer occurring fewer than $r$ times among
the non-overlined parts of $\pi$. Then
$$
\sum_{n \ge 0} \sigma_r\overline{\mathrm{mex}}(n)\, q^n =
\frac{(-q;q)_\infty\,(q^{2r};q^{2r})_\infty}{(q;q)_\infty\,(q^r;q^{2r})_\infty}.
$$

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 6.
-/
public theorem_wanted sigmaMexOverpartition_generating_function
    (r : ℕ) (hr : 0 < r) (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (sigmaMexOverpartition r n : ℂ) * q ^ n) =
      qPochhammerInfRaw (-q) q * qPochhammerInfRaw (q ^ (2 * r)) (q ^ (2 * r)) /
        (qPochhammerInfRaw q q *
          qPochhammerInfRaw (q ^ r) (q ^ (2 * r)))

/--
**Asymptotic formula for the overpartition r-mex sums.** Let $r$ be a positive integer and let
$\sigma_r\overline{\mathrm{mex}}(n)$ be the sum over all overpartitions $\pi$ of $n$ of
$\overline{\mathrm{mex}}_r(\pi)$, the least positive integer occurring fewer than $r$ times among
the non-overlined parts of $\pi$. Then
$\sigma_r\overline{\mathrm{mex}}(n) \sim e^{\pi\sqrt{n}} / (8 \sqrt{r}\, n^{3/4})$ as
$n \to \infty$, that is, the ratio of the two sides tends to $1$.

The denominator $8\sqrt{r}$ follows the published version of the paper; arXiv v1 prints $8r$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 7.
-/
public theorem_wanted sigmaMexOverpartition_r_asymptotic (r : ℕ) (hr : 0 < r) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (sigmaMexOverpartition r n : ℝ))
      (fun n => Real.exp (Real.pi * Real.sqrt n) /
        (8 * Real.sqrt r * (n : ℝ) ^ ((3 : ℝ) / 4)))

/--
**Density of overpartition r-mex sums divisible by powers of two.** Let $m$, $e$ and $k$ be
natural numbers with $k \ge 1$, let $r = 2^m 3^e$, and let
$\sigma_r\overline{\mathrm{mex}}(n)$ be the sum over all overpartitions $\pi$ of $n$ of
$\overline{\mathrm{mex}}_r(\pi)$, the least positive integer occurring fewer than $r$ times among
the non-overlined parts of $\pi$. Then the natural numbers $n$ with
$2^k \mid \sigma_r\overline{\mathrm{mex}}(n)$ have natural density $1$: the number of such $n$
with $n \le X$, divided by $X$, tends to $1$ as $X \to \infty$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 8.
-/
public theorem_wanted sigmaMexOverpartition_power_density
    (m e k : ℕ) (hk : 1 ≤ k) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter fun n =>
          Nat.ModEq (2 ^ k) (sigmaMexOverpartition (2 ^ m * 3 ^ e) n) 0).card : ℝ) /
          (X : ℝ))
      atTop (nhds 1)

/--
**Ingham's Tauberian theorem.** Let $a : \mathbb{N} \to \mathbb{R}$ be nonnegative and weakly
increasing, let $A : \mathbb{C} \to \mathbb{C}$ be a function, and let $\alpha$, $\beta$, $C$
be real numbers with $C > 0$. Suppose that for every complex $q$ with $|q| < 1$ the series
$\sum_{n \ge 0} a(n) q^n$ is summable with sum $A(q)$, and that for every complex $q$ with
$|q| > 1$ it is not summable. Suppose also that $A(e^{-t}) \sim \alpha t^\beta e^{C/t}$ as
$t \to 0^+$ through positive reals, and that for every $\Delta > 0$,
$A(e^{-z}) = O(|z|^\beta e^{C/|z|})$ as $z \to 0$ within the cone
$\{z \in \mathbb{C} : \mathrm{Re}\, z > 0,\ |\mathrm{Im}\, z| \le \Delta\, \mathrm{Re}\, z\}$.
Then, as $n \to \infty$,
$$a(n) \sim \frac{\alpha}{2\sqrt{\pi}} C^{(2\beta + 1)/4} n^{-(2\beta + 3)/4} e^{2\sqrt{Cn}}.$$

Nothing is assumed about the series on the circle $|q| = 1$, since radius of convergence one
permits either behavior there.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 9.
-/
public theorem_wanted ingham_tauberian
    (a : ℕ → ℝ) (A : ℂ → ℂ) (α β C : ℝ)
    (hseries : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n : ℕ => (a n : ℂ) * q ^ n) (A q))
    (hradius : ∀ q : ℂ, 1 < ‖q‖ →
      ¬Summable (fun n : ℕ => (a n : ℂ) * q ^ n))
    (hnonneg : ∀ n : ℕ, 0 ≤ a n)
    (hmono : Monotone a)
    (hC : 0 < C)
    (hreal : Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0))
      (fun t : ℝ => A (Real.exp (-t)))
      (fun t : ℝ => (α * t ^ β * Real.exp (C / t) : ℝ)))
    (hcomplex : ∀ Δ : ℝ, 0 < Δ →
      Asymptotics.IsBigO
        (nhdsWithin 0 {z : ℂ | 0 < z.re ∧ |z.im| ≤ Δ * z.re})
        (fun z : ℂ => A (Complex.exp (-z)))
        (fun z : ℂ => ((‖z‖ ^ β * Real.exp (C / ‖z‖) : ℝ) : ℂ))) :
    Asymptotics.IsEquivalent atTop a
      (fun n : ℕ =>
        α / (2 * Real.sqrt Real.pi) * C ^ ((2 * β + 1) / 4) *
          (n : ℝ) ^ (-(2 * β + 3) / 4) *
          Real.exp (2 * Real.sqrt (C * n)))

/--
**The r-mex sum of overpartitions as a sum of overpartition counts.** Let $n$ and $r$ be
natural numbers with $r \ge 1$, let $\overline{p}(m)$ be the number of overpartitions of $m$, let
$T_k = k(k+1)/2$ be the $k$-th triangular number, and let $\sigma_r\overline{\mathrm{mex}}(n)$ be
the sum over all overpartitions $\pi$ of $n$ of $\overline{\mathrm{mex}}_r(\pi)$, the least
positive integer occurring fewer than $r$ times among the non-overlined parts of $\pi$. Then
$$\sigma_r\overline{\mathrm{mex}}(n) = \sum_{k \ge 0,\; rT_k \le n} \overline{p}(n - rT_k).$$

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 10.
-/
public theorem_wanted sigmaMexOverpartition_eq_sum_shifted_count
    (n r : ℕ) (hr : 1 ≤ r) :
    (∑ k ∈ (Finset.range (n + 1)).filter
      (fun k => r * (k * (k + 1) / 2) ≤ n),
      overpartitionCount (n - r * (k * (k + 1) / 2))) =
      sigmaMexOverpartition r n

/--
**Eta-quotient congruence for sums of overpartition minimal excludants.** Let $r \ge 1$ and
$k \ge 1$ be integers, and for $n \ge 0$ let $\sigma_r \overline{\mathrm{mex}}(n)$ be the sum, over
all overpartitions of $n$, of the least positive integer occurring fewer than $r$ times among the
non-overlined parts. Then there are integers $c_0, c_1, c_2, \dots$ such that for every complex $q$
with $|q| < 1$, writing $f_d = (q^d; q^d)_\infty = \prod_{m \ge 1} (1 - q^{dm})$,
$$q^{3r} \frac{f_{48} f_{24r}^{2^k - 1}}{f_{24}^2 f_{48r}^{2^{k-1} - 2}} = \sum_{j \ge 0} c_j q^j,$$
and for every $j \ge 0$ we have $c_j \equiv \sigma_r \overline{\mathrm{mex}}(n) \pmod{2^k}$ when
$j = 24n + 3r$ with $n \ge 0$, and $c_j \equiv 0 \pmod{2^k}$ otherwise.

The exponent $2^{k-1} - 2$ is an integer; at $k = 1$ it equals $-1$, so $f_{48r}$ then appears
in the numerator.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 16.
-/
public theorem_wanted etaQuotient_sigmaMexOverpartition_modEq
    (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ c : ℕ → ℤ,
      (∀ q : ℂ, ‖q‖ < 1 →
        q ^ (3 * r) *
            qPochhammerInfRaw (q ^ 48) (q ^ 48) *
            qPochhammerInfRaw (q ^ (24 * r)) (q ^ (24 * r)) ^
              ((2 : ℕ) ^ k - 1) /
          (qPochhammerInfRaw (q ^ 24) (q ^ 24) ^ 2 *
            qPochhammerInfRaw (q ^ (48 * r)) (q ^ (48 * r)) ^
              ((2 : ℤ) ^ (k - 1) - 2)) =
          ∑' j : ℕ, (c j : ℂ) * q ^ j) ∧
      ∀ j : ℕ,
        Int.ModEq ((2 : ℤ) ^ k) (c j)
          (if 3 * r ≤ j ∧ 24 ∣ j - 3 * r then
            (sigmaMexOverpartition r ((j - 3 * r) / 24) : ℤ)
          else 0)

end

end MetaMathlibExt
