/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.LiminfLimsup
public import MathlibExt.Combinatorics.Enumerative.TotienomialCoefficient
public import MathlibExt.NumberTheory.GeneralizedFibocatalanNumber

namespace MetaMathlibExt

@[expose] public section

/-! Indices are `η : ℕ → ℕ` read from `0`: the paper's entry `e_i` (`i ≥ 1`)
is `η (i - 1)`, and the paper's partial sum `s_n = e_1 + ⋯ + e_n` is
`∑ i ∈ Finset.range n, η i`. The definitions of binomid index, lex-minimal
extension and the shift `σ^l` are stated as in the authors' follow-up
paper (Caalim and Tanaka, *On the monoid of lexicographically minimal
extensions*, arXiv:2505.20018, Section 1), which restates them from this
paper. -/

/-- **Binomid index.** An infinite binomid index is a sequence $(e_1, e_2, \dots)$ of
nonnegative integers such that $\sum_{i=n-k+1}^{n} e_i \ge \sum_{i=1}^{k} e_i$ for all
$1 \le k \le n$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53; definition as restated
in arXiv:2505.20018, Section 1. -/
public def IsBinomidIndex (η : ℕ → ℕ) : Prop :=
  ∀ k n : ℕ, k ≤ n → ∑ i ∈ Finset.range k, η i ≤ ∑ i ∈ Finset.Ico (n - k) n, η i

/-- **Constant sequences are binomid indices.** For every natural number $c$, the constant
sequence $(c, c, c, \dots)$ is a binomid index.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53. -/
public theorem isBinomidIndex_const (c : ℕ) : IsBinomidIndex fun _ => c := by
  intro k n hk
  simp [Finset.sum_const, Nat.sub_sub_self hk]

/-- **Lex-minimal extension.** Let $e = (e_1, e_2, \dots)$ be a sequence of nonnegative integers
and $m \ge 0$. Then $e$ is the lex-minimal extension of $(e_1, \dots, e_m)$ when $e$ is an
infinite binomid index and, for every infinite binomid index $g$ with $g_i = e_i$ for all
$i \le m$, either $g = e$ or $e$ is lexicographically smaller than $g$: there is a $j$ with
$e_i = g_i$ for all $i < j$ and $e_j < g_j$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53; definition as restated
in arXiv:2505.20018, Section 1. -/
public def IsLexMinimalExtensionOf (η : ℕ → ℕ) (m : ℕ) : Prop :=
  IsBinomidIndex η ∧ ∀ γ : ℕ → ℕ, IsBinomidIndex γ → (∀ i < m, γ i = η i) →
    η = γ ∨ ∃ j, (∀ i < j, η i = γ i) ∧ η j < γ j

/-- **Lex-minimal extensions.** A sequence $e = (e_1, e_2, \dots)$ of nonnegative integers is a
lex-minimal extension when, for some $m \ge 0$, it is the lex-minimal extension of
$(e_1, \dots, e_m)$. The set of all lex-minimal extensions is denoted $L$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53. -/
public def IsLexMinimalExtension (η : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, IsLexMinimalExtensionOf η m

/-- **The zero sequence is lex-minimal.** For every $m \ge 0$, the zero sequence
$(0, 0, \dots)$ is the lex-minimal extension of its first $m$ entries.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53. -/
public theorem isLexMinimalExtensionOf_zero (m : ℕ) :
    IsLexMinimalExtensionOf (fun _ => 0) m := by
  refine ⟨isBinomidIndex_const 0, fun γ _ _ => ?_⟩
  classical
  by_cases h : ∃ i, γ i ≠ 0
  · right
    refine ⟨Nat.find h, fun i hi => ?_, ?_⟩
    · have := Nat.find_min h hi
      simp only [ne_eq, not_not] at this
      simp [this]
    · have := Nat.find_spec h
      show 0 < γ (Nat.find h)
      omega
  · left
    funext i
    push Not at h
    simp [h i]

/-- **Right shift of a sequence.** For a natural number $l$, the right shift $\sigma^l$ sends a
sequence $\eta = (e_1, e_2, \dots)$ of nonnegative integers to the sequence
$(0, \dots, 0, e_1, e_2, \dots)$ obtained by prepending $l$ zeros: its first $l$ entries are $0$
and its $(l + i)$-th entry is $e_i$ for every $i \ge 1$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53; definition as restated
in arXiv:2505.20018, Section 1. -/
public def binomidShift (l : ℕ) (η : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i < l then 0 else η (i - l)

/-- **Shifting by zero places is the identity.** For every sequence $\eta$ of nonnegative
integers, $\sigma^0(\eta) = \eta$, where $\sigma^l$ is the right shift that prepends $l$ zeros.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53. -/
public theorem binomidShift_zero (η : ℕ → ℕ) : binomidShift 0 η = η := by
  funext i
  simp [binomidShift]

/-- **Monotone sequences are binomid indices.** Every non-decreasing sequence
$e_1 \le e_2 \le \cdots$ of nonnegative integers is an infinite binomid index.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 1
(`integers-2024-A53-prop-1`). -/
public theorem_wanted isBinomidIndex_of_monotone {η : ℕ → ℕ} (hη : Monotone η) :
    IsBinomidIndex η

/-- **Partial-sum characterization of binomid indices.** Let $\eta = (e_1, e_2, \dots)$ be a
sequence of nonnegative integers with partial sums $s_n = e_1 + \dots + e_n$ (so $s_0 = 0$).
Then $\eta$ is a binomid index if and only if $s_{n-k} + s_k \le s_n$ for all $k$ and $n$ with
$1 \le k < n$. Moreover, for every $m$, if $\eta$ is the lex-minimal extension of its first $m$
entries, then for every $n > m$
$$s_n = \max_{1 \le k < n} (s_{n-k} + s_k),$$
where the maximum over the empty range (for $n = 1$) is taken to be $0$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 1
(`integers-2024-A53-lem-1`). -/
public theorem_wanted isBinomidIndex_iff_partialSum (η : ℕ → ℕ) :
    (IsBinomidIndex η ↔ ∀ k n : ℕ, 1 ≤ k → k < n →
      ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i
        ≤ ∑ i ∈ Finset.range n, η i) ∧
    ∀ m : ℕ, IsLexMinimalExtensionOf η m → ∀ n : ℕ, m < n →
      ∑ i ∈ Finset.range n, η i
        = (Finset.Ico 1 n).sup fun k =>
            ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i

/-- **Monotone finite binomid indices extend periodically.** Let $m \ge 1$ and let
$e_1 \le e_2 \le \cdots \le e_m$ be nonnegative integers. Then the periodic sequence
$(e_1, \dots, e_m, e_1, \dots, e_m, \dots)$ is the lex-minimal extension of $(e_1, \dots, e_m)$.

A non-decreasing finite sequence is automatically a finite binomid index.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 3
(`integers-2024-A53-prop-3`). -/
public theorem_wanted isLexMinimalExtensionOf_periodic_of_monotoneOn {m : ℕ}
    (hm : 0 < m) {e : ℕ → ℕ} (he : MonotoneOn e (Set.Iio m)) :
    IsLexMinimalExtensionOf (fun i => e (i % m)) m

/-- **A lex-minimal extension periodic from its second entry is periodic.** Let
$\eta = (e_1, e_2, \dots)$ be a lex-minimal extension and let $p \ge 1$. If $e_{i+p} = e_i$
for every $i \ge 2$, then $e_{1+p} = e_1$, so the whole sequence $\eta$ is periodic with
period $p$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 4
(`integers-2024-A53-prop-4`). -/
public theorem_wanted IsLexMinimalExtension.apply_period_eq_apply_zero {η : ℕ → ℕ}
    (hη : IsLexMinimalExtension η) {p : ℕ} (hp : 0 < p)
    (hper : ∀ i, 1 ≤ i → η (i + p) = η i) : η p = η 0

/-- **Periodic binomid indices are lex-minimal extensions.** If an infinite binomid index
$e = (e_1, e_2, \dots)$ is periodic, that is, there is $p \ge 1$ with $e_{i+p} = e_i$ for all
$i$, then $e$ is a lex-minimal extension: it is the lex-minimal extension of
$(e_1, \dots, e_m)$ for some $m \ge 0$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 5
(`integers-2024-A53-prop-5`). -/
public theorem_wanted isLexMinimalExtension_of_periodic {η : ℕ → ℕ}
    (hη : IsBinomidIndex η) {p : ℕ} (hp : 0 < p) (hper : ∀ i, η (i + p) = η i) :
    IsLexMinimalExtension η

/-- **Lex-minimal extensions are closed under addition.** If $\eta_1$ and $\eta_2$ are
lex-minimal extensions, then their componentwise sum $\eta_1 + \eta_2$ is a lex-minimal
extension.

Since the zero sequence is also a lex-minimal extension, the set $L$ of lex-minimal extensions
is a monoid under componentwise addition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 1
(`integers-2024-A53-cor-1`). -/
public theorem_wanted IsLexMinimalExtension.add {η₁ η₂ : ℕ → ℕ}
    (h₁ : IsLexMinimalExtension η₁) (h₂ : IsLexMinimalExtension η₂) :
    IsLexMinimalExtension (η₁ + η₂)

/-- **Distinct shifts of lex-minimal extensions meet only in zero.** Let $L$ be the set of
lex-minimal extensions, and for a natural number $l$ let $\sigma^l$ be the right shift that
prepends $l$ zeros to a sequence. For natural numbers $l \neq m$,
$\sigma^l(L) \cap \sigma^m(L) = \{(0, 0, 0, \dots)\}$: the only sequence in both images is
the zero sequence.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 6
(`integers-2024-A53-prop-6`). -/
public theorem_wanted binomidShift_image_inter_eq_zero {l m : ℕ} (hlm : l ≠ m) :
    binomidShift l '' {η | IsLexMinimalExtension η}
        ∩ binomidShift m '' {η | IsLexMinimalExtension η}
      = {fun _ => 0}

/-- **Primes divide all inner binomial coefficients of infinitely many rows.** For every prime
$p$ there are infinitely many natural numbers $n$ such that $p$ divides the binomial coefficient
$\binom{n}{k}$ for every $k$ with $1 \le k < n$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 3
(`integers-2024-A53-cor-3`). -/
public theorem_wanted infinite_setOf_prime_dvd_choose {p : ℕ} (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → p ∣ n.choose k}.Infinite

/-- **Primes divide all inner Fibonomial coefficients of infinitely many rows.** Let $F_n$ be
the Fibonacci numbers and $F_n! = F_1 F_2 \cdots F_n$ the Fibonacci factorial. For every prime
$p$ there are infinitely many natural numbers $n$ such that for every $k$ with $1 \le k < n$ the
Fibonomial coefficient $F_n! / (F_k! \, F_{n-k}!)$ is an integer multiple of $p$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 4
(`integers-2024-A53-cor-4`). -/
public theorem_wanted infinite_setOf_prime_dvd_fibonomial {p : ℕ} (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → ∃ z : ℤ,
      fibonacciFactorial n / (fibonacciFactorial k * fibonacciFactorial (n - k))
        = (p : ℚ) * z}.Infinite

/-- **The lex-minimal extension is computed greedily.** Let $m \ge 1$ and let
$f = (f_1, f_2, \dots)$ be a sequence of nonnegative integers whose first $m$ entries form a
finite binomid index, that is, $\sum_{i=n-k+1}^{n} f_i \ge \sum_{i=1}^{k} f_i$ for all
$1 \le k \le n \le m$. Suppose that for every $n > m$ the entry $f_n$ equals the maximum,
over $1 \le k < n$, of the integers $\sum_{i=1}^{k} f_i - \sum_{i=n-k+1}^{n-1} f_i$. Then $f$
is the lex-minimal extension of $(f_1, \dots, f_m)$.

The differences are taken in the integers and may be negative; the condition says that
$f_n + \sum_{i=n-k+1}^{n-1} f_i \ge \sum_{i=1}^{k} f_i$ for every $1 \le k < n$, with equality
for some such $k$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 2
(`integers-2024-A53-prop-2`). -/
public theorem_wanted isLexMinimalExtensionOf_of_greedy {m : ℕ} (hm : 0 < m) {f : ℕ → ℕ}
    (hpre : ∀ k n : ℕ, k ≤ n → n ≤ m →
      ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.Ico (n - k) n, f i)
    (hle : ∀ j, m ≤ j → ∀ k, 1 ≤ k → k ≤ j →
      ∑ i ∈ Finset.range k, f i ≤ f j + ∑ i ∈ Finset.Ico (j + 1 - k) j, f i)
    (hex : ∀ j, m ≤ j → ∃ k, 1 ≤ k ∧ k ≤ j ∧
      ∑ i ∈ Finset.range k, f i = f j + ∑ i ∈ Finset.Ico (j + 1 - k) j, f i) :
    IsLexMinimalExtensionOf f m

/-- **Lex-minimal extensions have a nomid coefficient equal to one.** Let $m \ge 1$, let
$\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of its first $m$ entries, and let $p$ be a
prime. Write $f_i = p^{e_i}$ for $i \ge 1$ and, for $1 \le k \le n$, let
$[n, k]_f = \frac{f_n f_{n-1} \cdots f_{n-k+1}}{f_k f_{k-1} \cdots f_1}$ be the $f$-nomid
coefficient, the generalized binomial coefficient of $f$. Then for every $n > m$ there is some $k$
with $1 \le k < n$ and $[n, k]_f = 1$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 2
(`integers-2024-A53-cor-2`). -/
public theorem_wanted IsLexMinimalExtensionOf.exists_nomid_eq_one {η : ℕ → ℕ} {m : ℕ}
    (hm : 0 < m) (hη : IsLexMinimalExtensionOf η m) {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : m < n) :
    ∃ k, 1 ≤ k ∧ k < n ∧
      generalizedBinomialCoefficient (fun i => p ^ η (i - 1)) k (n - k) = 1

/-- **Nomid coefficients of binomid indices that are not lex-minimal extensions.** Let
$\mu = (e_1, e_2, \dots)$ be a binomid index such that for no $m$ is $\mu$ the lex-minimal
extension of its first $m$ entries, and let $p$ be a prime. Write $f_i = p^{e_i}$ for $i \ge 1$
and let $[n, k]_f = \frac{f_n f_{n-1} \cdots f_{n-k+1}}{f_k f_{k-1} \cdots f_1}$ be the
$f$-nomid coefficient. Then there are infinitely many natural numbers $n$ such that for every $k$
with $1 \le k < n$ the coefficient $[n, k]_f$ is an integer multiple of $p$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 2
(`integers-2024-A53-cor-2`). -/
public theorem_wanted infinite_setOf_prime_dvd_nomid_of_not_isLexMinimalExtension
    {μ : ℕ → ℕ} (hμ : IsBinomidIndex μ) (hlex : ¬ IsLexMinimalExtension μ) {p : ℕ}
    (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → ∃ z : ℤ,
      generalizedBinomialCoefficient (fun i => p ^ μ (i - 1)) k (n - k) = (p : ℚ) * z}.Infinite

/-- **Initial averages of a sequence.** For a sequence $\eta = (e_1, e_2, \dots)$ of
nonnegative integers and $i \ge 1$, the average $A_{i,0}(\eta)$ is the rational number
$s_i / i$, where $s_i = e_1 + \dots + e_i$ is the sum of the first $i$ entries; for $i = 0$
the value is $A_{0,0}(\eta) = 0$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Section 3; the same average
is the sequence `Ave(η)` of Caalim and Tanaka, *Generalized Binomial
Coefficients and the Monoid of Lexicographically Minimal Extensions*,
INTEGERS 26 (2026), Article A113, Section 2. -/
public def binomidAverage (η : ℕ → ℕ) (i : ℕ) : ℚ :=
  ((∑ l ∈ Finset.range i, η l : ℕ) : ℚ) / i

/-- **Averages of a constant sequence.** For every natural number $c$ and every $i \ge 1$,
the average $A_{i,0}$ of the first $i$ entries of the constant sequence $(c, c, c, \dots)$
equals $c$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Section 3. -/
public theorem binomidAverage_const (c : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    binomidAverage (fun _ => c) i = c := by
  have hi' : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  simp only [binomidAverage, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.cast_mul]
  field_simp

/-- **Upper average of a sequence.** For a sequence $\eta = (e_1, e_2, \dots)$ of nonnegative
integers with partial sums $s_i = e_1 + \dots + e_i$ and averages $A_{i,0}(\eta) = s_i / i$,
the upper average of $\eta$ is $A_0(\eta) = \limsup_{i \to \infty} A_{i,0}(\eta)$, taken in
the extended real numbers; it is $+\infty$ when $s_i / i$ is unbounded.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Section 3. -/
public noncomputable def binomidUpperAverage (η : ℕ → ℕ) : EReal :=
  Filter.limsup (fun i => ((binomidAverage η i : ℝ) : EReal)) Filter.atTop

/-- **Upper average of a constant sequence.** For every natural number $c$, the upper average
$A_0$ of the constant sequence $(c, c, c, \dots)$ equals $c$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Section 3. -/
public theorem binomidUpperAverage_const (c : ℕ) :
    binomidUpperAverage (fun _ => c) = ((c : ℝ) : EReal) := by
  have h : (fun i => ((binomidAverage (fun _ => c) i : ℝ) : EReal)) =ᶠ[Filter.atTop]
      fun _ => ((c : ℝ) : EReal) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with i hi
    rw [binomidAverage_const c hi]
    simp
  rw [binomidUpperAverage, Filter.limsup_congr h, Filter.limsup_const]

/-- **The Average Condition.** A sequence $\eta = (e_1, e_2, \dots)$ of nonnegative integers
satisfies the Average Condition when its upper average $A_0(\eta)$, the limit superior as
$n \to \infty$ of the averages $A_{n,0}(\eta) = (e_1 + \dots + e_n)/n$ taken in the extended
real line, equals $A_{i,0}(\eta)$ for some $i \ge 1$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3. -/
public def BinomidAverageCondition (η : ℕ → ℕ) : Prop :=
  ∃ i, 1 ≤ i ∧ binomidUpperAverage η = ((binomidAverage η i : ℝ) : EReal)

/-- **Constant sequences satisfy the Average Condition.** For every natural number $c$, the
constant sequence $(c, c, c, \dots)$ satisfies the Average Condition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3. -/
public theorem binomidAverageCondition_const (c : ℕ) :
    BinomidAverageCondition fun _ => c :=
  ⟨1, le_rfl, by rw [binomidUpperAverage_const, binomidAverage_const c le_rfl]; norm_cast⟩

/-- **Averages of a binomid index.** Let $\eta = (e_1, e_2, \dots)$ be a binomid index, write
$s_n = e_1 + \dots + e_n$, and for $i \ge 1$ and $l \ge 0$ let $A_{i,l} = (s_{i+l} - s_l)/i$
be the average of $e_{l+1}, \dots, e_{l+i}$. Then for all $i, l \ge 1$: $A_{i,l} \ge A_{i,0}$;
$A_{ki,0} \ge A_{i,0}$ for every $k \ge 1$; and
$A_{i+l,0} = \frac{i}{i+l} A_{i,l} + \frac{l}{l+i} A_{l,0}$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 2
(`integers-2024-A53-lem-2`). -/
public theorem_wanted IsBinomidIndex.binomidAverage_props {η : ℕ → ℕ} (hη : IsBinomidIndex η)
    {i l : ℕ} (hi : 1 ≤ i) (hl : 1 ≤ l) :
    binomidAverage η i ≤ ((∑ j ∈ Finset.Ico l (i + l), η j : ℕ) : ℚ) / i ∧
      (∀ k, 1 ≤ k → binomidAverage η i ≤ binomidAverage η (k * i)) ∧
      binomidAverage η (i + l) =
        (i : ℚ) / (i + l) * (((∑ j ∈ Finset.Ico l (i + l), η j : ℕ) : ℚ) / i) +
          (l : ℚ) / (l + i) * binomidAverage η l

/-- **The upper average of a binomid index is the supremum of its averages.** Let $\eta$ be a
binomid index, let $s_i$ be the sum of its first $i$ entries, let $A_{i,0}(\eta) = s_i / i$ for
$i \ge 1$, and let $A_0(\eta) = \limsup_{i \to \infty} A_{i,0}(\eta)$ be its upper average.
Then, in the extended real numbers, $A_0(\eta) = \sup_{i \ge 1} A_{i,0}(\eta)$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 2
(`integers-2024-A53-lem-2`). -/
public theorem_wanted IsBinomidIndex.binomidUpperAverage_eq_iSup {η : ℕ → ℕ}
    (hη : IsBinomidIndex η) :
    binomidUpperAverage η = ⨆ i : ℕ, ⨆ (_ : 1 ≤ i), ((binomidAverage η i : ℝ) : EReal)

/-- **Lex-minimal extensions satisfy the Average Condition.** Every lex-minimal extension
satisfies the Average Condition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3
(`integers-2024-A53-lem-3`). -/
public theorem_wanted IsLexMinimalExtension.binomidAverageCondition {η : ℕ → ℕ}
    (hη : IsLexMinimalExtension η) : BinomidAverageCondition η

/-- **The Average Condition gives eventually periodic lex-minimal extensions.** If an
infinite binomid index $e = (e_1, e_2, \dots)$ satisfies the Average Condition, then $e$ is
a lex-minimal extension, that is, the lex-minimal extension of $(e_1, \dots, e_m)$ for some
$m \ge 0$, and $e$ is eventually periodic: there are $N$ and $p \ge 1$ such that
$e_{n+p} = e_n$ for all $n \ge N$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Theorem 1
(`integers-2024-A53-thm-1`). -/
public theorem_wanted IsBinomidIndex.isLexMinimalExtension_and_eventually_periodic
    {η : ℕ → ℕ} (hη : IsBinomidIndex η) (hac : BinomidAverageCondition η) :
    IsLexMinimalExtension η ∧ ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → η (n + p) = η n

end

end MetaMathlibExt
