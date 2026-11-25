/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.EReal.Basic
public import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Binomid indices

Sequences `η : ℕ → ℕ` are indexed from zero. In the notation of Caalim and Tanaka,
the entry `e_i` for `i ≥ 1` is `η (i - 1)`, and the partial sum `s_n = e_1 + ⋯ + e_n`
is `∑ i ∈ Finset.range n, η i`. Their definitions of binomid indices, lex-minimal extensions
and the right shift appear in Section 1 of *On the monoid of lexicographically minimal
extensions* (arXiv:2505.20018).
-/

namespace MetaMathlibExt

@[expose] public section

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

/-- **Monotone sequences are binomid indices.** Every non-decreasing sequence
$e_1 \le e_2 \le \cdots$ of nonnegative integers is an infinite binomid index.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 1
(`integers-2024-A53-prop-1`). -/
public theorem isBinomidIndex_of_monotone {η : ℕ → ℕ} (hη : Monotone η) :
    IsBinomidIndex η := by
  intro k n hkn
  rw [Finset.sum_Ico_eq_sum_range, Nat.sub_sub_self hkn]
  exact Finset.sum_le_sum fun i _ => hη (Nat.le_add_left i _)

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
      change 0 < γ (Nat.find h)
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

end

end MetaMathlibExt
