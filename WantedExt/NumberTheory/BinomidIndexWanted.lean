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

/-- An infinite binomid index: a sequence of nonnegative integers with
`∑_{i=n-k+1}^{n} e_i ≥ ∑_{i=1}^{k} e_i` for all `1 ≤ k ≤ n`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53; definition as restated
in arXiv:2505.20018, Section 1. -/
public def IsBinomidIndex (η : ℕ → ℕ) : Prop :=
  ∀ k n : ℕ, k ≤ n → ∑ i ∈ Finset.range k, η i ≤ ∑ i ∈ Finset.Ico (n - k) n, η i

/-- Constant sequences are binomid indices.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53. -/
public theorem isBinomidIndex_const (c : ℕ) : IsBinomidIndex fun _ => c := by
  intro k n hk
  simp [Finset.sum_const, Nat.sub_sub_self hk]

/-- `η` is the lex-minimal extension of its first `m` entries: `η` is a
binomid index and is lexicographically at most every binomid index `γ`
with the same first `m` entries.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53; definition as restated
in arXiv:2505.20018, Section 1. -/
public def IsLexMinimalExtensionOf (η : ℕ → ℕ) (m : ℕ) : Prop :=
  IsBinomidIndex η ∧ ∀ γ : ℕ → ℕ, IsBinomidIndex γ → (∀ i < m, γ i = η i) →
    η = γ ∨ ∃ j, (∀ i < j, η i = γ i) ∧ η j < γ j

/-- `η` is a lex-minimal extension (of some finite binomid index); these
form the paper's set `L`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53. -/
public def IsLexMinimalExtension (η : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, IsLexMinimalExtensionOf η m

/-- The zero sequence is the lex-minimal extension of each of its prefixes.

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

/-- The right shift `σ^l`, sending `(e_1, e_2, …)` to `(0^l, e_1, e_2, …)`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53; definition as restated
in arXiv:2505.20018, Section 1. -/
public def binomidShift (l : ℕ) (η : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i < l then 0 else η (i - l)

/-- `σ^0` is the identity.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53. -/
public theorem binomidShift_zero (η : ℕ → ℕ) : binomidShift 0 η = η := by
  funext i
  simp [binomidShift]

/-- Proposition 1: a monotonic increasing sequence of nonnegative integers is
a binomid index.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 1
(`integers-2024-A53-prop-1`). -/
public theorem_wanted isBinomidIndex_of_monotone {η : ℕ → ℕ} (hη : Monotone η) :
    IsBinomidIndex η

/-- Lemma 1: with `s_n = e_1 + ⋯ + e_n`, `η` is a binomid index if and only if
`s_n ≥ s_{n-k} + s_k` for `1 ≤ k < n`; and if `η` is the lex-minimal
extension of its first `m` entries, then `s_n = max_{1 ≤ k < n} (s_{n-k} + s_k)`
for all `n > m` (the maximum over the empty range, for `n = 1`, is `0`).

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

/-- Proposition 3: if a finite binomid index `η = (e_1, …, e_m)` (`m ≥ 1`)
is monotonic increasing, then its lex-minimal extension is the periodic
repetition `η^∞`. The finite index is the first `m` values of `e`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 3
(`integers-2024-A53-prop-3`). -/
public theorem_wanted isLexMinimalExtensionOf_periodic_of_monotoneOn {m : ℕ}
    (hm : 0 < m) {e : ℕ → ℕ} (he : MonotoneOn e (Set.Iio m)) :
    IsLexMinimalExtensionOf (fun i => e (i % m)) m

/-- Proposition 4: the periodic part of a lex-minimal extension does not begin
at the second coordinate: if `(e_2, e_3, …)` is periodic with period `p`,
then `e_1 = e_{1+p}`, so the whole sequence is periodic.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 4
(`integers-2024-A53-prop-4`). -/
public theorem_wanted IsLexMinimalExtension.apply_period_eq_apply_zero {η : ℕ → ℕ}
    (hη : IsLexMinimalExtension η) {p : ℕ} (hp : 0 < p)
    (hper : ∀ i, 1 ≤ i → η (i + p) = η i) : η p = η 0

/-- Proposition 5: a purely periodic infinite binomid index is the
lex-minimal extension of some finite binomid index.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 5
(`integers-2024-A53-prop-5`). -/
public theorem_wanted isLexMinimalExtension_of_periodic {η : ℕ → ℕ}
    (hη : IsBinomidIndex η) {p : ℕ} (hp : 0 < p) (hper : ∀ i, η (i + p) = η i) :
    IsLexMinimalExtension η

/-- Corollary 1: the componentwise sum of two lex-minimal extensions is a
lex-minimal extension (so `L` is a monoid under componentwise addition).

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 1
(`integers-2024-A53-cor-1`). -/
public theorem_wanted IsLexMinimalExtension.add {η₁ η₂ : ℕ → ℕ}
    (h₁ : IsLexMinimalExtension η₁) (h₂ : IsLexMinimalExtension η₂) :
    IsLexMinimalExtension (η₁ + η₂)

/-- Proposition 6: for `l ≠ m`, `σ^l(L) ∩ σ^m(L) = {0^∞}`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 6
(`integers-2024-A53-prop-6`). -/
public theorem_wanted binomidShift_image_inter_eq_zero {l m : ℕ} (hlm : l ≠ m) :
    binomidShift l '' {η | IsLexMinimalExtension η}
        ∩ binomidShift m '' {η | IsLexMinimalExtension η}
      = {fun _ => 0}

/-- Corollary 3: for every prime `p` there are infinitely many `n` such that
`p` divides every binomial coefficient `binom(n, k)` with `1 ≤ k < n`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 3
(`integers-2024-A53-cor-3`). -/
public theorem_wanted infinite_setOf_prime_dvd_choose {p : ℕ} (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → p ∣ n.choose k}.Infinite

/-- Corollary 4: for every prime `p` there are infinitely many `n` such that
every Fibonomial coefficient `[n, k]_F = F_n! / (F_k! F_{n-k}!)` with
`1 ≤ k < n` is an integer multiple of `p` (`F_n!` is
`fibonacciFactorial`).

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 4
(`integers-2024-A53-cor-4`). -/
public theorem_wanted infinite_setOf_prime_dvd_fibonomial {p : ℕ} (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → ∃ z : ℤ,
      fibonacciFactorial n / (fibonacciFactorial k * fibonacciFactorial (n - k))
        = (p : ℚ) * z}.Infinite

/-- Proposition 2: the lex-minimal extension of a finite binomid index is given
greedily. If the first `m ≥ 1` entries of `f` form a finite binomid index and,
for every `j ≥ m`, `f j` is the maximum over `1 ≤ k ≤ j` of
`∑_{i<k} f i - ∑_{j+1-k ≤ i < j} f i` (the paper's
`f_n = max_{1 ≤ k < n} (∑_{i=1}^k f_i - ∑_{i=n-k+1}^{n-1} f_i)` with `n = j + 1`),
then `f` is the lex-minimal extension of its first `m` entries. The maximum is
stated in `ℕ` as: `f j` plus the second sum dominates every first sum, with
equality for some `k`.

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

/-- Corollary 2, first part: if `η` is the lex-minimal extension of its first
`m ≥ 1` entries and `p` is prime, then for every `n > m` some `p^η`-nomid
coefficient `[n, k]_{p^η}` with `1 ≤ k < n` equals `1`. The `f`-nomid
coefficient `[n, k]_f = f_n ⋯ f_{n-k+1} / (f_k ⋯ f_1)` is
`generalizedBinomialCoefficient f k (n - k)`, applied to the `1`-indexed
sequence `i ↦ p ^ η (i - 1)`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 2
(`integers-2024-A53-cor-2`). -/
public theorem_wanted IsLexMinimalExtensionOf.exists_nomid_eq_one {η : ℕ → ℕ} {m : ℕ}
    (hm : 0 < m) (hη : IsLexMinimalExtensionOf η m) {p : ℕ} (hp : p.Prime) {n : ℕ}
    (hn : m < n) :
    ∃ k, 1 ≤ k ∧ k < n ∧
      generalizedBinomialCoefficient (fun i => p ^ η (i - 1)) k (n - k) = 1

/-- Corollary 2, second part: if a binomid index `μ` is not a lex-minimal
extension of any finite binomid index and `p` is prime, then there are
infinitely many `n` such that every `p^μ`-nomid coefficient `[n, k]_{p^μ}`
with `1 ≤ k < n` is an integer multiple of `p`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 2
(`integers-2024-A53-cor-2`). -/
public theorem_wanted infinite_setOf_prime_dvd_nomid_of_not_isLexMinimalExtension
    {μ : ℕ → ℕ} (hμ : IsBinomidIndex μ) (hlex : ¬ IsLexMinimalExtension μ) {p : ℕ}
    (hp : p.Prime) :
    {n : ℕ | ∀ k, 1 ≤ k → k < n → ∃ z : ℤ,
      generalizedBinomialCoefficient (fun i => p ^ μ (i - 1)) k (n - k) = (p : ℚ) * z}.Infinite

/-- The average `A_{i,0}(η) = s_i / i` of the first `i` entries of `η`, where
`s_i = e_1 + ⋯ + e_i` is `∑ l ∈ Finset.range i, η l`; in Lean `A_{0,0} = 0`.
The two-index average `A_{i,l}(η) = (s_{i+l} - s_l) / i` is written inline as
`(∑ j ∈ Finset.Ico l (i + l), η j) / i`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Section 3; the same average
is the sequence `Ave(η)` of Caalim and Tanaka, *Generalized Binomial
Coefficients and the Monoid of Lexicographically Minimal Extensions*,
INTEGERS 26 (2026), Article A113, Section 2. -/
public def binomidAverage (η : ℕ → ℕ) (i : ℕ) : ℚ :=
  ((∑ l ∈ Finset.range i, η l : ℕ) : ℚ) / i

/-- Every average `A_{i,0}` with `i ≥ 1` of the constant sequence `c^∞` equals `c`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Section 3. -/
public theorem binomidAverage_const (c : ℕ) {i : ℕ} (hi : 1 ≤ i) :
    binomidAverage (fun _ => c) i = c := by
  have hi' : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  simp only [binomidAverage, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.cast_mul]
  field_simp

/-- The upper average `A_0(η) = limsup_i A_{i,0}(η)`, valued in `EReal`
(it is `⊤` when `s_i / i` is unbounded).

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Section 3. -/
public noncomputable def binomidUpperAverage (η : ℕ → ℕ) : EReal :=
  Filter.limsup (fun i => ((binomidAverage η i : ℝ) : EReal)) Filter.atTop

/-- The upper average of the constant sequence `c^∞` is `c`.

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

/-- The Average Condition: `A_0(η) = A_{i,0}(η)` for some `i ≥ 1`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3. -/
public def BinomidAverageCondition (η : ℕ → ℕ) : Prop :=
  ∃ i, 1 ≤ i ∧ binomidUpperAverage η = ((binomidAverage η i : ℝ) : EReal)

/-- Constant sequences satisfy the Average Condition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3. -/
public theorem binomidAverageCondition_const (c : ℕ) :
    BinomidAverageCondition fun _ => c :=
  ⟨1, le_rfl, by rw [binomidUpperAverage_const, binomidAverage_const c le_rfl]; norm_cast⟩

/-- Lemma 2, parts 1-3: for a binomid index `η` and `i, l ≥ 1`,
`A_{i,l} ≥ A_{i,0}`, `A_{ki,0} ≥ A_{i,0}` (for `k ≥ 1`), and
`A_{i+l,0} = i/(i+l) A_{i,l} + l/(l+i) A_{l,0}`, with `A_{i,0}` as
`binomidAverage η i` and `A_{i,l}` written out as `(s_{i+l} - s_l) / i`.

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

/-- Lemma 2, part 4: for a binomid index `η`, `A_0(η) = sup_{i ≥ 1} A_{i,0}(η)`
in `EReal`.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 2
(`integers-2024-A53-lem-2`). -/
public theorem_wanted IsBinomidIndex.binomidUpperAverage_eq_iSup {η : ℕ → ℕ}
    (hη : IsBinomidIndex η) :
    binomidUpperAverage η = ⨆ i : ℕ, ⨆ (_ : 1 ≤ i), ((binomidAverage η i : ℝ) : EReal)

/-- Lemma 3: a lex-minimal extension satisfies the Average Condition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3
(`integers-2024-A53-lem-3`). -/
public theorem_wanted IsLexMinimalExtension.binomidAverageCondition {η : ℕ → ℕ}
    (hη : IsLexMinimalExtension η) : BinomidAverageCondition η

/-- Theorem 1: an infinite binomid index satisfying the Average Condition is
the lex-minimal extension of some finite binomid index, and it is eventually
periodic.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Theorem 1
(`integers-2024-A53-thm-1`). -/
public theorem_wanted IsBinomidIndex.isLexMinimalExtension_and_eventually_periodic
    {η : ℕ → ℕ} (hη : IsBinomidIndex η) (hac : BinomidAverageCondition η) :
    IsLexMinimalExtension η ∧ ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → η (n + p) = η n

end

end MetaMathlibExt
