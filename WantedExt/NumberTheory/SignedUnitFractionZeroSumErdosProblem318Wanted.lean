/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Vanishing signed unit fraction sums (Erdős Problem 318)

Erdős Problem 318: let `A ⊆ ℕ` be an infinite arithmetic progression and `f : A → {-1, 1}`
non-constant. Must some finite nonempty `S ⊂ A` have `∑_{n ∈ S} f(n)/n = 0`? What if `A` is any set
of positive density? What if `A` is the set of squares other than `1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.SignedUnitFractionZeroSumErdosProblem318Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #318, https://www.erdosproblems.com/318 (status SOLVED
(LEAN)). UnsolvedMath record UM-00002044 (`EP-318`), dataset ulamai/UnsolvedMath v1.8.0.

One target per question, for the property `P₁` of a set `A` of positive integers. Arithmetic
progressions are `{a + k d}` with `a, d ≥ 1`. Positive density is read as natural density `δ > 0`,
the stronger hypothesis, so the refutation of the second question is the stronger statement.
Compared with the formal-conjectures statement `ErdosProblems/318.lean` (equivalent to
`erdos_318.variants.infinite_AP`, `erdos_318.parts.i` and `erdos_318.parts.ii`; no code imported).
-/

open Filter Topology

/-- Property `P₁` of a set `A` of positive integers: for every non-constant `f : A → {-1, 1}`
some finite nonempty `S ⊆ A` has `∑_{n ∈ S} f(n)/n = 0`. -/
def HasSignedZeroSums (A : Set ℕ) : Prop :=
  ∀ f : ℕ → ℤ, (∀ n ∈ A, f n = 1 ∨ f n = -1) → (∃ m ∈ A, ∃ n ∈ A, f m ≠ f n) →
    ∃ S : Finset ℕ, S.Nonempty ∧ (S : Set ℕ) ⊆ A ∧ ∑ n ∈ S, (f n : ℚ) / n = 0

/-- Erdős Problem 318, first question: every infinite arithmetic progression
`{a + k d : k ∈ ℕ}` of positive integers has property `P₁`. -/
def arithmeticProgressionsHaveSignedZeroSums : Prop :=
  ∀ a d : ℕ, 1 ≤ a → 1 ≤ d → HasSignedZeroSums {n | ∃ k : ℕ, n = a + k * d}

/-- Erdős Problem 318, second question: every set of positive integers with positive natural
density has property `P₁`. -/
def positiveDensitySetsHaveSignedZeroSums : Prop :=
  ∀ A : Set ℕ, 0 ∉ A →
    (∃ δ : ℝ, 0 < δ ∧ Tendsto (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 δ)) →
      HasSignedZeroSums A

/-- Erdős Problem 318, third question: the squares other than `1` have property `P₁`. -/
def nontrivialSquaresHaveSignedZeroSums : Prop :=
  HasSignedZeroSums {n | ∃ k : ℕ, 2 ≤ k ∧ n = k ^ 2}

/--
Resolved true: Sattler proved that every infinite arithmetic progression has property `P₁` (Erdős
and Straus had the case `A = ℕ`, Sattler the odd numbers). erdosproblems.com/318 lists the problem
as solved. Source: T. F. Bloom, Erdős Problems, Problem #318, https://www.erdosproblems.com/318
(status SOLVED (LEAN)); resolution: R. Sattler, On Erdős property P1 for the arithmetical sequence,
Nederl. Akad. Wetensch. Indag. Math. (1982), 347-352 (first question); R. Sattler, On Erdős property
P1 for the sequence of squarefree numbers, Nederl. Akad. Wetensch. Indag. Math. (1982), 341-346,
crediting Erdős (second question); D. Larsen, Erdős problem 318 (2026),
github.com/Larsen-Daniel/Erdos-318/blob/main/318.pdf (third question), erdosproblems.com/318:
Sattler proved every arithmetic progression has the property; it fails for any A containing exactly
one even number; Larsen proved it for the squares other than 1, https://www.erdosproblems.com/318.
-/
public theorem_wanted arithmeticProgressionsHaveSignedZeroSums_holds :
    arithmeticProgressionsHaveSignedZeroSums

/--
Resolved false: the property fails for every `A` containing exactly one even number, e.g. the odd
numbers together with `2` (density `1/2`): with `f(2) = -1` and `f = 1` on odd numbers, a sum
containing `1/2` has even reduced denominator and the others are positive (an observation of Erdős
recorded by Sattler). erdosproblems.com/318 lists the problem as solved. Source: T. F. Bloom, Erdős
Problems, Problem #318, https://www.erdosproblems.com/318 (status SOLVED (LEAN)); resolution: R.
Sattler, On Erdős property P1 for the arithmetical sequence, Nederl. Akad. Wetensch. Indag. Math.
(1982), 347-352 (first question); R. Sattler, On Erdős property P1 for the sequence of squarefree
numbers, Nederl. Akad. Wetensch. Indag. Math. (1982), 341-346, crediting Erdős (second question); D.
Larsen, Erdős problem 318 (2026), github.com/Larsen-Daniel/Erdos-318/blob/main/318.pdf (third
question), erdosproblems.com/318: Sattler proved every arithmetic progression has the property; it
fails for any A containing exactly one even number; Larsen proved it for the squares other than 1,
https://www.erdosproblems.com/318.
-/
public theorem_wanted positiveDensitySetsHaveSignedZeroSums_refuted :
    ¬ positiveDensitySetsHaveSignedZeroSums

/--
Resolved true: Larsen proved that the squares other than `1` have property `P₁` (with `1` it fails,
as `∑_{k ≥ 2} 1/k² < 1`). erdosproblems.com/318 lists the problem as solved. Source: T. F. Bloom,
Erdős Problems, Problem #318, https://www.erdosproblems.com/318 (status SOLVED (LEAN)); resolution:
R. Sattler, On Erdős property P1 for the arithmetical sequence, Nederl. Akad. Wetensch. Indag. Math.
(1982), 347-352 (first question); R. Sattler, On Erdős property P1 for the sequence of squarefree
numbers, Nederl. Akad. Wetensch. Indag. Math. (1982), 341-346, crediting Erdős (second question); D.
Larsen, Erdős problem 318 (2026), github.com/Larsen-Daniel/Erdos-318/blob/main/318.pdf (third
question), erdosproblems.com/318: Sattler proved every arithmetic progression has the property; it
fails for any A containing exactly one even number; Larsen proved it for the squares other than 1,
https://www.erdosproblems.com/318.
-/
public theorem_wanted nontrivialSquaresHaveSignedZeroSums_holds :
    nontrivialSquaresHaveSignedZeroSums

end MathlibExt.NumberTheory.SignedUnitFractionZeroSumErdosProblem318Wanted
