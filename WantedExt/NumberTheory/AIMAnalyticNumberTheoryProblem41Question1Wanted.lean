/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elliott's conjecture along a subsequence, two-point case (AimPL Sarnak's conjecture, Problem 7.4)

AimPL: Sarnak's conjecture, Section 7 "Generalizations", Problem 7.4, first question,
<https://aimpl.org/sarnakconjecture/7/> (UnsolvedMath record AIM-ANALYTIC_NUMBER_THEORY-0041; its
second question is the entry `AIMAnalyticNumberTheoryProblem41`): suppose that `f : ℕ → ℂ` is
multiplicative and, for all fixed Dirichlet characters `χ mod q` and `t ∈ ℝ`,
`∑_p (1 - Re f(p) χ̄(p) p^{it}) / p = ∞`. Does there exist a sequence `X_j → ∞` with
`∑_{n ≤ X_j} f(n) \overline{f(n+1)} = o(X_j)`?

Conventions. The problem is about Elliott's conjecture, whose functions are `1`-bounded, so `f`
is taken with `|f(n)| ≤ 1` (without a bound the hypothesis is far too weak: it does not even force
`f(n) = O(1)`).
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Nat.Prime.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.AIMAnalyticNumberTheoryProblem41Question1Wanted

open Filter Topology

/-- The non-pretentiousness hypothesis of Problem 7.4: for every Dirichlet character `χ` of every
modulus `q ≥ 1` and every `t ∈ ℝ`, the series `∑_p (1 - Re f(p) χ̄(p) p^{it}) / p` over the
primes diverges (its terms are nonnegative when `|f| ≤ 1`). -/
def IsNonPretentious (f : ArithmeticFunction ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
    ¬ Summable (fun p : Nat.Primes =>
      (1 - (f p * starRingEnd ℂ (χ (p : ZMod q)) * ((p : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)).re) /
        (p : ℝ))

/-- The class of functions in Problem 7.4: `1`-bounded multiplicative non-pretentious functions. -/
def IsAdmissible (f : ArithmeticFunction ℂ) : Prop :=
  f.IsMultiplicative ∧ (∀ n, ‖f n‖ ≤ 1) ∧ IsNonPretentious f

/-- Problem 7.4, first question: every admissible `f` has a sequence of scales `X_j → ∞` along
which `(1 / X_j) ∑_{1 ≤ n ≤ X_j} f(n) \overline{f(n+1)} → 0`. -/
def subsequenceTwoPoint : Prop :=
  ∀ f : ArithmeticFunction ℂ, IsAdmissible f →
    ∃ X : ℕ → ℕ, Tendsto X atTop atTop ∧
      Tendsto (fun j => (∑ n ∈ Finset.Icc 1 (X j), f n * starRingEnd ℂ (f (n + 1))) / (X j : ℂ))
        atTop (𝓝 0)

/--
Resolved true: Klurman, Mangerel and Teräväinen (arXiv:2304.05344, Theorem 1.1) prove that for
multiplicative f₁, f₂ : ℕ → 𝔻 with f₁ non-pretentious the two-point correlations (1/x)∑_{n≤x}
f₁(n+h₁)f₂(n+h₂) tend to 0 along a set of x of full upper logarithmic density; with f₁ = f and
f₂ = f̄ this answers the first question of AimPL Problem 7.4 positively, as the page's remark by
J. Teräväinen records. The second question remains open (entry
AIMAnalyticNumberTheoryProblem41). Source: O. Klurman, A. P. Mangerel and J. Teräväinen, On
Elliott's conjecture and applications, arXiv:2304.05344 (2023), Theorem 1.1,
https://arxiv.org/abs/2304.05344. Moved from
`OpenConjectures/NumberTheory/AIMAnalyticNumberTheoryProblem41Question1`.
-/
public theorem_wanted subsequenceTwoPoint_holds : subsequenceTwoPoint

end MathlibExt.NumberTheory.AIMAnalyticNumberTheoryProblem41Question1Wanted
