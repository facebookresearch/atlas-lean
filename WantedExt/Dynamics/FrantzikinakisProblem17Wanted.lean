/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiple ergodic averages problem 17
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.SetNotation
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Dynamics.FrantzikinakisProblem17Wanted

/-! Source record `AMR-047-0017__4800017`. -/

open MeasureTheory
open scoped BigOperators

/-!
# Multiple ergodic averages — Problem 17 ([AMR-047-0017])

Source: Frantzikinakis — Some open problems on multiple ergodic averages (2016),
Problem 17, source item Problem 17, https://arxiv.org/abs/1103.3808.

Clause list from the source (every item appears in the formal text below):
(a) `ℓ : ℕ` — number of polynomials / transformations.
(b) `p i ∈ ℤ[t]` — each `p i` is an integer polynomial (`Polynomial ℤ`),
    indexed by `i : Fin ℓ`.
(c) rational independence of `p₁, …, p_ℓ` — hypothesis `IsRationallyIndependent`.
(d) zero constant term — hypothesis `(p i).coeff 0 = 0`.
(e) ergodic setting — measurable space `X`, probability measure `μ`,
    ℤ-actions `T i : ℤ → (X → X)` with measurability,
    measure preservation, identity and additivity laws.
(f) `A ∈ 𝓧` — measurable set `A : Set X` with `MeasurableSet A`.
(g) `ε > 0` — positive real threshold.
(h) the recurrence times `n ∈ ℕ` are syndetic: some bound `B` such that
    every interval `[m, m + B]` contains a positive recurrence time `n`,
    with polynomials evaluated at `↑n : ℤ`; the transformations are
    required to commute across different indices.
(i) lower bound `μ(A ∩ T₁^{p₁(n)}A ∩ ⋯ ∩ T_ℓ^{p_ℓ(n)}A) ≥ μ(A)^(ℓ+1) - ε`,
    stated with `ENNReal.toReal`.
-/

/-- Rational independence of integer polynomials.

Source: [AMR-047-0017] Frantzikinakis, Some open problems on multiple ergodic
averages (2016), Problem 17, https://arxiv.org/abs/1103.3808: the hypothesis
that `p₁, …, p_ℓ ∈ ℤ[t]` are rationally independent. -/
def IsRationallyIndependent {ℓ : ℕ} (p : Fin ℓ → Polynomial ℤ) : Prop :=
  ∀ c : Fin ℓ → ℤ,
    (∃ a : ℤ, ∑ i, Polynomial.C (c i) * p i = Polynomial.C a) → ∀ i, c i = 0

/-- Multiple recurrence lower bound for rationally independent integer
polynomials with zero constant term.

Source: [AMR-047-0017] Frantzikinakis, Some open problems on multiple ergodic
averages (2016), Problem 17, https://arxiv.org/abs/1103.3808: for every
measurable `A` and every `ε > 0` the set of positive recurrence times `n`
with `μ(A ∩ T₁^{p₁(n)}A ∩ ⋯ ∩ T_ℓ^{p_ℓ(n)}A) ≥ μ(A)^(ℓ+1) - ε` is syndetic
(has bounded gaps); the transformations commute across indices. -/
@[nolint unusedArguments]
def conjecture (ℓ : ℕ) (X : Type*) [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : Fin ℓ → ℤ → (X → X)) (p : Fin ℓ → Polynomial ℤ) : Prop :=
  IsRationallyIndependent p →
    (∀ i, (p i).coeff 0 = 0) →
    (∀ i k, Measurable (T i k)) →
    (∀ i k, MeasurePreserving (T i k) μ μ) →
    (∀ i, T i 0 = id) →
    (∀ i a b x, T i (a + b) x = T i a (T i b x)) →
    (∀ i j a b x, T i a (T j b x) = T j b (T i a x)) →
    ∀ (A : Set X), MeasurableSet A → ∀ (ε : ℝ), 0 < ε →
      ∃ B : ℕ, ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ n ≤ m + B ∧ 0 < n ∧
        (μ (A ∩ Set.iInter fun i => (T i ((p i).eval ((↑n : ℤ)))) ⁻¹' A)).toReal ≥
          (μ A).toReal ^ (ℓ + 1) - ε

/-- Problem 17 for every system: `conjecture ℓ X μ T p` for every number `ℓ` of polynomials, every
probability space `(X, μ)`, all actions `T` and all integer polynomials `p`. -/
def conjectureAll : Prop :=
  ∀ (ℓ : ℕ) (X : Type*) [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (T : Fin ℓ → ℤ → (X → X)) (p : Fin ℓ → Polynomial ℤ), conjecture ℓ X μ T p

/--
Resolved true: Resolved affirmatively by Frantzikinakis and Kuca (Joint ergodicity for commuting
transformations and applications to polynomial sequences, Invent. Math. 239 (2025) 621-706,
arXiv:2207.12288, Corollary 2.11): for linearly independent integer polynomials with zero
constant term and any commuting system, the lower bound μ(A)^{ℓ+1} - ε holds on a set of n with
bounded gaps; the author's progress page (November 2025) marks Problem 17 solved. Source: N.
Frantzikinakis, B. Kuca, Joint ergodicity for commuting transformations and applications to
polynomial sequences, Invent. Math. 239 (2025) 621-706, arXiv:2207.12288,
https://arxiv.org/abs/2207.12288. Moved from `OpenConjectures/Dynamics/FrantzikinakisProblem17`.
-/
public theorem_wanted conjectureAll_holds : conjectureAll

end MathlibExt.Dynamics.FrantzikinakisProblem17Wanted
