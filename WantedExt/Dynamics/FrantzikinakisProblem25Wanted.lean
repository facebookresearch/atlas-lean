/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiple ergodic averages problem 25
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Dynamics.FrantzikinakisProblem25Wanted

/-! Source record `AMR-047-0025__4800025`. -/

open scoped BigOperators

/-!
# Clause list for [AMR-047-0025] Problem 25

Source: Frantzikinakis — Some open problems on multiple ergodic averages (2016),
Source item: Problem 25, arXiv: https://arxiv.org/abs/1103.3808.

(a) `ℓ : ℕ` is the number of functions and the order of recurrence.
(b) `a : Fin ℓ → ℝ → ℝ` is the family `ℱ = {a₁, …, a_ℓ}`.
(c) `a` lies in one Hardy field `H : Set (ℝ → ℝ)`.
(d) each `a i` has polynomial growth.
(e) `spanStar a` is the set `span*(ℱ)` of nonzero real linear combinations.
(f) separation: for every `f ∈ spanStar a`, every `c : ℝ`,
    every `p : Polynomial ℤ`, `|f t - c * p(t)| / Real.log t → ∞` as `t → ∞`.
(g) `([a₁(n)], …, [a_ℓ(n)])` uses integer parts `⌊a i n⌋`.
(h) conclusion: `IsGoodForRecurrence a` for a single transformation `T`.
-/

/-- Hardy-field carrier set.

Source: [AMR-047-0025] Problem 25 (Frantzikinakis 2016, arXiv:1103.3808);
formalizes "in one Hardy field": constants, ring operations,
eventual differentiability with derivative back in the field, and
eventual comparability of germs. -/
def IsHardyFieldSet (H : Set (ℝ → ℝ)) : Prop :=
  (∀ c : ℝ, (fun _ => c) ∈ H) ∧
  (∀ f g : ℝ → ℝ, f ∈ H → g ∈ H → (f + g) ∈ H ∧ (f * g) ∈ H) ∧
  (∀ f : ℝ → ℝ, f ∈ H →
    Filter.Eventually (fun t => f t ≠ 0) Filter.atTop → (fun t => (f t)⁻¹) ∈ H) ∧
  (∀ f : ℝ → ℝ, f ∈ H →
    Filter.Eventually (fun t => DifferentiableAt ℝ f t) Filter.atTop) ∧
  (∀ f : ℝ → ℝ, f ∈ H → deriv f ∈ H) ∧
  (∀ f g : ℝ → ℝ, f ∈ H → g ∈ H →
    Filter.Eventually (fun t => f t ≤ g t) Filter.atTop ∨
    Filter.Eventually (fun t => g t ≤ f t) Filter.atTop)

/-- Common Hardy field membership for the family `ℱ`.

Source: [AMR-047-0025] Problem 25 (Frantzikinakis 2016, arXiv:1103.3808);
formalizes "family of functions ... in one Hardy field". -/
def IsInCommonHardyField {ℓ : ℕ} (a : Fin ℓ → ℝ → ℝ) : Prop :=
  ∃ H : Set (ℝ → ℝ), IsHardyFieldSet H ∧ ∀ i, a i ∈ H

/-- Polynomial growth of a real function.

Source: [AMR-047-0025] Problem 25 (Frantzikinakis 2016, arXiv:1103.3808);
formalizes "functions of polynomial growth". -/
def HasPolynomialGrowth (a : ℝ → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ) (t₀ : ℝ), 0 < C ∧
    ∀ t : ℝ, t₀ ≤ t → |a t| ≤ C * |t| ^ k

/-- Nonzero linear combinations `span*(ℱ)`.

Source: [AMR-047-0025] Problem 25 (Frantzikinakis 2016, arXiv:1103.3808);
formalizes "`span*(ℱ)` denotes its nonzero linear combinations". -/
def spanStar {ℓ : ℕ} (a : Fin ℓ → ℝ → ℝ) : Set (ℝ → ℝ) :=
  {f | ∃ c : Fin ℓ → ℝ, f = (fun t => ∑ i, c i * a i t) ∧ ¬ Filter.EventuallyEq Filter.atTop f 0}

/-- Separation from polynomial multiples.

Source: [AMR-047-0025] Problem 25 (Frantzikinakis 2016, arXiv:1103.3808);
formalizes "for every `a ∈ span*(ℱ)` we have `|a(t) - c*p(t)| / log t → ∞`
(the source's logarithmic separation rate, `|a(t) - c*p(t)| ≻ log t`)
for every `c ∈ ℝ` and `p ∈ ℤ[t]`". -/
def HasHardySeparation {ℓ : ℕ} (a : Fin ℓ → ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, f ∈ spanStar a → ∀ c : ℝ, ∀ p : Polynomial ℤ,
    Filter.Tendsto
      (fun t => |f t - c * Polynomial.eval₂ (Int.castRingHom ℝ) t p| / Real.log t)
      Filter.atTop Filter.atTop

/-- Good for `ℓ`-recurrence of a single transformation.

Source: [AMR-047-0025] Problem 25 (Frantzikinakis 2016, arXiv:1103.3808);
formalizes "the collection `{([a₁(n)]), …, ([a_ℓ(n)])}` is good
for `ℓ`-recurrence of a single transformation": for every invertible
measure-preserving `T` on a probability space and every `A` of positive
measure there is `n ≠ 0` with
`μ (A ∩ ⋂ i, T ^ ⌊a i n⌋ ⁻¹' A) > 0`. -/
def IsGoodForRecurrence {ℓ : ℕ} (a : Fin ℓ → ℝ → ℝ) : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : Equiv.Perm X)
    (hTmeas : Measurable (T : X → X))
    (hTinv : Measurable ((T⁻¹ : Equiv.Perm X) : X → X))
    (hTpres : MeasureTheory.MeasurePreserving (T : X → X) μ μ)
    (A : Set X) (hAmeas : MeasurableSet A) (hApos : μ A > 0),
    ∃ n : ℕ, n ≠ 0 ∧
      μ (A ∩ (⋂ i, (((T ^ (⌊a i (n : ℝ)⌋ : ℤ) : Equiv.Perm X) : X → X) ⁻¹' A))) > 0

/-- Problem 25 statement: Hardy-field polynomial-growth family with the
polynomial separation hypothesis implies goodness for `ℓ`-recurrence.

Source: [AMR-047-0025] Problem 25 (Frantzikinakis 2016, arXiv:1103.3808,
"Show that the collection ... is good for `ℓ`-recurrence of a single
transformation"); stated as an implication proposition. Posed as an open problem
and since solved by Bergelson, Moreira and Richter (see `conjecture_holds` below). -/
def conjecture : Prop :=
  ∀ (ℓ : ℕ) (a : Fin ℓ → ℝ → ℝ),
    IsInCommonHardyField a →
    (∀ i, HasPolynomialGrowth (a i)) →
    HasHardySeparation a →
    IsGoodForRecurrence a

/--
Resolved true: Resolved affirmatively by Bergelson, Moreira and Richter (Multiple ergodic
averages along functions from a Hardy field: convergence, recurrence and combinatorial
applications, Adv. Math. 443 (2024) 109597, arXiv:2006.03558), as recorded on Frantzikinakis's
progress page (November 2025) for Problem 25. Their hypothesis |a(t) - c p(t)| -> ∞ is weaker
than the log-separated hypothesis formalized here, so the formalized statement follows. Source:
V. Bergelson, J. Moreira, F. K. Richter, Multiple ergodic averages along functions from a Hardy
field: convergence, recurrence and combinatorial applications, Adv. Math. 443 (2024) 109597,
arXiv:2006.03558, https://arxiv.org/abs/2006.03558. Moved from
`OpenConjectures/Dynamics/FrantzikinakisProblem25`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Dynamics.FrantzikinakisProblem25Wanted
