/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.SupremumOfSelectorProcesses` — annals_supremum_of_selector_processes (manifest `manifests/problems/annals_supremum_of_selector_processes.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.SupremumOfSelectorProcessesWanted` namespace. Mathematical
statements are unchanged. Source: J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.SetBernoulli
open ProbabilityTheory

@[expose] public section

namespace MathlibExt.Analysis.SupremumOfSelectorProcessesWanted
/-!
# Notation for AnnalsChallenge

This file defines notation (mostly probability-theoretic) for the AnnalsChallenge project.

Ported verbatim from `AnnalsChallenge/Notation.lean` in
<https://github.com/ImperialCollegeLondon/AnnalsChallenge> (v1.0.0, `e32eb14`). It is a
trusted support module, not a benchmark problem: it contains no `sorry` and no
`@[eval_problem]` declarations. It is imported by `LeanEval.Analysis.RademacherEnfloType`
and `LeanEval.Analysis.SupremumOfSelectorProcesses`.
-/

set_option autoImplicit false

namespace ProbabilityTheory

open MeasureTheory Lean

/-- Suppose `P : Measure Ω`, `X : Ω → E`:

`𝔼[X; P] = ∫ ω, ↑(X ω) ∂P`

is notation for the integral (expectation) of a function `X` with respect to the measure `P`. -/
macro "𝔼[" X:term "; " P:term "]" : term => `(∫ ω, ↑($X ω) ∂$P)

/-- Suppose `μ : Measure E`

`𝔼[t; X ∼ μ] = ∫ X; t ∂μ`

where `X` is a variable and `t` is a term (possibly) depending on `X`. In probability theory
this represents the expectation of a function of `X` when `X` has law `μ`. For example we
could write `𝔼[X ^ 2; X ∼ μ]` for the second moment of `μ`.
-/
notation "𝔼[" t "; " X " ∼ " μ "]" => MeasureTheory.integral μ (fun X ↦ ↑t)

/-- Suppose `P : Measure Ω`, `X : Ω → ℝ≥0∞`:

`𝔼⁻[X; P] = ∫⁻ ω, ↑(X ω) ∂P`

is notation for the lintegral (expectation) of a function `X` with respect to the measure `P`. -/
macro "𝔼⁻[" X:term "; " P:term "]" : term => `(∫⁻ ω, ↑($X ω) ∂$P)

/-- Suppose `μ : Measure ℝ≥0∞`

`𝔼[t; X ∼ μ] = ∫ X; t ∂μ`

where `X` is a variable and `t` is a term (possibly) depending on `X`. In probability theory
this represents the expectation of a function of `X` when `X` has law `μ`. For example we
could write `𝔼⁻[X ^ 2; X ∼ μ]` for the second moment of `μ`.
-/
notation "𝔼⁻[" t "; " X " ∼ " μ "]" => MeasureTheory.lintegral μ (fun X ↦ ↑t)

end ProbabilityTheory

/-!
# Main Statements from On a conjecture of Talagrand on selector processes and a consequence
# on positive empirical processes

We formalise the statements of the main results from J. Park and H. T. Pham,
`On a conjecture of Talagrand on selector processes and a consequence on positive empirical
processes`, Annals of Math, 199 (3) 2024.
-/

set_option autoImplicit false

namespace SupremumOfSelectorProcesses

open MeasureTheory ProbabilityTheory Measure unitInterval Finset

open scoped NNReal ENNReal

/-- Definition of a binomial random subset of `X` with parameter `p`. -/
noncomputable def binomialSetDistribution (X : Type*) (p : I) : Measure (Set X) :=
  setBernoulli Set.univ p

open Classical in
/-- Definition of a collection of sets being `p-small`. -/
def IsSmall {X : Type*} [Fintype X] (p : I) (𝓕 : Set (Set X)) : Prop :=
  ∃ 𝓖 : Set (Set X), 𝓕 ⊆ ⋃ s ∈ 𝓖, {t | s ⊆ t} ∧ (∑ s ∈ 𝓖, (p : ℝ) ^ s.ncard ≤ 2⁻¹)

open Classical in
/--
Statement of Theorem 1.2:

There exists `L > 0` such that for any `0 < p < 1`, finite type `X`, and set `Λ` of functions from
`X` to `ℝ≥0` such that `0 < 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i] < ∞`, the collection of sets

`{s ⊆ X | sup_{f ∈ Λ} ∑ i ∈ s, f i ≥ L * 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i]}`

is `p-small`, where `Xp` is a binomial random subset of `X` with parameter `p`.

Note: The assumption `0 < 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i] < ∞` is not explicitly stated in the theorem
but used in the last step of the proof where `𝔼 ≥ (L/L') * 𝔼` is a contradiction for `L > L'`.
Source: J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean Via leanprover/lean-eval@38361be, problem `annals_supremum_of_selector_processes`.
-/
public theorem_wanted theorem_1_2 : ∃ L : ℝ≥0, 0 < L ∧ ∀ (p : I), 0 < p → p < 1 →
    ∀ (X : Type*) [Fintype X] (Λ : Set (X → ℝ≥0)),
    0 < 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] →
    𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p] < ∞ →
    IsSmall p {s : Set X | ⨆ f ∈ Λ, ∑ i ∈ s, (f i : ℝ≥0∞) ≥
        L * 𝔼⁻[⨆ f ∈ Λ, ∑ i ∈ Xp, (f i : ℝ≥0∞); Xp ∼ binomialSetDistribution X p]}

/-- Given a sequence of `𝕋`-valued random variables `Y_1, …, Y_N` and a function `f : 𝕋 → ℝ≥0`,
define the random variable

`Z N Y f := N⁻¹ ∑ i ∈ {1,…,N}, f(Yᵢ)`

When the sequence `Y_1, …, Y_N` is i.i.d, we call `Z N Y f` an empirical process.
-/
noncomputable def Z {Ω 𝕋 : Type*} (N : ℕ) (Y : Fin N → Ω → 𝕋) (f : 𝕋 → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (N : ℝ≥0)⁻¹ * ∑ i : Fin N, f (Y i ω)

open Classical in
/--
Statement of Theorem 1.3:

There exists `L > 0` such that for any `N > 0`, i.i.d random variables `Y_1, …, Y_N` distributed
according to a Borel probability measure `ν` on a Polish space `𝕋`, if `𝓕` is a finite set of
non-negative functions in `L∞(𝕋)` and `0 < 𝔼[sup_{f ∈ 𝓕} Z Y f] < ∞` then there exists a finite
collection `𝓒` of pairs `(g, t)` where `g : 𝕋 → ℝ≥0`, `t > 0` such that

`{sup_{f ∈ 𝓕} Z N Y f ≥ L * 𝔼[sup_{f ∈ 𝓕} Z N Y f] } ⊆ ⋃ (g,t) ∈ 𝓒, {t ≤ Z N Y g}`

and

`∑ (g,t) ∈ 𝓒, P(t ≤ Z N Y g) ≤ 2⁻¹`.

Note: The requirement that the collection `𝓒` be finite is not explicitly stated in the paper.
However, `𝓒` must at least be assumed to be countable in order for the sum to make sense,
and the collections `𝓒` produced by the proof are indeed finite.

Source: J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean Via leanprover/lean-eval@38361be, problem `annals_supremum_of_selector_processes`.
-/
public theorem_wanted theorem_1_3 : ∃ L : ℝ≥0, 0 < L ∧ ∀ (N : ℕ), 0 < N →
    ∀ (𝕋 : Type*) [TopologicalSpace 𝕋] [PolishSpace 𝕋]
    [MeasurableSpace 𝕋] [BorelSpace 𝕋] (ν : Measure 𝕋) [IsProbabilityMeasure ν]
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (Y : Fin N → Ω → 𝕋),
    iIndepFun Y P → (∀ i, HasLaw (Y i) ν P) →
    ∀ (𝓕 : Set {f : 𝕋 → ℝ≥0 // Measurable f ∧ MemLp f ∞ ν}), Finite 𝓕 →
    0 < 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] → 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P] < ∞ →
    ∃ 𝓒 : Finset ({g : 𝕋 → ℝ≥0 // Measurable g} × {t : ℝ≥0 | t > 0}),
      {ω | ⨆ f ∈ 𝓕, Z N Y f ω ≥ L * 𝔼⁻[⨆ f ∈ 𝓕, (Z N Y f ·); P]} ⊆ ⋃ c ∈ 𝓒, {ω | c.2 ≤ Z N Y c.1 ω}
      ∧ ∑ c : 𝓒, P {ω | c.val.2 ≤ Z N Y c.val.1 ω} ≤ 2⁻¹

end SupremumOfSelectorProcesses

end MathlibExt.Analysis.SupremumOfSelectorProcessesWanted
