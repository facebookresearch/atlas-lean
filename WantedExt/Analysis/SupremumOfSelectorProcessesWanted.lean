/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On a conjecture of Talagrand on selector processes and a consequence on positive empirical
processes

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.SupremumOfSelectorProcesses` —
annals_supremum_of_selector_processes (manifest
`manifests/problems/annals_supremum_of_selector_processes.toml`, rev 1, submitter David Ledvinka,
status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.SupremumOfSelectorProcessesWanted`
namespace. Mathematical
statements are unchanged. Source: J. Park and H. T. Pham, `On a conjecture of Talagrand on
selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3)
2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0,
e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.SetBernoulli
public import MathlibExt.Analysis.SupremumOfSelectorProcesses
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

/-- **Empirical averages.** Given random variables $Y_1, \dots, Y_N$ on $\Omega$ with values in
$\mathbb{T}$ and a function $f : \mathbb{T} \to [0, \infty)$, $Z_N(f)$ is the random variable
$Z_N(f)(\omega) = \frac{1}{N} \sum_{i=1}^{N} f(Y_i(\omega))$, which is $0$ when $N = 0$.

When $Y_1, \dots, Y_N$ are i.i.d., $Z_N(f)$ is called an empirical process. -/
noncomputable def Z {Ω 𝕋 : Type*} (N : ℕ) (Y : Fin N → Ω → 𝕋) (f : 𝕋 → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (N : ℝ≥0)⁻¹ * ∑ i : Fin N, f (Y i ω)

open Classical in
/--
**Park–Pham theorem on positive empirical processes.** There is a real number $L > 0$ with the
following property. Let $N > 0$, let $\mathbb{T}$ be a Polish space with its Borel
$\sigma$-algebra and a probability measure $\nu$, and let $Y_1, \dots, Y_N$ be independent random
variables on a measure space $(\Omega, P)$ with values in $\mathbb{T}$, each with law $\nu$. For
$f : \mathbb{T} \to [0, \infty)$ let $Z_f = \frac{1}{N} \sum_{i=1}^{N} f(Y_i)$. Let
$\mathcal{F}$ be a finite set of measurable functions from $\mathbb{T}$ to $[0, \infty)$ that are
essentially bounded with respect to $\nu$, and write
$E = \mathbb{E}\bigl[\sup_{f \in \mathcal{F}} Z_f\bigr]$, computed in $[0, \infty]$. If
$0 < E < \infty$, then there is a finite collection $\mathcal{C}$ of pairs $(g, t)$, where
$g : \mathbb{T} \to [0, \infty)$ is measurable and $t > 0$ is real, such that every $\omega$
with $\sup_{f \in \mathcal{F}} Z_f(\omega) \ge L E$ satisfies $Z_g(\omega) \ge t$ for some
$(g, t) \in \mathcal{C}$, and $\sum_{(g, t) \in \mathcal{C}} P(Z_g \ge t) \le 1/2$.

The paper does not state explicitly that $\mathcal{C}$ is finite. It must at least be countable
for the sum to make sense, and the collections produced by the proof are finite.

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
