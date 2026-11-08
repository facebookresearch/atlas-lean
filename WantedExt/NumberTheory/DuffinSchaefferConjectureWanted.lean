/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the Duffin-Schaeffer conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.DuffinSchaefferConjecture` — annals_duffin_schaeffer_conjecture (manifest `manifests/problems/annals_duffin_schaeffer_conjecture.toml`, rev 1, submitter Katerina Hristova, Kevin Buzzard, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted` namespace. Mathematical
statements are unchanged. Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

namespace MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted
/-!
# Main Statements from On the Duffin-Schaeffer conjecture

We formalise the statements of the main results from D. Koukoulopoulos and J. Maynard,
`On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020.

## Implementation Details

In the paper, `ℕ` denotes the positive integers, which are denoted `ℕ+` in Lean.
Hence, no changes to the domains of the functions `ψ` and `ψ⋆` have been made in the formalisation.
-/

set_option autoImplicit false

namespace DuffinSchaefferConjecture

open NNReal ENNReal MeasureTheory

open scoped Nat

/-- Inequality 1.7: `|α - a / q| ≤ ψ q / q`. Here `α ∈ ℝ` and `ψ : ℕ → ℝ≥0` is a function. -/
def inequality_1_7 (ψ : ℕ+ → ℝ≥0) (α : ℝ) (a : ℕ) (q : ℕ+) : Prop :=
  |α - a / q| ≤ ψ q / q

/-- Definition of the set `𝒜` appearing in Theorem 1. -/
def 𝒜 (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc 0 1 | {(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ inequality_1_7 ψ α a q}.Infinite}

/--
Statement of Theorem 1:

If for `ψ : ℕ → ℝ≥0`, the infinite series `∑ (ψ q * φ q) / q`, where `φ` is the
Euler totient function, diverges, then the set `𝒜` defined above has Lebesgue measure `1`.
Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted theorem_1 (ψ : ℕ+ → ℝ≥0) (hdivergence : ¬ Summable fun q ↦ (ψ q * φ q) / q) :
    MeasurableSet (𝒜 ψ) ∧ volume (𝒜 ψ) = 1

/-- The set `𝒦` as defined in Theorem 2:
The `α ∈ [0,1]` such that inequality 1.7 `|α - a/q| ≤ ψ(q)/q` has infinitely many solutions `(a, q)`
with `0 ≤ a ≤ q`.

Note: we allow non-coprime `(a, q)` and we explicitly rule out `q = 0`. -/
def 𝒦 (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc 0 1 | {(a, q) : ℕ × ℕ+ | a ≤ q ∧ inequality_1_7 ψ α a q}.Infinite}

/-- Define `ψ⋆ : ℕ → ℝ≥0∞` by `ψ⋆ : q ↦ φ(q) * sup {ψ(n)/n : n ∈ ℕ+, q|n}`, where `φ` denotes
Euler's totient function. -/
noncomputable def ψ_star (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0∞ :=
  fun q ↦ φ q * sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n}

/--
Statement of Theorem 2(a):

Let `ψ : ℕ → ℝ≥0`, `𝒦` and `ψ⋆` be as above. Then, if `∑ ψ⋆ (q)` converges, `𝒦` has Lebesgue
measure `0`.
Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted theorem_2_a (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q, ψ_star ψ q < ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 0

/--
Statement of Theorem 2(b):

Let `ψ : ℕ → ℝ≥0`, `𝒦` and `ψ⋆` be as above. Then, if `∑ ψ⋆ (q)` diverges, `𝒦` has Lebesgue
measure `1`.
Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted theorem_2_b (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q, ψ_star ψ q = ∞) :
    MeasurableSet (𝒦 ψ) ∧ volume (𝒦 ψ) = 1

/-- The element `s` in the statement of Corollary 3. -/
noncomputable def s_inf (ψ : ℕ+ → ℝ≥0) : ℝ≥0 :=
  sInf {β | Summable fun q : ℕ+ ↦ φ q * (ψ q / q) ^ β.1}

/--
Statement of Corollary 3:

For a function `ψ : ℕ → [0, 1/2]`, the set `𝒜` and the element `s` defined as above,
the Hausdorff dimension of `𝒜` is the minimum of `s` and `1`.
Source: D. Koukoulopoulos and J. Maynard, `On the Duffin-Schaeffer conjecture`, Annals of Math, 192 (1) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_duffin_schaeffer_conjecture`.
-/
public theorem_wanted corollary_3 (ψ : ℕ+ → ℝ≥0) (hψ : ∀ n, ψ n ∈ Set.Icc 0 (1 / 2)) :
    dimH (𝒜 ψ) = min (s_inf ψ) 1

end DuffinSchaefferConjecture

end MathlibExt.NumberTheory.DuffinSchaefferConjectureWanted
