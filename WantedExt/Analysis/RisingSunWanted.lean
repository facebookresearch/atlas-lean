/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Riesz's rising sun lemma

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.RisingSun` — rising_sun_lemma (manifest `manifests/problems/rising_sun_lemma.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.RisingSunWanted` namespace. Mathematical
statements are unchanged. Source: F. Riesz (1932). Knill, §163.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.RisingSunWanted
namespace Analysis.RisingSun

/-!
# Riesz's rising sun lemma

`rising_sun_lemma`: every continuous real function on a compact interval has the
rising-sun property (the shadow set is open, empty iff the function is
antitone, and otherwise decomposes into disjoint open intervals with endpoint
inequality `f(c) ≤ f(d)`). Trusted helpers (`risingSunSet`,
`HasRisingSunDecomposition`, `HasRisingSunProperty`) are non-holes. Mathlib has
the monotone-a.e.-differentiable consequence but not the rising-sun lemma.
Category-(b) candidate from §163 of the Knill survey.
-/

open Set MeasureTheory
open scoped Topology

/-- Points of `(a,b)` lower than some later point. -/
def risingSunSet (a b : ℝ) (f : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ Ioo a b ∧ ∃ t ∈ Icc x b, x < t ∧ f x < f t}

/-- A countable disjoint open-interval decomposition with the endpoint
inequality `f(c_n) ≤ f(d_n)`. -/
def HasRisingSunDecomposition (E : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ c d : ℕ → ℝ,
    E = ⋃ n : ℕ, Ioo (c n) (d n) ∧
    (Set.PairwiseDisjoint (Set.univ : Set ℕ) fun n => Ioo (c n) (d n)) ∧
    ∀ n : ℕ, f (c n) ≤ f (d n)

/-- The rising-sun property on `[a,b]`. -/
def HasRisingSunProperty (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  IsOpen (risingSunSet a b f) ∧
  (risingSunSet a b f = ∅ ↔ AntitoneOn f (Icc a b)) ∧
  ((risingSunSet a b f).Nonempty → HasRisingSunDecomposition (risingSunSet a b f) f)

/- **Riesz's rising sun lemma.** Every continuous real function on a compact
interval has the rising-sun property. -/
/-- Source: F. Riesz (1932). Knill, §163. Via leanprover/lean-eval@38361be, problem `rising_sun_lemma`. -/
public theorem_wanted rising_sun_lemma {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    HasRisingSunProperty a b f

end Analysis.RisingSun

end MathlibExt.Analysis.RisingSunWanted
