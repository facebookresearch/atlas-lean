/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hausdorff moment problem: absolute-continuity criterion

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HausdorffAbsoluteContinuity` — hausdorff_absolute_continuity (manifest `manifests/problems/hausdorff_absolute_continuity.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted` namespace. Mathematical
statements are unchanged. Source: F. Hausdorff (1921–1923); see Shohat–Tamarkin, *The Problem of Moments*. Knill, *Some fundamental theorems in mathematics*, §115.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted
namespace Analysis.HausdorffAbsoluteContinuity

/-!
# Hausdorff moment problem: absolute-continuity criterion

`hausdorff_absolute_continuity`: a positive probability measure `μ` on the unit
cube is uniformly absolutely continuous with respect to Lebesgue measure iff its
moment differences are dominated by those of Lebesgue measure. This is the third
statement of §115 of the Knill survey (the moment realizability and positivity
criteria are the companion lean-eval problems). The trusted helpers (`cube`,
`monomial`, `momentOf`, `multiChoose`, `diff`, `UniformlyAbsolutelyContinuous`)
are non-holes. Mathlib has `SignedMeasure`, finite measures, and set integrals
but no moment-problem machinery.

Category-(b) candidate from §115 of the Knill survey (additional statement 2).
-/

open MeasureTheory
open scoped BigOperators NNReal

/-- The closed unit cube `Iᵈ = [0,1]ᵈ ⊆ ℝᵈ`. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The monomial `xⁿ = ∏ᵢ xᵢ^{nᵢ}`. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, (x i) ^ (n i)

/-- The `n`-th moment `∫_{Iᵈ} xⁿ dμ`. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

/-- The multi-index binomial coefficient `C(n,k) = ∏ᵢ C(nᵢ, kᵢ)`. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

/-- The iterated backward partial difference `(Δᵏa)ₙ` in closed form. -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

/-- `μ` is **uniformly absolutely continuous** w.r.t. `ν`: `μ ≤ C • ν` for some
constant `C` (an essentially-bounded Radon–Nikodym density). -/
def UniformlyAbsolutelyContinuous {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ C : ℝ≥0, μ ≤ C • ν

/- **Absolute continuity criterion (Hausdorff moment problem).** A positive
probability measure `μ` on the cube is uniformly absolutely continuous w.r.t.
Lebesgue measure iff there is `C` with `(Δᵏμ)ₙ ≤ C·(Δᵏν)ₙ` for all `k ≤ n`. -/
/-- Source: F. Hausdorff (1921–1923); see Shohat–Tamarkin, *The Problem of Moments*. Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem `hausdorff_absolute_continuity`. -/
public theorem_wanted hausdorff_absolute_continuity {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (hμ : μ ((cube d)ᶜ) = 0) :
    UniformlyAbsolutelyContinuous μ (volume.restrict (cube d)) ↔
      ∃ C : ℝ, ∀ k n : Fin d → ℕ, k ≤ n →
        diff (momentOf μ) k n ≤ C * diff (momentOf (volume.restrict (cube d))) k n

end Analysis.HausdorffAbsoluteContinuity

end MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted
