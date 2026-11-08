/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hausdorff–Hildebrandt–Schoenberg moment theorem, The Hausdorff positivity (complete-monotonicity) criterion

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HausdorffMoments` — hausdorff_hildebrandt_schoenberg (manifest `manifests/problems/hausdorff_hildebrandt_schoenberg.toml`, rev 1, submitter Kim Morrison, status archived); hausdorff_positivity_criterion (manifest `manifests/problems/hausdorff_positivity_criterion.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HausdorffMomentsWanted` namespace. Mathematical
statements are unchanged. Source: F. Hausdorff (1921, 1923); T. H. Hildebrandt and I. J. Schoenberg, *On linear functional operations and the moment problem for a finite interval in one or several dimensions*, Ann. of Math. 34 (1933). Knill, *Some fundamental theorems in mathematics*, §115. F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Math. Z. 9 (1921). Knill, *Some fundamental theorems in mathematics*, §115.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.HausdorffMomentsWanted
namespace Analysis

/-!
# The Hausdorff moment problem on the cube

`hausdorff_hildebrandt_schoenberg` is the Hausdorff–Hildebrandt–Schoenberg
theorem (1933): a multi-indexed real sequence is the moment sequence of a
signed bounded-variation Borel measure on the unit cube `Iᵈ = [0,1]ᵈ` iff it is
*Hausdorff bounded*. `hausdorff_positivity` is the Hausdorff positivity
criterion (1921): it comes from a *positive* finite measure iff it is completely
monotone (all iterated backward differences nonnegative).

A signed bounded-variation measure is encoded by its Jordan decomposition (a
difference of two finite positive measures); the moment integrals are taken over
the cube, so only the restriction to `Iᵈ` matters; the iterated backward
difference `Δᵏ` is given in closed form (the `ℕ`-subtraction `n − j` is genuine
in the `k ≤ n` regime the criteria use).

Mathlib has `SignedMeasure`, Jordan decomposition, finite measures, and set
integrals — enough to *state* the theorem — but no moment-problem machinery
(no Hausdorff/Hamburger/Stieltjes moment problem, no completely-monotone
sequences). The helper definitions below (`cube`, `monomial`, `momentOf`,
`IsMomentConfiguration`, `multiChoose`, `diff`, `HausdorffBounded`,
`IsPositiveMomentConfiguration`) are trusted (non-holes).

These are category-(b) candidates from §115 of the Knill survey
(`sections/115-moments.md`).
-/

open MeasureTheory
open scoped BigOperators NNReal

/-- The closed unit cube `Iᵈ = [0,1]ᵈ ⊆ ℝᵈ`. -/
def cube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The monomial `xⁿ = ∏ᵢ xᵢ^{nᵢ}` indexed by a multi-index `n ∈ ℕᵈ`. -/
def monomial {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∏ i, (x i) ^ (n i)

/-- The `n`-th moment `∫_{Iᵈ} xⁿ dμ` of a (positive) measure `μ`, integrated
over the cube. -/
noncomputable def momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (n : Fin d → ℕ) : ℝ :=
  ∫ x in cube d, monomial n x ∂μ

/-- `a` is a **moment configuration** of a signed (bounded-variation) measure on
the cube: there are finite positive measures `μ, ν` with
`aₙ = ∫ xⁿ dμ − ∫ xⁿ dν` for all `n` (the Jordan decomposition of the realizing
signed measure). -/
def IsMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ ν : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧
    ∀ n, a n = momentOf μ n - momentOf ν n

/-- The multi-index binomial coefficient `C(n,k) = ∏ᵢ C(nᵢ, kᵢ)`. -/
def multiChoose {d : ℕ} (n k : Fin d → ℕ) : ℕ := ∏ i, (n i).choose (k i)

/-- The iterated **backward** partial difference `(Δᵏa)ₙ`, in closed form
`∑_{0 ≤ j ≤ k} (−1)^{|k−j|} C(k,j) a_{n−j}` — the iterate of
`(Δᵢa)ₙ = a_{n−eᵢ} − aₙ`. The `ℕ`-subtraction `n − j` is genuine whenever
`k ≤ n` (the regime used below). -/
noncomputable def diff {d : ℕ} (a : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) : ℝ :=
  ∑ j ∈ Finset.Iic k,
    (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j)

/-- The moments `a` are **Hausdorff bounded**: there is `C` with
`∑_{0 ≤ k ≤ n} |C(n,k) · (Δᵏa)ₙ| ≤ C` for every `n`. -/
def HausdorffBounded {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : Fin d → ℕ,
    ∑ k ∈ Finset.Iic n, |(multiChoose n k : ℝ) * diff a k n| ≤ C

/-- `a` is a **positive** moment configuration: realized by a single finite
*positive* measure on the cube. -/
def IsPositiveMomentConfiguration {d : ℕ} (a : (Fin d → ℕ) → ℝ) : Prop :=
  ∃ μ : Measure (EuclideanSpace ℝ (Fin d)), IsFiniteMeasure μ ∧ ∀ n, a n = momentOf μ n

/- **Hausdorff–Hildebrandt–Schoenberg theorem.** A multi-indexed real sequence
is the moment sequence of a signed bounded-variation measure on the unit cube
`Iᵈ` iff its moments are Hausdorff bounded. -/
/-- Source: F. Hausdorff (1921, 1923); T. H. Hildebrandt and I. J. Schoenberg, *On linear functional operations and the moment problem for a finite interval in one or several dimensions*, Ann. of Math. 34 (1933). Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem `hausdorff_hildebrandt_schoenberg`. -/
public theorem_wanted hausdorff_hildebrandt_schoenberg {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsMomentConfiguration a ↔ HausdorffBounded a

/- **Hausdorff positivity criterion** (Hausdorff 1921). A moment configuration
comes from a positive measure iff all its iterated backward differences are
nonnegative — i.e. the sequence is *completely monotone*: `(Δᵏa)ₙ ≥ 0` for all
`k ≤ n`. -/
/-- Source: F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Math. Z. 9 (1921). Knill, *Some fundamental theorems in mathematics*, §115. Via leanprover/lean-eval@38361be, problem `hausdorff_positivity_criterion`. -/
public theorem_wanted hausdorff_positivity {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsPositiveMomentConfiguration a ↔ ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n

end Analysis

end MathlibExt.Analysis.HausdorffMomentsWanted
