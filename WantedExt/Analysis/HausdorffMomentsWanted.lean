/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hausdorff–Hildebrandt–Schoenberg moment theorem, The Hausdorff positivity
(complete-monotonicity) criterion

The positivity criterion and the shared definitions live in
`MathlibExt/Analysis/HausdorffMoments.lean`, which this module re-exports.

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HausdorffMoments` —
hausdorff_hildebrandt_schoenberg (manifest
`manifests/problems/hausdorff_hildebrandt_schoenberg.toml`, rev 1, submitter Kim Morrison, status
archived); hausdorff_positivity_criterion (manifest
`manifests/problems/hausdorff_positivity_criterion.toml`, rev 1, submitter Kim Morrison, status
archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HausdorffMomentsWanted` namespace.
Mathematical
statements are unchanged. Source: F. Hausdorff (1921, 1923); T. H. Hildebrandt and I. J.
Schoenberg, *On linear functional operations and the moment problem for a finite interval in one
or several dimensions*, Ann. of Math. 34 (1933). Knill, *Some fundamental theorems in
mathematics*, §115. F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Math. Z. 9 (1921).
Knill, *Some fundamental theorems in mathematics*, §115.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Analysis.HausdorffMoments

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

The shared definitions and the positivity criterion are in
`MathlibExt.Analysis.HausdorffMoments`.

These are category-(b) candidates from §115 of the Knill survey
(`sections/115-moments.md`).
-/

/- **Hausdorff–Hildebrandt–Schoenberg theorem.** A multi-indexed real sequence
is the moment sequence of a signed bounded-variation measure on the unit cube
`Iᵈ` iff its moments are Hausdorff bounded. -/
/-- **Hausdorff–Hildebrandt–Schoenberg moment theorem.** A real sequence $a$ indexed by
$\mathbb{N}^d$ is a moment configuration, that is, there are finite measures $\mu$ and $\nu$ on
$\mathbb{R}^d$ with $a_n = \int_{[0,1]^d} x^n \, d\mu(x) - \int_{[0,1]^d} x^n \, d\nu(x)$ for every
multi-index $n \in \mathbb{N}^d$, where $x^n = \prod_i x_i^{n_i}$, if and only if $a$ is Hausdorff
bounded.

Source: F. Hausdorff (1921, 1923); T. H. Hildebrandt and I. J. Schoenberg, *On linear functional
operations and the moment problem for a finite interval in one or several dimensions*, Ann. of Math.
34 (1933). Knill, *Some fundamental theorems in mathematics*, §115. Via
leanprover/lean-eval@38361be, problem `hausdorff_hildebrandt_schoenberg`. -/
public theorem_wanted hausdorff_hildebrandt_schoenberg {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsMomentConfiguration a ↔ HausdorffBounded a

end Analysis

end MathlibExt.Analysis.HausdorffMomentsWanted
