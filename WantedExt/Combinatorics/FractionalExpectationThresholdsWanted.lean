/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Thresholds versus fractional expectation-thresholds

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
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka

Portions of this file are taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module
`LeanEval.Combinatorics.FractionalExpectationThresholds` — annals_fractional_expectation_thresholds
(manifest `manifests/problems/annals_fractional_expectation_thresholds.toml`, rev 1,
submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted`
namespace. The definitions now live in `MathlibExt.Combinatorics.FractionalExpectationThresholds`,
and the constant is explicit. Source: K. Frankston, J. Kahn, B. Narayanan, and J. Park,
`Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021.
Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14),
AnnalsChallenge/AnnalsOfMathematics/2021-194-2-FractionalExpectationThresholds.lean
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.FractionalExpectationThresholds

@[expose] public section

namespace MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted
/-!
# Main Statement from Thresholds versus fractional expectation-thresholds

We formalise the statement of the main result from K. Frankston, J. Kahn, B. Narayanan, and J. Park,
`Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021.
-/

set_option autoImplicit false

namespace FractionalExpectationThresholds

/-- **Thresholds versus fractional expectation-thresholds.** Let $K=12/\ln 2$.
For every finite set $X$ and every increasing family $\mathcal F$
of subsets of $X$ (closed under taking supersets) with $\ell(\mathcal F) \ge 2$, where
$\ell(\mathcal F)$ is the size of a largest minimal element of $\mathcal F$,
$$p_c(\mathcal F) \le K \, q_f(\mathcal F) \log \ell(\mathcal F),$$
where $p_c$ is the threshold, $q_f$ the fractional expectation-threshold and $\log$ the
natural logarithm.

The hypothesis $\ell(\mathcal F) \ge 2$ is not explicit in the paper but is needed: if
$\ell(\mathcal F) = 1$ then $\log \ell(\mathcal F) = 0$, while $p_c(\mathcal F) \in (0, 1)$,
so the inequality cannot hold.

Source: K. Frankston, J. Kahn, B. Narayanan, and J. Park, `Thresholds versus fractional
expectation-thresholds`, Annals of Math, 194 (2) 2021. Statement taken from
https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14),
AnnalsChallenge/AnnalsOfMathematics/2021-194-2-FractionalExpectationThresholds.lean via
leanprover/lean-eval@38361be, problem `annals_fractional_expectation_thresholds`.
The explicit constant uses the uniform integral estimate of Bryan Park and Jan Vondrák,
https://arxiv.org/abs/2306.12576, §2.3.
-/
public theorem_wanted theorem_1_1 (X : Type*) [Fintype X] (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕)
    (hl𝓕 : 2 ≤ l 𝓕) : p_c 𝓕 ≤ K * q_f 𝓕 * Real.log (l 𝓕)

end FractionalExpectationThresholds

end MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted
