/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hausdorff–Hildebrandt–Schoenberg moment theorem, The Hausdorff positivity
(complete-monotonicity) criterion

Both Hausdorff moment criteria and their shared definitions live in
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

public import MathlibExt.Analysis.HausdorffMoments

/-!
# Compatibility import for the Hausdorff moment criteria

This module only re-exports the signed and positive Hausdorff moment criteria and their shared
definitions from `MathlibExt.Analysis.HausdorffMoments`.
-/
