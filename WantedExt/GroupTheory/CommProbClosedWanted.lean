/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Commuting probabilities are closed

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.CommProbClosed` — commProb_closed (manifest `manifests/problems/commProb_closed.toml`, rev 1, submitter Thomas Browning, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.CommProbClosedWanted` namespace. Mathematical
statements are unchanged. Source: https://arxiv.org/abs/2201.09402
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.GroupTheory.CommProbClosedWanted
namespace GroupTheory

/-!
Theorem 1.2 from Browning,
"Limit Points of Commuting Probabilities of Finite Groups" (`arXiv:2201.09402`).

Mathlib's definition of commuting probability is zero when the group is not finite,
so there is no need to add in `0` to make the set of commuting probabilities closed.
-/

/- The set of commuting probabilities of finite groups is closed. -/
/-- Source: https://arxiv.org/abs/2201.09402 Via leanprover/lean-eval@38361be, problem `commProb_closed`. -/
public theorem_wanted commProb_closed : IsClosed ({p : ℝ | ∃ (G : Type) (hG : Group G), @commProb G hG.toMul = p})

end GroupTheory

end MathlibExt.GroupTheory.CommProbClosedWanted
