/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chudnovsky formula for pi inverse

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.Chudnovsky` — chudnovsky_formula_for_pi_inv (manifest `manifests/problems/chudnovsky_formula_for_pi_inv.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.ChudnovskyWanted` namespace. Mathematical
statements are unchanged. Source: https://arxiv.org/abs/1809.00533
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Pi.Chudnovsky

@[expose] public section

namespace MathlibExt.Analysis.ChudnovskyWanted
namespace Analysis

open scoped Real

/-!
Chudnovsky's formula for `π⁻¹`.

Mathlib already defines the Chudnovsky series `chudnovskySum`; this benchmark asks for the missing
identity with `π⁻¹`.
-/
public theorem_wanted chudnovsky_formula_for_pi_inv :
    chudnovskySum = π⁻¹

end Analysis

end MathlibExt.Analysis.ChudnovskyWanted
