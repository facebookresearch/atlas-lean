/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abel–Ruffini theorem

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
the `abel_ruffini` statement below is taken verbatim from
leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e,
module `LeanEval.Algebra.AbelRuffini` (manifest
`manifests/problems/abel_ruffini.toml`, statement revision 1, submitter
Kim Morrison), which is distributed under the Apache License, Version 2.0.
The original statement had no per-file copyright header and lean-eval
ships no `NOTICE` file. Changes made in this file: converted the original
`@[eval_problem] theorem … := by sorry` into a Batteries
`theorem_wanted`, replaced `import Mathlib` and `EvalTools.Markers` with
minimal imports, placed the declaration in the
`MathlibExt.Algebra.AbelRuffiniWanted` namespace, and corrected the
source docstring's reversed forward/reverse direction descriptions. The
mathematical statement itself is unchanged.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.AbelRuffini
public import MathlibExt.FieldTheory.Galois.AbelRuffini

/-!
The notice above records the original wanted statement. The proof now lives in
`MathlibExt.FieldTheory.Galois.AbelRuffini`, which this module re-exports.
-/
