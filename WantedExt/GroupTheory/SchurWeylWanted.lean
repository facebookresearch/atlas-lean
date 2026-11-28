/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schur-Weyl duality: GL(V) image equals centralizer of S_k image, Schur-Weyl duality: S_k image equals centralizer of GL(V) image

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.SchurWeyl` — glAction_range_eq_centralizer_symAction (manifest `manifests/problems/glAction_range_eq_centralizer_symAction.toml`, rev 1, submitter Kim Morrison, status archived); symAction_range_eq_centralizer_glAction (manifest `manifests/problems/symAction_range_eq_centralizer_glAction.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.SchurWeylWanted` namespace. Mathematical
statements are unchanged. Source: H. Weyl, The Classical Groups, 1939; I. Schur, Über die rationalen Darstellungen der allgemeinen linearen Gruppe, 1927. H. Weyl, The Classical Groups, 1939; I. Schur, Über die rationalen Darstellungen der allgemeinen linearen Gruppe, 1927.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.GroupTheory.SchurWeyl

@[expose] public section

namespace MathlibExt.GroupTheory.SchurWeylWanted
namespace RepresentationTheory

open scoped TensorProduct

/-!
Schur–Weyl duality on `V^⊗k`.

Two commuting actions on `V^⊗k`:

* `symAction`: the symmetric group `S_k` acts by permuting tensor factors.
* `glAction`: the general linear group `GL(V)` acts diagonally as `g · (v₁ ⊗ ⋯ ⊗ v_k) =
  (g v₁) ⊗ ⋯ ⊗ (g v_k)`.

Schur–Weyl duality says their images in `End(V^⊗k)` generate mutual centralizers when `V` is
finite-dimensional over a field in which `k!` is invertible.

This compatibility module publicly re-exports `MathlibExt.GroupTheory.SchurWeyl`, which defines
both actions and proves both directions of the duality.
-/

end RepresentationTheory

end MathlibExt.GroupTheory.SchurWeylWanted
