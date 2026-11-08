/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Frobenius's theorem: the Frobenius kernel is normal

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.Frobenius` — frobenius_kernel_isNormal (manifest `manifests/problems/frobenius_kernel_isNormal.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.FrobeniusWanted` namespace. Mathematical
statements are unchanged. Source: G. Frobenius, Über auflösbare Gruppen IV, Sitzungsber. Akad. Wiss. Berlin (1901).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FrobeniusWanted
namespace GroupTheory

/-!
Frobenius's theorem on Frobenius groups.

A *Frobenius group* is a finite group `G` acting transitively and faithfully on
a set `X` (with `|X| ≥ 2`) such that:
* point stabilisers are non-trivial, and
* no non-identity element of `G` fixes more than one point of `X`.

Frobenius's theorem (1901) states that the *Frobenius kernel*
  `K = {1} ∪ {g ∈ G | g fixes no point of X}`
is a normal subgroup of `G`. The only known proof uses character theory
(induction of characters from a point stabiliser to `G`); no purely
group-theoretic proof has been found in over a century.
-/

/-- Source: G. Frobenius, Über auflösbare Gruppen IV, Sitzungsber. Akad. Wiss. Berlin (1901). Via leanprover/lean-eval@38361be, problem `frobenius_kernel_isNormal`. -/
public theorem_wanted frobenius_kernel_isNormal
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x}

end GroupTheory

end MathlibExt.GroupTheory.FrobeniusWanted
