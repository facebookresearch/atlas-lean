/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Possible orders of 5-transitive finite permutation groups

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.MultiplyTransitive` — five_transitive_card_classification (manifest `manifests/problems/five_transitive_card_classification.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.MultiplyTransitiveWanted` namespace. Mathematical
statements are unchanged. Source: Folklore via CFSG; classical work of Mathieu, Jordan; modern accounts in P. Cameron, Permutation Groups (1999).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.MultiplyTransitiveWanted
namespace GroupTheory

/-!
Classification of `5`-transitive finite permutation groups (uses CFSG).

If a finite group `G` acts faithfully and `5`-transitively on a set `X` of
cardinality `n ≥ 5`, then `|G|` is one of:

* `n!`             (`G ≅ Sₙ`,    any `n ≥ 5`)
* `n! / 2`         (`G ≅ Aₙ`,    any `n ≥ 7`)
* `95 040`         (`G ≅ M₁₂`,    `n = 12`)
* `244 823 040`    (`G ≅ M₂₄`,    `n = 24`)

These are the only `5`-transitive finite groups. The result is folklore via
the classification of finite simple groups: it follows from CFSG together with
classical work of Mathieu, Jordan, and others. No CFSG-free proof is known.

The `5 ≤ Fintype.card X` hypothesis prevents the `5`-transitivity condition
from being vacuously satisfied (otherwise any small action — e.g. `C₃` on
`Fin 3` — would qualify, since there are no injective maps `Fin 5 → X`).

The companion `4`-transitive classification additionally allows
`M₁₁` (`n = 11`, `|G| = 7920`) and `M₂₃` (`n = 23`, `|G| = 10 200 960`).
-/

/-- Source: Folklore via CFSG; classical work of Mathieu, Jordan; modern accounts in P. Cameron, Permutation Groups (1999). Via leanprover/lean-eval@38361be, problem `five_transitive_card_classification`. -/
public theorem_wanted five_transitive_card_classification
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    let n := Fintype.card X
    Fintype.card G = n.factorial ∨
    (7 ≤ n ∧ Fintype.card G = n.factorial / 2) ∨
    (n = 12 ∧ Fintype.card G = 95040) ∨
    (n = 24 ∧ Fintype.card G = 244823040)

end GroupTheory

end MathlibExt.GroupTheory.MultiplyTransitiveWanted
