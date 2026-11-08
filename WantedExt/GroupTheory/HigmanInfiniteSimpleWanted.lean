/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Higman's infinite finitely-presented simple group

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.HigmanInfiniteSimple` — higman_infinite_simple (manifest `manifests/problems/higman_infinite_simple.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.HigmanInfiniteSimpleWanted` namespace. Mathematical
statements are unchanged. Source: G. Higman, 'A finitely generated infinite simple group', J. London Math. Soc. 26 (1951) 61–64; G. Higman, *Finitely Presented Infinite Simple Groups*, Notes on Pure Mathematics 8, Australian National University, 1974. §122 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.HigmanInfiniteSimpleWanted
namespace GroupTheory
namespace HigmanInfiniteSimpleProblem

/-!
# Higman's infinite finitely-presented simple group

There exists an infinite, finitely presented, simple group. The first
such examples come from Graham Higman's 1974 monograph *Finitely
Presented Infinite Simple Groups* — the Higman–Thompson groups
`G_{n, r}`. (Higman's 1951 paper had earlier exhibited a finitely
*generated* infinite simple group — a simple quotient of the
four-generator group with no nontrivial finite quotients — but did
not give a finite presentation for the simple quotient.) §122 in
Knill's *Some Fundamental Theorems in Mathematics*.

Concretely: some `n` and a finite relator set
`rels ⊆ FreeGroup (Fin n)` for which `PresentedGroup rels` is both
simple and infinite. Pure existence of a pathological finite
presentation. Mathlib v4.32.2 has `FreeGroup`, `PresentedGroup`,
`IsSimpleGroup`, `Infinite`, HNN extensions, and Britton's lemma, but
no Higman–Thompson construction and no infinite finitely-presented
simple group on hand.
-/

/- **Higman's infinite simple group** (G. Higman 1951/1974). There
exists an infinite finitely presented simple group. -/
/-- Source: G. Higman, 'A finitely generated infinite simple group', J. London Math. Soc. 26 (1951) 61–64; G. Higman, *Finitely Presented Infinite Simple Groups*, Notes on Pure Mathematics 8, Australian National University, 1974. §122 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `higman_infinite_simple`. -/
public theorem_wanted higman_infinite_simple :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ IsSimpleGroup (PresentedGroup rels) ∧
        Infinite (PresentedGroup rels)

end HigmanInfiniteSimpleProblem
end GroupTheory

end MathlibExt.GroupTheory.HigmanInfiniteSimpleWanted
