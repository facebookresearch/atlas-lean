/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/GroupTheory/BooneHigmanEmbedding.lean`,
`LeanEval/GroupTheory/BooneHigmanSimple.lean`, and
`LeanEval/GroupTheory/NovikovUnsolvable.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), for the definition of word-problem solvability.
Copyright 2026 Lean FRO, LLC.
Author (benchmark submitter): Kim Morrison.
The ATLAS adaptation retains the shared definition in its existing namespace.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Solvable word problem for a group presentation

`WordProblemSolvable` expresses the computability of the identity predicate on signed words.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.WordProblemSolvableShared

/-- **Solvable word problem.** Let $G$ be a group, $n$ a natural number and $\varphi$ a
homomorphism from the free group on $n$ generators to $G$. The word problem is solvable for
$\varphi$ when the predicate on words $w$ (finite lists of letters, each a generator together
with a sign) given by $\varphi(w) = 1$ in $G$ is computable: some algorithm decides, given a
word $w$, whether $\varphi(w) = 1$.

When $\varphi$ is surjective, for instance the quotient map of a presentation of $G$ on $n$
generators, this is the classical word problem for $G$ with respect to these generators. -/
def WordProblemSolvable {G : Type*} [Group G] {n : ℕ}
    (φ : FreeGroup (Fin n) →* G) : Prop :=
  ComputablePred (fun w : List (Fin n × Bool) => φ (FreeGroup.mk w) = 1)

end MathlibExt.GroupTheory.WordProblemSolvableShared
