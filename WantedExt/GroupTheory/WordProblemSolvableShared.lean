/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared word-problem solvability predicate

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This neutral helper module is shared by the Boone–Higman and Novikov
wanted entries, so all three theorems speak about the same word-problem
predicate. The definition is the trusted (non-hole) helper from
leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e
(modules `LeanEval.GroupTheory.BooneHigmanEmbedding`,
`LeanEval.GroupTheory.BooneHigmanSimple`, and
`LeanEval.GroupTheory.NovikovUnsolvable`), distributed under the Apache
License, Version 2.0; it is unchanged apart from the namespace.
-/
module


public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE


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
