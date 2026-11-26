/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/GroupTheory/BooneHigmanSimple.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), for the statement of Kuznetsov's theorem.
Copyright 2026 Lean FRO, LLC.
Author (benchmark submitter): Kim Morrison.
The ATLAS adaptation uses a regular theorem with a proof and keeps the wanted statement.
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

public import MathlibExt.GroupTheory.WordProblemSolvableShared
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Subgroup.Simple
import MathlibExt.GroupTheory.BooneHigmanEmbedding

/-!
# Kuznetsov's theorem on finitely presented simple groups

`boone_higman_simple` proves that every finite presentation of a simple group has a solvable
word problem. The two searches enumerate normal-closure certificates for the original relators
and for the relators augmented by the input word.
-/

public section

open MathlibExt.GroupTheory.WordProblemSolvableShared

namespace MathlibExt.GroupTheory.BooneHigmanSimpleWanted.GroupTheory.BooneHigmanSimpleProblem

set_option linter.dupNamespace false in
/-- **Kuznetsov's theorem on finitely presented simple groups.** Let $G$ be a simple group, let
$F_n$ be the free group on $n$ generators, and let $\varphi \colon F_n \to G$ be a surjective
homomorphism whose kernel is the normal closure of finitely many elements. Then the word problem
of $G$ with respect to $\varphi$ is solvable: there is an algorithm that decides, for every word
$w$ in the $n$ generators and their inverses, whether $\varphi(w) = 1$.

Source: A.V. Kuznetsov, 'Algorithms as operations in algebraic systems', Uspekhi Mat. Nauk 13 (1958)
240–241 (Russian); W.W. Boone and G. Higman, 'An algebraic characterization of groups with soluble
word problem', J. Austral. Math. Soc. 18 (1974) 41–53. §122 in O. Knill, *Some Fundamental Theorems
in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `boone_higman_simple`. -/
theorem boone_higman_simple
    {G : Type*} [Group G] [IsSimpleGroup G]
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (_hsurj : Function.Surjective φ)
    (_hker : (MonoidHom.ker φ).IsFinitelyNormallyGenerated) :
    WordProblemSolvable φ := by
  have : Group.IsFinitelyPresented G := ⟨n, φ, _hsurj, _hker⟩
  exact BooneHigmanEmbeddingWanted.GroupTheory.BooneHigmanEmbedding.boone_higman_embedding
    (MonoidHom.id G) Function.injective_id (MonoidHom.id G) Function.injective_id φ _hsurj

end MathlibExt.GroupTheory.BooneHigmanSimpleWanted.GroupTheory.BooneHigmanSimpleProblem
