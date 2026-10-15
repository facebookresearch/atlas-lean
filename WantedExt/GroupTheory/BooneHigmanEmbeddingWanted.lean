/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Boone–Higman theorem (easy direction)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.BooneHigmanEmbedding` — boone_higman_embedding (manifest `manifests/problems/boone_higman_embedding.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.BooneHigmanEmbeddingWanted` namespace. Mathematical statements are unchanged except that the source's extra finite-normal-generation hypothesis on `ker φ` is dropped, matching the cited Boone–Higman theorem. Source: W. W. Boone & G. Higman, *An algebraic characterization of groups with soluble word problem*, J. Austral. Math. Soc. 18 (1974). Knill, *Some fundamental theorems in mathematics*, §122.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Computability.PartrecCode
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

open MathlibExt.GroupTheory.WordProblemSolvableShared

namespace MathlibExt.GroupTheory.BooneHigmanEmbeddingWanted
namespace GroupTheory.BooneHigmanEmbedding

/-!
# Boone–Higman theorem (easy direction)

`boone_higman_embedding`: if a finitely generated group `G` embeds in a simple
group `H` that embeds in a finitely presented group `K`, then `G` has a solvable
word problem — the "if" half of the Boone–Higman characterisation. The trusted
helper `WordProblemSolvable` (a non-hole) expresses decidability of "a word
represents the identity" via `ComputablePred`. Mathlib has finitely-presented
groups, free groups, simple groups, and computability, but no notion of the word
problem or the Boone–Higman theorem. (The main Kuznetsov/Boone–Higman, Novikov,
and Higman-infinite-simple statements of §122 are already in lean-eval.)

Category-(b) candidate from §122 of the Knill survey (additional statement 1).
-/


/- **Boone–Higman theorem (easy direction).** If a finitely generated group `G`
embeds (via injective `f`) into a simple group `H`, which embeds (via injective
`g`) into a finitely presented group `K`, then the word problem of `G` is
solvable. -/
/-- Source: W. W. Boone & G. Higman, *An algebraic characterization of groups with soluble word problem*, J. Austral. Math. Soc. 18 (1974). Knill, *Some fundamental theorems in mathematics*, §122. Via leanprover/lean-eval@38361be, problem `boone_higman_embedding`. -/
public theorem_wanted boone_higman_embedding
    {G H K : Type*} [Group G] [Group H] [Group K]
    [IsSimpleGroup H] [Group.IsFinitelyPresented K]
    (f : G →* H) (hf : Function.Injective f)
    (g : H →* K) (hg : Function.Injective g)
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ)
    : WordProblemSolvable φ

end GroupTheory.BooneHigmanEmbedding

end MathlibExt.GroupTheory.BooneHigmanEmbeddingWanted
