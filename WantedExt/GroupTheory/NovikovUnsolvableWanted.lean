/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Novikov's theorem: the word problem is undecidable for finitely presented groups

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.NovikovUnsolvable` — novikov_unsolvable (manifest `manifests/problems/novikov_unsolvable.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.NovikovUnsolvableWanted` namespace. Mathematical
statements are unchanged. Source: P.S. Novikov, 'On the algorithmic unsolvability of the word problem in group theory', Trudy Mat. Inst. Steklov. 44 (1955) 1–143 (Russian); W.W. Boone, 'The word problem', Ann. of Math. (2) 70 (1959) 207–265 (announced 1958). §122 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Computability.PartrecCode
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

open MathlibExt.GroupTheory.WordProblemSolvableShared

namespace MathlibExt.GroupTheory.NovikovUnsolvableWanted
namespace GroupTheory
namespace NovikovUnsolvableProblem

/-!
# Novikov's theorem: undecidability of the word problem

There exists a finitely presented group whose word problem is
undecidable. P.S. Novikov 1955 / W.W. Boone 1958. §122 in Knill's
*Some Fundamental Theorems in Mathematics*.

The standard encoding: a word in the generators `g₁, …, gₙ` and their
inverses is `List (Fin n × Bool)`, which is `Primcodable`. The word
problem of a finite presentation `φ : FreeGroup (Fin n) →* G` is the
predicate "`w` represents the identity of `G`", and solvability is
`ComputablePred` of that predicate. Novikov's theorem asserts the
existence of `n` and a finite relator set `rels ⊆ FreeGroup (Fin n)`
for which the canonical surjection
`PresentedGroup.mk rels : FreeGroup (Fin n) →* PresentedGroup rels`
has *no* such algorithm.
-/

/- The word problem of a finite presentation `φ` is **solvable** when
the predicate "the word `w` represents the identity of `G`" is
decidable by an algorithm. -/

/- **Novikov's theorem** (P.S. Novikov 1955; independently W.W. Boone
1958). There exists a finite presentation with undecidable word
problem. -/
/-- **Novikov–Boone theorem (unsolvability of the word problem).** There exist a natural number
$n$ and a finite set $R$ of elements of the free group $F_n$ on generators $g_1, \dots, g_n$ such
that the word problem of the canonical surjection from $F_n$ onto the presented group
$\langle g_1, \dots, g_n \mid R \rangle$ is not solvable: no algorithm decides, for a word $w$ in
the $g_i$ and their inverses, whether $w$ represents the identity of
$\langle g_1, \dots, g_n \mid R \rangle$.

Source: P.S. Novikov, 'On the algorithmic unsolvability of the word problem in group theory', Trudy Mat. Inst. Steklov. 44 (1955) 1–143 (Russian); W.W. Boone, 'The word problem', Ann. of Math. (2) 70 (1959) 207–265 (announced 1958). §122 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `novikov_unsolvable`. -/
public theorem_wanted novikov_unsolvable :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ ¬ WordProblemSolvable (PresentedGroup.mk rels)

end NovikovUnsolvableProblem
end GroupTheory

end MathlibExt.GroupTheory.NovikovUnsolvableWanted
