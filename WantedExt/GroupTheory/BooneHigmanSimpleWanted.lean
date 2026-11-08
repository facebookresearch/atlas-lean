/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kuznetsov's theorem: finitely presented simple groups have solvable word problem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.BooneHigmanSimple` — boone_higman_simple (manifest `manifests/problems/boone_higman_simple.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.BooneHigmanSimpleWanted` namespace. Mathematical
statements are unchanged. Source: A.V. Kuznetsov, 'Algorithms as operations in algebraic systems', Uspekhi Mat. Nauk 13 (1958) 240–241 (Russian); W.W. Boone and G. Higman, 'An algebraic characterization of groups with soluble word problem', J. Austral. Math. Soc. 18 (1974) 41–53. §122 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.Computability.PartrecCode
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

open MathlibExt.GroupTheory.WordProblemSolvableShared

namespace MathlibExt.GroupTheory.BooneHigmanSimpleWanted
namespace GroupTheory
namespace BooneHigmanSimpleProblem

/-!
# Kuznetsov / Boone–Higman: simple finitely presented groups have
solvable word problem

A finitely presented *simple* group has a decidable word problem.
This is Kuznetsov's theorem (A.V. Kuznetsov, 1958); the later
Boone–Higman characterisation (W.W. Boone and G. Higman, 1974) gives
the full iff statement situating Kuznetsov's result. §122 in Knill's
*Some Fundamental Theorems in Mathematics*.

A word in the generators `g₁, …, gₙ` and their inverses is encoded as
`List (Fin n × Bool)`, which is `Primcodable`. The word problem of a
finite presentation `φ : FreeGroup (Fin n) →* G` is the predicate "the
word `w` represents the identity of `G`"; it is **solvable** when this
predicate is decidable by an algorithm, captured by mathlib's
`ComputablePred`. The hypotheses `hsurj` + `hker` unpack
`Group.IsFinitelyPresented G` for this particular presentation `φ`.

Mathlib has `Group.IsFinitelyPresented`,
`Subgroup.IsFinitelyNormallyGenerated`, `FreeGroup`, `PresentedGroup`,
`IsSimpleGroup`, and the
`ComputablePred` / `Computable` / `Partrec` stack, but no notion of
the word problem of a group or the Kuznetsov / Boone–Higman / Novikov
theorems.
-/

/- The word problem of a finite presentation `φ` is **solvable** when
the predicate "the word `w` represents the identity of `G`" is
decidable by an algorithm. -/

/- **Kuznetsov's theorem** (A.V. Kuznetsov, 1958). A finitely presented
simple group has a solvable word problem. -/
/-- Source: A.V. Kuznetsov, 'Algorithms as operations in algebraic systems', Uspekhi Mat. Nauk 13 (1958) 240–241 (Russian); W.W. Boone and G. Higman, 'An algebraic characterization of groups with soluble word problem', J. Austral. Math. Soc. 18 (1974) 41–53. §122 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `boone_higman_simple`. -/
public theorem_wanted boone_higman_simple
    {G : Type*} [Group G] [IsSimpleGroup G]
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (_hsurj : Function.Surjective φ)
    (_hker : (MonoidHom.ker φ).IsFinitelyNormallyGenerated) :
    WordProblemSolvable φ

end BooneHigmanSimpleProblem
end GroupTheory

end MathlibExt.GroupTheory.BooneHigmanSimpleWanted
