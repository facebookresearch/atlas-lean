/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The spread of a finite group

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.SpreadOfAFiniteGroup` — annals_spread_of_a_finite_group (manifest `manifests/problems/annals_spread_of_a_finite_group.toml`, rev 1, submitter Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.SpreadOfAFiniteGroupWanted` namespace. Mathematical
statements are unchanged. Source: T. C. Burness, R. M. Guralnick, and S. Harper, `The spread of a finite group`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-SpreadOfAFiniteGroup.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.GroupTheory.SpreadOfAFiniteGroupWanted
/-!
# Main Statement from The spread of a finite group

We formalise the statement of the main result from T. C. Burness, R. M. Guralnick, and S. Harper,
`The spread of a finite group`, Annals of Math, 193 (2) 2021.
-/

set_option autoImplicit false

namespace SpreadOfAFiniteGroup

/-- Let `G` be a group. The spread `s G` of `G` is the largest integer `k` such that for any
non-trivial elements `x_1, ..., x_k` in `G`, there exists `y ∈ G` with `G = ⟨x_i, y⟩` for
all `i`. -/
noncomputable def s (G : Type*) [Group G] : ℕ∞ :=
  sSup ((↑) '' {k : ℕ | ∀ x : Fin k → G, 1 ∉ Set.range x → ∃ y, ∀ i, Subgroup.closure {x i, y} = ⊤})

/--
Statement of Theorem 1:

Let `G` be a finite group. Then the spread `s(G) ≥ 2` if and only if every proper quotient of `G`
is cyclic.
Source: T. C. Burness, R. M. Guralnick, and S. Harper, `The spread of a finite group`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-SpreadOfAFiniteGroup.lean Via leanprover/lean-eval@38361be, problem `annals_spread_of_a_finite_group`.
-/
public theorem_wanted theorem_1 (G : Type*) [Group G] [Finite G] :
    s G ≥ 2 ↔ ∀ (N : Subgroup G) [N.Normal] [Nontrivial N], IsCyclic (G ⧸ N)

end SpreadOfAFiniteGroup

end MathlibExt.GroupTheory.SpreadOfAFiniteGroupWanted
