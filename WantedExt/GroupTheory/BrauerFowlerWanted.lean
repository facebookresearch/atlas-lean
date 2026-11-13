/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Brauer–Fowler theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.BrauerFowler` — brauer_fowler (manifest `manifests/problems/brauer_fowler.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.BrauerFowlerWanted` namespace. Mathematical
statements are unchanged. Source: R. Brauer and K. A. Fowler, On groups of even order, Ann. of Math. (2) 62 (1955), 565-583. https://doi.org/10.2307/1970080
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Character

@[expose] public section

namespace MathlibExt.GroupTheory.BrauerFowlerWanted
namespace GroupTheory

/-!
# Brauer–Fowler theorem

Let `G` be a finite simple group with an involution `t`. Then `|G|` is
bounded by a function of `|C_G(t)|` alone. Equivalently: for each `n`,
only finitely many finite nonabelian simple groups have an involution
whose centralizer has order `n`.

Stated by Richard Brauer in 1954 (with Fowler) as a key motivation for
the project of classifying finite simple groups: it reduces the
classification (in principle) to studying involution centralizers, a
much smaller class of groups. The first general involution-centralizer
analyses (Brauer–Suzuki, Brauer–Suzuki–Wall, Janko) used this principle
to discover several sporadic simple groups, and it remained one of the
central organising ideas of the CFSG programme.

The bound `f` is not specified — any concrete bound suffices, the
classical Brauer–Fowler bound being roughly `(n^2)!`. The statement
quantifies over all finite simple groups `G` in a fixed universe.

The proof is short and uses only counting / orbit-counting arguments
together with the observation that any two involutions generate a
dihedral subgroup; no deep machinery is required.
-/

/- **Brauer–Fowler theorem.** There is a function bounding the order
of a finite nonabelian simple group by the order of any involution
centralizer. -/
/-- **Brauer–Fowler theorem.** There is a function $f \colon \mathbb{N} \to \mathbb{N}$ such that
for every finite nonabelian simple group $G$ and every element $t \in G$ of order $2$, with
centralizer $C_G(t)$ in $G$, the order of $G$ satisfies $|G| \le f(|C_G(t)|)$.

Source: R. Brauer and K. A. Fowler, On groups of even order, Ann. of Math. (2) 62 (1955), 565-583. https://doi.org/10.2307/1970080 Via leanprover/lean-eval@38361be, problem `brauer_fowler`. -/
public theorem_wanted brauer_fowler :
    ∃ f : ℕ → ℕ, ∀ (G : Type) [Group G] [Finite G],
      IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      ∀ t : G, orderOf t = 2 →
        Nat.card G ≤ f (Nat.card (Subgroup.centralizer ({t} : Set G)))

end GroupTheory

end MathlibExt.GroupTheory.BrauerFowlerWanted
