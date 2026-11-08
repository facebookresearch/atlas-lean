/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Glauberman's Z* theorem for isolated involutions

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.GlaubermanZStar` — glauberman_zStar (manifest `manifests/problems/glauberman_zStar.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.GlaubermanZStarWanted` namespace. Mathematical
statements are unchanged. Source: G. Glauberman, Central elements in core-free groups, J. Algebra 4 (1966).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace MathlibExt.GroupTheory.GlaubermanZStarWanted
namespace GroupTheory

/-!
Glauberman's `Z*`-theorem (1966).

Let `G` be a finite group and let `t ∈ G` be an *isolated involution*: an
element of order 2 such that no conjugate of `t` (other than `t` itself)
commutes with `t`. Then `t` is central in `G / O(G)`, where `O(G)` is the
largest normal subgroup of `G` of odd order.

Equivalently: there exists a normal subgroup `N ⊴ G` of odd order such that
every multiplicative commutator `g * t * g⁻¹ * t⁻¹` lies in `N`.

The hypothesis below is the *global* form of isolation ("no distinct conjugate
of `t` commutes with `t`"). This is equivalent to the more familiar local form
("`t` is the unique involution of a Sylow 2-subgroup of `C_G(t)`"), but is
self-contained and avoids reference to Sylow theory in the statement.

The proof is a deep application of modular (Brauer) representation theory and
is a cornerstone of the classification of finite simple groups: it is what
allows the local analysis to "fuse" 2-elements via odd-order normal subgroups.
-/

/-- Source: G. Glauberman, Central elements in core-free groups, J. Algebra 4 (1966). Via leanprover/lean-eval@38361be, problem `glauberman_zStar`. -/
public theorem_wanted glauberman_zStar
    (G : Type) [Group G] [Fintype G]
    (t : G) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N

end GroupTheory

end MathlibExt.GroupTheory.GlaubermanZStarWanted
