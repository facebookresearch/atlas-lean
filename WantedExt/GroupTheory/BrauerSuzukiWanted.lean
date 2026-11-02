/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Brauer–Suzuki theorem (quaternion Sylow 2-subgroup)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.BrauerSuzuki` — brauer_suzuki (manifest `manifests/problems/brauer_suzuki.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.BrauerSuzukiWanted` namespace. Mathematical
statements are unchanged. Source: R. Brauer and M. Suzuki, On finite groups of even order whose 2-Sylow group is a quaternion group, Proc. Nat. Acad. Sci. U.S.A. 45 (1959), 1757-1759. https://doi.org/10.1073/pnas.45.12.1757
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

@[expose] public section

namespace MathlibExt.GroupTheory.BrauerSuzukiWanted
namespace GroupTheory
namespace Defs

/-- **Odd core of a group.** The odd core $O(G)$ of a group $G$ is the supremum, in the lattice of
subgroups of $G$, of all normal subgroups of $G$ whose order is finite and odd.

For a finite group this is the largest normal subgroup of odd order, classically denoted $O(G)$
(in older notation $O_{2'}(G)$): the join of two normal subgroups of odd order is again a normal
subgroup of odd order, so the supremum is itself one. For an infinite group the definition still
makes sense as a subgroup, though it need not be of odd order.
-/
def oddCore (G : Type*) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}

/-- The odd core is normal: conjugation by any `g : G` fixes every normal
subgroup in the family pointwise, hence fixes their supremum setwise. -/
instance oddCore_normal (G : Type*) [Group G] : (oddCore G).Normal where
  conj_mem n hn g := by
    have hn' : n ∈ ⨆ N : {N : Subgroup G // N.Normal ∧ Odd (Nat.card N)},
        (N : Subgroup G) := by
      rwa [oddCore, sSup_eq_iSup'] at hn
    refine Subgroup.iSup_induction (C := fun y => g * y * g⁻¹ ∈ oddCore G)
      _ hn' (fun N x hxN => ?_) ?_ (fun x y hx hy => ?_)
    · -- `N.val` is a normal subgroup, so `g * x * g⁻¹ ∈ N.val ≤ oddCore G`
      have hN_norm : (N : Subgroup G).Normal := N.prop.1
      exact (le_sSup N.prop : (N : Subgroup G) ≤ oddCore G)
        (hN_norm.conj_mem x hxN g)
    · -- `g * 1 * g⁻¹ = 1 ∈ oddCore G`
      show g * 1 * g⁻¹ ∈ oddCore G
      simp
    · -- `g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹)`
      show g * (x * y) * g⁻¹ ∈ oddCore G
      have h_distr : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
        group
      rw [h_distr]
      exact mul_mem hx hy

end Defs
end GroupTheory

namespace GroupTheory

open GroupTheory.Defs

/-!
# Brauer–Suzuki theorem on generalized quaternion Sylow 2-subgroups

Let `G` be a finite group whose Sylow 2-subgroups are generalized
quaternion: isomorphic to `Q_{2^n}` for some `n ≥ 3`, i.e., to Mathlib's
`QuaternionGroup (2^(n-2))` (since `QuaternionGroup m` has order `4m`,
giving `|Q_{2^n}| = 2^n` and `n = log₂|P|`). Let `t` be the unique
involution of any (equivalently, every) Sylow 2-subgroup. Then the
image of `t` in `G / O(G)` is central, where `O(G)` is the largest
normal subgroup of `G` of odd order.

R. Brauer and M. Suzuki, "On finite groups of even order whose 2-Sylow
group is a quaternion group", Proc. Nat. Acad. Sci. U.S.A. 45 (1959).
This was the precursor of Glauberman's Z*-theorem (1966) and the
historical seed of the local-analysis programme in CFSG.

The conclusion is phrased entirely in the quotient `G / O(G)`,
applied to the image of `t` under `QuotientGroup.mk`; the value of
`t : G` only enters via that map.

Introduces `Defs/OddCore.lean` since Mathlib has no `oddCore`/`O(G)`
operation.
-/

/- **Brauer–Suzuki theorem (quaternion case).** -/
/-- **Brauer–Suzuki theorem.** Let $G$ be a finite group, let $O(G)$, the odd core of $G$, be the
subgroup generated by all normal subgroups of $G$ of odd order, let $n \ge 3$, and let $P$ be a
Sylow $2$-subgroup of $G$ isomorphic to the generalized quaternion group $Q_{2^n}$ of order $2^n$.
If $t \in P$ has order $2$, then the image of $t$ in $G / O(G)$ lies in the center of $G / O(G)$.

Source: R. Brauer and M. Suzuki, On finite groups of even order whose 2-Sylow group is a quaternion group, Proc. Nat. Acad. Sci. U.S.A. 45 (1959), 1757-1759. https://doi.org/10.1073/pnas.45.12.1757 Via leanprover/lean-eval@38361be, problem `brauer_suzuki`. -/
public theorem_wanted brauer_suzuki {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈
      Subgroup.center (G ⧸ oddCore G)

end GroupTheory

end MathlibExt.GroupTheory.BrauerSuzukiWanted
