/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Topologically quasinormal subgroups are normal (Kourovka Notebook Problem 9.33)

Kourovka Notebook, Archive of Solved Problems, Problem 9.33 (Yu. N. Mukhin; question of F. Kümmich
and H. Scheerer): if `H` is a closed subgroup of a connected locally compact group `G` such that
`closure (H X) = closure H * closure X` for every closed subgroup `X` of `G`, then is `H` normal?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic

@[expose] public section

namespace MathlibExt.Topology.TopologicallyQuasinormalNormalKourovka9Problem33Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.33 (Yu. N.
Mukhin; F. Kümmich, H. Scheerer). UnsolvedMath record UM-00700566 (`KOU-9.33`), dataset
ulamai/UnsolvedMath v1.8.0.

Reading. The printed hypothesis `closure (H X) = closure H * closure X` says, for closed `H` and
`X`, only that `H X` is closed; in a compact connected group every such product is closed, so the
printed statement would make every closed subgroup of `SO(3)` normal. The problem is the
Kümmich-Scheerer question on topologically quasinormal subgroups (`closure (X H) = closure (H X)`
for every closed subgroup `X`; Kümmich and Scheerer, Rend. Sem. Mat. Univ. Padova 69 (1983),
195-210), and the Archive's answer "Yes, it is" cites exactly Scheiderer's paper, whose abstract
defines `Q` to be topologically quasinormal when `closure (A Q) = closure (Q A)` for every closed
subgroup `A` and states "We show that every tqn subgroup of a connected locally compact group is
actually a normal subgroup" (zbMATH Zbl 0543.22003: "It has been conjectured that every tqn subgroup
of a connected locally compact group is actually a normal subgroup. We prove this to be correct").
The module states Scheiderer's theorem. Locally compact groups are Hausdorff.
-/

open scoped Pointwise

/-- The closed subgroup `Q` of the topological group `G` is topologically quasinormal (Kümmich and
Scheerer): `closure (A Q) = closure (Q A)` for every closed subgroup `A` of `G`. -/
def IsTopologicallyQuasinormal {G : Type*} [Group G] [TopologicalSpace G] (Q : Subgroup G) :
    Prop :=
  IsClosed (Q : Set G) ∧ ∀ A : Subgroup G, IsClosed (A : Set G) →
    closure ((A : Set G) * (Q : Set G)) = closure ((Q : Set G) * (A : Set G))

/-- Kourovka 9.33 (F. Kümmich, H. Scheerer), as resolved by Scheiderer: every topologically
quasinormal subgroup of a connected locally compact group is normal. -/
def topologicallyQuasinormalIsNormal : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [ConnectedSpace G] (Q : Subgroup G), IsTopologicallyQuasinormal Q → Q.Normal

/--
Resolved true: Scheiderer proves the Kümmich-Scheerer conjecture that every topologically
quasinormal subgroup of a connected locally compact group is normal, the answer the Kourovka Archive
gives to 9.33 (whose printed hypothesis `closure (H X) = closure H * closure X` is a misprint of
`closure (H X) = closure (X H)`). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 9.33 (Yu. N. Mukhin; F. Kümmich, H. Scheerer); resolution: C. Scheiderer,
Topologisch quasinormale Untergruppen zusammenhängender lokalkompakter Gruppen, Monatsh. Math. 98
(1984), 75-81, Kourovka Archive, Problem 9.33: Yes, it is (Scheiderer); paper, abstract: every
topologically quasinormal subgroup of a connected locally compact group is normal (also zbMATH Zbl
0543.22003), https://doi.org/10.1007/BF01536910.
-/
public theorem_wanted topologicallyQuasinormalIsNormal_holds : topologicallyQuasinormalIsNormal

end MathlibExt.Topology.TopologicallyQuasinormalNormalKourovka9Problem33Wanted
