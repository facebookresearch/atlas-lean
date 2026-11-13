/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite compact p-groups with finite centralizers (Kourovka Notebook Problem 9.34)

Kourovka Notebook, Archive of Solved Problems, Problem 9.34 (Yu. N. Mukhin (after S. K. Grosser and
W. N. Herfort)): does there exist an infinite compact `p`-group in which the centralizers of all
elements are finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace MathlibExt.GroupTheory.CompactPGroupFiniteCentralizersKourovka9Problem34Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.34 (Yu. N.
Mukhin). UnsolvedMath record UM-00700567 (`KOU-9.34`), dataset ulamai/UnsolvedMath v1.8.0.

Compact groups are Hausdorff topological groups; without `T2Space` an infinite abstract `p`-group
with finite centralizers (a Tarski monster) carries the indiscrete compact group topology. A
`p`-group is one in which every element has `p`-power order (`IsPGroup p G`). The centralizer of the
identity is the whole group, so "all elements" means all non-trivial elements.
-/

/-- Kourovka 9.34 (Yu. N. Mukhin, after S. K. Grosser and W. N. Herfort): there is an infinite
compact Hausdorff `p`-group (every element has `p`-power order) in which the centralizer of every
non-trivial element is finite. -/
def infiniteCompactPGroupFiniteCentralizers : Prop :=
  ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : TopologicalSpace G), p.Prime ∧ IsTopologicalGroup G ∧
    CompactSpace G ∧ T2Space G ∧ Infinite G ∧ IsPGroup p G ∧
    ∀ g : G, g ≠ 1 → (Subgroup.centralizer {g} : Set G).Finite

/--
Resolved false: the Kourovka Archive answers 9.34 "No, it does not exist", by the connection
established by Grosser and Herfort between this problem and the restricted Burnside problem together
with Zel'manov's positive solution of the latter. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 9.34 (Yu. N. Mukhin); resolution: S. K. Grosser and W. N.
Herfort, Abelian subgroups of topological groups, Trans. Amer. Math. Soc. 283 (1984), no. 1,
211-223; E. I. Zel'manov, Math. USSR-Izv. 36 (1991), 41-60; Math. USSR-Sb. 72 (1992), 543-565,
Kourovka Archive of Solved Problems, Problem 9.34: No, it does not exist, in view of the connection
with the restricted Burnside problem and Zel'manov's positive solution of the latter,
https://doi.org/10.1090/S0002-9947-1984-0735417-4.
-/
public theorem_wanted infiniteCompactPGroupFiniteCentralizers_refuted :
    ¬ infiniteCompactPGroupFiniteCentralizers

end MathlibExt.GroupTheory.CompactPGroupFiniteCentralizersKourovka9Problem34Wanted
