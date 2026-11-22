/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# `Aut G ≅ Aut H` for a proper subgroup of a `p`-group (Kourovka Notebook Problem 15.27)

Kourovka Notebook, Archive of Solved Problems, Problem 15.27 (Ya. G. Berkovich): is it possible that
`Aut G ≅ Aut H` for a finite `p`-group `G` of order greater than `2` and a proper subgroup `H < G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.27 (Ya. G.
Berkovich). UnsolvedMath record UM-00701115 (`KOU-15.27`), dataset ulamai/UnsolvedMath v1.8.0.

The target asks for some prime `p`. The bound `|G| > 2` excludes `G` of order `2` with `H = 1`.
`Aut` is `MulAut`, compared by a group isomorphism.
-/

/-- Kourovka 15.27 (Ya. G. Berkovich): for some prime `p` there are a finite `p`-group `G` of order
greater than `2` and a proper subgroup `H < G` with `Aut G ≅ Aut H`. -/
def autIsoAutOfProperSubgroup : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧ 2 < Nat.card G ∧
    ∃ H : Subgroup G, H ≠ ⊤ ∧ Nonempty (MulAut G ≃* MulAut H)

/--
Resolved true: the Kourovka Archive answers 15.27 "Yes, it is possible" (T. Li), with a `2`-group
`G` of order `32` and a subgroup `H` of order `16`. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 15.27 (Ya. G. Berkovich); resolution: T. Li, Arch. Math. 92
(2009), 287-290, Kourovka Archive, Problem 15.27 (answer: Yes, it is possible, for |G| = 2|H| = 32).
-/
public theorem_wanted autIsoAutOfProperSubgroup_holds : autIsoAutOfProperSubgroup

end MathlibExt.GroupTheory.AutomorphismGroupProperSubgroupKourovka15Problem27Wanted
