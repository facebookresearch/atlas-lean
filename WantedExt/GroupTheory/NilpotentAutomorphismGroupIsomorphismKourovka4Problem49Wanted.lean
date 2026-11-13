/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nilpotent groups with isomorphic automorphism groups (Kourovka Notebook Problem 4.49)

Kourovka Notebook, Archive of Solved Problems, Problem 4.49 (V. N. Remeslennikov): let `G` and `H`
be finitely generated torsion-free nilpotent groups such that `Aut G ≅ Aut H`. Does it follow that
`G ≅ H`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentAutomorphismGroupIsomorphismKourovka4Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.49 (V. N.
Remeslennikov). UnsolvedMath record UM-00700256 (`KOU-4.49`), dataset ulamai/UnsolvedMath v1.8.0.

Finitely generated is `Group.FG`, nilpotent is `Group.IsNilpotent`, and `Aut G` is `MulAut G`.
Torsion-free is written `∀ g, g ≠ 1 → ¬ IsOfFinOrder g`.
-/

/-- Kourovka 4.49 (V. N. Remeslennikov): finitely generated torsion-free nilpotent groups `G`, `H`
with isomorphic automorphism groups are isomorphic. -/
def isomorphicAutomorphismGroupsImplyIsomorphic : Prop :=
  ∀ (G H : Type) [Group G] [Group H], Group.FG G → Group.FG H → Group.IsNilpotent G →
    Group.IsNilpotent H → (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    (∀ h : H, h ≠ 1 → ¬ IsOfFinOrder h) → Nonempty (MulAut G ≃* MulAut H) →
    Nonempty (G ≃* H)

/--
Resolved false: Noskov and Roman'kov construct non-isomorphic finitely generated torsion-free
nilpotent groups with isomorphic automorphism groups; the Kourovka Archive answers 4.49 "No".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.49 (V. N.
Remeslennikov); resolution: G. A. Noskov and V. A. Roman'kov, On nilpotent groups with close groups
of automorphisms, Algebra and Logic 13 (1974), 306-311, Kourovka Archive of Solved Problems, Problem
4.49: No, https://doi.org/10.1007/BF01463202.
-/
public theorem_wanted isomorphicAutomorphismGroupsImplyIsomorphic_refuted :
    ¬ isomorphicAutomorphismGroupsImplyIsomorphic

end MathlibExt.GroupTheory.NilpotentAutomorphismGroupIsomorphismKourovka4Problem49Wanted
