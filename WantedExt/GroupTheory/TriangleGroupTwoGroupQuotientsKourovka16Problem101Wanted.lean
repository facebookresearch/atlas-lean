/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite `2`-group quotients of the `(2, 4, 8)` triangle group (Kourovka Notebook Problem 16.101)

Kourovka Notebook, Archive of Solved Problems, Problem 16.101 (J. Wiegold): do there exist
uncountably many infinite `2`-groups that are quotients of the group `⟨x, y | x² = y⁴ = (xy)⁸ = 1⟩`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.PresentedGroup

@[expose] public section

namespace MathlibExt.GroupTheory.TriangleGroupTwoGroupQuotientsKourovka16Problem101Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.101 (J.
Wiegold). UnsolvedMath record UM-00701292 (`KOU-16.101`), dataset ulamai/UnsolvedMath v1.8.0.

"Uncountably many" is read as an uncountable family of quotients by normal subgroups that are
pairwise non-isomorphic. A `2`-group is a group all of whose elements have `2`-power order
(`IsPGroup 2`). The group is Mathlib's `PresentedGroup` on two generators.
-/

/-- The group `⟨x, y | x² = y⁴ = (x y)⁸ = 1⟩`. -/
abbrev wiegoldGroup : Type :=
  PresentedGroup ({FreeGroup.of 0 ^ 2, FreeGroup.of 1 ^ 4, (FreeGroup.of 0 * FreeGroup.of 1) ^ 8} :
    Set (FreeGroup (Fin 2)))

/-- Kourovka 16.101 (J. Wiegold): there are uncountably many pairwise non-isomorphic infinite
`2`-groups that are quotients of `⟨x, y | x² = y⁴ = (x y)⁸ = 1⟩`. -/
def uncountablyManyInfiniteTwoGroupQuotients : Prop :=
  ∃ (ι : Type) (_ : Uncountable ι) (N : ι → Subgroup wiegoldGroup) (_ : ∀ i, (N i).Normal),
    (∀ i, Infinite (wiegoldGroup ⧸ N i) ∧ IsPGroup 2 (wiegoldGroup ⧸ N i)) ∧
      ∀ i j, Nonempty ((wiegoldGroup ⧸ N i) ≃* (wiegoldGroup ⧸ N j)) → i = j

/--
Resolved true: the Kourovka Archive answers 16.101 "Yes, there do" (Grigorchuk; Minasyan, Olshanskii
and Sonkin): uncountably many pairwise non-isomorphic infinite `2`-groups are quotients of `⟨x, y |
x² = y⁴ = (xy)⁸ = 1⟩`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 16.101 (J. Wiegold); resolution: R. I. Grigorchuk, Algebra Discrete Math. 2009, no. 4,
78-96; A. Minasyan, A. Yu. Olshanskii and D. Sonkin, Periodic quotients of hyperbolic and large
groups, Groups Geom. Dyn. 3 (2009), no. 3, 423-452, arXiv:0804.3328, Kourovka Archive, Problem
16.101 (answer: Yes, there do); Minasyan, Olshanskii and Sonkin, abstract (continua of pairwise
non-isomorphic periodic quotients, with a positive answer to Wiegold's question),
https://arxiv.org/abs/0804.3328.
-/
public theorem_wanted uncountablyManyInfiniteTwoGroupQuotients_holds :
    uncountablyManyInfiniteTwoGroupQuotients

end MathlibExt.GroupTheory.TriangleGroupTwoGroupQuotientsKourovka16Problem101Wanted
