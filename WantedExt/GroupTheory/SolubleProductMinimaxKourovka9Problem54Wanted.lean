/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Soluble products of minimax groups (Kourovka Notebook Problem 9.54)

Kourovka Notebook, Archive of Solved Problems, Problem 9.54 (D. J. S. Robinson): if `G = HK` is a
soluble group and `H`, `K` are minimax groups, is it true that `G` is a minimax group?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.MinimaxFiniteImagesKourovka12Problem90Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleProductMinimaxKourovka9Problem54Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.54 (D. J. S.
Robinson). UnsolvedMath record UM-00700587 (`KOU-9.54`), dataset ulamai/UnsolvedMath v1.8.0.

`G = HK` means that every element is a product `hk` (`(H : Set G) * K = univ`). Minimax groups are
the 12.90 entry's `IsMinimax`: a finite series `1 = G₀ ⊴ G₁ ⊴ ⋯ ⊴ Gₙ = G` each of whose factors
satisfies the maximal or the minimal condition on subgroups.
-/

open MathlibExt.GroupTheory.MinimaxFiniteImagesKourovka12Problem90Wanted
open scoped Pointwise

/-- Kourovka 9.54 (D. J. S. Robinson): a soluble group `G = HK` that is the product of two minimax
subgroups `H` and `K` (`IsMinimax`, from the 12.90 entry) is minimax. -/
def solubleProductMinimaxIsMinimax : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G), Group.IsSolvable G →
    (H : Set G) * (K : Set G) = Set.univ → IsMinimax H → IsMinimax K → IsMinimax G

/--
Resolved true: the Kourovka Archive answers 9.54 "Yes, it is true", citing Wilson's paper on soluble
products of minimax groups and Sysak: a soluble group that is the product of two minimax subgroups
is minimax. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.54
(D. J. S. Robinson); resolution: J. S. Wilson, Soluble products of minimax groups, and nearly
surjective derivations, J. Pure Appl. Algebra 53 (1988), no. 3, 297-318; Ya. P. Sysak, Radical
modules over groups of finite rank, Inst. of Math. Acad. Sci. Ukrain. SSR, Kiev, 1989 (Russian),
Kourovka Archive of Solved Problems, Problem 9.54: Yes, it is true,
https://doi.org/10.1016/0022-4049(88)90129-6.
-/
public theorem_wanted solubleProductMinimaxIsMinimax_holds : solubleProductMinimaxIsMinimax

end MathlibExt.GroupTheory.SolubleProductMinimaxKourovka9Problem54Wanted
