/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The set of compact elements of a totally disconnected group (Kourovka Notebook Problem 9.48)

Kourovka Notebook, Archive of Solved Problems, Problem 9.48 (I. V. Protasov): in a null-dimensional
locally compact group, is the set of all compact elements closed?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

namespace MathlibExt.GroupTheory.CompactElementsClosedKourovka9Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.48 (I. V.
Protasov). UnsolvedMath record UM-00700581 (`KOU-9.48`), dataset ulamai/UnsolvedMath v1.8.0.

Locally compact groups are Hausdorff topological groups; for them null-dimensional is the same as
totally disconnected. An element `g` is compact (periodic) if the closure of `⟨g⟩` is compact.
-/

/-- Kourovka 9.48 (I. V. Protasov): in a totally disconnected (null-dimensional) locally compact
Hausdorff group the set of compact elements, the `g` for which the closure of `⟨g⟩` is compact, is
closed. -/
def compactElementsClosed : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G],
    IsClosed {g : G | IsCompact (closure (Subgroup.zpowers g : Set G))}

/--
Resolved true: Willis proves that the set of periodic (compact) elements of a totally disconnected
locally compact group is closed (Bull. Austral. Math. Soc. 51 (1995), Theorem 2, using the tidy
subgroups of Math. Ann. 300 (1994); Theorem 2.8 in Brehm-Gheysens-Le Boudec-Rollin,
arXiv:1511.09238); the Kourovka Archive answers 9.48 "Yes, it is". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.48 (I. V. Protasov); resolution: G.
A. Willis, The structure of totally disconnected, locally compact groups, Math. Ann. 300 (1994),
341-363, G. A. Willis, Totally disconnected groups and proofs of conjectures of Hofmann and
Mukherjea, Bull. Austral. Math. Soc. 51 (1995), 489-494, Theorem 2 (the set P(G) of periodic
elements, those g with the closure of ⟨g⟩ compact, of a totally disconnected locally compact group G
is closed), proved with the tidy subgroups and scale function of the 1994 paper; restated as Theorem
2.8 in A. Brehm, M. Gheysens, A. Le Boudec and R. Rollin, The scale function and tidy subgroups,
arXiv:1511.09238; Kourovka Archive of Solved Problems, Problem 9.48: Yes, it is,
https://doi.org/10.1007/BF01450491.
-/
public theorem_wanted compactElementsClosed_holds : compactElementsClosed

end MathlibExt.GroupTheory.CompactElementsClosedKourovka9Problem48Wanted
