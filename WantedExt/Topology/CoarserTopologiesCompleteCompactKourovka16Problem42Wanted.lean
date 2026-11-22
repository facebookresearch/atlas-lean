/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abelian groups complete in every coarser group topology (Kourovka Notebook Problem 16.42)

Kourovka Notebook, Archive of Solved Problems, Problem 16.42 (E. G. Zelenyuk): is a topological
abelian group `(G, τ)` compact if every group topology `τ' ⊆ τ` on `G` is complete? (The answer is
yes if every continuous homomorphic image of `(G, τ)` is complete.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Cauchy

@[expose] public section

namespace MathlibExt.Topology.CoarserTopologiesCompleteCompactKourovka16Problem42Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.42 (E. G.
Zelenyuk). UnsolvedMath record UM-00701234 (`KOU-16.42`), dataset ulamai/UnsolvedMath v1.8.0.

Group topologies are Hausdorff, as in the resolution ("complete in each weaker Hausdorff group
topology"); for a non-Hausdorff `τ` no coarser topology is Hausdorff. A coarser topology `τ' ⊆ τ` is
`τ ≤ τ'` in Mathlib's order on topologies, and completeness refers to the group uniformity (the
right uniformity, equal to the left one for abelian groups).
-/

/-- Kourovka 16.42 (E. G. Zelenyuk): a Hausdorff abelian topological group `(G, τ)` is compact if
every Hausdorff group topology `τ' ⊆ τ` on `G` is complete. Coarser topologies are `τ ≤ τ'` in
Mathlib's order on topologies; completeness refers to the uniformity of the group topology (the
right uniformity, which equals the left one since `G` is abelian). -/
def completeCoarserTopologiesImpliesCompact : Prop :=
  ∀ (G : Type) [CommGroup G] (τ : TopologicalSpace G), @IsTopologicalGroup G τ _ → @T2Space G τ →
    (∀ (τ' : TopologicalSpace G) (h : @IsTopologicalGroup G τ' _), τ ≤ τ' → @T2Space G τ' →
      @CompleteSpace G (@IsTopologicalGroup.rightUniformSpace G _ τ' h)) →
    @CompactSpace G τ

/--
Resolved true: Banakh (Corollary 1.3) proves that an abelian topological group is compact if and
only if it is complete in each weaker Hausdorff group topology; the Kourovka Archive answers 16.42
"Yes, it is". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.42
(E. G. Zelenyuk); resolution: T. Banakh, A quantitative generalization of Prodanov-Stoyanov Theorem
on minimal Abelian topological groups, Topology Appl. 271 (2020), Article 106983, arXiv:1706.05411,
Corollary 1.3 (an Abelian topological group X is compact if and only if X is complete in each weaker
Hausdorff group topology); Kourovka Archive, Problem 16.42 (Yes, it is),
https://arxiv.org/abs/1706.05411.
-/
public theorem_wanted completeCoarserTopologiesImpliesCompact_holds :
    completeCoarserTopologiesImpliesCompact

end MathlibExt.Topology.CoarserTopologiesCompleteCompactKourovka16Problem42Wanted
