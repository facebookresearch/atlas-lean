/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partitions into absolutely dense subsets (Kourovka Notebook Problem 13.47)

Kourovka Notebook, Archive of Solved Problems, Problem 13.47 (I. V. Protasov): can every countable
abelian group with finitely many involutions be partitioned into two subsets that are dense in every
group topology?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Group.GroupTopology

@[expose] public section

namespace MathlibExt.GroupTheory.AbsolutelyDensePartitionKourovka13Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.47 (I. V.
Protasov). UnsolvedMath record UM-00700965 (`KOU-13.47`), dataset ulamai/UnsolvedMath v1.8.0.

"Every group topology" is read as every non-discrete Hausdorff group topology: no proper subset is
dense in the discrete topology, and without the Hausdorff condition the claim fails, e.g. for `ℤ ×
(ℤ/3)²` (the topology whose open sets are unions of cosets of a subgroup of order `3` forces every
line of the affine plane over `𝔽₃` to meet both cells, and that plane has no such 2-colouring). This
is Protasov's notion of an absolutely dense subset. Topologies range over Mathlib's `GroupTopology
G`.
-/

/-- Kourovka 13.47 (I. V. Protasov): every countable abelian group `G` with finitely many
involutions can be partitioned as `G = A₁ ∪ A₂` (disjointly) so that `A₁` and `A₂` are both dense
in every non-discrete Hausdorff group topology on `G`. -/
def countableAbsolutelyDensePartition : Prop :=
  ∀ (G : Type) [CommGroup G], Countable G → {g : G | g ≠ 1 ∧ g ^ 2 = 1}.Finite →
    ∃ A₁ A₂ : Set G, A₁ ∪ A₂ = Set.univ ∧ Disjoint A₁ A₂ ∧
      ∀ τ : GroupTopology G, @T2Space G τ.toTopologicalSpace → τ.toTopologicalSpace ≠ ⊥ →
        @Dense G τ.toTopologicalSpace A₁ ∧ @Dense G τ.toTopologicalSpace A₂

/--
Resolved true: the Kourovka Archive answers 13.47 "Yes, it can", citing Zelenyuk: every countable
abelian group with finitely many involutions splits into two cells that are dense in every
non-discrete Hausdorff group topology. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 13.47 (I. V. Protasov); resolution: E. G. Zelenyuk, Ukrain. Math. J. 51
(1999), no. 1, 44-50, Kourovka Archive, Problem 13.47 (answer: Yes, it can).
-/
public theorem_wanted countableAbsolutelyDensePartition_holds : countableAbsolutelyDensePartition

end MathlibExt.GroupTheory.AbsolutelyDensePartitionKourovka13Problem47Wanted
