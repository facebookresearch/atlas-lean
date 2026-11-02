/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closed cofinitary permutation groups need not be locally compact (Kourovka Notebook Problem 13.28)

Kourovka Notebook, Archive of Solved Problems, Problem 13.28 (D. M. Evans; P. J. Cameron): a
permutation group on an infinite set is cofinitary if its non-identity elements fix only finitely
many points. Is every closed cofinitary permutation group locally compact in the topology of
pointwise convergence?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Constructions
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology

@[expose] public section

namespace MathlibExt.GroupTheory.ClosedCofinitaryLocallyCompactKourovka13Problem28Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.28 (D. M.
Evans; P. J. Cameron). UnsolvedMath record UM-00700946 (`KOU-13.28`), dataset ulamai/UnsolvedMath
v1.8.0.

The topology of pointwise convergence on `Sym(Ω)` is the shared `Equiv.Perm.pointwiseTopology`
(induced from the product `Ω → Ω` of discrete spaces); closed means closed in `Sym(Ω)`, and local
compactness refers to the subspace topology on `G`.
-/

/-- **Cofinitary permutation groups.** A subgroup $G$ of the group of permutations of a set
$\Omega$ is cofinitary when every non-identity element of $G$ fixes only finitely many points of
$\Omega$. -/
def IsCofinitary {Ω : Type} (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ g ∈ G, g ≠ 1 → {x : Ω | g x = x}.Finite

/-- **Claim of Kourovka Problem 13.28.** For every infinite set $\Omega$, every cofinitary subgroup
$G$ of the group of permutations of $\Omega$ that is closed in the topology of pointwise
convergence is locally compact in the subspace topology. -/
def closedCofinitaryLocallyCompact : Prop :=
  ∀ (Ω : Type) [Infinite Ω] (G : Subgroup (Equiv.Perm Ω)), IsCofinitary G →
    @IsClosed _ (Equiv.Perm.pointwiseTopology (α := Ω)) (G : Set (Equiv.Perm Ω)) →
    @LocallyCompactSpace G
      (TopologicalSpace.induced ((↑) : G → Equiv.Perm Ω)
        (Equiv.Perm.pointwiseTopology (α := Ω)))

/--
**Closed cofinitary permutation groups need not be locally compact.** The claim of Kourovka
Problem 13.28 is false: there are an infinite set $\Omega$ and a subgroup $G$ of the group of
permutations of $\Omega$ such that $G$ is cofinitary (every non-identity element of $G$ fixes only
finitely many points of $\Omega$) and closed in the topology of pointwise convergence, but $G$ is
not locally compact in the subspace topology.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.28 (D. M.
Evans; P. J. Cameron); resolution: G. Hjorth, J. Algebra 200 (1998), no. 2, 439-448, Kourovka
Archive, Problem 13.28: No, not always.
-/
public theorem_wanted closedCofinitaryLocallyCompact_refuted : ¬ closedCofinitaryLocallyCompact

end MathlibExt.GroupTheory.ClosedCofinitaryLocallyCompactKourovka13Problem28Wanted
