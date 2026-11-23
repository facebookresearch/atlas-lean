/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Modularity of the lattice of group topologies (Kourovka Notebook Problem 14.4)

Kourovka Notebook, Problem 14.4 (V. I. Arnautov): (a) is there a nilpotent group `G` whose lattice
`𝓛(G)` of all group topologies is not modular? (b) is `𝓛(G)` non-modular for every countable
nilpotent non-abelian group `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Topology.Algebra.Group.GroupTopology

@[expose] public section

namespace MathlibExt.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.4 (V. I. Arnautov). UnsolvedMath record
UM-00700989 (`KOU-14.4`), dataset ulamai/UnsolvedMath v1.8.0.

`𝓛(G)` is the lattice of all (not necessarily Hausdorff) group topologies, Mathlib's `GroupTopology
G`; modularity does not depend on the direction of the order. In (b) "countable" is read as
countably infinite, as in the resolving paper: for a finite group the group topologies correspond to
normal subgroups, a modular lattice, so with finite groups (b) would fail for `Q₈`.
-/

/-- **Kourovka Problem 14.4(a) (nilpotent groups with non-modular topology lattice).** This
proposition states that some nilpotent group $G$ has a non-modular lattice $\mathcal{L}(G)$ of all
(not necessarily Hausdorff) group topologies. -/
def nilpotentGroupTopologyLatticeNotModular : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsNilpotent G ∧ ¬ IsModularLattice (GroupTopology G)

/-- **Kourovka Problem 14.4(b) (countable nilpotent groups).** This proposition states that for
every countably infinite non-abelian nilpotent group $G$, the lattice $\mathcal{L}(G)$ of all (not
necessarily Hausdorff) group topologies on $G$ is not modular. -/
def countableNilpotentNonabelianTopologyLatticeNotModular : Prop :=
  ∀ (G : Type) [Group G], Countable G → Infinite G → Group.IsNilpotent G →
    (∃ x y : G, x * y ≠ y * x) → ¬ IsModularLattice (GroupTopology G)

/--
**A nilpotent group with non-modular lattice of group topologies.** There is a nilpotent group $G$
whose lattice of all (not necessarily Hausdorff) group topologies is not modular.

Arnautov and Topală found such a group; the Kourovka Notebook (21st issue) answers 14.4(a) "Yes".

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 14.4 (V. I. Arnautov); resolution: (a) V. Arnautov and A. Topală,
Bul. Acad. Ştiinţe Repub. Mold. Mat. 1998, no. 2(27), 130-131; (b) D. Peng, On the lattice of group
topologies, preprint, arXiv:2310.08269 (2023), (b) Theorem 1.1: there is a countably infinite
non-abelian nilpotent group whose lattice of all (not necessarily Hausdorff) group topologies is
modular; the Kourovka Notebook (21st issue) marks 14.4 solved: a) Yes; b) No, there are such groups
with modular L(G), https://arxiv.org/abs/2310.08269.
-/
public theorem_wanted nilpotentGroupTopologyLatticeNotModular_holds :
    nilpotentGroupTopologyLatticeNotModular

/--
**A countable nilpotent group with modular lattice of group topologies.** It is not the case that
for every countably infinite non-abelian nilpotent group $G$ the lattice of all (not necessarily
Hausdorff) group topologies on $G$ is not modular; that is, some countably infinite non-abelian
nilpotent group has a modular lattice of group topologies.

Peng constructs (Theorem 1.1) a countably infinite non-abelian nilpotent group whose lattice of
group topologies is modular; the Kourovka Notebook (21st issue) answers 14.4(b) "No".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.4 (V. I. Arnautov); resolution: (a) V.
Arnautov and A. Topală, Bul. Acad. Ştiinţe Repub. Mold. Mat. 1998, no. 2(27), 130-131; (b) D. Peng,
On the lattice of group topologies, preprint, arXiv:2310.08269 (2023), (b) Theorem 1.1: there is a
countably infinite non-abelian nilpotent group whose lattice of all (not necessarily Hausdorff)
group topologies is modular; the Kourovka Notebook (21st issue) marks 14.4 solved: a) Yes; b) No,
there are such groups with modular L(G), https://arxiv.org/abs/2310.08269.
-/
public theorem_wanted countableNilpotentNonabelianTopologyLatticeNotModular_refuted :
    ¬ countableNilpotentNonabelianTopologyLatticeNotModular

end MathlibExt.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4Wanted
