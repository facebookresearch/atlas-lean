/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local isomorphism classes of simple tdlc groups (Kourovka Notebook Problem 19.22)

Kourovka Notebook, Problem 19.22 (P.-E. Caprace), marked solved in the 21st issue: let `𝒮` be the
class of non-discrete compactly generated, topologically simple, totally disconnected locally
compact groups; two topological groups are locally isomorphic if they contain isomorphic open
subgroups. Is the number of local isomorphism classes of groups in `𝒮` uncountable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

namespace MathlibExt.GroupTheory.LocalIsomorphismClassesSimpleTdlcKourovka19Problem22Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.22 (P.-E. Caprace). UnsolvedMath record
UM-00701570 (`KOU-19.22`), dataset ulamai/UnsolvedMath v1.8.0.

Groups in `𝒮` are Hausdorff topological groups in `Type`; compactly generated means generated as a
group by a compact subset; topologically simple means nontrivial with no closed normal subgroups
other than `⊥` and `⊤`. Local isomorphism is an isomorphism of topological groups between open
subgroups (`≃ₜ*`). "Uncountably many classes" is stated as an uncountable family of groups in `𝒮`
that are pairwise not locally isomorphic.
-/

/-- **Caprace's class $\mathcal{S}$.** A group $G$ with a topology belongs to the class
$\mathcal{S}$ when it is a topological group that is Hausdorff, totally disconnected, locally
compact and not discrete, is generated as a group by some compact subset, and is topologically
simple: $G$ is nontrivial and its only closed normal subgroups are the trivial subgroup and $G$
itself. -/
def IsInClassS (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  IsTopologicalGroup G ∧ T2Space G ∧ TotallyDisconnectedSpace G ∧ LocallyCompactSpace G ∧
    ¬ DiscreteTopology G ∧ (∃ K : Set G, IsCompact K ∧ Subgroup.closure K = ⊤) ∧ Nontrivial G ∧
    ∀ N : Subgroup G, N.Normal → IsClosed (N : Set G) → N = ⊥ ∨ N = ⊤

/-- Two topological groups are locally isomorphic: they contain open subgroups that are isomorphic
as topological groups. -/
def LocallyIsomorphic (G H : Type) [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] :
    Prop :=
  ∃ (U : OpenSubgroup G) (V : OpenSubgroup H), Nonempty ((U : Subgroup G) ≃ₜ* (V : Subgroup H))

/-- **Caprace's problem on local isomorphism classes (Kourovka 19.22).** The statement that the
groups in Caprace's class $\mathcal{S}$ fall into uncountably many local isomorphism classes: there
is a family $(G_i)_{i \in I}$ of groups in $\mathcal{S}$, indexed by an uncountable set $I$, such
that $G_i$ and $G_j$ are not locally isomorphic whenever $i \ne j$. -/
def uncountablyManyLocalIsomorphismClasses : Prop :=
  ∃ (ι : Type) (_ : Uncountable ι) (G : ι → Type) (_ : ∀ i, Group (G i))
    (_ : ∀ i, TopologicalSpace (G i)),
    (∀ i, IsInClassS (G i)) ∧ ∀ i j, i ≠ j → ¬ LocallyIsomorphic (G i) (G j)

/--
**Uncountably many local isomorphism classes of simple tdlc groups.** There is a family
$(G_i)_{i \in I}$ of groups in Caprace's class $\mathcal{S}$ (non-discrete, compactly generated,
topologically simple, totally disconnected, locally compact Hausdorff topological groups), indexed
by an uncountable set $I$, such that $G_i$ and $G_j$ are not locally isomorphic whenever $i \ne j$.
This answers Kourovka Notebook Problem 19.22 (P.-E. Caprace) in the affirmative.

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 19.22 (P.-E. Caprace); resolution: I. Castellano, J. Fariña-Asategui, M. E.
Garciarena, B. Marchionna, M. Quick, C. D. Reid, S. M. Smith, S. Tornier, M. Vannacci and J. S.
Wilson, Uncountably many local isomorphism types of compactly generated simple groups, preprint,
arXiv:2609.17410 (2026), Theorem A: there exist 2^ℵ₀ many non-discrete compactly generated simple
tdlc groups which are not pairwise locally isomorphic; the Kourovka Notebook (21st issue) marks
19.22 solved: Yes, it is, https://arxiv.org/abs/2609.17410.
-/
public theorem_wanted uncountablyManyLocalIsomorphismClasses_holds :
    uncountablyManyLocalIsomorphismClasses

end MathlibExt.GroupTheory.LocalIsomorphismClassesSimpleTdlcKourovka19Problem22Wanted
