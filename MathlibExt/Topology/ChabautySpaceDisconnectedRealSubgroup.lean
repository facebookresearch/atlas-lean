/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Connected.Clopen

/-!
# A locally compact group containing ℝ with disconnected Chabauty space

A Hausdorff locally compact topological group can contain a topologically embedded copy of the
additive group of `ℝ` without its Chabauty space of closed subgroups being connected. We use
`ℝ × A₅`, with the alternating group on five letters given the discrete topology, rather than
Tsybenko's matrix group. As in the perfect-group case of Cornulier's proof, a subgroup that
projects onto the finite factor must contain that factor: its commutators have trivial real
coordinate and project onto the perfect factor. This condition defines a nontrivial clopen set.

## References

* E. I. Khukhro and V. D. Mazurov (eds.), *Unsolved Problems in Group Theory: The Kourovka
  Notebook*, 21st issue, Novosibirsk (2026), Archive of Solved Problems, Problem 8.61
  (I. V. Protasov), p. 246, arXiv:1401.0300v49.
* Yu. V. Tsybenko, *Abstracts of 17th All-USSR Algebraic Conf., Part 1*, Minsk (1983), p. 213,
  the original matrix counterexample, as cited in the archive.
* Yves Cornulier, *On the Chabauty space of locally compact abelian groups*, Algebraic & Geometric
  Topology **11** (2011), 2007–2035, Theorem 1.3 and the discussion preceding Theorem 1.5 (p. 2009),
  and Proposition 8.6, doi:10.2140/agt.2011.11.2007.
* Igor V. Protasov, *Selective Survey on Spaces of Closed Subgroups of Topological Groups*,
  Axioms **7** (2018), no. 4, article 75, §1.1 and Theorem 8, doi:10.3390/axioms7040075.
-/

@[expose] public section

namespace MathlibExt.Topology.ChabautySpaceConnectedRealSubgroupKourovka8Problem61Wanted

/-- The Chabauty topology on the closed subgroups of `G`, with subbasic open sets
`{H | H ∩ K = ∅}` for compact `K` and `{H | H ∩ U ≠ ∅}` for open `U`. -/
abbrev chabautyTopology (G : Type) [TopologicalSpace G] [Group G] :
    TopologicalSpace {H : Subgroup G // IsClosed (H : Set G)} :=
  TopologicalSpace.generateFrom
    ({S | ∃ K : Set G, IsCompact K ∧ S = {H | Disjoint (H.1 : Set G) K}} ∪
      {S | ∃ U : Set G, IsOpen U ∧ S = {H | ((H.1 : Set G) ∩ U).Nonempty}})

/-- Kourovka 8.61 (I. V. Protasov): if a locally compact group `G` contains a subgroup
topologically isomorphic to the additive group `ℝ` (a topological embedding of `ℝ` as a group
homomorphism), then the space of closed subgroups of `G` is connected in the Chabauty topology. -/
def chabautySpaceConnectedOfRealSubgroup : Prop :=
  ∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G], (∃ φ : Multiplicative ℝ →* G, Topology.IsEmbedding φ) →
    @ConnectedSpace _ (chabautyTopology G)

/-- A nontrivial finite discrete perfect factor disconnects the Chabauty space of a product
with an abelian group whose topology is `T₁`. -/
private theorem not_connectedSpace_chabautyTopology_prod
    {A F : Type} [CommGroup A] [TopologicalSpace A] [T1Space A]
    [Group F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] [Nontrivial F]
    (hperfect : commutator F = ⊤) : ¬ @ConnectedSpace _ (chabautyTopology (A × F)) := by
  let X := {H : Subgroup (A × F) // IsClosed (H : Set (A × F))}
  let _ : TopologicalSpace X := chabautyTopology (A × F)
  intro hconn
  let _ : ConnectedSpace X := hconn
  let S : Set X := {H | ∀ f : F, (1, f) ∈ H.1}
  have hiff (H : X) : H ∈ S ↔ ∀ f : F, ∃ g ∈ H.1, g.2 = f := by
    refine ⟨fun h f ↦ ⟨(1, f), h f, rfl⟩, fun h f ↦ ?_⟩
    let π := MonoidHom.snd A F
    have hπ : H.1.map π = ⊤ := eq_top_iff.mpr (fun x _ ↦ h x)
    have hmap : (⁅H.1, H.1⁆ : Subgroup (A × F)).map π = ⊤ := by
      rw [Subgroup.map_commutator, hπ, ← commutator_def, hperfect]
    have hf : f ∈ (⁅H.1, H.1⁆ : Subgroup (A × F)).map π := hmap.symm ▸ Subgroup.mem_top f
    obtain ⟨g, hg, hgf⟩ := Subgroup.mem_map.mp hf
    have hm : g.1 ∈ (⁅H.1, H.1⁆ : Subgroup (A × F)).map (MonoidHom.fst A F) :=
      ⟨g, hg, rfl⟩
    rw [Subgroup.map_commutator] at hm
    have hc : g.1 ∈ commutator A := Subgroup.commutator_mono le_top le_top hm
    rw [commutator_eq_bot, Subgroup.mem_bot] at hc
    have hg' : g = (1, f) := Prod.ext hc hgf
    exact hg' ▸ H.1.commutator_le_self hg
  have hOpen : IsOpen S := by
    let U (f : F) : Set (A × F) := Prod.snd ⁻¹' {f}
    have hS : S = ⋂ f : F, {H : X | ((H.1 : Set (A × F)) ∩ U f).Nonempty} := by
      ext H
      rw [hiff, Set.mem_iInter]
      simp only [Set.mem_ofPred_eq, Set.Nonempty, Set.mem_inter_iff, U, Set.mem_preimage,
        Set.mem_singleton_iff, SetLike.mem_coe]
    rw [hS]
    refine isOpen_iInter_of_finite fun f ↦ TopologicalSpace.isOpen_generateFrom_of_mem ?_
    exact Or.inr ⟨U f, (isOpen_discrete _).preimage continuous_snd, rfl⟩
  have hClosed : IsClosed S := by
    have hS : S = ⋂ f : F, {H : X | (1, f) ∈ H.1} := by
      ext H
      simp [S]
    rw [hS]
    refine isClosed_iInter fun f ↦ isOpen_compl_iff.mp ?_
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    refine Or.inl ⟨{(1, f)}, isCompact_singleton, ?_⟩
    ext H
    change (1, f) ∉ H.1 ↔ Disjoint (H.1 : Set (A × F)) {(1, f)}
    exact Set.disjoint_singleton_right.symm
  have htop : (⟨⊤, isClosed_univ⟩ : X) ∈ S := fun _ ↦ Subgroup.mem_top _
  have hS := IsClopen.eq_univ ⟨hClosed, hOpen⟩ ⟨_, htop⟩
  let bot : X := ⟨⊥, by simpa only [Subgroup.coe_bot] using isClosed_singleton⟩
  have hbot : bot ∈ S := hS.symm ▸ Set.mem_univ bot
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  exact hf (congrArg Prod.snd (Subgroup.mem_bot.mp (hbot f)))

/--
Resolved false: the Kourovka Archive answers 8.61 "No, not always", citing Tsybenko (1983): the
group of matrices `[[1, z₁, r], [0, 1, z₂], [0, 0, 1]]`, `z₁, z₂ ∈ ℤ`, `r ∈ ℝ`, is locally compact
and contains a central subgroup topologically isomorphic to `ℝ`, but its space of closed subgroups
is not connected. For a nontrivial locally compact abelian group, the Chabauty space is connected
exactly when the group contains such a subgroup. The trivial group has a singleton Chabauty
space but contains no copy of `ℝ` (Cornulier, Theorem 1.3 and the discussion before Theorem 1.5).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.61 (I. V.
Protasov); resolution: Yu. V. Tsybenko, Abstracts of the 17th All-Union Algebraic Conference, Part
1, Minsk, 1983, 213 (Russian), Kourovka Archive, Problem 8.61: No, not always; the group H of
matrices [[1, z₁, r], [0, 1, z₂], [0, 0, 1]] with z₁, z₂ ∈ ℤ and r ∈ ℝ is locally compact and
contains a central subgroup topologically isomorphic to ℝ, but L(H) is not connected,
https://arxiv.org/abs/1401.0300v49.
-/
theorem chabautySpaceConnectedOfRealSubgroup_refuted :
    ¬ chabautySpaceConnectedOfRealSubgroup := by
  intro h
  let _ : TopologicalSpace (alternatingGroup (Fin 5)) := ⊥
  let _ : DiscreteTopology (alternatingGroup (Fin 5)) := ⟨rfl⟩
  let φ := MonoidHom.inl (Multiplicative ℝ) (alternatingGroup (Fin 5))
  have hφ : Topology.IsEmbedding φ := isEmbedding_prodMkLeft (1 : alternatingGroup (Fin 5))
  exact not_connectedSpace_chabautyTopology_prod
    (commutator_alternatingGroup_eq_top (by simp)) (h _ ⟨φ, hφ⟩)

end MathlibExt.Topology.ChabautySpaceConnectedRealSubgroupKourovka8Problem61Wanted
