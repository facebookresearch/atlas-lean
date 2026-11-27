/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Regular

/-!
# Total disconnectedness of a closed-subgroup coset quotient

For a compact totally disconnected topological group `G` and any closed subgroup `H`, the
left-coset quotient `G/H` is totally disconnected.

The subgroup need not be normal. Nested subgroup inclusions induce continuous maps of their
coset quotients; these are maps of topological spaces, not quotient-group homomorphisms in
general.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Pointwise

open Set Topology

namespace QuotientGroup

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Continuous projection between nested left-coset quotients.** Let `G` be a group with a
topology and `H≤P` subgroups. The map `G/H → G/P` sends the coset of `g` to its coset
modulo `P` and is continuous. Closedness or normality of the subgroups is not required. -/
private def cosetProjection {H P : Subgroup G} (h : H ≤ P) :
    C(G ⧸ H, G ⧸ P) :=
  ⟨Quotient.map' id fun _ _ hab =>
      QuotientGroup.leftRel_apply.mpr
        (h (QuotientGroup.leftRel_apply.mp hab)),
    continuous_id.quotient_map' fun _ _ hab =>
      QuotientGroup.leftRel_apply.mpr
        (h (QuotientGroup.leftRel_apply.mp hab))⟩

/-- **Closed-subgroup left-coset quotient is totally disconnected.** Let `G` be a compact
totally disconnected topological group. for every closed subgroup `H≤G`, `G/H` with its
quotient topology is totally disconnected, without normality of `H`. -/
theorem totallyDisconnectedSpace_of_isClosed
    (H : Subgroup G) [IsClosed (H : Set G)] :
    TotallyDisconnectedSpace (G ⧸ H) := by
  have hsep : TotallySeparatedSpace (G ⧸ H) :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun q r hqr => by
      revert hqr
      refine Quotient.inductionOn₂ q r ?_
      intro g h hqr
      have hd : g⁻¹ * h ∉ H := by
        intro hd
        exact hqr (Quotient.sound'
          (QuotientGroup.leftRel_apply.mpr hd))
      let U : Set G := ((g⁻¹ * h) • (H : Set G))ᶜ
      have hUopen : IsOpen U := by
        exact ((Homeomorph.mulLeft (g⁻¹ * h)).isClosedMap _
          (show IsClosed (H : Set G) from inferInstance)).isOpen_compl
      have h1U : (1 : G) ∈ U := by
        refine Set.mem_compl ?_
        rintro ⟨n, hn, hdn⟩
        have : g⁻¹ * h = n⁻¹ := by
          simpa [eq_comm] using (eq_inv_of_mul_eq_one_left hdn)
        exact hd (this ▸ inv_mem_iff.mpr hn)
      obtain ⟨M, hMU⟩ :=
        ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
          hUopen h1U
      let P : Subgroup G := M.toSubgroup ⊔ H
      have hPopen : IsOpen (P : Set G) :=
        Subgroup.isOpen_mono le_sup_left M.isOpen
      have hdP : g⁻¹ * h ∉ P := by
        intro hmem
        rcases Subgroup.mem_sup_of_normal_left.mp hmem with
          ⟨m, hm, n, hn, hmn⟩
        rw [← eq_mul_inv_iff_mul_eq] at hmn
        exact hMU (hmn ▸ hm)
          (mem_leftCoset (g⁻¹ * h) (inv_mem_iff.mpr hn))
      let f : C(G ⧸ H, G ⧸ P) := cosetProjection le_sup_right
      let _ : DiscreteTopology (G ⧸ P) :=
        QuotientGroup.discreteTopology hPopen
      let C : Set (G ⧸ H) := f ⁻¹' {f (QuotientGroup.mk g)}
      refine ⟨C, ?_, ?_, ?_⟩
      · exact ⟨isClosed_singleton.preimage f.continuous,
          (isOpen_discrete {f (QuotientGroup.mk g)}).preimage f.continuous⟩
      · simp [C]
      · change f (QuotientGroup.mk h) ≠ f (QuotientGroup.mk g)
        intro heq
        apply hdP
        have hmem : h⁻¹ * g ∈ P := QuotientGroup.eq.mp heq
        simpa [mul_inv_rev] using P.inv_mem hmem
  let _ : TotallySeparatedSpace (G ⧸ H) := hsep
  infer_instance

end QuotientGroup

end
