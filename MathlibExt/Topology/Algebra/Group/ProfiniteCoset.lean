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
# Total disconnectedness of closed coset quotients

If `H` is a closed subgroup of a compact totally disconnected topological
group `G`, then the left-coset quotient `G/H` is totally disconnected.  No
normality hypothesis is needed: the proof separates two cosets by mapping
to the discrete coset quotient by an auxiliary open subgroup.

The result is theorem-valued and installs no global instance.  It is a
topological precursor for continuous-section theorems; this file constructs
no section and makes no Shapiro, Hochschild--Serre, residue, or norm-residue
claim.

## Main declaration

* `QuotientGroup.totallyDisconnectedSpace_of_isClosed`

## Reference

The motivating closed-coset section theorem is J.-P. Serre,
*Galois Cohomology*, Chapter I, Section 1, Proposition 1.
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

/-- The continuous map from left `H`-cosets to left `P`-cosets induced by
an inclusion `H ≤ P`. -/
private def cosetProjection {H P : Subgroup G} (h : H ≤ P) :
    C(G ⧸ H, G ⧸ P) :=
  ⟨Quotient.map' id fun _ _ hab =>
      QuotientGroup.leftRel_apply.mpr
        (h (QuotientGroup.leftRel_apply.mp hab)),
    continuous_id.quotient_map' fun _ _ hab =>
      QuotientGroup.leftRel_apply.mpr
        (h (QuotientGroup.leftRel_apply.mp hab))⟩

/-- A left-coset quotient of a compact totally disconnected topological
group by any closed subgroup is totally disconnected.  This theorem does
not install a global instance and does not require the subgroup to be
normal. -/
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
