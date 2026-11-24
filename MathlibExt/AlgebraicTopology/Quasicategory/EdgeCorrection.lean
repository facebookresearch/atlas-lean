/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryTwo
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
# Strict correction of an edge through an inner fibration

An edge of the source can be corrected within its represented homotopy
class to have any prescribed actual image edge representing the same
morphism downstairs. Both endpoints and the complete base two-simplex
are retained. The codomain is a quasicategory; the original edge need
not be an equivalence.

This moves the existing inner-horn proof from CobaseChangeMono into a
neutral module. Its three private support lemmas and public statement
and proof are retained verbatim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet

private lemma cobaseMono_δ_one_comp_yonedaEdge {E : SSet.{u}}
    {x₀ x₁ : E _⦋0⦌} (e : Edge x₀ x₁) :
    stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e.edge =
      yonedaEquiv.symm x₀ := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq]

private lemma cobaseMono_δ_zero_comp_yonedaEdge {E : SSet.{u}}
    {x₀ x₁ : E _⦋0⦌} (e : Edge x₀ x₁) :
    stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge =
      yonedaEquiv.symm x₁ := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, e.tgt_eq]

private lemma cobaseMono_horn_two_one_le_boundary :
    Λ[2, (1 : Fin 3)] ≤ boundary 2 := by
  rw [horn_eq_iSup]
  apply iSup_le
  intro j
  exact face_singleton_compl_le_boundary (j : Fin 3)

/-- **Edge correction through an inner fibration.** Let `p : E ⟶ B`
be an inner fibration with `B` a quasicategory, let `u` be an edge
of `E`, and let `w` be an edge of `B` between the images of the
endpoints of `u` representing the same morphism of `hB` as the image
of `u`. Then there is an edge `u'` of `E` with the same endpoints
as `u`, representing the same morphism of `hE` as `u`, whose strict
image under `p` is `w`. The lift is against the inner horn
`Λ[2, 1]`, with horn assembled from `u` and an identity edge
through `SSet.boundary.twoDesc`. -/
theorem exists_edge_correction_of_innerFibration {E B : SSet.{u}}
    (p : E ⟶ B) (hp : InnerFibration p) [Quasicategory B]
    {x₀ x₁ : E _⦋0⦌} (u : Edge x₀ x₁)
    (w : Edge (p.app _ x₀) (p.app _ x₁))
    (h : HomotopyCategory.homMk w = HomotopyCategory.homMk (u.map p)) :
    ∃ u' : Edge x₀ x₁, HomotopyCategory.homMk u' = HomotopyCategory.homMk u ∧
      (u'.map p).edge = w.edge := by
  have hcomp : HomotopyCategory.homMk (u.map p) ≫ HomotopyCategory.homMk (Edge.id (p.app _ x₁)) =
      HomotopyCategory.homMk w := by
    rw [HomotopyCategory.homMk_id, Category.comp_id, h]
  obtain ⟨T⟩ := Edge.nonempty_compStruct_of_homMk_comp_eq hcomp
  -- The horn `Λ[2, 1] ⟶ E` with `2`-face `u` and `0`-face the identity.
  have h₀ : stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm u.edge =
      stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm u.edge := rfl
  have h₁ : stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm u.edge =
      stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm (Edge.id x₁).edge := by
    rw [cobaseMono_δ_zero_comp_yonedaEdge,
      cobaseMono_δ_one_comp_yonedaEdge]
  have h₂ : stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm u.edge =
      stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm (Edge.id x₁).edge := by
    rw [cobaseMono_δ_zero_comp_yonedaEdge,
      cobaseMono_δ_zero_comp_yonedaEdge]
  set θ : (Λ[2, (1 : Fin 3)] : SSet.{u}) ⟶ E :=
    Subcomplex.homOfLE cobaseMono_horn_two_one_le_boundary ≫
      boundary.twoDesc (yonedaEquiv.symm u.edge) (yonedaEquiv.symm u.edge)
        (yonedaEquiv.symm (Edge.id x₁).edge) h₀ h₁ h₂ with hθ
  have hface : ∀ (j : Fin 3) (hj : j ≠ (1 : Fin 3)),
      horn.ι (1 : Fin 3) j hj ≫ θ = boundary.ι j ≫
        boundary.twoDesc (yonedaEquiv.symm u.edge)
          (yonedaEquiv.symm u.edge) (yonedaEquiv.symm (Edge.id x₁).edge)
          h₀ h₁ h₂ := by
    intro j hj
    rw [hθ, ← Category.assoc]
    congr 1
  have hw : θ ≫ p = Λ[2, (1 : Fin 3)].ι ≫ yonedaEquiv.symm T.simplex := by
    apply horn.hom_ext
    intro j hj
    rw [← horn.yonedaEquiv_ι, ← yonedaEquiv_comp, ← yonedaEquiv_comp]
    congr 1
    have hj02 : j = 0 ∨ j = 2 := by
      fin_cases j
      · exact Or.inl rfl
      · exact absurd rfl hj
      · exact Or.inr rfl
    rcases hj02 with rfl | rfl
    · rw [← Category.assoc, hface, boundary.twoDesc_ι_zero,
        ← Category.assoc, horn.ι_ι]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp]
      simp only [Equiv.apply_symm_apply]
      rw [T.d₀]
      have hid : p.app _ (Edge.id x₁).edge = (Edge.id (p.app _ x₁)).edge := by
        rw [← Edge.map_id, Edge.map_edge]
      exact hid
    · rw [← Category.assoc, hface, boundary.twoDesc_ι_two,
        ← Category.assoc, horn.ι_ι]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp]
      simp only [Equiv.apply_symm_apply]
      rw [T.d₂, Edge.map_edge]
  let sq : CommSq θ Λ[2, (1 : Fin 3)].ι p (yonedaEquiv.symm T.simplex) :=
    CommSq.mk hw
  have hlp : HasLiftingProperty Λ[2, (1 : Fin 3)].ι p :=
    hp.mem _ (horn_ι_mem_innerHornInclusions (by decide) (by decide))
  obtain ⟨⟨l, hl_left, hl_right⟩⟩ := (hlp.sq_hasLift sq).exists_lift
  have hd2 : E.δ 2 (yonedaEquiv l) = u.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have e1 : stdSimplex.δ (2 : Fin 3) ≫ l = yonedaEquiv.symm u.edge := by
      rw [← horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide), Category.assoc,
        hl_left, hface, boundary.twoDesc_ι_two]
    rw [e1, Equiv.apply_symm_apply]
  have hd0 : E.δ 0 (yonedaEquiv l) = (Edge.id x₁).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have e1 : stdSimplex.δ (0 : Fin 3) ≫ l =
        yonedaEquiv.symm (Edge.id x₁).edge := by
      rw [← horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide), Category.assoc,
        hl_left, hface, boundary.twoDesc_ι_zero]
    rw [e1, Equiv.apply_symm_apply]
  have happ : p.app _ (yonedaEquiv l) = T.simplex := by
    rw [← yonedaEquiv_comp, hl_right, Equiv.apply_symm_apply]
  have hsrc : E.δ 1 (E.δ 1 (yonedaEquiv l)) = x₀ := by
    have key : E.δ (1 : Fin 2) (E.δ (1 : Fin 3) (yonedaEquiv l)) =
        E.δ (1 : Fin 2) (E.δ (2 : Fin 3) (yonedaEquiv l)) :=
      δ_comp_δ_self_apply _
    rw [key, hd2, u.src_eq]
  have htgt : E.δ 0 (E.δ 1 (yonedaEquiv l)) = x₁ := by
    have key : E.δ (0 : Fin 2) (E.δ (1 : Fin 3) (yonedaEquiv l)) =
        E.δ (0 : Fin 2) (E.δ (0 : Fin 3) (yonedaEquiv l)) :=
      δ_comp_δ_apply le_rfl _
    rw [key, hd0]
    exact (Edge.id x₁).tgt_eq
  let u' : Edge x₀ x₁ := Edge.mk (E.δ 1 (yonedaEquiv l)) hsrc htgt
  have hCS : Edge.CompStruct u (Edge.id x₁) u' :=
    Edge.CompStruct.mk (yonedaEquiv l) hd2 hd0 rfl
  refine ⟨u', ?_, ?_⟩
  · have hc := HomotopyCategory.homMk_comp_homMk hCS
    rw [HomotopyCategory.homMk_id, Category.comp_id] at hc
    exact hc.symm
  · rw [Edge.map_edge]
    calc p.app _ (E.δ 1 (yonedaEquiv l))
        = B.δ 1 (p.app _ (yonedaEquiv l)) :=
          δ_naturality_apply p 1 _
      _ = w.edge := by rw [happ]; exact T.d₁

end SSet

end
