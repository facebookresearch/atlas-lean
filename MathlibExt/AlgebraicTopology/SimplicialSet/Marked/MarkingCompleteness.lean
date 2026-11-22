/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointEdgeLifts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CompositionCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalRLP
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CocartesianCriticalRLP
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.LiftUniqueness
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LiftUniqueness

/-!
# Completeness of the supplied intrinsic marking

The actual endpoint cell supplies a marked lift of the same whole base
edge. Native lift comparison gives an equivalence edge and the original
composition triangle. If equivalences and the long edges of such marked
triangles are marked, every Cartesian or cocartesian edge is marked.
The base need not be Kan or a quasicategory for this comparison argument.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Marked composition lifting closes the marking under every supplied original composition triangle. -/
theorem compStruct_long_mem_marking {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    (hc : HasLiftingProperty compositionCell.{u} p)
    {x y z : Y.toSSet _⦋0⦌} {e : Edge x y} {f : Edge y z} {g : Edge x z}
    (H : Edge.CompStruct e f g) (he : e.edge ∈ Y.marking) (hf : f.edge ∈ Y.marking) :
    g.edge ∈ Y.marking := by
  have h := (compositionCell_rlp_iff p).mp hc (yonedaEquiv.symm H.simplex)
  have h₂ : (yonedaEquiv.symm H.simplex).app (op ⦋1⦌)
      (yonedaEquiv (stdSimplex.δ (2 : Fin 3))) = e.edge := by
    rw [← yonedaEquiv_comp, stdSimplex.δ_comp_yonedaEquiv_symm, H.d₂, Equiv.apply_symm_apply]
  have h₀ : (yonedaEquiv.symm H.simplex).app (op ⦋1⦌)
      (yonedaEquiv (stdSimplex.δ (0 : Fin 3))) = f.edge := by
    rw [← yonedaEquiv_comp, stdSimplex.δ_comp_yonedaEquiv_symm, H.d₀, Equiv.apply_symm_apply]
  have h₁ : (yonedaEquiv.symm H.simplex).app (op ⦋1⦌) compositionLongEdge.{u} = g.edge := by
    change (yonedaEquiv.symm H.simplex).app (op ⦋1⦌)
      (yonedaEquiv (stdSimplex.δ (1 : Fin 3))) = g.edge
    rw [← yonedaEquiv_comp, stdSimplex.δ_comp_yonedaEquiv_symm, H.d₁, Equiv.apply_symm_apply]
  exact h₁ ▸ h (h₂.symm ▸ he) (h₀.symm ▸ hf)

/-- Actual marked target lifts and equivalence triangles mark every intrinsic Cartesian edge. -/
theorem cartesian_mem_marking_of_cells {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    [InnerFibration p.hom]
    (he : HasLiftingProperty cartesianEndpointCell.{u} p)
    (hc : ∀ n : ℕ, HasLiftingProperty (cartesianCriticalCell.{u} n) p)
    (ht : HasLiftingProperty compositionCell.{u} p)
    (hm : ∀ (e : Y.toSSet _⦋1⦌), (Edge.mk' e).IsEquivalence → e ∈ Y.marking)
    (e : Y.toSSet _⦋1⦌) (hcart : CartesianEdge.IsPCartesian p.hom (yonedaEquiv.symm e)) :
    e ∈ Y.marking := by
  let a := Edge.mk' e
  obtain ⟨x, f, hf, hmap⟩ := exists_marked_target_lift p he _ _ (a.map p.hom)
  have hfCart : CartesianEdge.IsPCartesian p.hom (yonedaEquiv.symm f.edge) :=
    (cartesianCriticalCell_rlp_iff p).mp hc f.edge hf
  obtain ⟨k, H, hk, _, _⟩ := CartesianEdge.exists_equivalence_comparison p.hom a f
    hcart hfCart hmap.symm
  have hkMark : k.edge ∈ Y.marking := hm _ (hk.of_edge_eq rfl)
  exact compStruct_long_mem_marking p ht H hkMark hf

/-- The reversed native cocartesian comparison marks the given long edge, with all original vertices retained. -/
theorem cocartesian_mem_marking_of_cells {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B)
    [InnerFibration p.hom]
    (he : HasLiftingProperty cocartesianEndpointCell.{u} p)
    (hc : ∀ n : ℕ, HasLiftingProperty (cocartesianCriticalCell.{u} n) p)
    (ht : HasLiftingProperty compositionCell.{u} p)
    (hm : ∀ (e : Y.toSSet _⦋1⦌), (Edge.mk' e).IsEquivalence → e ∈ Y.marking)
    (e : Y.toSSet _⦋1⦌) (hcart : CocartesianEdge.IsPCocartesian p.hom (yonedaEquiv.symm e)) :
    e ∈ Y.marking := by
  let a := Edge.mk' e
  obtain ⟨y, f, hf, hmap⟩ := exists_marked_source_lift p he _ _ (a.map p.hom)
  have hfCart : CocartesianEdge.IsPCocartesian p.hom (yonedaEquiv.symm f.edge) :=
    (cocartesianCriticalCell_rlp_iff p).mp hc f.edge hf
  obtain ⟨k, H, hk, _, _⟩ := CocartesianEdge.exists_equivalence_comparison p.hom f a
    hfCart hcart hmap.symm
  have hkMark : k.edge ∈ Y.marking := hm _ (hk.of_edge_eq rfl)
  exact compStruct_long_mem_marking p ht H hf hkMark

end SSet.Marked
