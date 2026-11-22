/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.LiftComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RelativeCancellation
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeCompStruct
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeUnits

/-!
# Actual vertical equivalences between Cartesian lifts

The two original comparison triangles project to literal left units.
Relative inner composition and association retain the prescribed double-unit
base simplices. Relative Cartesian cancellation proves both original Ho
inverse equations. The comparison edge is therefore an actual equivalence,
with its entire original identity image and triangle retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- The actual comparisons over left units compose to the original identity in Ho. -/
theorem comparison_comp_toHoHom_eq_id {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    {x x' y : X _⦋0⦌} (e : Edge x y) (he : IsPCartesian p (yonedaEquiv.symm e.edge))
    (f : Edge x' y) (h : Edge x x') (g : Edge x' x)
    (Hh : Edge.CompStruct h f e) (Hg : Edge.CompStruct g e f)
    (hHh : p.app (op ⦋2⦌) Hh.simplex = B.σ 0 (f.map p).edge)
    (hHg : p.app (op ⦋2⦌) Hg.simplex = B.σ 0 (e.map p).edge)
    (hmap : (e.map p).edge = (f.map p).edge) :
    h.toHoHom ≫ g.toHoHom = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) := by
  have hpx : p.app (op ⦋0⦌) x = p.app (op ⦋0⦌) x' :=
    (e.map p).src_eq.symm.trans ((congrArg (B.δ (1 : Fin 2)) hmap).trans (f.map p).src_eq)
  have hh : (h.map p).edge = (Edge.id (p.app _ x')).edge := by
    rw [Edge.map_edge, ← Hh.d₂, SSet.δ_naturality_apply, hHh]
    exact (Edge.CompStruct.idComp (f.map p)).d₂
  have hg : (g.map p).edge = (Edge.id (p.app _ x)).edge := by
    rw [Edge.map_edge, ← Hg.d₂, SSet.δ_naturality_apply, hHg]
    exact (Edge.CompStruct.idComp (e.map p)).d₂
  have hh' : (h.map p).edge = (Edge.id (p.app _ x)).edge :=
    hh.trans (congrArg (fun a => (Edge.id a).edge) hpx.symm)
  let S : Edge.CompStruct (h.map p) (g.map p) (Edge.id (p.app _ x)) :=
    (Edge.CompStruct.idCompId (p.app _ x)).ofEq hh'.symm hg.symm rfl
  obtain ⟨k, K, hK, -⟩ := Edge.CompStruct.exists_over p h g (Edge.id (p.app _ x)) S
  let b := (e.map p).leftUnitThree
  have hb₀ : p.app (op ⦋2⦌) Hg.simplex = B.δ (0 : Fin 4) b :=
    hHg.trans (e.map p).leftUnitThree_δ_zero.symm
  have hb₂ : p.app (op ⦋2⦌) Hh.simplex = B.δ (2 : Fin 4) b :=
    hHh.trans ((congrArg (B.σ (0 : Fin 2)) hmap.symm).trans
      (e.map p).leftUnitThree_δ_two.symm)
  have hb₃ : p.app (op ⦋2⦌) K.simplex = B.δ (3 : Fin 4) b :=
    hK.trans (e.map p).leftUnitThree_δ_three.symm
  obtain ⟨L, hL⟩ := Edge.CompStruct.exists_assoc_left_over p K Hg Hh b hb₀ hb₂ hb₃
  have hunit : p.app (op ⦋2⦌) L.simplex = B.σ 0 (e.map p).edge :=
    hL.trans (e.map p).leftUnitThree_δ_one
  rw [Edge.toHoHom_comp K]
  exact toHoHom_eq_id_of_compStruct_over_leftUnit p e he k L hunit

/-- Two actual Cartesian target lifts of the same whole base edge admit an original vertical equivalence. -/
theorem exists_equivalence_comparison {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    {x x' y : X _⦋0⦌} (e : Edge x y) (f : Edge x' y)
    (he : IsPCartesian p (yonedaEquiv.symm e.edge))
    (hf : IsPCartesian p (yonedaEquiv.symm f.edge))
    (hmap : (e.map p).edge = (f.map p).edge) :
    ∃ (h : Edge x x') (H : Edge.CompStruct h f e), h.IsEquivalence ∧
      p.app (op ⦋2⦌) H.simplex = B.σ 0 (f.map p).edge ∧
      (h.map p).edge = (Edge.id (p.app _ x')).edge := by
  obtain ⟨h, Hh, hHh, hh⟩ := exists_comparison_triangle p e f hf hmap
  obtain ⟨g, Hg, hHg, -⟩ := exists_comparison_triangle p f e he hmap.symm
  have h_hg := comparison_comp_toHoHom_eq_id p e he f h g Hh Hg hHh hHg hmap
  have h_gh := comparison_comp_toHoHom_eq_id p f hf e g h Hg Hh hHg hHh hmap.symm
  have hEq : h.IsEquivalence := by
    change IsIso h.toHoHom
    exact ⟨g.toHoHom, h_hg, h_gh⟩
  exact ⟨h, Hh, hEq, hHh, hh⟩

end SSet.CartesianEdge
