/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LiftComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.RelativeCancellation
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeCompStruct
import MathlibExt.AlgebraicTopology.SimplicialSet.RelativeUnits

/-!
# Actual vertical equivalences between cocartesian lifts

The two original source-lift comparison triangles project to right units.
Relative inner composition and association retain the whole prescribed
base double unit. Cocartesian cancellation proves both original inverse
relations in Ho, retaining the comparison edge and its original identity image.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- The original comparisons over right units compose to the same identity in Ho. -/
theorem comparison_comp_toHoHom_eq_id {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    {x y y' : X _⦋0⦌} (e : Edge x y) (he : IsPCocartesian p (yonedaEquiv.symm e.edge))
    (f : Edge x y') (h : Edge y y') (g : Edge y' y)
    (Hh : Edge.CompStruct e h f) (Hg : Edge.CompStruct f g e)
    (hHh : p.app (op ⦋2⦌) Hh.simplex = B.σ 1 (e.map p).edge)
    (hHg : p.app (op ⦋2⦌) Hg.simplex = B.σ 1 (f.map p).edge)
    (hmap : (e.map p).edge = (f.map p).edge) :
    h.toHoHom ≫ g.toHoHom = 𝟙 (HomotopyCategory.mk y : hoFunctor.obj X) := by
  have hpy : p.app (op ⦋0⦌) y = p.app (op ⦋0⦌) y' :=
    (e.map p).tgt_eq.symm.trans ((congrArg (B.δ (0 : Fin 2)) hmap).trans (f.map p).tgt_eq)
  have hh : (h.map p).edge = (Edge.id (p.app _ y)).edge := by
    rw [Edge.map_edge, ← Hh.d₀, SSet.δ_naturality_apply, hHh]
    exact (Edge.CompStruct.compId (e.map p)).d₀
  have hg : (g.map p).edge = (Edge.id (p.app _ y')).edge := by
    rw [Edge.map_edge, ← Hg.d₀, SSet.δ_naturality_apply, hHg]
    exact (Edge.CompStruct.compId (f.map p)).d₀
  have hg' : (g.map p).edge = (Edge.id (p.app _ y)).edge :=
    hg.trans (congrArg (fun a => (Edge.id a).edge) hpy.symm)
  let S : Edge.CompStruct (h.map p) (g.map p) (Edge.id (p.app _ y)) :=
    (Edge.CompStruct.idCompId (p.app _ y)).ofEq hh.symm hg'.symm rfl
  obtain ⟨k, K, hK, -⟩ := Edge.CompStruct.exists_over p h g (Edge.id (p.app _ y)) S
  let b := (e.map p).rightUnitThree
  have hb₀ : p.app (op ⦋2⦌) K.simplex = B.δ (0 : Fin 4) b :=
    hK.trans (e.map p).rightUnitThree_δ_zero.symm
  have hb₁ : p.app (op ⦋2⦌) Hg.simplex = B.δ (1 : Fin 4) b :=
    hHg.trans ((congrArg (B.σ (1 : Fin 2)) hmap.symm).trans
      (e.map p).rightUnitThree_δ_one.symm)
  have hb₃ : p.app (op ⦋2⦌) Hh.simplex = B.δ (3 : Fin 4) b :=
    hHh.trans (e.map p).rightUnitThree_δ_three.symm
  obtain ⟨L, hL⟩ := Edge.CompStruct.exists_assoc_right_over p Hh K Hg b hb₀ hb₁ hb₃
  have hunit : p.app (op ⦋2⦌) L.simplex = B.σ 1 (e.map p).edge :=
    hL.trans (e.map p).rightUnitThree_δ_two
  rw [Edge.toHoHom_comp K]
  exact toHoHom_eq_id_of_compStruct_over_rightUnit p e he k L hunit

/-- Two actual cocartesian source lifts admit a vertical equivalence over the original whole base edge. -/
theorem exists_equivalence_comparison {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p]
    {x y y' : X _⦋0⦌} (e : Edge x y) (f : Edge x y')
    (he : IsPCocartesian p (yonedaEquiv.symm e.edge))
    (hf : IsPCocartesian p (yonedaEquiv.symm f.edge))
    (hmap : (f.map p).edge = (e.map p).edge) :
    ∃ (h : Edge y y') (H : Edge.CompStruct e h f), h.IsEquivalence ∧
      p.app (op ⦋2⦌) H.simplex = B.σ 1 (e.map p).edge ∧
      (h.map p).edge = (Edge.id (p.app _ y)).edge := by
  obtain ⟨h, Hh, hHh, hh⟩ := exists_comparison_triangle p e f he hmap
  obtain ⟨g, Hg, hHg, -⟩ := exists_comparison_triangle p f e hf hmap.symm
  have h_hg := comparison_comp_toHoHom_eq_id p e he f h g Hh Hg hHh hHg hmap.symm
  have h_gh := comparison_comp_toHoHom_eq_id p f hf e g h Hg Hh hHg hHh hmap
  have hEq : h.IsEquivalence := by
    change IsIso h.toHoHom
    exact ⟨g.toHoHom, h_hg, h_gh⟩
  exact ⟨h, Hh, hEq, hHh, hh⟩

end SSet.CocartesianEdge
