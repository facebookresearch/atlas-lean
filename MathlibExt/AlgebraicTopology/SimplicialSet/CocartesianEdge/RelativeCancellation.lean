/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.CancellationHorn

/-!
# Cancellation over the specified right-unit triangle

The full base image of the given triangle is a right unit. Its base three-simplex
is the double first degeneracy of the original base edge. Cocartesian lifting
of that prescribed simplex proves cancellation even when the base edge is not
an equivalence. No inner-fibration or quasicategory hypothesis is required.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- The cancellation horn lies over the original double-degenerate base simplex. -/
theorem cancellationHorn_base {X B : SSet.{u}} (p : X ⟶ B)
    {x y : X _⦋0⦌} {e : Edge x y} {h : Edge y y} (H : Edge.CompStruct e h e)
    (hH : p.app (op ⦋2⦌) H.simplex = B.σ 1 (e.map p).edge) :
    cancellationHorn H ≫ p = Λ[3, (0 : Fin 4)].ι ≫
      yonedaEquiv.symm (B.σ 1 (B.σ 1 (e.map p).edge)) := by
  apply horn.hom_ext'
  intro j hj
  have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
  rw [← Category.assoc, cancellationHorn_face, horn.ι_ι_assoc]
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hcases : j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases hcases with hj1 | hj2 | hj3
  · have hj1' : j = 1 := Fin.ext hj1
    subst j
    simp only [cancellationFaces, show (1 : Fin 4) ≠ 3 by decide, ite_false,
      Equiv.apply_symm_apply, Edge.CompStruct.compId_simplex, σ_naturality_apply]
    have hd := δ_comp_σ_self_apply (S := B) (1 : Fin 3) (B.σ 1 (e.map p).edge)
    exact hd.symm
  · have hj2' : j = 2 := Fin.ext hj2
    subst j
    simp only [cancellationFaces, show (2 : Fin 4) ≠ 3 by decide, ite_false,
      Equiv.apply_symm_apply, Edge.CompStruct.compId_simplex, σ_naturality_apply]
    have hd := δ_comp_σ_succ_apply (S := B) (1 : Fin 3) (B.σ 1 (e.map p).edge)
    exact hd.symm
  · have hj3' : j = 3 := Fin.ext hj3
    subst j
    simp only [cancellationFaces, ite_true, Equiv.apply_symm_apply]
    have hd := δ_comp_σ_of_gt'_apply (S := B) (i := (3 : Fin 4))
      (j := (1 : Fin 3)) (by decide) (B.σ 1 (e.map p).edge)
    change B.δ 3 (B.σ 1 (B.σ 1 (e.map p).edge)) =
      B.σ 1 (B.δ 2 (B.σ 1 (e.map p).edge)) at hd
    have hd' := δ_comp_σ_succ_apply (S := B) (1 : Fin 2) (e.map p).edge
    rw [hd]
    exact hH.trans (congrArg (B.σ (1 : Fin 2)) hd').symm

/-- Relative cancellation retains the whole right-unit base triangle, with no base-edge equivalence. -/
theorem toHoHom_eq_id_of_compStruct_over_rightUnit {X B : SSet.{u}} (p : X ⟶ B)
    {x y : X _⦋0⦌} (e : Edge x y)
    (he : IsPCocartesian p (yonedaEquiv.symm e.edge))
    (h : Edge y y) (H : Edge.CompStruct e h e)
    (hH : p.app (op ⦋2⦌) H.simplex = B.σ 1 (e.map p).edge) :
    h.toHoHom = 𝟙 (HomotopyCategory.mk y : hoFunctor.obj X) := by
  have he' : IsPCocartesian p (yonedaEquiv.symm (leftHornEdge (cancellationHorn H)).edge) :=
    (congrArg yonedaEquiv.symm (cancellationHorn_edge H)).symm ▸ he
  obtain ⟨T, hT, -⟩ := exists_fill_leftHorn_of_isPCocartesian
    (cancellationHorn H) (yonedaEquiv.symm (B.σ 1 (B.σ 1 (e.map p).edge)))
    (cancellationHorn_base p H hH) he'
  exact toHoHom_eq_id_of_cancellationHorn_fill H T hT

end SSet.CocartesianEdge
