/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.CancellationHorn

/-!
# Cancellation over the specified left-unit triangle

The full base image of the given triangle is a left unit. Its base three-simplex
is the double zeroth degeneracy of the original base edge. Cartesian lifting
of that prescribed simplex proves cancellation even when the base edge is not
an equivalence. No inner-fibration or quasicategory hypothesis is required.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- The cancellation horn lies over the original double-degenerate base simplex. -/
theorem cancellationHorn_base {X B : SSet.{u}} (p : X ⟶ B)
    {x y : X _⦋0⦌} {e : Edge x y} {h : Edge x x} (H : Edge.CompStruct h e e)
    (hH : p.app (op ⦋2⦌) H.simplex = B.σ 0 (e.map p).edge) :
    cancellationHorn H ≫ p = Λ[3, Fin.last 3].ι ≫
      yonedaEquiv.symm (B.σ 0 (B.σ 0 (e.map p).edge)) := by
  apply horn.hom_ext'
  intro j hj
  have hjv : j.val ≠ 3 := fun h => hj (Fin.ext h)
  rw [← Category.assoc, cancellationHorn_face, horn.ι_ι_assoc]
  apply yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
  rcases hcases with hj0 | hj1 | hj2
  · have hj0' : j = 0 := Fin.ext hj0
    subst j
    simp only [cancellationFaces, ite_true, Equiv.apply_symm_apply]
    have hd := δ_comp_σ_self_apply (S := B) (0 : Fin 3) (B.σ 0 (e.map p).edge)
    change B.δ 0 (B.σ 0 (B.σ 0 (e.map p).edge)) = B.σ 0 (e.map p).edge at hd
    rw [hd]
    exact hH
  · have hj1' : j = 1 := Fin.ext hj1
    subst j
    simp only [cancellationFaces, show (1 : Fin 4) ≠ 0 by decide, ite_false,
      Equiv.apply_symm_apply, Edge.CompStruct.idComp_simplex, σ_naturality_apply]
    have hd := δ_comp_σ_succ_apply (S := B) (0 : Fin 3) (B.σ 0 (e.map p).edge)
    exact hd.symm
  · have hj2' : j = 2 := Fin.ext hj2
    subst j
    simp only [cancellationFaces, show (2 : Fin 4) ≠ 0 by decide, ite_false,
      Equiv.apply_symm_apply, Edge.CompStruct.idComp_simplex, σ_naturality_apply]
    have hd := δ_comp_σ_of_gt'_apply (S := B) (i := (2 : Fin 4))
      (j := (0 : Fin 3)) (by decide) (B.σ 0 (e.map p).edge)
    change B.δ 2 (B.σ 0 (B.σ 0 (e.map p).edge)) =
      B.σ 0 (B.δ 1 (B.σ 0 (e.map p).edge)) at hd
    have hd' := δ_comp_σ_succ_apply (S := B) (0 : Fin 2) (e.map p).edge
    exact (hd.trans (congrArg (B.σ (0 : Fin 2)) hd')).symm

/-- Relative cancellation retains the whole left-unit base triangle, with no base-edge equivalence. -/
theorem toHoHom_eq_id_of_compStruct_over_leftUnit {X B : SSet.{u}} (p : X ⟶ B)
    {x y : X _⦋0⦌} (e : Edge x y)
    (he : IsPCartesian p (yonedaEquiv.symm e.edge))
    (h : Edge x x) (H : Edge.CompStruct h e e)
    (hH : p.app (op ⦋2⦌) H.simplex = B.σ 0 (e.map p).edge) :
    h.toHoHom = 𝟙 (HomotopyCategory.mk x : hoFunctor.obj X) := by
  have he' : IsPCartesian p (yonedaEquiv.symm (rightHornEdge (cancellationHorn H)).edge) :=
    (congrArg yonedaEquiv.symm (cancellationHorn_edge H)).symm ▸ he
  obtain ⟨T, hT, -⟩ := exists_fill_rightHorn_of_isPCartesian
    (cancellationHorn H) (yonedaEquiv.symm (B.σ 0 (B.σ 0 (e.map p).edge)))
    (cancellationHorn_base p H hH) he'
  exact toHoHom_eq_id_of_cancellationHorn_fill H T hT

end SSet.CartesianEdge
