/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LeftHornFaces
import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv

/-!
# The original inverse triangle lifted through a cocartesian edge

The supplied whole base inverse triangle is retained as the bottom of the
left two-horn. Cocartesian lifting supplies the same first edge and diagonal,
and the original inverse edge has its entire specified base image.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- Lift the supplied first inverse triangle without changing the original critical edge. -/
theorem exists_inverse_triangle {X B : SSet.{u}} (p : X ⟶ B) {x y : X _⦋0⦌}
    (e : Edge x y) (he : IsPCocartesian p (yonedaEquiv.symm e.edge))
    (I : Edge.InvStruct (e.map p)) :
    ∃ (g : Edge y x) (H : Edge.CompStruct e g (Edge.id x)), (g.map p).edge = I.inv.edge := by
  have glue : stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e.edge =
      stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm (Edge.id x).edge :=
    e.δ_one_yonedaEquiv_symm.trans (Edge.id x).δ_one_yonedaEquiv_symm.symm
  obtain ⟨σ₀, h₂, h₁⟩ := horn₂₀.isPushout.exists_desc
    (yonedaEquiv.symm e.edge) (yonedaEquiv.symm (Edge.id x).edge) glue
  let b : (Δ[2] : SSet.{u}) ⟶ B := yonedaEquiv.symm I.homInvId.simplex
  have hb₂ : stdSimplex.δ (2 : Fin 3) ≫ b = yonedaEquiv.symm (e.map p).edge :=
    I.homInvId.δ_two_yonedaEquiv_symm
  have hb₁ : stdSimplex.δ (1 : Fin 3) ≫ b = yonedaEquiv.symm (Edge.id (p.app _ x)).edge :=
    I.homInvId.δ_one_yonedaEquiv_symm
  have hi₂ : horn₂₀.ι₀₁.{u} ≫ (horn 2 (0 : Fin 3)).ι = stdSimplex.δ (2 : Fin 3) :=
    horn.ι_ι 0 (2 : Fin 3) (by decide)
  have hi₁ : horn₂₀.ι₀₂.{u} ≫ (horn 2 (0 : Fin 3)).ι = stdSimplex.δ (1 : Fin 3) :=
    horn.ι_ι 0 (1 : Fin 3) (by decide)
  have hsq : σ₀ ≫ p = (horn 2 (0 : Fin 3)).ι ≫ b := by
    apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, h₂]
      calc
        _ = yonedaEquiv.symm (e.map p).edge := by rw [yonedaEquiv_symm_comp, ← Edge.map_edge]
        _ = stdSimplex.δ (2 : Fin 3) ≫ b := hb₂.symm
        _ = _ := by simpa only [Category.assoc] using congrArg (fun f => f ≫ b) hi₂.symm
    · rw [← Category.assoc, h₁]
      calc
        _ = yonedaEquiv.symm (Edge.id (p.app _ x)).edge := by
          rw [yonedaEquiv_symm_comp, ← Edge.map_edge, Edge.map_id]
        _ = stdSimplex.δ (1 : Fin 3) ≫ b := hb₁.symm
        _ = _ := by simpa only [Category.assoc] using congrArg (fun f => f ≫ b) hi₁.symm
  have hc : (leftHornEdge σ₀).edge = e.edge := by
    rw [leftHornEdge_two, h₂, Equiv.apply_symm_apply]
  have hp₀ : IsPCocartesian p (yonedaEquiv.symm (leftHornEdge σ₀).edge) :=
    (congrArg yonedaEquiv.symm hc).symm ▸ he
  obtain ⟨T, hT, hpT⟩ := exists_fill_leftHorn_of_isPCocartesian σ₀ b hsq hp₀
  have hT₂ : stdSimplex.δ (2 : Fin 3) ≫ T = yonedaEquiv.symm e.edge := by
    rw [← horn.ι_ι_assoc (0 : Fin 3) (2 : Fin 3) (by decide), hT]
    exact h₂
  have hT₁ : stdSimplex.δ (1 : Fin 3) ≫ T = yonedaEquiv.symm (Edge.id x).edge := by
    rw [← horn.ι_ι_assoc (0 : Fin 3) (1 : Fin 3) (by decide), hT]
    exact h₁
  have hd₂ : X.δ (2 : Fin 3) (yonedaEquiv T) = e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hT₂, Equiv.apply_symm_apply]
  have hd₁ : X.δ (1 : Fin 3) (yonedaEquiv T) = (Edge.id x).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hT₁, Equiv.apply_symm_apply]
  obtain ⟨a₀, a₁, a₂, e', g, k, H, hH⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv T)
  have he' : e'.edge = e.edge := H.d₂.symm.trans ((congrArg (X.δ (2 : Fin 3)) hH).trans hd₂)
  have hk : k.edge = (Edge.id x).edge := H.d₁.symm.trans ((congrArg (X.δ (1 : Fin 3)) hH).trans hd₁)
  have ha₀ : a₀ = x := by rw [← e'.src_eq, he', e.src_eq]
  have ha₁ : a₁ = y := by rw [← e'.tgt_eq, he', e.tgt_eq]
  have ha₂ : a₂ = x := by rw [← k.tgt_eq, hk, (Edge.id x).tgt_eq]
  subst a₀
  subst a₁
  subst a₂
  have ee : e' = e := Edge.ext he'
  have kk : k = Edge.id x := Edge.ext hk
  subst e'
  subst k
  refine ⟨g, H, ?_⟩
  have hb : p.app _ (yonedaEquiv T) = I.homInvId.simplex := by
    rw [← yonedaEquiv_comp, hpT]
    exact Equiv.apply_symm_apply yonedaEquiv _
  rw [Edge.map_edge, ← H.d₀, hH, SSet.δ_naturality_apply, hb]
  exact I.homInvId.d₀

end SSet.CocartesianEdge
