/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornFaces
import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv

/-!
# Original inverse-edge lifts through a Cartesian critical edge

Use the supplied inverse triangle in the base as the entire bottom
simplex of a right outer-horn square. The actual Cartesian critical edge
provides the filler. Its original triangle gives an inverse on one side
and retains the whole image of the lifted inverse edge.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- Lift the supplied base inverse triangle with its actual critical Cartesian edge. -/
theorem exists_inverse_triangle {X B : SSet.{u}} (p : X ⟶ B) {x y : X _⦋0⦌}
    (e : Edge x y) (he : IsPCartesian p (yonedaEquiv.symm e.edge))
    (I : Edge.InvStruct (e.map p)) :
    ∃ (g : Edge y x) (H : Edge.CompStruct g e (Edge.id y)), (g.map p).edge = I.inv.edge := by
  have glue : stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm (Edge.id y).edge =
      stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge :=
    (Edge.id y).δ_zero_yonedaEquiv_symm.trans e.δ_zero_yonedaEquiv_symm.symm
  obtain ⟨σ₀, h₁, h₀⟩ := horn₂₂.isPushout.exists_desc
    (yonedaEquiv.symm (Edge.id y).edge) (yonedaEquiv.symm e.edge) glue
  let b : (Δ[2] : SSet.{u}) ⟶ B := yonedaEquiv.symm I.invHomId.simplex
  have hb₀ : stdSimplex.δ (0 : Fin 3) ≫ b = yonedaEquiv.symm (e.map p).edge :=
    I.invHomId.δ_zero_yonedaEquiv_symm
  have hb₁ : stdSimplex.δ (1 : Fin 3) ≫ b = yonedaEquiv.symm (Edge.id (p.app _ y)).edge :=
    I.invHomId.δ_one_yonedaEquiv_symm
  have hi₁ : horn₂₂.ι₀₂.{u} ≫ (horn 2 (Fin.last 2)).ι = stdSimplex.δ (1 : Fin 3) :=
    horn.ι_ι (Fin.last 2) (1 : Fin 3) (by decide)
  have hi₀ : horn₂₂.ι₁₂.{u} ≫ (horn 2 (Fin.last 2)).ι = stdSimplex.δ (0 : Fin 3) :=
    horn.ι_ι (Fin.last 2) (0 : Fin 3) (by decide)
  have hsq : σ₀ ≫ p = (horn 2 (Fin.last 2)).ι ≫ b := by
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, h₁]
      calc
        _ = yonedaEquiv.symm (Edge.id (p.app _ y)).edge := by
          rw [yonedaEquiv_symm_comp, ← Edge.map_edge, Edge.map_id]
        _ = stdSimplex.δ (1 : Fin 3) ≫ b := hb₁.symm
        _ = _ := by simpa only [Category.assoc] using congrArg (fun f => f ≫ b) hi₁.symm
    · rw [← Category.assoc, h₀]
      calc
        _ = yonedaEquiv.symm (e.map p).edge := by rw [yonedaEquiv_symm_comp, ← Edge.map_edge]
        _ = stdSimplex.δ (0 : Fin 3) ≫ b := hb₀.symm
        _ = _ := by simpa only [Category.assoc] using congrArg (fun f => f ≫ b) hi₀.symm
  have hc : (rightHornEdge σ₀).edge = e.edge := by
    rw [rightHornEdge_two, h₀, Equiv.apply_symm_apply]
  have hp₀ : IsPCartesian p (yonedaEquiv.symm (rightHornEdge σ₀).edge) :=
    (congrArg yonedaEquiv.symm hc).symm ▸ he
  obtain ⟨T, hT, hpT⟩ := exists_fill_rightHorn_of_isPCartesian σ₀ b hsq hp₀
  have hT₀ : stdSimplex.δ (0 : Fin 3) ≫ T = yonedaEquiv.symm e.edge := by
    rw [← horn.ι_ι_assoc (Fin.last 2) (0 : Fin 3) (by decide), hT]
    exact h₀
  have hT₁ : stdSimplex.δ (1 : Fin 3) ≫ T = yonedaEquiv.symm (Edge.id y).edge := by
    rw [← horn.ι_ι_assoc (Fin.last 2) (1 : Fin 3) (by decide), hT]
    exact h₁
  have hd₀ : X.δ (0 : Fin 3) (yonedaEquiv T) = e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hT₀,
      Equiv.apply_symm_apply]
  have hd₁ : X.δ (1 : Fin 3) (yonedaEquiv T) = (Edge.id y).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hT₁,
      Equiv.apply_symm_apply]
  obtain ⟨a₀, a₁, a₂, g, e', k, H, hH⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv T)
  have he' : e'.edge = e.edge := H.d₀.symm.trans ((congrArg (X.δ (0 : Fin 3)) hH).trans hd₀)
  have hk : k.edge = (Edge.id y).edge := H.d₁.symm.trans ((congrArg (X.δ (1 : Fin 3)) hH).trans hd₁)
  have ha₀ : a₀ = y := by rw [← k.src_eq, hk, (Edge.id y).src_eq]
  have ha₁ : a₁ = x := by rw [← e'.src_eq, he', e.src_eq]
  have ha₂ : a₂ = y := by rw [← e'.tgt_eq, he', e.tgt_eq]
  subst a₀
  subst a₁
  subst a₂
  have ee : e' = e := Edge.ext he'
  have kk : k = Edge.id y := Edge.ext hk
  subst e'
  subst k
  refine ⟨g, H, ?_⟩
  have hb : p.app _ (yonedaEquiv T) = I.invHomId.simplex := by
    rw [← yonedaEquiv_comp, hpT]
    exact Equiv.apply_symm_apply yonedaEquiv _
  rw [Edge.map_edge, ← H.d₂, hH, SSet.δ_naturality_apply, hb]
  exact I.invHomId.d₂

end SSet.CartesianEdge
