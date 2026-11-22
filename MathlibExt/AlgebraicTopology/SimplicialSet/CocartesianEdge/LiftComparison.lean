/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LeftHornFaces
import MathlibExt.AlgebraicTopology.SimplicialSet.CompStructCompat

/-!
# The original cocartesian comparison triangle over a right unit

A cocartesian source lift supplies a comparison after that lift to any
original lift of the same whole base edge. The entire triangle and the
vertical comparison-edge image are retained literally.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

/-- Compare a cocartesian source lift with another original lift of the same whole base edge. -/
theorem exists_comparison_triangle {X B : SSet.{u}} (p : X ⟶ B)
    {x y y' : X _⦋0⦌} (e : Edge x y) (f : Edge x y')
    (he : IsPCocartesian p (yonedaEquiv.symm e.edge))
    (hmap : (f.map p).edge = (e.map p).edge) :
    ∃ (h : Edge y y') (H : Edge.CompStruct e h f),
      p.app (op ⦋2⦌) H.simplex = B.σ 1 (e.map p).edge ∧
      (h.map p).edge = (Edge.id (p.app (op ⦋0⦌) y)).edge := by
  have glue : stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm e.edge =
      stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm f.edge :=
    e.δ_one_yonedaEquiv_symm.trans f.δ_one_yonedaEquiv_symm.symm
  obtain ⟨σ₀, h₂, h₁⟩ := horn₂₀.isPushout.exists_desc
    (yonedaEquiv.symm e.edge) (yonedaEquiv.symm f.edge) glue
  have h₂' : horn.ι (0 : Fin 3) (2 : Fin 3) (by decide) ≫ σ₀ = yonedaEquiv.symm e.edge := h₂
  have h₁' : horn.ι (0 : Fin 3) (1 : Fin 3) (by decide) ≫ σ₀ = yonedaEquiv.symm f.edge := h₁
  have hi₂ : horn₂₀.ι₀₁.{u} ≫ (horn 2 (0 : Fin 3)).ι = stdSimplex.δ (2 : Fin 3) :=
    horn.ι_ι (0 : Fin 3) (2 : Fin 3) (by decide)
  have hi₁ : horn₂₀.ι₀₂.{u} ≫ (horn 2 (0 : Fin 3)).ι = stdSimplex.δ (1 : Fin 3) :=
    horn.ι_ι (0 : Fin 3) (1 : Fin 3) (by decide)
  let U := Edge.CompStruct.compId (e.map p)
  let b : (Δ[2] : SSet.{u}) ⟶ B := yonedaEquiv.symm U.simplex
  have hsq : σ₀ ≫ p = (horn 2 (0 : Fin 3)).ι ≫ b := by
    apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, h₂, ← Category.assoc, hi₂, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (fun a : B _⦋1⦌ => yonedaEquiv.symm a) U.d₂.symm
    · rw [← Category.assoc, h₁, ← Category.assoc, hi₁, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (fun a : B _⦋1⦌ => yonedaEquiv.symm a) (hmap.trans U.d₁.symm)
  have hc : (leftHornEdge σ₀).edge = e.edge := by
    rw [leftHornEdge_two, h₂, Equiv.apply_symm_apply]
  have he' : IsPCocartesian p (yonedaEquiv.symm (leftHornEdge σ₀).edge) :=
    (congrArg yonedaEquiv.symm hc).symm ▸ he
  obtain ⟨T, hT, hpT⟩ := exists_fill_leftHorn_of_isPCocartesian σ₀ b hsq he'
  have hd₂ : X.δ (2 : Fin 3) (yonedaEquiv T) = e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (0 : Fin 3) (2 : Fin 3) (by decide),
      hT, h₂', Equiv.apply_symm_apply]
  have hd₁ : X.δ (1 : Fin 3) (yonedaEquiv T) = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (0 : Fin 3) (1 : Fin 3) (by decide),
      hT, h₁', Equiv.apply_symm_apply]
  obtain ⟨a₀, a₁, a₂, e', h, f', H, hH⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv T)
  have he'' : e'.edge = e.edge := H.d₂.symm.trans ((congrArg (X.δ (2 : Fin 3)) hH).trans hd₂)
  have hf : f'.edge = f.edge := H.d₁.symm.trans ((congrArg (X.δ (1 : Fin 3)) hH).trans hd₁)
  have ha₀ : a₀ = x := by rw [← e'.src_eq, he'', e.src_eq]
  have ha₁ : a₁ = y := by rw [← e'.tgt_eq, he'', e.tgt_eq]
  have ha₂ : a₂ = y' := by rw [← f'.tgt_eq, hf, f.tgt_eq]
  subst a₀
  subst a₁
  subst a₂
  have ee : e' = e := Edge.ext he''
  have ff : f' = f := Edge.ext hf
  subst e'
  subst f'
  have hb : p.app (op ⦋2⦌) H.simplex = U.simplex := by
    rw [hH, ← yonedaEquiv_comp, hpT]
    exact Equiv.apply_symm_apply yonedaEquiv _
  refine ⟨h, H, hb, ?_⟩
  rw [Edge.map_edge, ← H.d₀, SSet.δ_naturality_apply, hb]
  exact U.d₀

end SSet.CocartesianEdge
