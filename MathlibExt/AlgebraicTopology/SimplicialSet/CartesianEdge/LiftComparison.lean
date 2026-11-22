/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornFaces
import MathlibExt.AlgebraicTopology.SimplicialSet.CompStructCompat

/-!
# The original relative comparison triangle between two edge lifts

A Cartesian target lift of the same whole base edge supplies a comparison
before that lift. The comparison triangle projects to the literal left unit
of the base edge, and its comparison edge projects to the original identity.
No equivalence or uniqueness of that comparison is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

/-- Compare an original lift to a Cartesian target lift over the same entire base edge. -/
theorem exists_comparison_triangle {X B : SSet.{u}} (p : X ⟶ B)
    {x x' y : X _⦋0⦌} (e : Edge x y) (f : Edge x' y)
    (hf : IsPCartesian p (yonedaEquiv.symm f.edge))
    (hmap : (e.map p).edge = (f.map p).edge) :
    ∃ (h : Edge x x') (H : Edge.CompStruct h f e),
      p.app (op ⦋2⦌) H.simplex = B.σ 0 (f.map p).edge ∧
      (h.map p).edge = (Edge.id (p.app (op ⦋0⦌) x')).edge := by
  have glue : stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm e.edge =
      stdSimplex.δ (0 : Fin 2) ≫ yonedaEquiv.symm f.edge :=
    e.δ_zero_yonedaEquiv_symm.trans f.δ_zero_yonedaEquiv_symm.symm
  obtain ⟨σ₀, h₁, h₀⟩ := horn₂₂.isPushout.exists_desc
    (yonedaEquiv.symm e.edge) (yonedaEquiv.symm f.edge) glue
  have h₀' : horn.ι (Fin.last 2) (0 : Fin 3) (by decide) ≫ σ₀ = yonedaEquiv.symm f.edge := h₀
  have h₁' : horn.ι (Fin.last 2) (1 : Fin 3) (by decide) ≫ σ₀ = yonedaEquiv.symm e.edge := h₁
  have hi₀ : horn₂₂.ι₁₂.{u} ≫ (horn 2 (Fin.last 2)).ι = stdSimplex.δ (0 : Fin 3) :=
    horn.ι_ι (Fin.last 2) (0 : Fin 3) (by decide)
  have hi₁ : horn₂₂.ι₀₂.{u} ≫ (horn 2 (Fin.last 2)).ι = stdSimplex.δ (1 : Fin 3) :=
    horn.ι_ι (Fin.last 2) (1 : Fin 3) (by decide)
  let U := Edge.CompStruct.idComp (f.map p)
  let b : (Δ[2] : SSet.{u}) ⟶ B := yonedaEquiv.symm U.simplex
  have hsq : σ₀ ≫ p = (horn 2 (Fin.last 2)).ι ≫ b := by
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, h₁, ← Category.assoc, hi₁, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (fun a : B _⦋1⦌ => yonedaEquiv.symm a) (hmap.trans U.d₁.symm)
    · rw [← Category.assoc, h₀, ← Category.assoc, hi₀, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (fun a : B _⦋1⦌ => yonedaEquiv.symm a) U.d₀.symm
  have hc : (rightHornEdge σ₀).edge = f.edge := by
    rw [rightHornEdge_two, h₀, Equiv.apply_symm_apply]
  have hf' : IsPCartesian p (yonedaEquiv.symm (rightHornEdge σ₀).edge) :=
    (congrArg yonedaEquiv.symm hc).symm ▸ hf
  obtain ⟨T, hT, hpT⟩ := exists_fill_rightHorn_of_isPCartesian σ₀ b hsq hf'
  have hd₀ : X.δ (0 : Fin 3) (yonedaEquiv T) = f.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (Fin.last 2) (0 : Fin 3) (by decide),
      hT, h₀', Equiv.apply_symm_apply]
  have hd₁ : X.δ (1 : Fin 3) (yonedaEquiv T) = e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (Fin.last 2) (1 : Fin 3) (by decide),
      hT, h₁', Equiv.apply_symm_apply]
  obtain ⟨a₀, a₁, a₂, h, f', e', H, hH⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv T)
  have hf'' : f'.edge = f.edge := H.d₀.symm.trans ((congrArg (X.δ (0 : Fin 3)) hH).trans hd₀)
  have he' : e'.edge = e.edge := H.d₁.symm.trans ((congrArg (X.δ (1 : Fin 3)) hH).trans hd₁)
  have ha₀ : a₀ = x := by rw [← e'.src_eq, he', e.src_eq]
  have ha₁ : a₁ = x' := by rw [← f'.src_eq, hf'', f.src_eq]
  have ha₂ : a₂ = y := by rw [← f'.tgt_eq, hf'', f.tgt_eq]
  subst a₀
  subst a₁
  subst a₂
  have ff : f' = f := Edge.ext hf''
  have ee : e' = e := Edge.ext he'
  subst f'
  subst e'
  have hb : p.app (op ⦋2⦌) H.simplex = U.simplex := by
    rw [hH, ← yonedaEquiv_comp, hpT]
    exact Equiv.apply_symm_apply yonedaEquiv _
  refine ⟨h, H, hb, ?_⟩
  rw [Edge.map_edge, ← H.d₂, SSet.δ_naturality_apply, hb]
  exact U.d₂

end SSet.CartesianEdge
