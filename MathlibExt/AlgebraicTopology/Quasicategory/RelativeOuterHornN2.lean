/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.InnerFibration
public import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHorn

/-!
# Strict relative special outer horn filling in dimension two

An inner fibration with quasicategory target lifts a right two-horn whose
edge `{1, 2}` is an equivalence in the source. The lift preserves the
entire supplied horn and the entire prescribed base triangle.

The proof uses an inverse-unit triangle, one absolute right three-horn
filler in the base, and two inner-horn lifts in the source. The source is
a quasicategory by `quasicategory_of_innerFibration`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

/-- Three compatible faces of a tetrahedron extend when their last
edge is an equivalence. Each supplied triangle is preserved exactly. -/
private theorem exists_tetrahedron_of_faces_of_isEquivalence {D : SSet.{u}}
    [Quasicategory D] (f₀ f₁ f₂ : (Δ[2] : SSet.{u}) ⟶ D)
    (h₀₁ : stdSimplex.δ (0 : Fin 3) ≫ f₀ = stdSimplex.δ (0 : Fin 3) ≫ f₁)
    (h₀₂ : stdSimplex.δ (1 : Fin 3) ≫ f₀ = stdSimplex.δ (0 : Fin 3) ≫ f₂)
    (h₁₂ : stdSimplex.δ (1 : Fin 3) ≫ f₁ = stdSimplex.δ (1 : Fin 3) ≫ f₂)
    (he : (Edge.mk' (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ f₀))).IsEquivalence) :
    ∃ T : (Δ[3] : SSet.{u}) ⟶ D,
      stdSimplex.δ (0 : Fin 4) ≫ T = f₀ ∧
      stdSimplex.δ (1 : Fin 4) ≫ T = f₁ ∧ stdSimplex.δ (2 : Fin 4) ≫ T = f₂ := by
  let f : ∀ (j : Fin 4) (_ : j ≠ Fin.last 3), (Δ[2] : SSet.{u}) ⟶ D :=
    fun j _ ↦ ![f₀, f₁, f₂, f₂] j
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;>
      simp only [f, Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
        Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;> simp_all
  let φ : (Λ[3, Fin.last 3] : SSet.{u}) ⟶ D := hf.desc
  have hφ : ∀ (j : Fin 4) (hj : j ≠ Fin.last 3),
      horn.ι (Fin.last 3) j hj ≫ φ = f j hj :=
    fun j hj ↦ hf.ι_desc j hj
  have hφ0 : φ.app _ (horn.face (Fin.last 3) 0 (by decide)) = yonedaEquiv f₀ := by
    simpa only [f, Matrix.cons_val_zero, horn.ι,
      yonedaEquiv_symm_comp, Equiv.apply_symm_apply] using
      congrArg yonedaEquiv (hφ 0 (by decide))
  have hedge : (rightHornEdge φ).edge =
      (Edge.mk' (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ f₀))).edge := by
    have hface : (Λ[3, Fin.last 3] : SSet.{u}).δ (0 : Fin 3)
        (horn.face (Fin.last 3) 0 (by decide)) =
        rightHornEdgeSimplex.{u} 1 := by decide
    have hn : φ.app _ ((Λ[3, Fin.last 3] : SSet.{u}).δ (0 : Fin 3)
        (horn.face (Fin.last 3) 0 (by decide))) =
        D.δ (0 : Fin 3) (φ.app _ (horn.face (Fin.last 3) 0 (by decide))) :=
      NatTrans.naturality_apply φ (SimplexCategory.δ (0 : Fin 3)).op _
    rw [hface] at hn
    rw [rightHornEdge_edge, Edge.mk'_edge, hn, hφ0, stdSimplex.yonedaEquiv_δ_comp]
  obtain ⟨T, hT⟩ := exists_fill_horn_three_last_of_isEquivalence φ
    ((Edge.isEquivalence_iff_of_edge_eq hedge).mpr he)
  have hTf : ∀ (j : Fin 4) (hj : j ≠ Fin.last 3),
      stdSimplex.δ j ≫ T = f j hj := by
    intro j hj
    calc
      _ = horn.ι (Fin.last 3) j hj ≫ φ := by rw [hT, horn.ι_ι_assoc]
      _ = f j hj := hφ j hj
  exact ⟨T, by simpa [f] using hTf 0 (by decide),
    by simpa [f] using hTf 1 (by decide), by simpa [f] using hTf 2 (by decide)⟩

/-- Strict relative right two-horn filling for an inner fibration with
quasicategory target. The critical edge is the supplied `{1, 2}` edge,
and the filler maps to the complete prescribed base simplex. -/
theorem exists_fill_relativeSpecialOuterHorn_two_two {C D : SSet.{u}}
    {q : C ⟶ D} [InnerFibration q] [Quasicategory D]
    (σ₀ : (Λ[2, 2] : SSet.{u}) ⟶ C) (σBar : (Δ[2] : SSet.{u}) ⟶ D)
    (hsq : σ₀ ≫ q = Λ[2, 2].ι ≫ σBar)
    (hg : (Edge.mk'
      (yonedaEquiv (horn.ι 2 0 (by decide) ≫ σ₀))).IsEquivalence) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ C,
      Λ[2, 2].ι ≫ σ = σ₀ ∧ σ ≫ q = σBar := by
  have : Quasicategory C := quasicategory_of_innerFibration q
  let g : (Δ[1] : SSet.{u}) ⟶ C := horn.ι 2 0 (by decide) ≫ σ₀
  let h : (Δ[1] : SSet.{u}) ⟶ C := horn.ι 2 1 (by decide) ≫ σ₀
  have hgh : stdSimplex.δ (0 : Fin 2) ≫ g =
      stdSimplex.δ (0 : Fin 2) ≫ h :=
    (horn.IsCompatible.of_hom σ₀).δ_pred_comp 0 1
      (by decide) (by decide) (by decide)
  have hgh' : C.δ 0 (yonedaEquiv g) = C.δ 0 (yonedaEquiv h) := by
    simpa only [stdSimplex.yonedaEquiv_δ_comp] using congrArg yonedaEquiv hgh
  have hgq : g ≫ q = stdSimplex.δ (0 : Fin 3) ≫ σBar := by
    simp only [g, Category.assoc, hsq, horn.ι_ι_assoc]
  have hhq : h ≫ q = stdSimplex.δ (1 : Fin 3) ≫ σBar := by
    simp only [h, Category.assoc, hsq, horn.ι_ι_assoc]
  -- The inverse-unit triangle has vertices `(x₂, x₁, x₂)`.
  let e := Edge.mk' (yonedaEquiv g)
  have he : e.IsEquivalence := hg
  obtain ⟨I⟩ := he.nonempty_invStruct
  let α : (Δ[2] : SSet.{u}) ⟶ C := yonedaEquiv.symm I.invHomId.simplex
  let gi : (Δ[1] : SSet.{u}) ⟶ C := yonedaEquiv.symm I.inv.edge
  let β : (Δ[2] : SSet.{u}) ⟶ C :=
    yonedaEquiv.symm (C.σ (1 : Fin 2) (yonedaEquiv h))
  have α0 : stdSimplex.δ (0 : Fin 3) ≫ α = g := by
    dsimp only [α]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, I.invHomId.d₀,
      Edge.mk'_edge, Equiv.symm_apply_apply]
  have α2 : stdSimplex.δ (2 : Fin 3) ≫ α = gi := by
    dsimp only [α, gi]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, I.invHomId.d₂]
  have β1 : stdSimplex.δ (1 : Fin 3) ≫ β = h := by
    dsimp only [β]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      show C.δ (1 : Fin 3) (C.σ (1 : Fin 2) (yonedaEquiv h)) = yonedaEquiv h from
        ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_self' C
          (show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from rfl))
          (yonedaEquiv h), Equiv.symm_apply_apply]
  have β2 : stdSimplex.δ (2 : Fin 3) ≫ β = h := by
    dsimp only [β]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      show C.δ (2 : Fin 3) (C.σ (1 : Fin 2) (yonedaEquiv h)) = yonedaEquiv h from
        ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_succ' C
          (show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl))
          (yonedaEquiv h), Equiv.symm_apply_apply]
  have α1β0 : stdSimplex.δ (1 : Fin 3) ≫ α =
      stdSimplex.δ (0 : Fin 3) ≫ β := by
    dsimp only [α, β]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm, I.invHomId.d₁, Edge.id_edge,
      show C.δ (0 : Fin 3) (C.σ (1 : Fin 2) (yonedaEquiv h)) =
        C.σ (0 : Fin 1) (C.δ (0 : Fin 2) (yonedaEquiv h)) from
        ConcreteCategory.congr_hom (SimplicialObject.δ_comp_σ_of_le C
          (show (0 : Fin 2) ≤ Fin.castSucc (0 : Fin 1) by decide))
          (yonedaEquiv h), hgh']
  have gih : stdSimplex.δ (1 : Fin 2) ≫ gi =
      stdSimplex.δ (0 : Fin 2) ≫ h := by
    dsimp only [gi]
    apply yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, I.inv.src_eq]
    exact hgh'
  -- Vertices in the base: `(qx₀, qx₂, qx₁, qx₂)`.
  have h01 : stdSimplex.δ (0 : Fin 3) ≫ (α ≫ q) =
      stdSimplex.δ (0 : Fin 3) ≫ σBar := by
    rw [← Category.assoc, α0, hgq]
  have h02 : stdSimplex.δ (1 : Fin 3) ≫ (α ≫ q) =
      stdSimplex.δ (0 : Fin 3) ≫ (β ≫ q) := by
    rw [← Category.assoc, α1β0, Category.assoc]
  have h12 : stdSimplex.δ (1 : Fin 3) ≫ σBar =
      stdSimplex.δ (1 : Fin 3) ≫ (β ≫ q) := by
    rw [← Category.assoc, β1, hhq]
  have hgmap : (Edge.mk' (yonedaEquiv (g ≫ q))).IsEquivalence := by
    apply (Edge.isEquivalence_iff_of_edge_eq
      (show (Edge.mk' (yonedaEquiv (g ≫ q))).edge = (e.map q).edge by
        rw [Edge.mk'_edge, Edge.map_edge, yonedaEquiv_comp]
        rfl)).mpr
    exact he.map q
  have hlast : (Edge.mk'
      (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ (α ≫ q)))).IsEquivalence := by
    have hm : stdSimplex.δ (0 : Fin 3) ≫ (α ≫ q) = g ≫ q := by
      rw [← Category.assoc, α0]
    rw [hm]
    exact hgmap
  obtain ⟨T, T0, T1, T2⟩ := exists_tetrahedron_of_faces_of_isEquivalence
    (α ≫ q) σBar (β ≫ q) h01 h02 h12 hlast
  -- First source lift: the inner horn on `(x₀, x₂, x₁)` over `d₃T`.
  let fu : ∀ (j : Fin 3) (_ : j ≠ 1), (Δ[1] : SSet.{u}) ⟶ C :=
    fun j _ ↦ ![gi, gi, h] j
  have hfu : horn.IsCompatible fu := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;>
      simp only [fu, Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
        Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;> simp_all
  have d03 : stdSimplex.{u}.δ (0 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) =
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
    simpa only [show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
      show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl] using
      stdSimplex.{u}.δ_comp_δ (show (0 : Fin 3) ≤ 2 by decide)
  have d23 : stdSimplex.{u}.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) =
      stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) := by
    simpa only [show (2 : Fin 3).succ = (3 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl] using
      stdSimplex.{u}.δ_comp_δ (show (2 : Fin 3) ≤ 2 by decide)
  have hbase : ∀ (j : Fin 3) (hj : j ≠ 1),
      fu j hj ≫ q = stdSimplex.δ j ≫ (stdSimplex.δ (3 : Fin 4) ≫ T) := by
    intro j hj
    fin_cases j
    · change gi ≫ q = stdSimplex.δ 0 ≫ (stdSimplex.δ 3 ≫ T)
      conv_rhs => rw [← Category.assoc, d03, Category.assoc, T0, ← Category.assoc, α2]
    · exact (hj rfl).elim
    · change h ≫ q = stdSimplex.δ 2 ≫ (stdSimplex.δ 3 ≫ T)
      conv_rhs => rw [← Category.assoc, d23, Category.assoc, T2, ← Category.assoc, β2]
  obtain ⟨U, hU, Uq⟩ := horn.IsCompatible.exists_lift_of_innerFibration
    (i := (1 : Fin 3)) (f := fu) q (by decide) (by decide) hfu
    (stdSimplex.δ (3 : Fin 4) ≫ T) (fun j hj ↦ (hbase j hj).symm)
  have U0 : stdSimplex.δ (0 : Fin 3) ≫ U = gi := by
    simpa [fu] using hU 0 (by decide)
  have U2 : stdSimplex.δ (2 : Fin 3) ≫ U = h := by
    simpa [fu] using hU 2 (by decide)
  -- Second source lift: the inner horn on `(x₀, x₂, x₁, x₂)`.
  let χ : (Λ[3, 1] : SSet.{u}) ⟶ C :=
    horn₃₁.desc α β U (α2.trans U0.symm) α1β0 (β2.trans U2.symm)
  have χ0 : horn.ι 1 0 (by decide) ≫ χ = α := horn₃₁.ι₀_desc ..
  have χ2 : horn.ι 1 2 (by decide) ≫ χ = β := horn₃₁.ι₂_desc ..
  have χ3 : horn.ι 1 3 (by decide) ≫ χ = U := horn₃₁.ι₃_desc ..
  have hχbase : ∀ (j : Fin 4) (hj : j ≠ 1),
      stdSimplex.δ j ≫ T = (horn.ι 1 j hj ≫ χ) ≫ q := by
    intro j hj
    fin_cases j <;> simp only [Fin.isValue, Fin.reduceFinMk]
    · rw [χ0, T0]
    · exact (hj rfl).elim
    · rw [χ2, T2]
    · rw [χ3, Uq]
  obtain ⟨V, hV, Vq⟩ := horn.IsCompatible.exists_lift_of_innerFibration
    (i := (1 : Fin 4)) q (by decide) (by decide)
    (horn.IsCompatible.of_hom χ) T hχbase
  have V0 : stdSimplex.δ (0 : Fin 4) ≫ V = α := (hV 0 (by decide)).trans χ0
  have V2 : stdSimplex.δ (2 : Fin 4) ≫ V = β := (hV 2 (by decide)).trans χ2
  let σ : (Δ[2] : SSet.{u}) ⟶ C := stdSimplex.δ 1 ≫ V
  have d01 : stdSimplex.{u}.δ (0 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) =
      stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
    simpa only [show (0 : Fin 3).succ = (1 : Fin 4) from rfl,
      show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl] using
      stdSimplex.{u}.δ_comp_δ (show (0 : Fin 3) ≤ 0 by decide)
  have d11 : stdSimplex.{u}.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4) := by
    simpa only [show (1 : Fin 3).succ = (2 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl] using
      stdSimplex.{u}.δ_comp_δ (show (1 : Fin 3) ≤ 1 by decide)
  have σ0 : stdSimplex.δ (0 : Fin 3) ≫ σ = g := by
    dsimp only [σ]
    rw [← Category.assoc, d01, Category.assoc, V0, α0]
  have σ1 : stdSimplex.δ (1 : Fin 3) ≫ σ = h := by
    dsimp only [σ]
    rw [← Category.assoc, ← d11, Category.assoc, V2, β1]
  refine ⟨σ, ?_, ?_⟩
  · apply horn.hom_ext'
    intro j hj
    fin_cases j
    · simpa only [Fin.isValue, Fin.reduceFinMk, horn.ι_ι_assoc, g] using σ0
    · simpa only [Fin.isValue, Fin.reduceFinMk, horn.ι_ι_assoc, h] using σ1
    · exact (hj rfl).elim
  · dsimp only [σ]
    rw [Category.assoc, Vq, T1]

end SSet
