/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomDeformation
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexContraction

/-!
# Deformation of a boundary lifting square to a constant base

Let `f : X → Y` be a Kan fibration and consider a commuting boundary square with
left map `∂Δ[n] → Δ[n]`, top map `t`, and bottom simplex `b : Δ[n] → Y`.
Contracting the simplex to its last vertex gives a new boundary top map `t₁` over
the constant simplex at that vertex, with equivalent existence of diagonal lifts.

The boundary top map is allowed to change during the deformation, while the boundary
inclusion and the fibration remain the same. The construction applies to every
`n ≥ 0` and in every simplicial-set universe.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial SSet
  HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace SSet

/-- The vertex-`0` face inclusion into `Δ[1]` is the horn `Λ[1, 0]`. -/
private theorem faceZero_mem_anodyneExtensions :
    SSet.anodyneExtensions
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq : (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
      SSet.horn (n := 1) (0 : Fin 2) := by
    have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
    calc (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)
        = SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = SSet.horn (n := 1) (0 : Fin 2) := by
          ext m x
          simp [SSet.horn_eq_iSup]
  rw [h_eq]
  exact SSet.anodyneExtensions.horn_ι (0 : Fin 2)

/-- The endpoint-`0` vertex inclusion `δ 1 : Δ[0] ⟶ Δ[1]` is anodyne. -/
private theorem deltaOne_mem_anodyneExtensions :
    SSet.anodyneExtensions (SSet.stdSimplex.δ (1 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have h_eq : SSet.stdSimplex.δ (1 : Fin 2) =
      (SSet.stdSimplex.faceSingletonIso (0 : Fin 2)).hom ≫
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι :=
    SSet.stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ.symm
  rw [h_eq]
  exact SSet.anodyneExtensions.comp_mem _ _
    (SSet.anodyneExtensions.of_isIso _) faceZero_mem_anodyneExtensions

/-- The endpoint-`0` cylinder inclusion over any base is anodyne. -/
private theorem endpointZero_mem_anodyneExtensions (A : SSet.{u}) :
    SSet.anodyneExtensions (A ◁ (SSet.stdSimplex.δ (1 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1])) :=
  SSet.anodyneExtensions.whiskerLeft deltaOne_mem_anodyneExtensions A

end SSet

namespace SSet.CommSq

variable {X Y : SSet.{u}} {f : X ⟶ Y} [Fibration f]
  {n : ℕ} {t : (∂Δ[n] : SSet.{u}) ⟶ X} {b : Δ[n] ⟶ Y}

/--
For a boundary square over a Kan fibration, there exist a vertex `y` and a new
top map `t₁` over the constant simplex at `y`, such that the original square has
a diagonal lift exactly when the new square does. The construction uses the last
vertex of the original bottom simplex.
-/
theorem exists_const_base_reduction (sq₀ : CommSq t (SSet.boundary n).ι f b) :
    ∃ (y : Y _⦋0⦌) (t₁ : (∂Δ[n] : SSet.{u}) ⟶ X)
      (sq₁ : CommSq t₁ (SSet.boundary n).ι f (SSet.const y)),
      t₁ ≫ f = SSet.const y ∧ (sq₀.HasLift ↔ sq₁.HasLift) := by
  -- The contraction of the simplex onto its last vertex.
  set H : SSet.Homotopy (𝟙 (Δ[n] : SSet.{u}))
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))) :=
    SSet.stdSimplex.homotopyIdConstLast n with hH
  have hH₀ : SSet.ι₀ ≫ H.h = 𝟙 (Δ[n] : SSet.{u}) := SSet.Homotopy.h₀ H
  have hH₁ : SSet.ι₁ ≫ H.h =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n)) :=
    SSet.Homotopy.h₁ H
  -- Cylinder base over `Y`: the contraction pushed forward along `b`.
  have hb₀ : SSet.ι₀ ≫ (H.h ≫ b) = b := by
    rw [← Category.assoc, hH₀, Category.id_comp]
  have hb₁ : SSet.ι₁ ≫ (H.h ≫ b) =
      SSet.const (b.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
    rw [← Category.assoc, hH₁, SSet.const_comp]
  -- The whiskered contraction agrees with the boundary inclusion at endpoint 0.
  have h0 : SSet.ι₀ ≫ ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h) =
      (SSet.boundary n).ι := by
    calc SSet.ι₀ ≫ ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h)
        = (SSet.ι₀ ≫ (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u})) ≫ H.h := by
          rw [Category.assoc]
      _ = ((SSet.boundary n).ι ≫ SSet.ι₀) ≫ H.h := by rw [SSet.ι₀_comp]
      _ = (SSet.boundary n).ι ≫ (SSet.ι₀ ≫ H.h) := by rw [← Category.assoc]
      _ = (SSet.boundary n).ι ≫ 𝟙 (Δ[n] : SSet.{u}) := by rw [hH₀]
      _ = (SSet.boundary n).ι := by rw [Category.comp_id]
  have hW : ((∂Δ[n] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫
        ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h) =
      (SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).hom ≫
        (SSet.boundary n).ι := by
    calc ((∂Δ[n] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫
            ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h)
        = ((SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).hom ≫ SSet.ι₀) ≫
            ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h) := by
            rw [← SSet.stdSimplex.rightUnitor_hom_ι₀]
      _ = (SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).hom ≫
            (SSet.ι₀ ≫ ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h)) := by
            rw [Category.assoc]
      _ = (SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).hom ≫
            (SSet.boundary n).ι := by rw [h0]
  -- The lifting square against the anodyne endpoint inclusion.
  have sqW : ((SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).hom ≫ t) ≫ f =
      ((∂Δ[n] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫
        ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ (H.h ≫ b)) := by
    rw [Category.assoc, sq₀.w, ← Category.assoc, ← hW]
    simp only [Category.assoc]
  have hEnd : SSet.anodyneExtensions
      ((∂Δ[n] : SSet.{u}) ◁ (SSet.stdSimplex.δ (1 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1])) :=
    SSet.endpointZero_mem_anodyneExtensions _
  have hlp : HasLiftingProperty
      ((∂Δ[n] : SSet.{u}) ◁ (SSet.stdSimplex.δ (1 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1])) f :=
    SSet.anodyneExtensions.hasLeftLiftingProperty hEnd f
  have sqLift : CommSq
      ((SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).hom ≫ t)
      ((∂Δ[n] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2)) f
      ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ (H.h ≫ b)) := ⟨sqW⟩
  obtain ⟨T, hTL, hTR⟩ := (hlp.sq_hasLift sqLift).exists_lift
  -- Endpoint 0 of the lifted homotopy recovers the original top.
  have ht₀ : SSet.ι₀ ≫ T = t := by
    have h : SSet.ι₀ (X := (∂Δ[n] : SSet.{u})) =
        (SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).inv ≫
          ((∂Δ[n] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2)) :=
      (SSet.stdSimplex.rightUnitor_inv_map_δ_one _).symm
    calc SSet.ι₀ ≫ T
        = ((SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).inv ≫
            ((∂Δ[n] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2))) ≫ T := by
          rw [h]
      _ = (SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).inv ≫
            (((∂Δ[n] : SSet.{u}) ◁ SSet.stdSimplex.δ (1 : Fin 2)) ≫ T) := by
            rw [← Category.assoc]
      _ = (SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).inv ≫
            ((SSet.stdSimplex.rightUnitor (∂Δ[n] : SSet.{u})).hom ≫ t) := by
            rw [hTL]
      _ = t := by
          rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- New top at endpoint 1; it lands strictly over the constant base.
  set t₁ : (∂Δ[n] : SSet.{u}) ⟶ X := SSet.ι₁ ≫ T with ht₁
  have ht₁f : t₁ ≫ f =
      SSet.const (b.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
    calc t₁ ≫ f = (SSet.ι₁ ≫ T) ≫ f := by rw [ht₁]
      _ = SSet.ι₁ ≫ (T ≫ f) := by rw [Category.assoc]
      _ = SSet.ι₁ ≫
            ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ (H.h ≫ b)) := by
            rw [hTR]
      _ = ((SSet.boundary n).ι ≫ SSet.ι₁) ≫ (H.h ≫ b) := by
          rw [← Category.assoc, SSet.ι₁_comp]
      _ = (SSet.boundary n).ι ≫
            SSet.const
              (b.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
          rw [Category.assoc, hb₁]
      _ = SSet.const
            (b.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
          rw [SSet.comp_const]
  have sq₁ : CommSq t₁ (SSet.boundary n).ι f
      (SSet.const
        (b.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n)))) := by
    refine ⟨?_⟩
    simp only [SSet.comp_const]
    exact ht₁f
  -- The cylinder square and deformation invariance of `HasLift`.
  have sqCyl : CommSq T ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u})) f (H.h ≫ b) :=
    ⟨hTR⟩
  have ht₁' : SSet.ι₁ ≫ T = t₁ := by rw [ht₁]
  have hIff := SSet.CommSq.hasLift_iff_of_deformation (i := (SSet.boundary n).ι)
    (p := f) sqCyl (t₀ := t) (t₁ := t₁)
    (b₀ := b)
    (b₁ := SSet.const
      (b.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))))
    ht₀ ht₁' hb₀ hb₁
  have r₀ : (SSet.CommSq.commSq₀_of_deformation sqCyl ht₀ hb₀).HasLift ↔
      sq₀.HasLift :=
    Iff.rfl
  have r₁ : (SSet.CommSq.commSq₁_of_deformation sqCyl ht₁' hb₁).HasLift ↔
      sq₁.HasLift :=
    Iff.rfl
  exact ⟨_, _, sq₁, ht₁f, r₀.symm.trans (hIff.trans r₁)⟩

end SSet.CommSq
