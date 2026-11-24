/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Fundamental groupoid action on homotopy groups

This module provides the public fundamental groupoid action `π.action` on `π n`,
with its identity, composition, equivalence (`actionEquiv` / `actionFunctor`)
and map-naturality (`action_naturality`) laws. Chosen horn fillers and raw
edge transport are private implementation details.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra Limits
open scoped SSet.modelCategoryQuillen
open scoped Simplicial

namespace SSet

namespace KanComplex

namespace FundamentalGroupoid

variable {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}

-- ActionStruct with prism map, boundary and endpoint equations
structure ActionStruct (p : Edge x y) (s : X.PtSimplex n x) (t : X.PtSimplex n y) where
  prism : Δ[n] ⊗ Δ[1] ⟶ X
  boundary :
      (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ prism =
        snd _ _ ≫ yonedaEquiv.symm (Edge.edge p)
  left : ι₀ ≫ prism = SSet.RelativeMorphism.map s
  right : ι₁ ≫ prism = SSet.RelativeMorphism.map t

omit [KanComplex X] in
@[reassoc (attr := simp)]
lemma ActionStruct.boundary_assoc {p : Edge x y} {s : X.PtSimplex n x}
    {t : X.PtSimplex n y} (h : ActionStruct (X := X) (n := n) p s t) :
    (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ h.prism =
      snd _ _ ≫ yonedaEquiv.symm (Edge.edge p) :=
  h.boundary

omit [KanComplex X] in
@[reassoc (attr := simp)]
lemma ActionStruct.left_assoc {p : Edge x y} {s : X.PtSimplex n x}
    {t : X.PtSimplex n y} (h : ActionStruct (X := X) (n := n) p s t) :
    (ι₀ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫ h.prism = SSet.RelativeMorphism.map s :=
  h.left

omit [KanComplex X] in
@[reassoc (attr := simp)]
lemma ActionStruct.right_assoc {p : Edge x y} {s : X.PtSimplex n x}
    {t : X.PtSimplex n y} (h : ActionStruct (X := X) (n := n) p s t) :
    (ι₁ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫ h.prism = SSet.RelativeMorphism.map t :=
  h.right

-- Pushforward along a simplicial map
noncomputable def ActionStruct.pushforward {Y : SSet.{u}} [KanComplex Y]
    {n : ℕ} {x y : X _⦋0⦌} {p : Edge x y} {s : X.PtSimplex n x} {t : X.PtSimplex n y}
    (h : ActionStruct p s t) (f : X ⟶ Y) :
    ActionStruct (p.map f) (SSet.PtSimplex.map f rfl s) (SSet.PtSimplex.map f rfl t) where
  prism := h.prism ≫ f
  boundary := by
    have hb := h.boundary
    have h1 : (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ (h.prism ≫ f) =
      ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ h.prism) ≫ f := by
      rw [Category.assoc]
    rw [h1, hb, Category.assoc]
    congr 1
    -- snd ≫ yonedaEquiv.symm (Edge.edge p) ≫ f = snd ≫ yonedaEquiv.symm (Edge.edge (p.map f))
    have : yonedaEquiv.symm (Edge.edge p) ≫ f = yonedaEquiv.symm (Edge.edge (p.map f)) := by
      rw [yonedaEquiv_symm_comp]
      rw [← Edge.map_edge]
    rw [this]
  left := by
    have hl := h.left
    have h1 : (ι₀ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫ (h.prism ≫ f) =
      ((ι₀ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫ h.prism) ≫ f := by
      rw [Category.assoc]
    rw [h1, hl]
    rfl
  right := by
    have hr := h.right
    have h1 : (ι₁ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫ (h.prism ≫ f) =
      ((ι₁ : Δ[n] ⟶ Δ[n] ⊗ Δ[1]) ≫ h.prism) ≫ f := by
      rw [Category.assoc]
    rw [h1, hr]
    rfl

-- Identity action: prism is fst ≫ SSet.RelativeMorphism.map s
noncomputable def ActionStruct.id {n : ℕ} {x : X _⦋0⦌} (s : X.PtSimplex n x) :
    ActionStruct (Edge.id x) s s where
  prism := fst _ _ ≫ SSet.RelativeMorphism.map s
  boundary := by
    -- Both sides are constant at x; use that boundary of s is const and id edge is const
    have h1 :
        (SSet.boundary n).ι ≫ SSet.RelativeMorphism.map s =
          SSet.const (X := (SSet.boundary n : SSet.{u})) x := by
      have hcomm := s.comm
      -- s.comm : (boundary n).ι ≫ SSet.RelativeMorphism.map s = const ⟨x,_⟩ ≫ (ofSimplex x).ι
      simp only [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const] at hcomm
      exact hcomm
    have h2 :
        (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫
          (fst _ _ ≫ SSet.RelativeMorphism.map s) =
          SSet.const (X := (SSet.boundary n : SSet.{u}) ⊗ Δ[1]) x := by
      calc (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ (fst _ _ ≫ SSet.RelativeMorphism.map s)
          = ((SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ fst _ _) ≫
            SSet.RelativeMorphism.map s := by rw [Category.assoc]
        _ = (fst _ _ ≫ (SSet.boundary n).ι) ≫ SSet.RelativeMorphism.map s := by
            simp
        _ = fst _ _ ≫ ((SSet.boundary n).ι ≫ SSet.RelativeMorphism.map s) := by rw [Category.assoc]
        _ = fst _ _ ≫ SSet.const (X := (SSet.boundary n : SSet.{u})) x := by rw [h1]
        _ = SSet.const (X := (SSet.boundary n : SSet.{u}) ⊗ Δ[1]) x := by simp [SSet.comp_const]
    have h3 : snd _ _ ≫ yonedaEquiv.symm (Edge.edge (Edge.id x)) =
      SSet.const (X := (SSet.boundary n : SSet.{u}) ⊗ Δ[1]) x := by
      have hid : Edge.edge (Edge.id x) = X.σ 0 x := rfl
      rw [hid]
      have hconst : (yonedaEquiv.symm (X.σ 0 x) : Δ[1] ⟶ X) = SSet.const x := by
        rw [← stdSimplex.σ_comp_yonedaEquiv_symm, yonedaEquiv_symm_zero, comp_const]
      rw [hconst]
      simp [SSet.comp_const]
    rw [h2, h3]
  left := by
    simp
  right := by
    simp

-- Existence of ActionStruct via anodyne lifting (uses unionProd.isPushout, pushout-product)
-- Uses Subcomplex.unionProd.isPushout, the boundary×face union (boundary n ∪ face {0}),
-- the relevant anodyne-extension pushout-product theorem (anodyneExtensions_unionProd_ι),
-- and fibrant lifting for KanComplex X.
lemma exists_actionStruct {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : Edge x y) (s : X.PtSimplex n x) :
    ∃ t : X.PtSimplex n y, Nonempty (ActionStruct p s t) := by
  let A : (Δ[n] : SSet.{u}).Subcomplex := SSet.boundary n
  let B : (Δ[1] : SSet.{u}).Subcomplex := stdSimplex.face ({1}ᶜ : Finset (Fin 2))
  -- B = face {0} = horn 1 0
  have hB : anodyneExtensions B.ι := by
    have h_eq : B = SSet.horn 1 0 := by
      ext m x
      simp [B, SSet.horn_eq_iSup]
    rw [h_eq]
    exact anodyneExtensions.horn_ι (0 : Fin 2)
  have hAnodyne : anodyneExtensions (A.unionProd B).ι :=
    SSet.anodyneExtensions_unionProd_ι A B hB
  let g₁ : (A : SSet.{u}) ⊗ Δ[1] ⟶ X := snd _ _ ≫ yonedaEquiv.symm p.edge
  let g₂ : Δ[n] ⊗ (B : SSet.{u}) ⟶ X := fst _ _ ≫ SSet.RelativeMorphism.map s
  have h_agree : (A.ι ▷ (B : SSet.{u})) ≫ g₂ = ((A : SSet.{u}) ◁ B.ι) ≫ g₁ := by
    have h1 : (A.ι ▷ (B : SSet.{u})) ≫ g₂ =
        SSet.const (X := (A : SSet.{u}) ⊗ (B : SSet.{u})) x := by
      calc (A.ι ▷ (B : SSet.{u})) ≫ g₂
          = (A.ι ▷ (B : SSet.{u})) ≫ (fst _ _ ≫ SSet.RelativeMorphism.map s) := rfl
        _ = (fst _ _ ≫ A.ι) ≫ SSet.RelativeMorphism.map s := by
            have : (A.ι ▷ (B : SSet.{u})) ≫ fst _ _ = fst _ _ ≫ A.ι := rfl
            rw [← Category.assoc, this, Category.assoc]
        _ = fst _ _ ≫ (A.ι ≫ SSet.RelativeMorphism.map s) := by rw [← Category.assoc]
        _ = fst _ _ ≫ SSet.const (X := (A : SSet.{u})) x := by
            have hs : A.ι ≫ SSet.RelativeMorphism.map s = SSet.const x := by
              have hcomm := s.comm
              simp only [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const] at hcomm
              exact hcomm
            rw [hs]
        _ = SSet.const (X := (A : SSet.{u}) ⊗ (B : SSet.{u})) x := by simp [SSet.comp_const]
    have h2 : ((A : SSet.{u}) ◁ B.ι) ≫ g₁ =
      SSet.const (X := (A : SSet.{u}) ⊗ (B : SSet.{u})) x := by
      calc ((A : SSet.{u}) ◁ B.ι) ≫ g₁
          = ((A : SSet.{u}) ◁ B.ι) ≫ (snd _ _ ≫ yonedaEquiv.symm p.edge) := rfl
        _ = (snd _ _ ≫ B.ι) ≫ yonedaEquiv.symm p.edge := by
            have : ((A : SSet.{u}) ◁ B.ι) ≫ snd _ _ = snd _ _ ≫ B.ι := rfl
            rw [← Category.assoc, this, Category.assoc]
        _ = snd _ _ ≫ (B.ι ≫ yonedaEquiv.symm p.edge) := by rw [← Category.assoc]
        _ = snd _ _ ≫ SSet.const (X := (B : SSet.{u})) x := by
            have h_B_ι_eq : B.ι =
              (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫ stdSimplex.δ 1 := by
              have hι : (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ B.ι = stdSimplex.δ 1 :=
                stdSimplex.faceSingletonComplIso_hom_ι (1 : Fin 2)
              calc B.ι = (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫
                (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ B.ι := by simp
                _ = (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫
                  stdSimplex.δ 1 := by rw [hι]
            have hBconst : B.ι ≫ yonedaEquiv.symm p.edge = SSet.const (X := (B : SSet.{u})) x := by
              calc B.ι ≫ yonedaEquiv.symm p.edge
                  = ((stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫ stdSimplex.δ 1) ≫
                    yonedaEquiv.symm p.edge := by rw [h_B_ι_eq]
                _ = (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫ (stdSimplex.δ 1 ≫
                  yonedaEquiv.symm p.edge) := by rw [Category.assoc]
                _ = (stdSimplex.faceSingletonComplIso (1 : Fin 2)).inv ≫
                  SSet.const (X := Δ[0]) x := by
                    rw [stdSimplex.δ_comp_yonedaEquiv_symm, p.src_eq, SSet.yonedaEquiv_symm_zero]
                _ = SSet.const (X := (B : SSet.{u})) x := by simp [SSet.comp_const]
            rw [hBconst]
        _ = SSet.const (X := (A : SSet.{u}) ⊗ (B : SSet.{u})) x := by simp [SSet.comp_const]
    rw [h1, h2]
  let f₀ : (A.unionProd B : SSet.{u}) ⟶ X := (Subcomplex.unionProd.isPushout A B).desc g₂ g₁ h_agree
  have hf₁ : Subcomplex.unionProd.ι₁ A B ≫ f₀ =
    g₂ := (Subcomplex.unionProd.isPushout A B).inl_desc _ _ _
  have hf₂ : Subcomplex.unionProd.ι₂ A B ≫ f₀ =
    g₁ := (Subcomplex.unionProd.isPushout A B).inr_desc _ _ _
  have hLift : HasLiftingProperty (A.unionProd B).ι (terminal.from X) := by
    apply hAnodyne
    rwa [← HomotopicalAlgebra.fibration_iff]
  have hSq : CommSq f₀ (A.unionProd B).ι (terminal.from X) (terminal.from _) := ⟨by simp⟩
  have hHasLift : hSq.HasLift := hLift.sq_hasLift hSq
  have : hSq.HasLift := hHasLift
  let prism : Δ[n] ⊗ Δ[1] ⟶ X := hSq.lift
  have hprism : (A.unionProd B).ι ≫ prism = f₀ := hSq.fac_left
  have h_boundary : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ prism = snd _ _ ≫ yonedaEquiv.symm p.edge := by
    have hι₂ : (A.ι ▷ (Δ[1] : SSet.{u})) = Subcomplex.unionProd.ι₂ A B ≫ (A.unionProd B).ι :=
      (Subcomplex.unionProd.ι₂_ι A B).symm
    calc (A.ι ▷ (Δ[1] : SSet.{u})) ≫ prism
        = (Subcomplex.unionProd.ι₂ A B ≫ (A.unionProd B).ι) ≫ prism := by rw [hι₂]
      _ = Subcomplex.unionProd.ι₂ A B ≫ ((A.unionProd B).ι ≫ prism) := by rw [Category.assoc]
      _ = Subcomplex.unionProd.ι₂ A B ≫ f₀ := by rw [hprism]
      _ = g₁ := hf₂
  have h_left : SSet.ι₀ (X := Δ[n]) ≫ prism = SSet.RelativeMorphism.map s := by
    have hι₀ : SSet.ι₀ (X := Δ[n]) =
      (stdSimplex.rightUnitor Δ[n]).inv ≫ (Δ[n] ◁ stdSimplex.δ (1 : Fin 2)) :=
      (stdSimplex.rightUnitor_inv_map_δ_one _).symm
    have hδ : stdSimplex.δ (1 : Fin 2) = (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ B.ι :=
      (stdSimplex.faceSingletonComplIso_hom_ι (1 : Fin 2)).symm
    have hW : Δ[n] ◁ ((stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ B.ι) =
        Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ Δ[n] ◁ B.ι :=
      MonoidalCategory.whiskerLeft_comp _ _ _
    have hι₁ : (Δ[n] ◁ B.ι) = Subcomplex.unionProd.ι₁ A B ≫ (A.unionProd B).ι :=
      (Subcomplex.unionProd.ι₁_ι A B).symm
    calc SSet.ι₀ ≫ prism
        = ((stdSimplex.rightUnitor Δ[n]).inv ≫ (Δ[n] ◁ stdSimplex.δ (1 : Fin 2))) ≫
          prism := by rw [hι₀]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫ ((Δ[n] ◁ stdSimplex.δ (1 : Fin 2)) ≫
        prism) := by rw [Category.assoc]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        ((Δ[n] ◁ ((stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ B.ι)) ≫ prism) := by rw [hδ]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        (((Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ Δ[n] ◁ B.ι) ≫
          prism)) := by rw [hW]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        (Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom) ≫ ((Δ[n] ◁ B.ι) ≫ prism) := by
          simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        (Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom) ≫
          ((Subcomplex.unionProd.ι₁ A B ≫ (A.unionProd B).ι) ≫ prism) := by rw [hι₁]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        (Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom) ≫ (Subcomplex.unionProd.ι₁ A B ≫
          ((A.unionProd B).ι ≫ prism)) := by
          simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        (Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom) ≫ (Subcomplex.unionProd.ι₁ A B ≫
          f₀) := by rw [hprism]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        (Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom) ≫ g₂ := by rw [hf₁]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        (Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom) ≫ fst _ _ ≫
          SSet.RelativeMorphism.map s := rfl
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫
        ((Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ fst _ _) ≫
          SSet.RelativeMorphism.map s) := by
          simp only [Category.assoc]
      _ = (stdSimplex.rightUnitor Δ[n]).inv ≫ (fst _ _ ≫ SSet.RelativeMorphism.map s) := by
          have hfst : Δ[n] ◁ (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫ fst _ _ =
            fst _ _ := by simp
          rw [hfst]
      _ = ((stdSimplex.rightUnitor Δ[n]).inv ≫ fst _ _) ≫
        SSet.RelativeMorphism.map s := by rw [Category.assoc]
      _ = SSet.RelativeMorphism.map s := by rw [stdSimplex.rightUnitor_inv_fst, Category.id_comp]
  let tMap : Δ[n] ⟶ X := SSet.ι₁ (X := Δ[n]) ≫ prism
  have ht_comm : (SSet.boundary n).ι ≫ tMap = SSet.const (X := (SSet.boundary n : SSet.{u})) y := by
    have hι₁comp : (SSet.boundary n).ι ≫ SSet.ι₁ (X := Δ[n]) =
      SSet.ι₁ (X := (A : SSet.{u})) ≫ (A.ι ▷ (Δ[1] : SSet.{u})) :=
      (SSet.ι₁_comp A.ι).symm
    calc (SSet.boundary n).ι ≫ tMap
        = (SSet.boundary n).ι ≫ (SSet.ι₁ (X := Δ[n]) ≫ prism) := rfl
      _ = ((SSet.boundary n).ι ≫ SSet.ι₁ (X := Δ[n])) ≫ prism := by rw [Category.assoc]
      _ = (SSet.ι₁ (X := (A : SSet.{u})) ≫ (A.ι ▷ (Δ[1] : SSet.{u}))) ≫ prism := by rw [hι₁comp]
      _ = SSet.ι₁ (X := (A : SSet.{u})) ≫ ((A.ι ▷ (Δ[1] : SSet.{u})) ≫
        prism) := by rw [Category.assoc]
      _ = SSet.ι₁ (X := (A : SSet.{u})) ≫ snd _ _ ≫ yonedaEquiv.symm p.edge := by rw [h_boundary]
      _ = SSet.const (X := (A : SSet.{u})) y := by
          have hι₁snd : SSet.ι₁ (X := (A : SSet.{u})) ≫ snd _ _ =
            SSet.const (X := (A : SSet.{u})) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
            SSet.ι₁_snd _
          have h1 : SSet.ι₁ (X := (A : SSet.{u})) ≫ snd _ _ ≫ yonedaEquiv.symm p.edge =
              SSet.const (X := (A : SSet.{u})) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
                yonedaEquiv.symm p.edge := by
            calc SSet.ι₁ (X := (A : SSet.{u})) ≫ snd _ _ ≫ yonedaEquiv.symm p.edge
                = (SSet.ι₁ (X := (A : SSet.{u})) ≫ snd _ _) ≫
                  yonedaEquiv.symm p.edge := by rw [Category.assoc]
              _ = SSet.const (X := (A : SSet.{u})) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
                yonedaEquiv.symm p.edge := by rw [hι₁snd]
          have h2 : SSet.const (X := (A : SSet.{u})) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
            yonedaEquiv.symm p.edge = SSet.const (X := (A : SSet.{u})) y := by
            rw [SSet.const_comp]
            congr 1
            have h_eq : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
              stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 2)) := by
              have h := stdSimplex.δ_zero_eq_const
              have hy : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]) =
                SSet.yonedaEquiv (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : Δ[0] ⟶ Δ[1])
                  := congrArg SSet.yonedaEquiv h
              simp [SSet.yonedaEquiv_const] at hy
              exact hy.symm
            rw [h_eq]
            have h_app : (SSet.yonedaEquiv.symm p.edge).app (Opposite.op ⦋0⦌)
              (stdSimplex.objEquiv.symm (SimplexCategory.δ (0 : Fin 2))) =
                X.δ (0 : Fin 2) p.edge := rfl
            rw [h_app, p.tgt_eq]
          rw [h1, h2]
  let t : X.PtSimplex n y := ⟨tMap, ht_comm⟩
  have h_right : SSet.ι₁ (X := Δ[n]) ≫ prism = SSet.RelativeMorphism.map t := rfl
  exact ⟨t, ⟨⟨prism, h_boundary, h_left, h_right⟩⟩⟩

-- Uniqueness: two targets for same p,s are RelStruct₀-related via two-parameter prism
theorem ActionStruct.unique {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    {p : Edge x y} {s : X.PtSimplex n x} {t₁ t₂ : X.PtSimplex n y}
    (h₁ : ActionStruct p s t₁) (h₂ : ActionStruct p s t₂) :
    Nonempty (t₁.RelStruct₀ t₂) := by
  let A_sub : (Δ[n] : SSet.{u}).Subcomplex := SSet.boundary n
  let A : SSet.{u} := (A_sub : SSet.{u})
  let H : SSet.{u} := (ihom (Δ[n] : SSet.{u})).obj X
  let K : SSet.{u} := (ihom A).obj X
  let r : H ⟶ K := (MonoidalClosed.pre A_sub.ι).app X
  have : Fibration r := inferInstance
  let e₁ : Δ[1] ⟶ H := MonoidalClosed.curry h₁.prism
  let e₂ : Δ[1] ⟶ H := MonoidalClosed.curry h₂.prism
  let q : Δ[1] ⟶ K :=
    MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫ yonedaEquiv.symm (Edge.edge p))
  have he₁ : e₁ ≫ r = q := by
    simp only [e₁, r, q]
    rw [MonoidalClosed.curry_pre_app]
    rw [h₁.boundary]
  have he₂ : e₂ ≫ r = q := by
    simp only [e₂, r, q]
    rw [MonoidalClosed.curry_pre_app]
    rw [h₂.boundary]
  let b : Δ[2] ⟶ K := stdSimplex.σ (1 : Fin 2) ≫ q
  have h_src : stdSimplex.δ (1 : Fin 2) ≫ e₁ = stdSimplex.δ (1 : Fin 2) ≫ e₂ := by
    have h1 : stdSimplex.δ (1 : Fin 2) ≫ e₁ =
        MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
          SSet.RelativeMorphism.map s) := by
      calc stdSimplex.δ (1 : Fin 2) ≫ e₁
          = stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry h₁.prism := rfl
        _ = MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (1 : Fin 2)) ≫ h₁.prism) := by
            rw [← MonoidalClosed.curry_natural_left]
        _ = MonoidalClosed.curry (((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            SSet.ι₀ (X := (Δ[n] : SSet.{u}))) ≫ h₁.prism) := by
            rw [← SSet.stdSimplex.rightUnitor_hom_ι₀]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            (SSet.ι₀ (X := (Δ[n] : SSet.{u})) ≫ h₁.prism)) := by
            rw [Category.assoc]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            SSet.RelativeMorphism.map s) := by rw [h₁.left]
    have h2 : stdSimplex.δ (1 : Fin 2) ≫ e₂ =
        MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
          SSet.RelativeMorphism.map s) := by
      calc stdSimplex.δ (1 : Fin 2) ≫ e₂
          = stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry h₂.prism := rfl
        _ = MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (1 : Fin 2)) ≫ h₂.prism) := by
            rw [← MonoidalClosed.curry_natural_left]
        _ = MonoidalClosed.curry (((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            SSet.ι₀ (X := (Δ[n] : SSet.{u}))) ≫ h₂.prism) := by
            rw [← SSet.stdSimplex.rightUnitor_hom_ι₀]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            (SSet.ι₀ (X := (Δ[n] : SSet.{u})) ≫ h₂.prism)) := by
            rw [Category.assoc]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            SSet.RelativeMorphism.map s) := by rw [h₂.left]
    rw [h1, h2]
  let f : (j : Fin 3) → (hj : j ≠ (0 : Fin 3)) → (Δ[1] ⟶ H) := fun j hj =>
    match j with
    | 0 => False.elim (hj rfl)
    | 1 => e₂
    | 2 => e₁
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    have hj_ne : j.val ≠ 0 := by
      intro h
      exact hj (Fin.eq_of_val_eq h)
    have hk_ne : k.val ≠ 0 := by
      intro h
      exact hk (Fin.eq_of_val_eq h)
    have hjk_val : j.val < k.val := hjk
    have hj_val : j.val = 1 := by omega
    have hk_val : k.val = 2 := by omega
    have hj_eq : j = (1 : Fin 3) := Fin.eq_of_val_eq hj_val
    have hk_eq : k = (2 : Fin 3) := Fin.eq_of_val_eq hk_val
    subst hj_eq
    subst hk_eq
    simp [f, h_src.symm]
  have hb : ∀ (j : Fin 3) (hj : j ≠ (0 : Fin 3)), f j hj ≫ r = stdSimplex.δ j ≫ b := by
    intro j hj
    have hj_ne : j.val ≠ 0 := by
      intro h
      exact hj (Fin.eq_of_val_eq h)
    have hj_val : j.val = 1 ∨ j.val = 2 := by omega
    rcases hj_val with hj1 | hj2
    · have hj_eq : j = (1 : Fin 3) := Fin.eq_of_val_eq hj1
      subst hj_eq
      simp only [f, he₂, b]
      have h1 : stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) := by
        have h : (1 : Fin 3) = Fin.castSucc (1 : Fin 2) := rfl
        rw [h, stdSimplex.δ_comp_σ_self]
      calc MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge)
          = 𝟙 _ ≫ MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge) := by simp
        _ = (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2)) ≫
            MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge) := by rw [h1]
        _ = stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) ≫
            MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge) := by
            rw [Category.assoc]
    · have hj_eq : j = (2 : Fin 3) := Fin.eq_of_val_eq hj2
      subst hj_eq
      simp only [f, he₁, b]
      have h1 : stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) := by
        have h : (2 : Fin 3) = Fin.succ (1 : Fin 2) := rfl
        rw [h, stdSimplex.δ_comp_σ_succ]
      calc MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge)
          = 𝟙 _ ≫ MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge) := by simp
        _ = (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2)) ≫
            MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge) := by rw [h1]
        _ = stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) ≫
            MonoidalClosed.curry (snd A Δ[1] ≫ yonedaEquiv.symm p.edge) := by
            rw [Category.assoc]
  obtain ⟨F, hF⟩ := hf.exists_lift r b hb
  have hF_eq : ∀ (j : Fin 3) (hj : j ≠ (0 : Fin 3)), stdSimplex.δ j ≫ F = f j hj :=
    hF.1
  have hF_r : F ≫ r = b := hF.2
  let e₀ : Δ[1] ⟶ H := stdSimplex.δ (0 : Fin 3) ≫ F
  let hMap : Δ[n] ⊗ Δ[1] ⟶ X := MonoidalClosed.uncurry e₀
  have h_left : SSet.ι₀ (X := Δ[n]) ≫ hMap = SSet.RelativeMorphism.map t₁ := by
    have hF2 : stdSimplex.δ (2 : Fin 3) ≫ F = e₁ := hF_eq 2 (by decide)
    have h_e0_src : stdSimplex.δ (1 : Fin 2) ≫ e₀ = stdSimplex.δ (0 : Fin 2) ≫ e₁ := by
      calc stdSimplex.δ (1 : Fin 2) ≫ e₀
          = stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (Fin.castSucc (0 : Fin 2)) ≫ F) := rfl
        _ = (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (Fin.castSucc (0 : Fin 2))) ≫
          F := by rw [Category.assoc]
        _ = (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (Fin.succ (1 : Fin 2))) ≫ F := by
            rw [← SSet.stdSimplex.δ_comp_δ (by decide : (0 : Fin 2) ≤ 1)]
        _ = stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (Fin.succ (1 : Fin 2)) ≫
          F) := by rw [← Category.assoc]
        _ = stdSimplex.δ (0 : Fin 2) ≫ e₁ := by
            have h2 : stdSimplex.δ (Fin.succ (1 : Fin 2)) = stdSimplex.δ (2 : Fin 3) := rfl
            rw [h2, hF2]
    calc SSet.ι₀ ≫ hMap
        = SSet.ι₀ ≫ MonoidalClosed.uncurry e₀ := rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
        MonoidalClosed.uncurry (stdSimplex.δ (1 : Fin 2) ≫ e₀) := by
          rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_one]
          rw [Category.assoc]
          rw [← MonoidalClosed.uncurry_natural_left]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
        MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫ e₁) := by rw [h_e0_src]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
        MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry h₁.prism) := rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
        MonoidalClosed.uncurry (MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (0 : Fin 2)) ≫
          h₁.prism)) := by rw [← MonoidalClosed.curry_natural_left]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫ ((Δ[n] ◁ stdSimplex.δ (0 : Fin 2)) ≫
        h₁.prism) := by rw [MonoidalClosed.uncurry_curry]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            SSet.ι₁ ≫ h₁.prism) := by
          simp
      _ = SSet.ι₁ ≫ h₁.prism := by simp
      _ = SSet.RelativeMorphism.map t₁ := h₁.right
  have h_right : SSet.ι₁ (X := Δ[n]) ≫ hMap = SSet.RelativeMorphism.map t₂ := by
    have hF1 : stdSimplex.δ (1 : Fin 3) ≫ F = e₂ := hF_eq 1 (by decide)
    have h_e0_tgt : stdSimplex.δ (0 : Fin 2) ≫ e₀ = stdSimplex.δ (0 : Fin 2) ≫ e₂ := by
      calc stdSimplex.δ (0 : Fin 2) ≫ e₀
          = stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (Fin.castSucc (0 : Fin 2)) ≫ F) := rfl
        _ = (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (Fin.castSucc (0 : Fin 2))) ≫
          F := by rw [Category.assoc]
        _ = (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (Fin.succ (0 : Fin 2))) ≫ F := by
            rw [SSet.stdSimplex.δ_comp_δ_self (n := 0) (i := (0 : Fin 2))]
        _ = stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (Fin.succ (0 : Fin 2)) ≫
          F) := by rw [← Category.assoc]
        _ = stdSimplex.δ (0 : Fin 2) ≫ e₂ := by
            have h2 : stdSimplex.δ (Fin.succ (0 : Fin 2)) = stdSimplex.δ (1 : Fin 3) := rfl
            rw [h2, hF1]
    calc SSet.ι₁ ≫ hMap
        = SSet.ι₁ ≫ MonoidalClosed.uncurry e₀ := rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫ e₀) := by
          rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_zero]
          rw [Category.assoc]
          rw [← MonoidalClosed.uncurry_natural_left]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫ e₂) := by rw [h_e0_tgt]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry h₂.prism) := rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            MonoidalClosed.uncurry (MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (0 : Fin 2)) ≫
              h₂.prism)) := by
          rw [← MonoidalClosed.curry_natural_left]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            ((Δ[n] ◁ stdSimplex.δ (0 : Fin 2)) ≫ h₂.prism) := by rw [MonoidalClosed.uncurry_curry]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
            ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫ SSet.ι₁ ≫ h₂.prism) := by
          rw [← SSet.stdSimplex.rightUnitor_hom_ι₁_assoc]
      _ = SSet.ι₁ ≫ h₂.prism := by simp
      _ = SSet.RelativeMorphism.map t₂ := h₂.right
  have h_rel : (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ hMap =
      SSet.const (X := (SSet.boundary n : SSet.{u}) ⊗ Δ[1]) y := by
    have h_uncurry_pre : (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ hMap =
        MonoidalClosed.uncurry (e₀ ≫ r) := by
      rw [← MonoidalClosed.uncurry_pre_app]
    have h_e0_r : e₀ ≫ r = stdSimplex.δ (0 : Fin 3) ≫ b := by
      calc e₀ ≫ r = (stdSimplex.δ (0 : Fin 3) ≫ F) ≫ r := by dsimp only [e₀]
        _ = stdSimplex.δ (0 : Fin 3) ≫ (F ≫ r) := by rw [Category.assoc]
        _ = stdSimplex.δ (0 : Fin 3) ≫ b := by rw [hF_r]
    have h_delta_sigma : stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) =
        stdSimplex.σ (0 : Fin 1) ≫ stdSimplex.δ (0 : Fin 2) :=
      stdSimplex.δ_comp_σ_of_le (n := 0) (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide)
    have h_uncurry_q : MonoidalClosed.uncurry q =
        snd A (Δ[1] : SSet.{u}) ≫ yonedaEquiv.symm (Edge.edge p) := by
      simp only [q]
      rw [MonoidalClosed.uncurry_curry]
    calc (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ hMap
        = MonoidalClosed.uncurry (e₀ ≫ r) := h_uncurry_pre
      _ = MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 3) ≫ b) := by rw [h_e0_r]
      _ = MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) ≫ q) := rfl
      _ = MonoidalClosed.uncurry (stdSimplex.σ (0 : Fin 1) ≫ stdSimplex.δ (0 : Fin 2) ≫ q) := by
          congr 1
          rw [← Category.assoc, h_delta_sigma, Category.assoc]
      _ = (A ◁ stdSimplex.σ (0 : Fin 1)) ≫ MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫
        q) := by
          simp [MonoidalClosed.uncurry_natural_left]
      _ = (A ◁ stdSimplex.σ (0 : Fin 1)) ≫ (A ◁ stdSimplex.δ (0 : Fin 2)) ≫
        MonoidalClosed.uncurry q := by
          simp [MonoidalClosed.uncurry_natural_left]
      _ = (A ◁ stdSimplex.σ (0 : Fin 1)) ≫ (A ◁ stdSimplex.δ (0 : Fin 2)) ≫
            (snd A (Δ[1] : SSet.{u}) ≫ yonedaEquiv.symm (Edge.edge p)) := by rw [h_uncurry_q]
      _ = (A ◁ stdSimplex.σ (0 : Fin 1)) ≫
            (snd A (Δ[0] : SSet.{u}) ≫ stdSimplex.δ (0 : Fin 2)) ≫
              yonedaEquiv.symm (Edge.edge p) := by
          have h_nat : A ◁ stdSimplex.δ (0 : Fin 2) ≫ snd A (Δ[1] : SSet.{u}) =
              snd A (Δ[0] : SSet.{u}) ≫ stdSimplex.δ (0 : Fin 2) := by simp
          simp [Category.assoc]
      _ = (A ◁ stdSimplex.σ (0 : Fin 1)) ≫ snd A (Δ[0] : SSet.{u}) ≫
            (stdSimplex.δ (0 : Fin 2) ≫
              yonedaEquiv.symm (Edge.edge p)) := by simp only [Category.assoc]
      _ = (A ◁ stdSimplex.σ (0 : Fin 1)) ≫ snd A (Δ[0] : SSet.{u}) ≫
            SSet.const (X := Δ[0]) y := by
          simp [stdSimplex.δ_comp_yonedaEquiv_symm, p.tgt_eq, SSet.yonedaEquiv_symm_zero]
      _ = SSet.const (X := A ⊗ Δ[1]) y := by simp [SSet.comp_const]
  exact ⟨SSet.PtSimplex.Homotopy.relStruct₀ ⟨hMap, h_left, h_right, h_rel⟩⟩

-- Composition of actions via inner horn filling
noncomputable def ActionStruct.comp
    {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    {s₀ : X.PtSimplex n x₀} {s₁ : X.PtSimplex n x₁} {s₂ : X.PtSimplex n x₂}
    (he : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : ActionStruct e₀₁ s₀ s₁) (h₁₂ : ActionStruct e₁₂ s₁ s₂) :
    ActionStruct e₀₂ s₀ s₂ := by
  let A_sub : (Δ[n] : SSet.{u}).Subcomplex := SSet.boundary n
  let A : SSet.{u} := (A_sub : SSet.{u})
  let H : SSet.{u} := (ihom (Δ[n] : SSet.{u})).obj X
  let K : SSet.{u} := (ihom A).obj X
  let r : H ⟶ K := (MonoidalClosed.pre A_sub.ι).app X
  have : Fibration r := inferInstance
  let e₀₁' : Δ[1] ⟶ H := MonoidalClosed.curry h₀₁.prism
  let e₁₂' : Δ[1] ⟶ H := MonoidalClosed.curry h₁₂.prism
  let b : Δ[2] ⟶ K :=
    MonoidalClosed.curry (snd A (Δ[2] : SSet.{u}) ≫ yonedaEquiv.symm he.simplex)
  have he₀₁' : e₀₁' ≫ r = stdSimplex.δ (2 : Fin 3) ≫ b := by
    calc e₀₁' ≫ r
        = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
            yonedaEquiv.symm (Edge.edge e₀₁)) := by
          simp only [e₀₁', r]
          rw [MonoidalClosed.curry_pre_app, h₀₁.boundary]
      _ = stdSimplex.δ (2 : Fin 3) ≫ b := by
          simp only [b]
          calc MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                yonedaEquiv.symm (Edge.edge e₀₁))
              = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                  yonedaEquiv.symm (X.δ 2 he.simplex)) := by rw [he.d₂]
            _ = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                  (stdSimplex.δ (2 : Fin 3) ≫ yonedaEquiv.symm he.simplex)) := by
                rw [← stdSimplex.δ_comp_yonedaEquiv_symm]
            _ = MonoidalClosed.curry ((snd A (Δ[1] : SSet.{u}) ≫
                  stdSimplex.δ (2 : Fin 3)) ≫ yonedaEquiv.symm he.simplex) := by
                rw [Category.assoc]
            _ = MonoidalClosed.curry (((A ◁ stdSimplex.δ (2 : Fin 3)) ≫
                    snd A (Δ[2] : SSet.{u})) ≫ yonedaEquiv.symm he.simplex) := by
                have h_eq : snd A (Δ[1] : SSet.{u}) ≫
                    stdSimplex.δ (2 : Fin 3) =
                    (A ◁ stdSimplex.δ (2 : Fin 3)) ≫ snd A (Δ[2] : SSet.{u}) := by
                  ext n x
                  simp
                rw [h_eq]
            _ = MonoidalClosed.curry ((A ◁ stdSimplex.δ (2 : Fin 3)) ≫
                    (snd A (Δ[2] : SSet.{u}) ≫ yonedaEquiv.symm he.simplex)) := by
                rw [← Category.assoc]
            _ = stdSimplex.δ (2 : Fin 3) ≫
                  MonoidalClosed.curry (snd A (Δ[2] : SSet.{u}) ≫
                    yonedaEquiv.symm he.simplex) := by
                rw [MonoidalClosed.curry_natural_left]
  have he₁₂' : e₁₂' ≫ r = stdSimplex.δ (0 : Fin 3) ≫ b := by
    calc e₁₂' ≫ r
        = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
            yonedaEquiv.symm (Edge.edge e₁₂)) := by
          simp only [e₁₂', r]
          rw [MonoidalClosed.curry_pre_app, h₁₂.boundary]
      _ = stdSimplex.δ (0 : Fin 3) ≫ b := by
          simp only [b]
          calc MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                yonedaEquiv.symm (Edge.edge e₁₂))
              = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                  yonedaEquiv.symm (X.δ 0 he.simplex)) := by rw [he.d₀]
            _ = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                  (stdSimplex.δ (0 : Fin 3) ≫ yonedaEquiv.symm he.simplex)) := by
                rw [← stdSimplex.δ_comp_yonedaEquiv_symm]
            _ = MonoidalClosed.curry ((snd A (Δ[1] : SSet.{u}) ≫
                  stdSimplex.δ (0 : Fin 3)) ≫ yonedaEquiv.symm he.simplex) := by
                rw [Category.assoc]
            _ = MonoidalClosed.curry (((A ◁ stdSimplex.δ (0 : Fin 3)) ≫
                    snd A (Δ[2] : SSet.{u})) ≫ yonedaEquiv.symm he.simplex) := by
                have h_eq : snd A (Δ[1] : SSet.{u}) ≫
                    stdSimplex.δ (0 : Fin 3) =
                    (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ snd A (Δ[2] : SSet.{u}) := by
                  ext n x
                  simp
                rw [h_eq]
            _ = MonoidalClosed.curry ((A ◁ stdSimplex.δ (0 : Fin 3)) ≫
                    (snd A (Δ[2] : SSet.{u}) ≫ yonedaEquiv.symm he.simplex)) := by
                rw [← Category.assoc]
            _ = stdSimplex.δ (0 : Fin 3) ≫
                  MonoidalClosed.curry (snd A (Δ[2] : SSet.{u}) ≫
                    yonedaEquiv.symm he.simplex) := by
                rw [MonoidalClosed.curry_natural_left]
  have hcompat : stdSimplex.δ (1 : Fin 2) ≫ e₁₂' =
      stdSimplex.δ (0 : Fin 2) ≫ e₀₁' := by
    have h1 : stdSimplex.δ (1 : Fin 2) ≫ e₁₂' =
        MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
          SSet.RelativeMorphism.map s₁) := by
      calc stdSimplex.δ (1 : Fin 2) ≫ e₁₂'
          = stdSimplex.δ (1 : Fin 2) ≫ MonoidalClosed.curry h₁₂.prism := rfl
        _ = MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (1 : Fin 2)) ≫ h₁₂.prism) := by
            rw [← MonoidalClosed.curry_natural_left]
        _ = MonoidalClosed.curry
              (((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫ SSet.ι₀) ≫
                h₁₂.prism) := by rw [← SSet.stdSimplex.rightUnitor_hom_ι₀]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
              (SSet.ι₀ ≫ h₁₂.prism)) := by rw [Category.assoc]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
              SSet.RelativeMorphism.map s₁) := by rw [h₁₂.left]
    have h2 : stdSimplex.δ (0 : Fin 2) ≫ e₀₁' =
        MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
          SSet.RelativeMorphism.map s₁) := by
      calc stdSimplex.δ (0 : Fin 2) ≫ e₀₁'
          = stdSimplex.δ (0 : Fin 2) ≫ MonoidalClosed.curry h₀₁.prism := rfl
        _ = MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (0 : Fin 2)) ≫ h₀₁.prism) := by
            rw [← MonoidalClosed.curry_natural_left]
        _ = MonoidalClosed.curry
              (((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫ SSet.ι₁) ≫
                h₀₁.prism) := by rw [← SSet.stdSimplex.rightUnitor_hom_ι₁]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
              (SSet.ι₁ ≫ h₀₁.prism)) := by rw [Category.assoc]
        _ = MonoidalClosed.curry ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
              SSet.RelativeMorphism.map s₁) := by rw [h₀₁.right]
    rw [h1, h2]
  let f : (j : Fin 3) → (hj : j ≠ (1 : Fin 3)) → (Δ[1] ⟶ H) := fun j hj =>
    match j with
    | 0 => e₁₂'
    | 1 => False.elim (hj rfl)
    | 2 => e₀₁'
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    have hj_ne : j.val ≠ 1 := by
      intro h
      exact hj (Fin.eq_of_val_eq h)
    have hk_ne : k.val ≠ 1 := by
      intro h
      exact hk (Fin.eq_of_val_eq h)
    have hj0 : j.val = 0 := by omega
    have hk2 : k.val = 2 := by omega
    have hj_eq : j = 0 := Fin.eq_of_val_eq hj0
    have hk_eq : k = 2 := Fin.eq_of_val_eq hk2
    subst hj_eq
    subst hk_eq
    simp only [f]
    exact hcompat
  have hb : ∀ (j : Fin 3) (hj : j ≠ (1 : Fin 3)),
      f j hj ≫ r = stdSimplex.δ j ≫ b := by
    intro j hj
    fin_cases j
    · simp [f, he₁₂']
    · exact False.elim (hj rfl)
    · simp [f, he₀₁']
  let F : Δ[2] ⟶ H := hf.lift r b hb
  have hF₀ : stdSimplex.δ (0 : Fin 3) ≫ F = e₁₂' := by
    have := hf.δ_lift (j := (0 : Fin 3)) r b hb (by decide)
    simpa [f] using this
  have hF₂ : stdSimplex.δ (2 : Fin 3) ≫ F = e₀₁' := by
    have := hf.δ_lift (j := (2 : Fin 3)) r b hb (by decide)
    simpa [f] using this
  have hFr : F ≫ r = b := hf.lift_comp r b hb
  let e₀₂' : Δ[1] ⟶ H := stdSimplex.δ (1 : Fin 3) ≫ F
  let prism : Δ[n] ⊗ Δ[1] ⟶ X := MonoidalClosed.uncurry e₀₂'
  have h_left : SSet.ι₀ ≫ prism = SSet.RelativeMorphism.map s₀ := by
    have hδ₁ : stdSimplex.δ (1 : Fin 2) ≫ e₀₂' =
        stdSimplex.δ (1 : Fin 2) ≫ e₀₁' := by
      calc stdSimplex.δ (1 : Fin 2) ≫ e₀₂'
          = stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (1 : Fin 3) ≫ F) := rfl
        _ = stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (Fin.castSucc (1 : Fin 2)) ≫ F) := by
            have h : (1 : Fin 3) = Fin.castSucc (1 : Fin 2) := by decide
            rw [h]
        _ = (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (Fin.castSucc (1 : Fin 2))) ≫ F := by
            rw [Category.assoc]
        _ = (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (Fin.succ (1 : Fin 2))) ≫ F := by
            have h_eq : stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (Fin.castSucc (1 : Fin 2)) =
              stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (Fin.succ (1 : Fin 2)) :=
              CosimplicialObject.δ_comp_δ_self (X := SSet.stdSimplex) (i := (1 : Fin 2))
            rw [h_eq]
        _ = (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3)) ≫ F := by
            have h : Fin.succ (1 : Fin 2) = (2 : Fin 3) := by decide
            rw [h]
        _ = stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (2 : Fin 3) ≫ F) := by
            rw [← Category.assoc]
        _ = stdSimplex.δ (1 : Fin 2) ≫ e₀₁' := by rw [hF₂]
    calc SSet.ι₀ ≫ prism
        = SSet.ι₀ ≫ MonoidalClosed.uncurry e₀₂' := rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          MonoidalClosed.uncurry (stdSimplex.δ (1 : Fin 2) ≫ e₀₂') := by
          rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_one, Category.assoc,
            ← MonoidalClosed.uncurry_natural_left]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          MonoidalClosed.uncurry (stdSimplex.δ (1 : Fin 2) ≫ e₀₁') := by rw [hδ₁]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          MonoidalClosed.uncurry
            (MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (1 : Fin 2)) ≫ h₀₁.prism)) := by
            rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          ((Δ[n] ◁ stdSimplex.δ (1 : Fin 2)) ≫ h₀₁.prism) := by
            rw [MonoidalClosed.uncurry_curry]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            SSet.ι₀) ≫ h₀₁.prism := by
          rw [← SSet.stdSimplex.rightUnitor_hom_ι₀]
      _ = SSet.ι₀ ≫ h₀₁.prism := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = SSet.RelativeMorphism.map s₀ := h₀₁.left
  have h_right : SSet.ι₁ ≫ prism = SSet.RelativeMorphism.map s₂ := by
    have hδ₀ : stdSimplex.δ (0 : Fin 2) ≫ e₀₂' =
        stdSimplex.δ (0 : Fin 2) ≫ e₁₂' := by
      calc stdSimplex.δ (0 : Fin 2) ≫ e₀₂'
          = stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (1 : Fin 3) ≫ F) := rfl
        _ = stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (Fin.succ (0 : Fin 2)) ≫ F) := by
            have h : (1 : Fin 3) = Fin.succ (0 : Fin 2) := by decide
            rw [h]
        _ = (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (Fin.succ (0 : Fin 2))) ≫ F := by
            rw [Category.assoc]
        _ = (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (Fin.castSucc (0 : Fin 2))) ≫ F := by
            have h_eq : stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (Fin.succ (0 : Fin 2)) =
              stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (Fin.castSucc (0 : Fin 2)) :=
              (CosimplicialObject.δ_comp_δ_self (X := SSet.stdSimplex) (i := (0 : Fin 2))).symm
            rw [h_eq]
        _ = (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3)) ≫ F := by
            have h : Fin.castSucc (0 : Fin 2) = (0 : Fin 3) := by decide
            rw [h]
        _ = stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (0 : Fin 3) ≫ F) := by
            rw [← Category.assoc]
        _ = stdSimplex.δ (0 : Fin 2) ≫ e₁₂' := by rw [hF₀]
    calc SSet.ι₁ ≫ prism
        = SSet.ι₁ ≫ MonoidalClosed.uncurry e₀₂' := rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫ e₀₂') := by
          rw [← SSet.stdSimplex.rightUnitor_inv_map_δ_zero, Category.assoc,
            ← MonoidalClosed.uncurry_natural_left]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          MonoidalClosed.uncurry (stdSimplex.δ (0 : Fin 2) ≫ e₁₂') := by rw [hδ₀]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          MonoidalClosed.uncurry
            (MonoidalClosed.curry ((Δ[n] ◁ stdSimplex.δ (0 : Fin 2)) ≫ h₁₂.prism)) := by
            rfl
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          ((Δ[n] ◁ stdSimplex.δ (0 : Fin 2)) ≫ h₁₂.prism) := by
            rw [MonoidalClosed.uncurry_curry]
      _ = (SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).inv ≫
          ((SSet.stdSimplex.rightUnitor (Δ[n] : SSet.{u})).hom ≫
            SSet.ι₁) ≫ h₁₂.prism := by
          rw [← SSet.stdSimplex.rightUnitor_hom_ι₁]
      _ = SSet.ι₁ ≫ h₁₂.prism := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = SSet.RelativeMorphism.map s₂ := h₁₂.right
  have h_boundary : (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ prism =
      snd _ _ ≫ yonedaEquiv.symm (Edge.edge e₀₂) := by
    have h_uncurry : (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ prism =
        MonoidalClosed.uncurry (e₀₂' ≫ r) := by
      rw [← MonoidalClosed.uncurry_pre_app]
    have he₀₂ : e₀₂' ≫ r = stdSimplex.δ (1 : Fin 3) ≫ b := by
      calc e₀₂' ≫ r = (stdSimplex.δ (1 : Fin 3) ≫ F) ≫ r := rfl
        _ = stdSimplex.δ (1 : Fin 3) ≫ (F ≫ r) := by rw [Category.assoc]
        _ = stdSimplex.δ (1 : Fin 3) ≫ b := by rw [hFr]
    have hδ : stdSimplex.δ (1 : Fin 3) ≫ b =
        MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
          yonedaEquiv.symm (Edge.edge e₀₂)) := by
      calc stdSimplex.δ (1 : Fin 3) ≫ b
          = stdSimplex.δ (1 : Fin 3) ≫
              MonoidalClosed.curry (snd A (Δ[2] : SSet.{u}) ≫
                yonedaEquiv.symm he.simplex) := rfl
        _ = MonoidalClosed.curry ((A ◁ stdSimplex.δ (1 : Fin 3)) ≫
              snd A (Δ[2] : SSet.{u}) ≫ yonedaEquiv.symm he.simplex) := by
              rw [← MonoidalClosed.curry_natural_left]
        _ = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
              yonedaEquiv.symm (Edge.edge e₀₂)) := by
              calc MonoidalClosed.curry ((A ◁ stdSimplex.δ (1 : Fin 3)) ≫
                    snd A (Δ[2] : SSet.{u}) ≫ yonedaEquiv.symm he.simplex)
                  = MonoidalClosed.curry (((A ◁ stdSimplex.δ (1 : Fin 3)) ≫
                        snd A (Δ[2] : SSet.{u})) ≫ yonedaEquiv.symm he.simplex) := by
                    rw [Category.assoc]
                _ = MonoidalClosed.curry ((snd A (Δ[1] : SSet.{u}) ≫
                        stdSimplex.δ (1 : Fin 3)) ≫ yonedaEquiv.symm he.simplex) := by
                    have h_eq : (A ◁ stdSimplex.δ (1 : Fin 3)) ≫
                        snd A (Δ[2] : SSet.{u}) =
                        snd A (Δ[1] : SSet.{u}) ≫ stdSimplex.δ (1 : Fin 3) := by
                      ext n x
                      simp
                    rw [h_eq]
                _ = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                      (stdSimplex.δ (1 : Fin 3) ≫ yonedaEquiv.symm he.simplex)) := by
                    rw [← Category.assoc]
                _ = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                      yonedaEquiv.symm (X.δ 1 he.simplex)) := by
                    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
                _ = MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
                      yonedaEquiv.symm (Edge.edge e₀₂)) := by rw [he.d₁]
    calc (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ prism
        = MonoidalClosed.uncurry (e₀₂' ≫ r) := h_uncurry
      _ = MonoidalClosed.uncurry (stdSimplex.δ (1 : Fin 3) ≫ b) := by rw [he₀₂]
      _ = MonoidalClosed.uncurry
            (MonoidalClosed.curry (snd A (Δ[1] : SSet.{u}) ≫
              yonedaEquiv.symm (Edge.edge e₀₂))) := by rw [hδ]
      _ = snd _ _ ≫ yonedaEquiv.symm (Edge.edge e₀₂) := by
            rw [MonoidalClosed.uncurry_curry]
  exact ⟨prism, h_boundary, h_left, h_right⟩


noncomputable def ActionStruct.ofRelStruct₀
    {p q : X.PtSimplex n x} (h : p.RelStruct₀ q) :
    ActionStruct (Edge.id x) p q where
  prism := h.homotopy.h
  left := h.homotopy.h₀
  right := h.homotopy.h₁
  boundary := by
    have hr := h.homotopy.rel
    have h1 : (SSet.boundary n).ι ▷ (Δ[1] : SSet.{u}) ≫ h.homotopy.h =
        SSet.const (X := (SSet.boundary n : SSet.{u}) ⊗ Δ[1]) x := by
      rw [hr]
      simp [SSet.Subcomplex.ofSimplex_ι, SSet.comp_const]
    have h2 : snd _ _ ≫ yonedaEquiv.symm (Edge.edge (Edge.id x)) =
        SSet.const (X := (SSet.boundary n : SSet.{u}) ⊗ Δ[1]) x := by
      have hid : Edge.edge (Edge.id x) = X.σ 0 x := by
        simp [Edge.id_edge]
      calc snd _ _ ≫ yonedaEquiv.symm (Edge.edge (Edge.id x))
          = snd _ _ ≫ yonedaEquiv.symm (X.σ 0 x) := by rw [hid]
        _ = snd _ _ ≫ SSet.const x := by
            have : yonedaEquiv.symm (X.σ 0 x) = SSet.const x := by
              rw [← stdSimplex.σ_comp_yonedaEquiv_symm, yonedaEquiv_symm_zero, comp_const]
            rw [this]
        _ = SSet.const (X := (SSet.boundary n : SSet.{u}) ⊗ Δ[1]) x := by
            simp [SSet.comp_const]
    rw [h1, h2]

end FundamentalGroupoid

end KanComplex

end SSet

end

public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra Limits
open scoped SSet.modelCategoryQuillen
open scoped Simplicial

namespace SSet

namespace KanComplex

namespace π

variable {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] {n : ℕ} {x y z : X _⦋0⦌}

/-
Raw basepoint transport is isolated in chosen fillers.
The public surface below (`action`, `actionEquiv`, bijectivity, naturality)
is what later `W` lemmas need. Names are chosen to adapt to PR #42587
pseudofunctor API (`action`/`actionEquiv`/`actionFunctor`).
Raw helpers are intentionally not exposed as public API; they are kept
private-conceptually (named with `raw` prefix) to allow later replacement.
-/

-- Genuine raw horn filler via chosen target from exists_actionStruct
private noncomputable def rawHornFiller (X : SSet.{u}) [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (e : Edge x y) (p : X.PtSimplex n x) : X.PtSimplex n y :=
  (FundamentalGroupoid.exists_actionStruct e p).choose

-- Conceptually private; kept module-internal via `raw` naming.
private noncomputable def rawTransportPtSimplex {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (e : Edge x y) (p : X.PtSimplex n x) : X.PtSimplex n y :=
  rawHornFiller X e p

private noncomputable def rawTransportActionStruct {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X
  _⦋0⦌}
    (e : Edge x y) (p : X.PtSimplex n x) :
    FundamentalGroupoid.ActionStruct e p (rawTransportPtSimplex e p) := by
  unfold rawTransportPtSimplex rawHornFiller
  exact (FundamentalGroupoid.exists_actionStruct e p).choose_spec.some

private lemma rawTransport_compat {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (e : Edge x y) {p q : X.PtSimplex n x}
    (h : Nonempty (p.RelStruct₀ q)) :
    Nonempty ((rawTransportPtSimplex (X := X) e p).RelStruct₀ (rawTransportPtSimplex (X := X) e q))
      := by
  obtain ⟨h⟩ := h
  let hRel : FundamentalGroupoid.ActionStruct (Edge.id x) p q :=
    FundamentalGroupoid.ActionStruct.ofRelStruct₀ h
  let h₁ : FundamentalGroupoid.ActionStruct e p (rawTransportPtSimplex (X := X) e p) :=
    rawTransportActionStruct (X := X) e p
  let h₂ : FundamentalGroupoid.ActionStruct e q (rawTransportPtSimplex (X := X) e q) :=
    rawTransportActionStruct (X := X) e q
  let hComp : FundamentalGroupoid.ActionStruct e p (rawTransportPtSimplex (X := X) e q) :=
    FundamentalGroupoid.ActionStruct.comp (Edge.CompStruct.idComp e) hRel h₂
  exact FundamentalGroupoid.ActionStruct.unique h₁ hComp

private lemma rawTransport_edge_homotopy {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    {e e' : Edge x y}
    (h : Nonempty (Edge.HomotopyL e e')) (p : X.PtSimplex n x) :
    Nonempty ((rawTransportPtSimplex (X := X) e p).RelStruct₀ (rawTransportPtSimplex (X := X) e'
      p)) := by
  obtain ⟨h⟩ := h
  let h₁ : FundamentalGroupoid.ActionStruct e p (rawTransportPtSimplex (X := X) e p) :=
    rawTransportActionStruct (X := X) e p
  let hId : FundamentalGroupoid.ActionStruct (Edge.id y) (rawTransportPtSimplex (X := X) e p)
      (rawTransportPtSimplex (X := X) e p) :=
    FundamentalGroupoid.ActionStruct.id (rawTransportPtSimplex (X := X) e p)
  let hComp : FundamentalGroupoid.ActionStruct e' p (rawTransportPtSimplex (X := X) e p) :=
    FundamentalGroupoid.ActionStruct.comp h h₁ hId
  let h₂ : FundamentalGroupoid.ActionStruct e' p (rawTransportPtSimplex (X := X) e' p) :=
    rawTransportActionStruct (X := X) e' p
  exact FundamentalGroupoid.ActionStruct.unique hComp h₂

/-- Action of an edge on homotopy groups, factoring through `PtSimplex` transport. -/
private noncomputable def edgeAction {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (e : Edge x y) : π n X x → π n X y :=
  Quot.lift (fun p => π.mk (rawTransportPtSimplex e p))
    (fun p q h => by
      have h_eq : π.mk p = π.mk q := Quot.sound h
      rw [π.mk_eq_mk_iff] at h_eq
      rw [π.mk_eq_mk_iff]
      exact rawTransport_compat e h_eq
    )

@[simp]
private lemma edgeAction_mk {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (e : Edge x y) (p : X.PtSimplex n x) :
    edgeAction (n := n) e (π.mk p) = π.mk (rawTransportPtSimplex (X := X) e p) :=
  rfl

private lemma edgeAction_congr {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    {e e' : Edge x y} (h : SSet.FundamentalGroupoid.homMk (X := X) e =
      SSet.FundamentalGroupoid.homMk e') :
    @edgeAction X _ n x y e = @edgeAction X _ n x y e' := by
  have hHomotopy : Nonempty (Edge.HomotopyL e e') :=
    (SSet.FundamentalGroupoid.homMk_eq_iff_nonempty_homotopyL.mp h)
  funext q
  induction q using π.rec with
  | mk p =>
    simp only [edgeAction_mk]
    rw [π.mk_eq_mk_iff]
    exact rawTransport_edge_homotopy hHomotopy p

/-- Fundamental-groupoid action on `π n`: transport along a morphism `p : mk x ⟶ mk y`.
The definition is by picking an edge representative; well-definedness is via
`edgeAction_congr`. This avoids exposing raw horn fillers. -/
noncomputable def action {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) :
    π n X x → π n X y :=
  edgeAction (Classical.choose (SSet.FundamentalGroupoid.homMk_surjective p))

private lemma action_homMk {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (e : Edge x y) :
    (action (n := n) (SSet.FundamentalGroupoid.homMk (X := X) e) :
        π n X x → π n X y) = edgeAction (n := n) e := by
  have h : SSet.FundamentalGroupoid.homMk
      (Classical.choose
        (SSet.FundamentalGroupoid.homMk_surjective
          (SSet.FundamentalGroupoid.homMk (X := X) e))) =
      SSet.FundamentalGroupoid.homMk (X := X) e :=
    Classical.choose_spec
      (SSet.FundamentalGroupoid.homMk_surjective
        (SSet.FundamentalGroupoid.homMk (X := X) e))
  simp only [action]
  exact edgeAction_congr h

/-- Action of an edge on `π` via `homMk` coincides with any `ActionStruct` witness. -/
lemma action_homMk_mk_eq_mk_of_actionStruct
    {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    {e : Edge x y} {s : X.PtSimplex n x} {t : X.PtSimplex n y}
    (h : FundamentalGroupoid.ActionStruct e s t) :
    action (SSet.FundamentalGroupoid.homMk (X := X) e) (π.mk s) = π.mk t := by
  rw [action_homMk (X := X) (e := e), edgeAction_mk (X := X) (e := e), π.mk_eq_mk_iff]
  exact FundamentalGroupoid.ActionStruct.unique (rawTransportActionStruct (X := X) e s) h

@[simp]
lemma action_id {X : SSet.{u}} [KanComplex X] {n : ℕ} (x : X _⦋0⦌) :
    (action (n := n) (𝟙 (SSet.FundamentalGroupoid.mk (X := X) x)) : π n X x → π n X x) =
      _root_.id := by
  have h : (𝟙 (SSet.FundamentalGroupoid.mk (X := X) x)) =
      SSet.FundamentalGroupoid.homMk (X := X) (Edge.id x) :=
    (SSet.FundamentalGroupoid.homMk_id (X := X) x).symm
  rw [h, action_homMk]
  funext q
  induction q using π.rec with
  | mk p =>
    simp only [edgeAction_mk]
    have h_id : (_root_.id : π n X x → π n X x) (π.mk p) = π.mk p := rfl
    rw [h_id]
    rw [π.mk_eq_mk_iff]
    exact FundamentalGroupoid.ActionStruct.unique
      (rawTransportActionStruct (X := X) (Edge.id x) p)
      (FundamentalGroupoid.ActionStruct.id (X := X) p)

lemma action_comp {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y z : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y)
    (q : SSet.FundamentalGroupoid.mk (X := X) y ⟶ SSet.FundamentalGroupoid.mk z) :
    (action (n := n) (p ≫ q) : π n X x → π n X z) = (action (n := n) q) ∘ (action (n := n) p) := by
  induction p using SSet.FundamentalGroupoid.hom_rec_of_kanComplex with
  | homMk e₁ =>
    induction q using SSet.FundamentalGroupoid.hom_rec_of_kanComplex with
    | homMk e₂ =>
      let e := Edge.comp e₁ e₂
      have he : Edge.CompStruct e₁ e₂ e := Edge.compStruct e₁ e₂
      have h_left : (action (n := n)
          (SSet.FundamentalGroupoid.homMk (X := X) e₁ ≫
            SSet.FundamentalGroupoid.homMk (X := X) e₂) : π n X x → π n X z) =
          edgeAction (n := n) e := by
        rw [he.homMk_comp, action_homMk]
      have h1 : action (n := n) (SSet.FundamentalGroupoid.homMk (X := X) e₁) =
          edgeAction (n := n) e₁ :=
        action_homMk (X := X) e₁
      have h2 : action (n := n) (SSet.FundamentalGroupoid.homMk (X := X) e₂) =
          edgeAction (n := n) e₂ :=
        action_homMk (X := X) e₂
      rw [h_left, h1, h2]
      funext r
      induction r using π.rec with
      | mk s =>
        simp only [Function.comp_apply, edgeAction_mk]
        rw [π.mk_eq_mk_iff]
        let h₁ : FundamentalGroupoid.ActionStruct e₁ s (rawTransportPtSimplex e₁ s) :=
          rawTransportActionStruct e₁ s
        let h₂ : FundamentalGroupoid.ActionStruct e₂ (rawTransportPtSimplex e₁ s)
            (rawTransportPtSimplex e₂ (rawTransportPtSimplex e₁ s)) :=
          rawTransportActionStruct e₂ (rawTransportPtSimplex e₁ s)
        let h_comp : FundamentalGroupoid.ActionStruct e s
            (rawTransportPtSimplex e₂ (rawTransportPtSimplex e₁ s)) :=
          FundamentalGroupoid.ActionStruct.comp he h₁ h₂
        let h_target : FundamentalGroupoid.ActionStruct e s
            (rawTransportPtSimplex e s) :=
          rawTransportActionStruct e s
        exact FundamentalGroupoid.ActionStruct.unique h_target h_comp

/-- Equivalence induced by the action of a fundamental-groupoid morphism. -/
@[expose] noncomputable def actionEquiv {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) :
    π n X x ≃ π n X y where
  toFun := action (n := n) p
  invFun := action (n := n) (inv p)
  left_inv := by
    intro q
    have h_eq : (action (n := n) (inv p) ∘ action (n := n) p) q = q := by
      have h_comp : action (n := n) (p ≫ inv p) =
          action (n := n) (inv p) ∘ action (n := n) p :=
        action_comp (n := n) p (inv p)
      have h_id : action (n := n) (p ≫ inv p) = _root_.id := by
        rw [IsIso.hom_inv_id p, action_id]
      have h : action (n := n) (inv p) ∘ action (n := n) p = _root_.id := by
        rw [← h_comp, h_id]
      exact congrFun h q
    simpa using h_eq
  right_inv := by
    intro q
    have h_eq : (action (n := n) p ∘ action (n := n) (inv p)) q = q := by
      have h_comp : action (n := n) (inv p ≫ p) =
          action (n := n) p ∘ action (n := n) (inv p) :=
        action_comp (n := n) (inv p) p
      have h_id : action (n := n) (inv p ≫ p) = _root_.id := by
        rw [IsIso.inv_hom_id p, action_id]
      have h : action (n := n) p ∘ action (n := n) (inv p) = _root_.id := by
        rw [← h_comp, h_id]
      exact congrFun h q
    simpa using h_eq

@[simp]
lemma actionEquiv_apply {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) (q : π n X x) :
    actionEquiv (n := n) p q = action (n := n) p q :=
  rfl

lemma action_bijective {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) :
    Function.Bijective (action (n := n) p : π n X x → π n X y) :=
  (actionEquiv (n := n) p).bijective

lemma action_injective {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) :
    Function.Injective (action (n := n) p : π n X x → π n X y) :=
  (action_bijective (n := n) p).1

lemma action_surjective {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) :
    Function.Surjective (action (n := n) p : π n X x → π n X y) :=
  (action_bijective (n := n) p).2

/-- Naturality of the action under `π.map`. For `f : X ⟶ Y`, the action intertwines
with pushforward on `π`. This is the key lemma for `W.of_precomp`. -/
lemma action_naturality {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {n : ℕ} {x y : X _⦋0⦌}
    (f : X ⟶ Y) (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y)
    (q : π n X x) :
    π.map f rfl n (action (n := n) p q) =
      action (n := n) ((SSet.mapFundamentalGroupoid f).map p) (π.map f rfl n q) := by
  induction p using SSet.FundamentalGroupoid.hom_rec_of_kanComplex with
  | homMk e =>
    induction q using π.rec with
    | mk s =>
      have h_left_action :
          action (SSet.FundamentalGroupoid.homMk (X := X) e) (π.mk s) =
            π.mk (rawTransportPtSimplex (X := X) e s) :=
        action_homMk_mk_eq_mk_of_actionStruct
          (X := X) (rawTransportActionStruct (X := X) e s)
      have h_map_left :
          π.map f rfl n (π.mk (rawTransportPtSimplex (X := X) e s)) =
            π.mk (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) :=
        rfl
      have h_left :
          π.map f rfl n
              (action (SSet.FundamentalGroupoid.homMk (X := X) e) (π.mk s)) =
            π.mk (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) := by
        calc π.map f rfl n
                (action (SSet.FundamentalGroupoid.homMk (X := X) e) (π.mk s))
            = π.map f rfl n (π.mk (rawTransportPtSimplex (X := X) e s)) := by
              rw [h_left_action]
          _ = π.mk (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) :=
              h_map_left
      have h_fg :
          (SSet.mapFundamentalGroupoid f).map
              (SSet.FundamentalGroupoid.homMk (X := X) e) =
            SSet.FundamentalGroupoid.homMk (X := Y) (e.map f) :=
        SSet.mapFundamentalGroupoid_map_homMk (X := X) (Y := Y) f e
      have h_map_right :
          π.map f rfl n (π.mk s) =
            π.mk (SSet.PtSimplex.map f rfl s) :=
        rfl
      have h_push :
          FundamentalGroupoid.ActionStruct (e.map f)
            (SSet.PtSimplex.map f rfl s)
            (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) :=
        (rawTransportActionStruct (X := X) e s).pushforward f
      have h_right_action :
          action (SSet.FundamentalGroupoid.homMk (X := Y) (e.map f))
              (π.mk (SSet.PtSimplex.map f rfl s)) =
            π.mk (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) :=
        action_homMk_mk_eq_mk_of_actionStruct (X := Y) h_push
      have h_right :
          action
              (SSet.FundamentalGroupoid.homMk (X := Y) (e.map f))
              (π.map f rfl n (π.mk s)) =
            π.mk (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) := by
        calc action
                (SSet.FundamentalGroupoid.homMk (X := Y) (e.map f))
                (π.map f rfl n (π.mk s))
            = action
                (SSet.FundamentalGroupoid.homMk (X := Y) (e.map f))
                (π.mk (SSet.PtSimplex.map f rfl s)) := by rw [h_map_right]
          _ = π.mk (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) :=
              h_right_action
      have h_right_fg :
          action ((SSet.mapFundamentalGroupoid f).map
              (SSet.FundamentalGroupoid.homMk (X := X) e))
              (π.map f rfl n (π.mk s)) =
            π.mk (SSet.PtSimplex.map f rfl (rawTransportPtSimplex (X := X) e s)) := by
        rw [h_fg]
        exact h_right
      exact h_left.trans h_right_fg.symm

-- General version with explicit basepoint equalities, derived from the rfl case.
-- Uses cast to align `π n Y x'` with `π n Y (f x)` for well-typed application.
lemma action_naturality_eq {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {n : ℕ} {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (f : X ⟶ Y) (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y)
    (hx : f.app _ x = x') (hy : f.app _ y = y') (q : π n X x) :
    HEq (π.map f hy n (action (n := n) p q))
      (action (n := n) ((SSet.mapFundamentalGroupoid f).map p)
        (cast (congrArg (π n Y) hx.symm) (π.map f hx n q))) := by
  subst hx
  subst hy
  exact heq_of_eq (action_naturality f p q)

-- Compatibility aliases for PR #42587 pseudofunctor naming.
noncomputable abbrev pseudofunctorAction {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) :
    π n X x → π n X y :=
  action (n := n) p

noncomputable abbrev pseudofunctorActionEquiv {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶ SSet.FundamentalGroupoid.mk y) :
    π n X x ≃ π n X y :=
  actionEquiv (n := n) p

/-- Functor from the fundamental groupoid to `Type` sending `x ↦ π n X x`.
This packages the action for use as a pseudofunctor in PR #42587. -/
@[expose] noncomputable def actionFunctor (X : SSet.{u}) [KanComplex X] (n : ℕ) :
    SSet.FundamentalGroupoid X ⥤ Type u where
  obj x := π n X x.pt
  map {x y} p := ↾(action (n := n) p)
  map_id x := by
    ext q
    have h := action_id (X := X) (n := n) x.pt
    exact congrFun h q
  map_comp {x y z} p q := by
    ext r
    have h := action_comp (n := n) p q
    exact congrFun h r

@[simp]
lemma actionFunctor_obj_mk {X : SSet.{u}} [KanComplex X] (n : ℕ) (x : X _⦋0⦌) :
    (actionFunctor X n).obj (SSet.FundamentalGroupoid.mk (X := X) x) = π n X x :=
  rfl

private lemma actionFunctor_map_homMk {X : SSet.{u}} [KanComplex X] {n : ℕ} {x y : X _⦋0⦌}
    (e : Edge x y) (q : π n X x) :
    (actionFunctor (X := X) n).map (SSet.FundamentalGroupoid.homMk (X := X) e) q =
      edgeAction (n := n) e q := by
  have h :
      (ConcreteCategory.hom
          ((actionFunctor (X := X) n).map
            (SSet.FundamentalGroupoid.homMk (X := X) e)) :
          π n X x → π n X y) =
        action (n := n) (SSet.FundamentalGroupoid.homMk (X := X) e) :=
      rfl
  rw [h]
  exact congrFun (action_homMk (X := X) e) q

end π

end KanComplex

end SSet

end
