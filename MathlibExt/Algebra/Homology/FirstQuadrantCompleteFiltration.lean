/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Order.WithBotTop
public import MathlibExt.Algebra.Homology.FirstQuadrantSpectralObject
public import MathlibExt.Algebra.Homology.MappingConeCokernelConnecting

/-!
# Complete indexing of a first-quadrant filtration

The horizontal filtration of a first-quadrant total complex extends from
natural stages to the extended integers. The bottom and every negative
finite stage are zero, a nonnegative finite stage is the corresponding
horizontal filtration stage, and the top stage is the full total complex.

This filtration defines a canonical `EInt`-indexed mapping-cone spectral object.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows Pretriangulated

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The zero subcomplex of the total complex. -/
noncomputable def horizontalCompleteFilteredTotalZeroMonoOver :
    MonoOver (K.total (ComplexShape.down ℕ)) :=
  MonoOver.mk
    (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
      K.total (ComplexShape.down ℕ))
    (hf := { right_cancellation := fun g h _ =>
      HomologicalComplex.isZero_zero.eq_of_tgt g h })

/-- The subcomplex at an extended filtration index.  Bottom and negative
finite indices give zero, nonnegative indices give the corresponding finite
stage, and top gives the full total complex. -/
noncomputable def horizontalCompleteFilteredTotalMonoOver (i : EInt) :
    MonoOver (K.total (ComplexShape.down ℕ)) :=
  WithBotTop.rec
    (horizontalCompleteFilteredTotalZeroMonoOver K)
    (fun a => if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K)
    (MonoOver.mk (𝟙 (K.total (ComplexShape.down ℕ)))) i

/-- The chain complex at an extended horizontal-filtration index. -/
abbrev horizontalCompleteFilteredTotalComplex (i : EInt) :
    ChainComplex C ℕ :=
  (horizontalCompleteFilteredTotalMonoOver K i).obj.left

/-- The inclusion of an extended filtration stage into the total complex. -/
abbrev horizontalCompleteFilteredTotalToTotal (i : EInt) :
    horizontalCompleteFilteredTotalComplex K i ⟶
      K.total (ComplexShape.down ℕ) :=
  (horizontalCompleteFilteredTotalMonoOver K i).arrow

/-- The morphism of subcomplexes induced by an inequality of extended
filtration indices. -/
noncomputable def horizontalCompleteFilteredTotalMonoOverMap
    {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalMonoOver K i ⟶
      horizontalCompleteFilteredTotalMonoOver K j := by
  induction i using WithBotTop.rec with
  | bot =>
      change horizontalCompleteFilteredTotalZeroMonoOver K ⟶ _
      refine MonoOver.homMk 0 ?_
      simp [horizontalCompleteFilteredTotalZeroMonoOver]
  | coe a =>
      induction j using WithBotTop.rec with
      | bot => simp at h
      | coe b =>
          have hab : a ≤ b := by simpa using h
          by_cases ha : 0 ≤ a
          · have hb : 0 ≤ b := ha.trans hab
            change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                (if 0 ≤ b then
                  (horizontalTotalFiltration K).toMonoOver.obj b.toNat
                else horizontalCompleteFilteredTotalZeroMonoOver K)
            rw [ite_eq_left ha, ite_eq_left hb]
            exact MonoOver.homMk
              (horizontalFilteredTotalComplexMap K
                (Int.toNat_le_toNat hab))
              (horizontalFilteredTotalComplexMap_toTotal K
                (Int.toNat_le_toNat hab))
          · change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                (if 0 ≤ b then
                  (horizontalTotalFiltration K).toMonoOver.obj b.toNat
                else horizontalCompleteFilteredTotalZeroMonoOver K)
            rw [ite_eq_right ha]
            refine MonoOver.homMk 0 ?_
            simp [horizontalCompleteFilteredTotalZeroMonoOver]
      | top =>
          by_cases ha : 0 ≤ a
          · change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                MonoOver.mk (𝟙 (K.total (ComplexShape.down ℕ)))
            rw [ite_eq_left ha]
            refine MonoOver.homMk
              (horizontalFilteredTotalComplexToTotal K a.toNat) ?_
            change horizontalFilteredTotalComplexToTotal K a.toNat ≫
                𝟙 _ = horizontalFilteredTotalComplexToTotal K a.toNat
            simp
          · change (if 0 ≤ a then
                (horizontalTotalFiltration K).toMonoOver.obj a.toNat
              else horizontalCompleteFilteredTotalZeroMonoOver K) ⟶
                MonoOver.mk (𝟙 (K.total (ComplexShape.down ℕ)))
            rw [ite_eq_right ha]
            refine MonoOver.homMk 0 ?_
            simp [horizontalCompleteFilteredTotalZeroMonoOver]
  | top =>
      have hj : j = ⊤ := top_le_iff.mp h
      subst j
      exact 𝟙 _

/-- The underlying chain map between two extended filtration stages. -/
noncomputable def horizontalCompleteFilteredTotalMap
    {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex K j :=
  (horizontalCompleteFilteredTotalMonoOverMap K h).hom.left

@[reassoc]
theorem horizontalCompleteFilteredTotalMap_toTotal
    {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalMap K h ≫
        horizontalCompleteFilteredTotalToTotal K j =
      horizontalCompleteFilteredTotalToTotal K i :=
  MonoOver.w (horizontalCompleteFilteredTotalMonoOverMap K h)

/-- The complete extended-integer horizontal filtration. -/
noncomputable def horizontalCompleteTotalFiltration :
    CategoryTheory.Filtration (K.total (ComplexShape.down ℕ)) EInt where
  toMonoOver :=
    { obj := horizontalCompleteFilteredTotalMonoOver K
      map := fun {i j} f =>
        horizontalCompleteFilteredTotalMonoOverMap K (leOfHom f)
      map_id := by
        intro i
        apply Subsingleton.elim
      map_comp := by
        intro i j k f g
        apply Subsingleton.elim }

@[simp]
theorem horizontalCompleteFilteredTotalComplex_bot :
    horizontalCompleteFilteredTotalComplex K ⊥ =
      (HomologicalComplex.zero : ChainComplex C ℕ) :=
  rfl

@[simp]
theorem horizontalCompleteFilteredTotalComplex_top :
    horizontalCompleteFilteredTotalComplex K ⊤ =
      K.total (ComplexShape.down ℕ) :=
  rfl

theorem horizontalCompleteFilteredTotalComplex_coe_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) =
      horizontalFilteredTotalComplex K a.toNat := by
  change (if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K).obj.left = _
  rw [ite_eq_left ha]
  exact horizontalTotalFiltration_diagram_obj K a.toNat

theorem horizontalCompleteFilteredTotalComplex_coe_of_neg
    (a : ℤ) (ha : a < 0) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) =
      (HomologicalComplex.zero : ChainComplex C ℕ) := by
  have hna : ¬0 ≤ a := by omega
  change (if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K).obj.left = _
  rw [ite_eq_right hna]
  rfl

@[simp]
theorem horizontalCompleteFilteredTotalToTotal_top :
    horizontalCompleteFilteredTotalToTotal K ⊤ = 𝟙 _ :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltration_diagram_obj (i : EInt) :
    (horizontalCompleteTotalFiltration K).diagram.obj i =
      horizontalCompleteFilteredTotalComplex K i :=
  rfl

theorem horizontalCompleteTotalFiltration_diagram_map
    {i j : EInt} (h : i ≤ j) :
    (horizontalCompleteTotalFiltration K).diagram.map (homOfLE h) =
      horizontalCompleteFilteredTotalMap K h :=
  rfl

@[simp]
theorem horizontalCompleteTotalFiltration_ι_app (i : EInt) :
    (horizontalCompleteTotalFiltration K).ι.app i =
      horizontalCompleteFilteredTotalToTotal K i :=
  rfl

/-- A nonnegative finite complete-filtration stage is already the full total
in every total degree not exceeding that stage. -/
noncomputable def horizontalCompleteFilteredTotalEvalIsoOfLE
    (a : ℤ) (ha : 0 ≤ a) (n : ℕ) (h : n ≤ a.toNat) :
    (horizontalCompleteFilteredTotalComplex K (a : EInt)).X n ≅
      (K.total (ComplexShape.down ℕ)).X n :=
  (HomologicalComplex.eval C (ComplexShape.down ℕ) n).mapIso
      (eqToIso (horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha)) ≪≫
    horizontalFilteredTotalIsoOfLE K a.toNat n h

/-- The complete filtration diagram reindexed as integer cochain complexes. -/
noncomputable def horizontalCompleteFiltrationCochainDiagram :
    EInt ⥤ CochainComplex C ℤ :=
  (horizontalCompleteTotalFiltration K).diagram ⋙
    ComplexShape.embeddingDownNat.extendFunctor C

/-- Mapping-cone composition triangle for the images under a functor.  Its
middle object uses `F.map (f ≫ g)` literally, matching the functor on
composable arrows; it is canonically isomorphic to the usual triangle whose
middle map is `F.map f ≫ F.map g`. -/
noncomputable def functorMappingConeCompTriangle
    (F : EInt ⥤ CochainComplex C ℤ)
    {X Y Z : EInt} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Triangle (CochainComplex C ℤ) :=
  Triangle.mk
    (CochainComplex.mappingCone.map (F.map f) (F.map (f ≫ g)) (𝟙 _)
      (F.map g) (by simp [F.map_comp]))
    (CochainComplex.mappingCone.map (F.map (f ≫ g)) (F.map g) (F.map f)
      (𝟙 _) (by simp [F.map_comp]))
    ((CochainComplex.mappingCone.triangle (F.map g)).mor₃ ≫
      (CochainComplex.mappingCone.inr (F.map f))⟦1⟧')

/-- Mapping-cone functor on arrows of the complete filtration, normalized so
its object is definitionally the cone of the mapped filtration morphism. -/
noncomputable def horizontalCompleteFiltrationMappingConeFunctor :
    ComposableArrows EInt 1 ⥤ CochainComplex C ℤ where
  obj D := CochainComplex.mappingCone
    ((horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1))
  map {X Y} φ :=
    CochainComplex.mappingCone.map
      ((horizontalCompleteFiltrationCochainDiagram K).map (X.map' 0 1))
      ((horizontalCompleteFiltrationCochainDiagram K).map (Y.map' 0 1))
      ((horizontalCompleteFiltrationCochainDiagram K).map (φ.app 0))
      ((horizontalCompleteFiltrationCochainDiagram K).map (φ.app 1)) (by
        rw [← (horizontalCompleteFiltrationCochainDiagram K).map_comp,
          ← (horizontalCompleteFiltrationCochainDiagram K).map_comp]
        apply (horizontalCompleteFiltrationCochainDiagram K).congr_map
        have hφ := naturality' φ 0 1
        change X.map' 0 1 ≫ φ.app 1 = φ.app 0 ≫ Y.map' 0 1 at hφ
        exact hφ)
  map_id D := by
    dsimp
    simpa using CochainComplex.mappingCone.map_id
      ((horizontalCompleteFiltrationCochainDiagram K).map (D.map' 0 1))
  map_comp φ ψ := by
    dsimp
    rw [← CochainComplex.mappingCone.map_comp]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- The mapping-cone spectral object of the complete horizontal filtration. -/
noncomputable def horizontalCompleteFiltrationTriangulatedSpectralObject :
    CategoryTheory.Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) EInt where
  ω₁ :=
    horizontalCompleteFiltrationMappingConeFunctor K ⋙
      HomotopyCategory.quotient C (ComplexShape.up ℤ)
  δ'.app D := ((HomotopyCategory.quotient C
    (ComplexShape.up ℤ)).mapTriangle.obj
      (functorMappingConeCompTriangle
        (horizontalCompleteFiltrationCochainDiagram K)
        (D.map' 0 1) (D.map' 1 2))).mor₃
  δ'.naturality D₁ D₂ φ := by
    obtain ⟨_, _, _, f₁, g₁, rfl⟩ := ComposableArrows.mk₂_surjective D₁
    obtain ⟨_, _, _, f₂, g₂, rfl⟩ := ComposableArrows.mk₂_surjective D₂
    let F := horizontalCompleteFiltrationCochainDiagram K
    let φ' : mk₂ (F.map f₁) (F.map g₁) ⟶ mk₂ (F.map f₂) (F.map g₂) :=
      homMk₂ (F.map (φ.app 0)) (F.map (φ.app 1)) (F.map (φ.app 2))
        (by
          change F.map f₁ ≫ F.map (φ.app 1) = F.map (φ.app 0) ≫ F.map f₂
          rw [← F.map_comp, ← F.map_comp]
          apply F.congr_map
          have hφ := naturality' φ 0 1
          change f₁ ≫ φ.app 1 = φ.app 0 ≫ f₂ at hφ
          exact hφ)
        (by
          change F.map g₁ ≫ F.map (φ.app 2) = F.map (φ.app 1) ≫ F.map g₂
          rw [← F.map_comp, ← F.map_comp]
          apply F.congr_map
          have hφ := naturality' φ 1 2
          change g₁ ≫ φ.app 2 = φ.app 1 ≫ g₂ at hφ
          exact hφ)
    have eq := CochainComplex.mappingConeCompTriangle_mor₃_naturality
      (F.map f₁) (F.map g₁) (F.map f₂) (F.map g₂) φ'
    dsimp [F, φ', ComposableArrows.Precomp.map,
      horizontalCompleteFiltrationMappingConeFunctor,
      functorMappingConeCompTriangle] at eq ⊢
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp [eq]
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    let F := horizontalCompleteFiltrationCochainDiagram K
    let hfg := F.map_comp f g
    let e₂ :
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone (F.map (f ≫ g))) ≅
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone (F.map f ≫ F.map g)) :=
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso
        (CochainComplex.mappingCone.isoOfHomEq (C := C) hfg)
    refine isomorphic_distinguished _
      (HomotopyCategory.mappingConeCompTriangleh_distinguished
        (F.map f) (F.map g)) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e₂ (Iso.refl _) ?_ ?_ ?_
    · have hc := CochainComplex.mappingCone.map_comp_isoOfHomEq
        (F.map f) (𝟙 _) (F.map g) hfg
        (by simp [hfg]) (by simp)
      have hQ := (HomotopyCategory.quotient C
        (ComplexShape.up ℤ)).congr_map hc
      simpa [F, e₂, horizontalCompleteFiltrationMappingConeFunctor,
        functorMappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangleh,
        ComposableArrows.Precomp.map, ← Functor.map_comp] using hQ
    · have hc := (CochainComplex.mappingCone.isoOfHomEq_hom_comp_map
        (F.map g) (F.map f) (𝟙 _) hfg
        (by simp [hfg]) (by simp)).symm
      have hQ := (HomotopyCategory.quotient C
        (ComplexShape.up ℤ)).congr_map hc
      simpa [F, e₂, horizontalCompleteFiltrationMappingConeFunctor,
        functorMappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangleh,
        ComposableArrows.Precomp.map, ← Functor.map_comp] using hQ
    · simp [F, horizontalCompleteFiltrationMappingConeFunctor,
        functorMappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangle,
        CochainComplex.mappingConeCompTriangleh,
        ComposableArrows.Precomp.map]

end HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The abelian spectral object of the complete horizontal filtration. -/
noncomputable def horizontalCompleteFiltrationSpectralObject :
    CategoryTheory.Abelian.SpectralObject C EInt :=
  (horizontalCompleteFiltrationTriangulatedSpectralObject K).mapHomologicalFunctor
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0)

/-- The connecting morphism of the complete-filtration spectral object is
definitionally the connecting morphism of the standard mapping-cone
composition triangle on the two mapped filtration arrows. -/
theorem horizontalCompleteFiltrationSpectralObject_δ
    {i j k : EInt} (f : i ⟶ j) (g : j ⟶ k)
    (n n' : ℤ) (h : n + 1 = n') :
    (horizontalCompleteFiltrationSpectralObject K).δ f g n n' h =
      (HomotopyCategory.homologyFunctor C
        (ComplexShape.up ℤ) 0).homologySequenceδ
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
            (CochainComplex.mappingConeCompTriangle
              ((horizontalCompleteFiltrationCochainDiagram K).map f)
              ((horizontalCompleteFiltrationCochainDiagram K).map g)))
          n n' h := by
  rfl

end HomologicalComplex₂

end
