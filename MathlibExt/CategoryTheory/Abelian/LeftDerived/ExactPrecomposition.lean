/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AugmentedExactComparison
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.PrecompositionNaturality

/-!
# Directional left-derived comparison for exact source restriction

An additive homology-preserving functor U sends a target-ring projective resolution to an exact
augmented complex. The source-ring projective resolution maps into that complex. This gives the
canonical directional map `U ⋙ L.leftDerived n ⟶ (U ⋙ L).leftDerived n` even when U does not
preserve projectives. If U does preserve projectives, it is exactly the inverse of the existing
precomposition isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' u'' v''

namespace CategoryTheory.Functor

attribute [local implicit_reducible] HomologicalComplex.homologyFunctor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

/-- The original mapped augmentation, without assigning projectivity to its image terms. -/
def mapChainAugmentation (U : C ⥤ D) [U.Additive]
    {X : C} {K : ChainComplex C ℕ} (π : K ⟶ (ChainComplex.single₀ C).obj X) :
    (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
      (ChainComplex.single₀ D).obj (U.obj X) :=
  (U.mapHomologicalComplex (ComplexShape.down ℕ)).map π ≫
    (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.down ℕ) 0).hom.app X

/-- The mapped augmentation keeps its original degree-zero image. -/
theorem mapChainAugmentation_f_zero (U : C ⥤ D) [U.Additive]
    {X : C} {K : ChainComplex C ℕ} (π : K ⟶ (ChainComplex.single₀ C).obj X) :
    (mapChainAugmentation U π).f 0 = U.map (π.f 0) := by
  change U.map (π.f 0) ≫
    ((HomologicalComplex.singleMapHomologicalComplex U
      (ComplexShape.down ℕ) 0).hom.app X).f 0 = _
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    Functor.map_id, Category.comp_id]
  change U.map (π.f 0) ≫ U.map (𝟙 X) ≫ 𝟙 (U.obj X) = U.map (π.f 0)
  exact (congrArg (fun z => U.map (π.f 0) ≫ z ≫ 𝟙 (U.obj X))
    (U.map_id X)).trans
      ((congrArg (fun z => U.map (π.f 0) ≫ z)
        (Category.comp_id (𝟙 (U.obj X)))).trans (Category.comp_id _))

/-- Homology preservation earns an exact mapped augmented complex; no projectivity is claimed. -/
theorem mapChainAugmentation_quasiIso (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
    {X : C} {K : ChainComplex C ℕ} (π : K ⟶ (ChainComplex.single₀ C).obj X)
    [QuasiIso π] : QuasiIso (mapChainAugmentation U π) := by
  unfold mapChainAugmentation
  infer_instance

/-- Mapping an augmentation square retains that same original square. -/
theorem mapChainAugmentation_naturality (U : C ⥤ D) [U.Additive]
    {X Y : C} {K K' : ChainComplex C ℕ}
    (π : K ⟶ (ChainComplex.single₀ C).obj X)
    (π' : K' ⟶ (ChainComplex.single₀ C).obj Y) (f : X ⟶ Y) (a : K ⟶ K')
    (ha : a ≫ π' = π ≫ (ChainComplex.single₀ C).map f) :
    (U.mapHomologicalComplex (ComplexShape.down ℕ)).map a ≫ mapChainAugmentation U π' =
      mapChainAugmentation U π ≫ (ChainComplex.single₀ D).map (U.map f) := by
  unfold mapChainAugmentation
  rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_comp, Category.assoc]
  have hσ :
      (U.mapHomologicalComplex (ComplexShape.down ℕ)).map ((ChainComplex.single₀ C).map f) ≫
          (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.down ℕ) 0).hom.app Y =
        (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.down ℕ) 0).hom.app X ≫
          (ChainComplex.single₀ D).map (U.map f) := by
    simpa only [Functor.comp_map, ChainComplex.single₀] using
      (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.down ℕ) 0).hom.naturality f
  exact (congrArg (fun z => (U.mapHomologicalComplex (ComplexShape.down ℕ)).map π ≫ z) hσ).trans
    (Category.assoc _ _ _).symm

/-- The complex-composition map keeps the original opcycles augmentation. -/
theorem mapChainAugmentation_opcycles_composition
    (U : C ⥤ D) [U.Additive] (L : D ⥤ E) [L.Additive]
    {X : C} (P : ProjectiveResolution X) :
    HomologicalComplex.opcyclesMap
        ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
          (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).hom.app P.complex) 0 ≫
      P.fromLeftDerivedZero' (U ⋙ L) =
        ChainComplex.mappedAugmentationDesc L (mapChainAugmentation U P.π) := by
  let K := (L.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
  apply (cancel_epi (K.pOpcycles 0)).1
  rw [HomologicalComplex.p_opcyclesMap_assoc,
    ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',
    ChainComplex.pOpcycles_comp_mappedAugmentationDesc]
  change (𝟙 _) ≫ L.map (U.map (P.π.f 0)) =
    L.map ((mapChainAugmentation U P.π).f 0)
  rw [Category.id_comp, mapChainAugmentation_f_zero]
  rfl

/-- Composition of the complex functors carries the original degree-zero augmentation. -/
theorem mapChainAugmentation_homologyZero_composition
    (U : C ⥤ D) [U.Additive] (L : D ⥤ E) [L.Additive]
    {X : C} (P : ProjectiveResolution X) :
    HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
          (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).hom.app P.complex) 0 ≫
      ChainComplex.mappedAugmentationHomologyZero (U ⋙ L) P.π =
        ChainComplex.mappedAugmentationHomologyZero L (mapChainAugmentation U P.π) := by
  change HomologicalComplex.homologyMap
      ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
        (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).hom.app P.complex) 0 ≫
    (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyι 0 ≫
      P.fromLeftDerivedZero' (U ⋙ L) = _
  rw [HomologicalComplex.homologyι_naturality_assoc,
    mapChainAugmentation_opcycles_composition]
  rfl

section Derived

variable [HasProjectiveResolutions C] [HasProjectiveResolutions D]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology] (L : D ⥤ E) [L.Additive]

/-- The source projective resolution maps into the exact image of any target resolution. -/
def leftDerivedPrecompHomWithResolution (n : ℕ) {X : C} (P : ProjectiveResolution X) :
    (L.leftDerived n).obj (U.obj X) ⟶ ((U ⋙ L).leftDerived n).obj X := by
  letI : QuasiIso (mapChainAugmentation U P.π) := mapChainAugmentation_quasiIso U P.π
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)
  exact leftDerivedObjToAugmentedHom L
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
      (mapChainAugmentation U P.π) (𝟙 (U.obj X)) n ≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).map
      (χ.hom.app P.complex) ≫ (P.isoLeftDerivedObj (U ⋙ L) n).inv

/-- Resolution maps earn input naturality of the directional comparison. -/
theorem leftDerivedPrecompHomWithResolution_naturality (n : ℕ)
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (L.leftDerived n).map (U.map f) ≫ leftDerivedPrecompHomWithResolution U L n Q =
      leftDerivedPrecompHomWithResolution U L n P ≫ ((U ⋙ L).leftDerived n).map f := by
  let a := ProjectiveResolution.lift f P Q
  let b := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map a
  let ρP := mapChainAugmentation U P.π
  let ρQ := mapChainAugmentation U Q.π
  letI : QuasiIso ρP := mapChainAugmentation_quasiIso U P.π
  letI : QuasiIso ρQ := mapChainAugmentation_quasiIso U Q.π
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)
  let tP := leftDerivedObjToAugmentedHom L
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ρP (𝟙 (U.obj X)) n
  let tQ := leftDerivedObjToAugmentedHom L
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ (𝟙 (U.obj Y)) n
  have hρ : b ≫ ρQ = ρP ≫ (ChainComplex.single₀ D).map (U.map f) :=
    mapChainAugmentation_naturality U P.π Q.π f a
      (ProjectiveResolution.lift_commutes f P Q)
  have hL : (L.leftDerived n).map (U.map f) ≫ tQ =
      tP ≫ H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map b) := by
    have hSource := leftDerivedObjToAugmentedHom_naturality_source L
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ
      (U.map f) (𝟙 (U.obj Y)) n
    have hTarget := leftDerivedObjToAugmentedHom_naturality_target L ρP ρQ
      (𝟙 (U.obj X)) (U.map f) b hρ n
    have hS : (L.leftDerived n).map (U.map f) ≫ tQ =
        leftDerivedObjToAugmentedHom L
          ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ (U.map f) n := by
      simpa only [tQ, Category.comp_id] using hSource
    have hT : leftDerivedObjToAugmentedHom L
          ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) ρQ (U.map f) n =
        tP ≫ H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map b) := by
      simpa only [tP, H, Functor.comp_map, Category.id_comp] using hTarget.symm
    exact hS.trans hT
  have hχ : H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map b) ≫
      H.map (χ.hom.app Q.complex) = H.map (χ.hom.app P.complex) ≫
        H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map a) :=
    (isoWhiskerRight χ H).hom.naturality a
  have hLast : (P.isoLeftDerivedObj (U ⋙ L) n).inv ≫ ((U ⋙ L).leftDerived n).map f =
      H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map a) ≫
        (Q.isoLeftDerivedObj (U ⋙ L) n).inv :=
    ProjectiveResolution.isoLeftDerivedObj_inv_naturality f P Q a
      (ProjectiveResolution.lift_commutes_zero f P Q) (U ⋙ L) n
  have s₁ : CommSq tP ((L.leftDerived n).map (U.map f))
      (H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map b)) tQ := ⟨hL.symm⟩
  have s₂ : CommSq (H.map (χ.hom.app P.complex))
      (H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map b))
      (H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map a))
      (H.map (χ.hom.app Q.complex)) := ⟨hχ.symm⟩
  have s₃ : CommSq (P.isoLeftDerivedObj (U ⋙ L) n).inv
      (H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map a))
      (((U ⋙ L).leftDerived n).map f) (Q.isoLeftDerivedObj (U ⋙ L) n).inv := ⟨hLast⟩
  change (L.leftDerived n).map (U.map f) ≫
      (tQ ≫ H.map (χ.hom.app Q.complex) ≫ (Q.isoLeftDerivedObj (U ⋙ L) n).inv) =
    (tP ≫ H.map (χ.hom.app P.complex) ≫ (P.isoLeftDerivedObj (U ⋙ L) n).inv) ≫
      ((U ⋙ L).leftDerived n).map f
  exact (s₁.horiz_comp (s₂.horiz_comp s₃)).w.symm

/-- The target-ring resolution choice does not change the directional map. -/
theorem leftDerivedPrecompHomWithResolution_independent (n : ℕ) {X : C}
    (P Q : ProjectiveResolution X) :
    leftDerivedPrecompHomWithResolution U L n P =
      leftDerivedPrecompHomWithResolution U L n Q := by
  have h := leftDerivedPrecompHomWithResolution_naturality U L n (𝟙 X) P Q
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- The canonical directional left-derived comparison for an exact source functor. -/
def leftDerivedPrecompHomOfPreservesHomology (n : ℕ) :
    U ⋙ L.leftDerived n ⟶ (U ⋙ L).leftDerived n where
  app X := leftDerivedPrecompHomWithResolution U L n (projectiveResolution X)
  naturality {X Y} f := leftDerivedPrecompHomWithResolution_naturality U L n f
    (projectiveResolution X) (projectiveResolution Y)

/-- Every target-ring resolution computes the same canonical component. -/
theorem leftDerivedPrecompHomOfPreservesHomology_app (n : ℕ) {X : C}
    (P : ProjectiveResolution X) :
    (leftDerivedPrecompHomOfPreservesHomology U L n).app X =
      leftDerivedPrecompHomWithResolution U L n P :=
  leftDerivedPrecompHomWithResolution_independent U L n (projectiveResolution X) P

/--
When source precomposition genuinely preserves projectives, this directional comparison is exactly
the existing inverse isomorphism.
-/
theorem leftDerivedPrecompHomOfPreservesHomology_eq_inv
    [U.PreservesProjectiveObjects] (n : ℕ) :
    leftDerivedPrecompHomOfPreservesHomology U L n = (leftDerivedPrecompIso U L n).inv := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  letI : QuasiIso (mapChainAugmentation U P.π) := mapChainAugmentation_quasiIso U P.π
  rw [leftDerivedPrecompHomOfPreservesHomology_app U L n P,
    leftDerivedPrecompIso_inv_app U L n P]
  have h := leftDerivedObjToAugmentedHom_projective_target L
    (U.mapProjectiveResolution P) (𝟙 (U.obj X)) n
  simp only [Functor.map_id, Category.id_comp] at h
  change (leftDerivedObjToAugmentedHom L
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
      (mapChainAugmentation U P.π) (𝟙 (U.obj X)) n ≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).map
      ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
        (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).hom.app P.complex) ≫
      (P.isoLeftDerivedObj (U ⋙ L) n).inv) = _
  have h' : leftDerivedObjToAugmentedHom L
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
      (mapChainAugmentation U P.π) (𝟙 (U.obj X)) n =
      ((U.mapProjectiveResolution P).isoLeftDerivedObj L n).hom := h
  exact congrArg (fun z => z ≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).map
      ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
        (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).hom.app P.complex) ≫
      (P.isoLeftDerivedObj (U ⋙ L) n).inv) h'

/--
The directional comparison retains the degree-zero augmentation. L is only additive; U alone
preserves homology.
-/
theorem leftDerivedPrecompHomOfPreservesHomology_zero_augmentation :
    leftDerivedPrecompHomOfPreservesHomology U L 0 ≫ (U ⋙ L).fromLeftDerivedZero =
      whiskerLeft U L.fromLeftDerivedZero := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let ρ := mapChainAugmentation U P.π
  letI : QuasiIso ρ := mapChainAugmentation_quasiIso U P.π
  let t := leftDerivedObjToAugmentedHom L
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ρ (𝟙 (U.obj X)) 0
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)
  let K := ((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  rw [NatTrans.comp_app, whiskerLeft_app,
    leftDerivedPrecompHomOfPreservesHomology_app U L 0 P,
    P.fromLeftDerivedZero_eq (U ⋙ L)]
  change (t ≫ HomologicalComplex.homologyMap (χ.hom.app P.complex) 0 ≫
      (P.isoLeftDerivedObj (U ⋙ L) 0).inv) ≫
    ((P.isoLeftDerivedObj (U ⋙ L) 0).hom ≫ K.homologyι 0 ≫
      P.fromLeftDerivedZero' (U ⋙ L)) = L.fromLeftDerivedZero.app (U.obj X)
  have cancelTriple {W A B Z V : E} (f : W ⟶ A) (g : A ⟶ B)
      (e : Z ≅ B) (h : B ⟶ V) :
      (f ≫ g ≫ e.inv) ≫ (e.hom ≫ h) = f ≫ g ≫ h := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc
    (t ≫ HomologicalComplex.homologyMap (χ.hom.app P.complex) 0 ≫
        (P.isoLeftDerivedObj (U ⋙ L) 0).inv) ≫
      ((P.isoLeftDerivedObj (U ⋙ L) 0).hom ≫ K.homologyι 0 ≫
        P.fromLeftDerivedZero' (U ⋙ L)) =
        t ≫ HomologicalComplex.homologyMap (χ.hom.app P.complex) 0 ≫
          K.homologyι 0 ≫ P.fromLeftDerivedZero' (U ⋙ L) := cancelTriple t _ _ _
    _ = t ≫ (HomologicalComplex.homologyMap (χ.hom.app P.complex) 0 ≫
        ChainComplex.mappedAugmentationHomologyZero (U ⋙ L) P.π) := rfl
    _ = t ≫ ChainComplex.mappedAugmentationHomologyZero L ρ :=
      congrArg (fun z => t ≫ z) (mapChainAugmentation_homologyZero_composition U L P)
    _ = L.fromLeftDerivedZero.app (U.obj X) := by
      simpa only [t, Functor.map_id, Category.comp_id] using
        leftDerivedObjToAugmentedHom_zero_augmentation L
          ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ρ (𝟙 (U.obj X))

/-- An additive-functor transformation commutes with the directional comparison. -/
theorem leftDerivedPrecompHomOfPreservesHomology_naturality_functor
    {M : D ⥤ E} [M.Additive] (τ : L ⟶ M) (n : ℕ) :
    whiskerLeft U (NatTrans.leftDerived τ n) ≫
        leftDerivedPrecompHomOfPreservesHomology U M n =
      leftDerivedPrecompHomOfPreservesHomology U L n ≫
        NatTrans.leftDerived (whiskerLeft U τ) n := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let Q := (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let ρ := mapChainAugmentation U P.π
  letI : QuasiIso ρ := mapChainAugmentation_quasiIso U P.π
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let tL := leftDerivedObjToAugmentedHom L Q ρ (𝟙 (U.obj X)) n
  let tM := leftDerivedObjToAugmentedHom M Q ρ (𝟙 (U.obj X)) n
  let χL := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)
  let χM := Functor.mapHomologicalComplexCompIso (F := U) (G := M)
    (Iso.refl (U ⋙ M)) (ComplexShape.down ℕ)
  let a := (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app Q
  let b := (NatTrans.mapHomologicalComplex (whiskerLeft U τ)
    (ComplexShape.down ℕ)).app P.complex
  have h₁ : (NatTrans.leftDerived τ n).app (U.obj X) ≫ tM = tL ≫ H.map a :=
    leftDerivedObjToAugmentedHom_naturality_functor τ Q ρ (𝟙 (U.obj X)) n
  have hComplex : a ≫ χM.hom.app P.complex = χL.hom.app P.complex ≫ b := by
    apply HomologicalComplex.hom_ext
    intro i
    change τ.app (U.obj (P.complex.X i)) ≫ (𝟙 _) = (𝟙 _) ≫
      τ.app (U.obj (P.complex.X i))
    simp only [Category.comp_id, Category.id_comp]
  have h₂ : H.map a ≫ H.map (χM.hom.app P.complex) =
      H.map (χL.hom.app P.complex) ≫ H.map b := by
    simpa only [Functor.map_comp] using congrArg H.map hComplex
  have h₃ : H.map b ≫ (P.isoLeftDerivedObj (U ⋙ M) n).inv =
      (P.isoLeftDerivedObj (U ⋙ L) n).inv ≫
        (NatTrans.leftDerived (whiskerLeft U τ) n).app X :=
    ProjectiveResolution.isoLeftDerivedObj_inv_naturality_functor P (whiskerLeft U τ) n
  rw [NatTrans.comp_app, NatTrans.comp_app, whiskerLeft_app,
    leftDerivedPrecompHomOfPreservesHomology_app U L n P,
    leftDerivedPrecompHomOfPreservesHomology_app U M n P]
  change (NatTrans.leftDerived τ n).app (U.obj X) ≫
      (tM ≫ H.map (χM.hom.app P.complex) ≫ (P.isoLeftDerivedObj (U ⋙ M) n).inv) =
    (tL ≫ H.map (χL.hom.app P.complex) ≫ (P.isoLeftDerivedObj (U ⋙ L) n).inv) ≫
      (NatTrans.leftDerived (whiskerLeft U τ) n).app X
  have s₁ : CommSq tL ((NatTrans.leftDerived τ n).app (U.obj X))
      (H.map a) tM := ⟨h₁.symm⟩
  have s₂ : CommSq (H.map (χL.hom.app P.complex)) (H.map a)
      (H.map b) (H.map (χM.hom.app P.complex)) := ⟨h₂.symm⟩
  have s₃ : CommSq (P.isoLeftDerivedObj (U ⋙ L) n).inv (H.map b)
      ((NatTrans.leftDerived (whiskerLeft U τ) n).app X)
      (P.isoLeftDerivedObj (U ⋙ M) n).inv := ⟨h₃.symm⟩
  exact (s₁.horiz_comp (s₂.horiz_comp s₃)).w.symm

end Derived

end CategoryTheory.Functor
