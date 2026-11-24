/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.Injective.MapResolution
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.NatIso
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Right-derived precomposition using mapped injective resolutions
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
variable (B : D ⥤ A) [B.Additive]

/-- Composite-complex homology is compared with the mapped resolution. -/
def rightDerivedPrecompHomologyIso (q : ℕ) {X : C} (I : InjectiveResolution X) :
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).obj
        (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).obj
        ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (F.mapInjectiveResolution I).cocomplex) :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).mapIso
    (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ B)) (ComplexShape.up ℕ)).app
      I.cocomplex).symm)

/-- An arbitrary resolution gives the right-derived precomposition map. -/
def rightDerivedPrecompIsoWithResolution (q : ℕ) {X : C} (I : InjectiveResolution X) :
    ((F ⋙ B).rightDerived q).obj X ≅ (B.rightDerived q).obj (F.obj X) :=
  I.isoRightDerivedObj (F ⋙ B) q ≪≫
    rightDerivedPrecompHomologyIso F B q I ≪≫
      ((F.mapInjectiveResolution I).isoRightDerivedObj B q).symm

/-- Naturality uses the SAME mapped cocomplex morphism and augmentation. -/
theorem rightDerivedPrecompIsoWithResolution_naturality (q : ℕ)
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : InjectiveResolution.Hom I J f) :
    ((F ⋙ B).rightDerived q).map f ≫
        (rightDerivedPrecompIsoWithResolution F B q J).hom =
      (rightDerivedPrecompIsoWithResolution F B q I).hom ≫
        (B.rightDerived q).map (F.map f) := by
  let aI := I.isoRightDerivedObj (F ⋙ B) q
  let aJ := J.isoRightDerivedObj (F ⋙ B) q
  let bI := rightDerivedPrecompHomologyIso F B q I
  let bJ := rightDerivedPrecompHomologyIso F B q J
  let cI := (F.mapInjectiveResolution I).isoRightDerivedObj B q
  let cJ := (F.mapInjectiveResolution J).isoRightDerivedObj B q
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
  let φF := F.mapInjectiveResolutionHom φ
  have ha : ((F ⋙ B).rightDerived q).map f ≫ aJ.hom =
      aI.hom ≫ H.map (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) := by
    rw [(F ⋙ B).rightDerived_map_eq q f φ.hom φ.ι_comp_hom]
    change (aI.hom ≫ H.map (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)
      ≫ aJ.inv) ≫ aJ.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hb : H.map (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫
      bJ.hom = bI.hom ≫ H.map ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map φF.hom) := by
    exact (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ B)) (ComplexShape.up ℕ)).symm
      H).hom.naturality φ.hom
  have hc : cI.inv ≫ (B.rightDerived q).map (F.map f) =
      H.map ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map φF.hom) ≫ cJ.inv := by
    rw [B.rightDerived_map_eq q (F.map f) φF.hom φF.ι_comp_hom]
    change cI.inv ≫ (cI.hom ≫ H.map
      ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map φF.hom) ≫ cJ.inv) = _
    simp only [Iso.inv_hom_id_assoc]
  change ((F ⋙ B).rightDerived q).map f ≫ (aJ.hom ≫ bJ.hom ≫ cJ.inv) =
    (aI.hom ≫ bI.hom ≫ cI.inv) ≫ (B.rightDerived q).map (F.map f)
  calc
    _ = (((F ⋙ B).rightDerived q).map f ≫ aJ.hom) ≫ bJ.hom ≫ cJ.inv := by
      simp only [Category.assoc]
    _ = (aI.hom ≫ H.map
      (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)) ≫
        bJ.hom ≫ cJ.inv := by rw [ha]
    _ = aI.hom ≫ (H.map
      (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫ bJ.hom) ≫
        cJ.inv := by simp only [Category.assoc]
    _ = aI.hom ≫ (bI.hom ≫ H.map
      ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map φF.hom)) ≫ cJ.inv := by rw [hb]
    _ = (aI.hom ≫ bI.hom) ≫ (H.map
      ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map φF.hom) ≫ cJ.inv) := by
      simp only [Category.assoc]
    _ = (aI.hom ≫ bI.hom) ≫ (cI.inv ≫ (B.rightDerived q).map (F.map f)) := by rw [← hc]
    _ = _ := by simp only [Category.assoc]

/-- Every resolution choice gives the SAME precomposition component. -/
theorem rightDerivedPrecompIsoWithResolution_eq (q : ℕ) {X : C}
    (I J : InjectiveResolution X) :
    rightDerivedPrecompIsoWithResolution F B q I =
      rightDerivedPrecompIsoWithResolution F B q J := by
  let φ := InjectiveResolution.descHom (𝟙 X) I J
  have h := rightDerivedPrecompIsoWithResolution_naturality F B q (𝟙 X) I J φ
  apply Iso.ext
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- The all-object natural isomorphism uses the chosen resolution only as a provider. -/
def rightDerivedPrecompIso (q : ℕ) : (F ⋙ B).rightDerived q ≅ F ⋙ B.rightDerived q :=
  NatIso.ofComponents
    (fun X => rightDerivedPrecompIsoWithResolution F B q (injectiveResolution X))
    (fun f => by
      let φ := InjectiveResolution.descHom f (injectiveResolution _) (injectiveResolution _)
      exact rightDerivedPrecompIsoWithResolution_naturality F B q f
        (injectiveResolution _) (injectiveResolution _) φ)

/-- The fixed natural family retains the comparison computed from ANY original resolution. -/
theorem rightDerivedPrecompIso_app_eq (q : ℕ) {X : C} (I : InjectiveResolution X) :
    (rightDerivedPrecompIso F B q).app X = rightDerivedPrecompIsoWithResolution F B q I :=
  rightDerivedPrecompIsoWithResolution_eq F B q (injectiveResolution X) I


omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- The mapped single-object augmentation keeps its literal degree-zero component. -/
theorem mapInjectiveResolution_iota_zero {X : C} (I : InjectiveResolution X) :
    (F.mapInjectiveResolution I).ι.f 0 = F.map (I.ι.f 0) := by
  dsimp only [Functor.mapInjectiveResolution]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  erw [Functor.map_id]
  change (𝟙 (F.obj X) ≫ 𝟙 (F.obj X)) ≫ F.map (I.ι.f 0) = F.map (I.ι.f 0)
  simp only [Category.id_comp]
  rfl

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- At zero the complex-composition map preserves the canonical augmentation cycles. -/
theorem rightDerivedPrecomp_cycles_zero {X : C} (I : InjectiveResolution X) :
    I.toRightDerivedZero' (F ⋙ B) ≫ HomologicalComplex.cyclesMap
      (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ B))
        (ComplexShape.up ℕ)).app I.cocomplex).inv) 0 =
      (F.mapInjectiveResolution I).toRightDerivedZero' B := by
  apply (cancel_mono (HomologicalComplex.iCycles
    ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (F.mapInjectiveResolution I).cocomplex) 0)).1
  erw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  rw [mapInjectiveResolution_iota_zero]
  change (F ⋙ B).map (I.ι.f 0) ≫ 𝟙 _ = B.map (F.map (I.ι.f 0))
  exact Category.comp_id _

/-- The precomposition comparison intertwines the canonical zero-derived maps. -/
theorem rightDerivedPrecompIsoWithResolution_toRightDerivedZero {X : C}
    (I : InjectiveResolution X) :
    (F ⋙ B).toRightDerivedZero.app X ≫
      (rightDerivedPrecompIsoWithResolution F B 0 I).hom =
      B.toRightDerivedZero.app (F.obj X) := by
  rw [I.toRightDerivedZero_eq (F ⋙ B),
    (F.mapInjectiveResolution I).toRightDerivedZero_eq B]
  simp only [rightDerivedPrecompIsoWithResolution, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc
    ((((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).leftHomologyπ
    ((((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).leftHomologyIso.hom]
  rw [← ShortComplex.homologyπ]
  simp only [CochainComplex.isoHomologyπ₀, HomologicalComplex.isoHomologyπ_hom]
  change I.toRightDerivedZero' (F ⋙ B) ≫
      (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
      HomologicalComplex.homologyMap
        (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ B))
          (ComplexShape.up ℕ)).app I.cocomplex).inv) 0 ≫
      ((F.mapInjectiveResolution I).isoRightDerivedObj B 0).inv =
    (F.mapInjectiveResolution I).toRightDerivedZero' B ≫
      ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (F.mapInjectiveResolution I).cocomplex).homologyπ 0 ≫
      ((F.mapInjectiveResolution I).isoRightDerivedObj B 0).inv
  erw [HomologicalComplex.homologyπ_naturality_assoc,
    ← Category.assoc, rightDerivedPrecomp_cycles_zero]
  rfl

/-- The fixed natural family preserves zero normalization for every original object. -/
theorem rightDerivedPrecompIso_toRightDerivedZero (X : C) :
    (F ⋙ B).toRightDerivedZero.app X ≫ (rightDerivedPrecompIso F B 0).hom.app X =
      B.toRightDerivedZero.app (F.obj X) :=
  rightDerivedPrecompIsoWithResolution_toRightDerivedZero F B (injectiveResolution X)


omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- Every resolution morphism induces the same homology-composition square. -/
theorem rightDerivedPrecompHomologyIso_naturality (q : ℕ)
    {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫
      (rightDerivedPrecompHomologyIso F B q J).hom =
    (rightDerivedPrecompHomologyIso F B q I).hom ≫
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (F.mapInjectiveResolutionHom φ).hom) :=
  (isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ B)) (ComplexShape.up ℕ)).symm
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q)).hom.naturality φ.hom

/-- The component formula is also available directly for its forward morphism. -/
theorem rightDerivedPrecompIso_hom_app_eq (q : ℕ) {X : C} (I : InjectiveResolution X) :
    (rightDerivedPrecompIso F B q).hom.app X =
      (rightDerivedPrecompIsoWithResolution F B q I).hom :=
  congrArg Iso.hom (rightDerivedPrecompIso_app_eq F B q I)

/-- Canonical zero-derived identifications retain the precomposition map. -/
theorem rightDerivedPrecompIso_zeroIsoSelf
    [PreservesFiniteLimits (F ⋙ B)] [PreservesFiniteLimits B] (X : C) :
    (rightDerivedPrecompIso F B 0).hom.app X ≫
        B.rightDerivedZeroIsoSelf.hom.app (F.obj X) =
      (F ⋙ B).rightDerivedZeroIsoSelf.hom.app X := by
  apply (cancel_epi ((F ⋙ B).toRightDerivedZero.app X)).1
  rw [← Category.assoc, rightDerivedPrecompIso_toRightDerivedZero,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app]
  rfl

end CategoryTheory.Functor


namespace CategoryTheory.NatTrans
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable {P Q : C ⥤ A} [P.Additive] [Q.Additive]

omit [HasInjectiveResolutions C] in
/-- A termwise natural transformation carries the augmentation cycles to each other. -/
theorem mapHomologicalComplex_toRightDerivedZero' (α : P ⟶ Q)
    {X : C} (I : InjectiveResolution X) :
    I.toRightDerivedZero' P ≫ HomologicalComplex.cyclesMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app I.cocomplex) 0 =
      α.app X ≫ I.toRightDerivedZero' Q := by
  apply (cancel_mono (HomologicalComplex.iCycles
    ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) 0)).1
  erw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  change P.map (I.ι.f 0) ≫ α.app (I.cocomplex.X 0) = α.app X ≫ Q.map (I.ι.f 0)
  exact α.naturality (I.ι.f 0)

/-- The derived natural transformation respects the canonical degree-zero maps. -/
theorem rightDerived_toRightDerivedZero (α : P ⟶ Q) (X : C) :
    P.toRightDerivedZero.app X ≫ (NatTrans.rightDerived α 0).app X =
      α.app X ≫ Q.toRightDerivedZero.app X := by
  let I := injectiveResolution X
  rw [I.toRightDerivedZero_eq P, I.toRightDerivedZero_eq Q]
  change (I.toRightDerivedZero' P ≫
      ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
      (I.isoRightDerivedObj P 0).inv) ≫ (NatTrans.rightDerived α 0).app X =
    α.app X ≫ I.toRightDerivedZero' Q ≫
      ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ 0 ≫
      (I.isoRightDerivedObj Q 0).inv
  erw [Category.assoc, Category.assoc,
    ← I.isoRightDerivedObj_inv_naturality_functor α 0,
    HomologicalComplex.homologyπ_naturality_assoc,
    ← Category.assoc, mapHomologicalComplex_toRightDerivedZero']
  exact Category.assoc _ _ _

end CategoryTheory.NatTrans

namespace CategoryTheory.NatIso
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable {P Q : C ⥤ A} [P.Additive] [Q.Additive]



/-- A fixed derived natural isomorphism respects both canonical degree-zero identifications. -/
theorem rightDerived_zeroIsoSelf [PreservesFiniteLimits P] [PreservesFiniteLimits Q]
    (α : P ≅ Q) (X : C) :
    (rightDerived α 0).hom.app X ≫ Q.rightDerivedZeroIsoSelf.hom.app X =
      P.rightDerivedZeroIsoSelf.hom.app X ≫ α.hom.app X := by
  apply (cancel_epi (P.toRightDerivedZero.app X)).1
  change P.toRightDerivedZero.app X ≫
      ((NatTrans.rightDerived α.hom 0).app X ≫ Q.rightDerivedZeroIsoSelf.hom.app X) = _
  rw [← Category.assoc, NatTrans.rightDerived_toRightDerivedZero, Category.assoc,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app, Category.comp_id,
    ← Category.assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app, Category.id_comp]

end CategoryTheory.NatIso



namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
variable (B : D ⥤ A) [B.Additive]
variable {P : C ⥤ A} [P.Additive]

/-- A fixed underived comparison is followed by right-derived precomposition. -/
def rightDerivedPrecompIsoOfIso (α : P ≅ F ⋙ B) (q : ℕ) :
    P.rightDerived q ≅ F ⋙ B.rightDerived q :=
  NatIso.rightDerived α q ≪≫ rightDerivedPrecompIso F B q

/-- The fixed all-degree comparison is computed on ANY source resolution. -/
theorem rightDerivedPrecompIsoOfIso_resolution_formula
    (α : P ≅ F ⋙ B) (q : ℕ) {X : C} (I : InjectiveResolution X) :
    (rightDerivedPrecompIsoOfIso F B α q).hom.app X =
      (I.isoRightDerivedObj P q).hom ≫
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex) ≫
      (rightDerivedPrecompHomologyIso F B q I).hom ≫
      ((F.mapInjectiveResolution I).isoRightDerivedObj B q).inv := by
  let a := I.isoRightDerivedObj (F ⋙ B) q
  let b := rightDerivedPrecompHomologyIso F B q I
  let c := (F.mapInjectiveResolution I).isoRightDerivedObj B q
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
  have hα : (NatTrans.rightDerived α.hom q).app X ≫ a.hom =
      (I.isoRightDerivedObj P q).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex) :=
    I.isoRightDerivedObj_hom_naturality_functor α.hom q
  have hp : (rightDerivedPrecompIso F B q).hom.app X = a.hom ≫ b.hom ≫ c.inv := by
    simpa only [rightDerivedPrecompIsoWithResolution, Iso.trans_hom, Iso.symm_hom,
      a, b, c, Category.assoc] using rightDerivedPrecompIso_hom_app_eq F B q I
  change (NatTrans.rightDerived α.hom q).app X ≫
    (rightDerivedPrecompIso F B q).hom.app X = _
  rw [hp]
  calc
    _ = ((NatTrans.rightDerived α.hom q).app X ≫ a.hom) ≫ b.hom ≫ c.inv := by
      simp only [Category.assoc]
    _ = ((I.isoRightDerivedObj P q).hom ≫ H.map
        ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex)) ≫
          b.hom ≫ c.inv := by rw [hα]
    _ = _ := by
      simp only [Category.assoc]
      rfl

/-- The full comparison retains the zero-derived map of its source functor. -/
theorem rightDerivedPrecompIsoOfIso_toRightDerivedZero
    (α : P ≅ F ⋙ B) (X : C) :
    P.toRightDerivedZero.app X ≫ (rightDerivedPrecompIsoOfIso F B α 0).hom.app X =
      α.hom.app X ≫ B.toRightDerivedZero.app (F.obj X) := by
  change P.toRightDerivedZero.app X ≫
    ((NatTrans.rightDerived α.hom 0).app X ≫ (rightDerivedPrecompIso F B 0).hom.app X) = _
  rw [← Category.assoc, NatTrans.rightDerived_toRightDerivedZero, Category.assoc,
    rightDerivedPrecompIso_toRightDerivedZero]

/-- Both zero-derived identifications recover the originally fixed comparison. -/
theorem rightDerivedPrecompIsoOfIso_zeroIsoSelf
    [PreservesFiniteLimits P] [PreservesFiniteLimits B] (α : P ≅ F ⋙ B) (X : C) :
    (rightDerivedPrecompIsoOfIso F B α 0).hom.app X ≫
        B.rightDerivedZeroIsoSelf.hom.app (F.obj X) =
      P.rightDerivedZeroIsoSelf.hom.app X ≫ α.hom.app X := by
  apply (cancel_epi (P.toRightDerivedZero.app X)).1
  rw [← Category.assoc, rightDerivedPrecompIsoOfIso_toRightDerivedZero, Category.assoc,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app]
  erw [Category.comp_id, ← Category.assoc,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app, Category.id_comp]

end CategoryTheory.Functor


namespace CategoryTheory.InjectiveResolution
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]

/--
The canonical resolution-choice comparison is the homology map of ANY bundled comparison over the
identity.
-/
theorem cohomologyComparisonIso_hom_eq_map {X : C} {I J : InjectiveResolution X}
    (φ : InjectiveResolution.Hom I J (𝟙 X)) (P : C ⥤ A) [P.Additive] (q : ℕ) :
    (cohomologyComparisonIso I J P q).hom =
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) := by
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
  let aI := I.isoRightDerivedObj P q
  let aJ := J.isoRightDerivedObj P q
  have hn : (P.rightDerived q).map (𝟙 X) ≫ aJ.hom =
      aI.hom ≫ H.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) := by
    rw [P.rightDerived_map_eq q (𝟙 X) φ.hom φ.ι_comp_hom]
    change (aI.hom ≫ H.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)
      ≫ aJ.inv) ≫ aJ.hom = aI.hom ≫
        H.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi aI.hom).1
  change aI.hom ≫ (aI.inv ≫ aJ.hom) = _
  rw [Iso.hom_inv_id_assoc]
  simpa only [Functor.map_id, Category.id_comp] using hn

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
variable (B : D ⥤ A) [B.Additive]
variable {P : C ⥤ A} [P.Additive]

/-- The fixed underived map is applied term by term on the same resolution. -/
def rightDerivedPrecompHomologyIsoOfIso (α : P ≅ F ⋙ B) (q : ℕ)
    {X : C} (I : InjectiveResolution X) :
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).obj
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).obj
        ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (F.mapInjectiveResolution I).cocomplex) :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).mapIso
    ((NatIso.mapHomologicalComplex α (ComplexShape.up ℕ)).app I.cocomplex) ≪≫
      rightDerivedPrecompHomologyIso F B q I

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- Every source-resolution map gives the literal homology square. -/
theorem rightDerivedPrecompHomologyIsoOfIso_naturality (α : P ≅ F ⋙ B) (q : ℕ)
    {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫
      (rightDerivedPrecompHomologyIsoOfIso F B α q J).hom =
    (rightDerivedPrecompHomologyIsoOfIso F B α q I).hom ≫
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q).map
        ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (F.mapInjectiveResolutionHom φ).hom) := by
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) q
  let aI := H.map ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex)
  let aJ := H.map ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app J.cocomplex)
  have ha : H.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫ aJ =
      aI ≫ H.map (((F ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) :=
    (isoWhiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℕ)) H).hom.naturality φ.hom
  have hb := rightDerivedPrecompHomologyIso_naturality F B q φ
  change H.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map φ.hom) ≫
      (aJ ≫ (rightDerivedPrecompHomologyIso F B q J).hom) =
    (aI ≫ (rightDerivedPrecompHomologyIso F B q I).hom) ≫
      H.map ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map
        (F.mapInjectiveResolutionHom φ).hom)
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

/-- Every canonical resolution choice comparison commutes with the SAME termwise map. -/
theorem rightDerivedPrecompHomologyIsoOfIso_comparison (α : P ≅ F ⋙ B) (q : ℕ)
    {X : C} (I J : InjectiveResolution X) :
    (InjectiveResolution.cohomologyComparisonIso I J P q).hom ≫
        (rightDerivedPrecompHomologyIsoOfIso F B α q J).hom =
      (rightDerivedPrecompHomologyIsoOfIso F B α q I).hom ≫
        (InjectiveResolution.cohomologyComparisonIso
          (F.mapInjectiveResolution I) (F.mapInjectiveResolution J) B q).hom := by
  let φ := InjectiveResolution.descHom (𝟙 X) I J
  let ψ := (F.mapInjectiveResolutionHom φ).cast (F.map_id X)
  have hl := InjectiveResolution.cohomologyComparisonIso_hom_eq_map φ P q
  have hr := InjectiveResolution.cohomologyComparisonIso_hom_eq_map ψ B q
  rw [hl, hr]
  exact rightDerivedPrecompHomologyIsoOfIso_naturality F B α q φ

/-- The arbitrary-resolution formula uses the exact termwise natural isomorphism. -/
theorem rightDerivedPrecompIsoOfIso_resolution_iso (α : P ≅ F ⋙ B) (q : ℕ)
    {X : C} (I : InjectiveResolution X) :
    (rightDerivedPrecompIsoOfIso F B α q).hom.app X =
      (I.isoRightDerivedObj P q).hom ≫
        (rightDerivedPrecompHomologyIsoOfIso F B α q I).hom ≫
          ((F.mapInjectiveResolution I).isoRightDerivedObj B q).inv := by
  have he : ((NatIso.mapHomologicalComplex α (ComplexShape.up ℕ)).app I.cocomplex).hom =
      (NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I.cocomplex := rfl
  simpa only [rightDerivedPrecompHomologyIsoOfIso, Iso.trans_hom, Functor.mapIso_hom,
    he, Category.assoc] using rightDerivedPrecompIsoOfIso_resolution_formula F B α q I

end CategoryTheory.Functor


namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
variable (B : D ⥤ A) [B.Additive] [PreservesFiniteLimits B]
variable {P : C ⥤ A} [P.Additive]

/-- A source section goes through the zero-derived comparison to the fixed underived map. -/
theorem rightDerivedPrecompIsoOfIso_zero_section (α : P ≅ F ⋙ B) (X : C) :
    P.toRightDerivedZero.app X ≫
      (rightDerivedPrecompIsoOfIso F B α 0).hom.app X ≫
        B.rightDerivedZeroIsoSelf.hom.app (F.obj X) = α.hom.app X := by
  rw [← Category.assoc, rightDerivedPrecompIsoOfIso_toRightDerivedZero, Category.assoc,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app]
  erw [Category.comp_id]

end CategoryTheory.Functor
