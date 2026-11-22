/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex

import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.ScalarActionTransport

/-!
# The actual scalar-extension/ambient-tensor mate

The proved original cotensor scalar comparison gives the actual isomorphism
between scalar extension followed by ambient tensor and the other original
order. The mate is formed from the actual balanced scalar adjunction and
the original ambient tensor-Hom adjunctions. Its complete unit comparison
retains the original scalar unit and literal ambient tensor map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.Mod.ExtensionOfScalars
open scoped CategoryTheory.MonObj

namespace CategoryTheory.HomogeneousLocalization.ScalarActionTransport

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
  {A B : C} [MonObj A] [MonObj B] (p : A ⟶ B) [IsMonHom p]
  [HasCoequalizers (Mod C B)]

/-- The actual extension/tensor comparison is the original cotensor scalar mate. -/
def inductionTensorIso (U : C) :
    Mod.AmbientTensor.functor A U ⋙ induction p ≅ induction p ⋙ Mod.AmbientTensor.functor B U :=
  asIso ((conjugateEquiv
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).comp (AmbientTensorHom.adjunction B U))
    ((AmbientTensorHom.adjunction A U).comp (CategoryTheory.Mod.ExtensionOfScalars.adjunction p))).symm
      (cotensorNatIso p U).inv)

/-- The actual whole mate retains the original inverse cotensor comparison. -/
theorem inductionTensorIso_conjugate (U : C) :
    conjugateEquiv
      ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).comp (AmbientTensorHom.adjunction B U))
      ((AmbientTensorHom.adjunction A U).comp (CategoryTheory.Mod.ExtensionOfScalars.adjunction p))
      (inductionTensorIso p U).hom = (cotensorNatIso p U).inv := by
  exact (conjugateEquiv
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).comp (AmbientTensorHom.adjunction B U))
    ((AmbientTensorHom.adjunction A U).comp (CategoryTheory.Mod.ExtensionOfScalars.adjunction p))).apply_symm_apply _

/-- Both actual composite-adjunction units retain the same whole original scalar/tensor mate. -/
theorem inductionTensorIso_unit (U : C) (M : Mod C A) :
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).comp (AmbientTensorHom.adjunction B U)).unit.app M ≫
        (cotensorNatIso p U).inv.app (((induction p) ⋙ Mod.AmbientTensor.functor B U).obj M) =
      ((AmbientTensorHom.adjunction A U).comp (CategoryTheory.Mod.ExtensionOfScalars.adjunction p)).unit.app M ≫
        (restriction p ⋙ AmbientTensorHom.rightFunctor A U).map ((inductionTensorIso p U).hom.app M) :=
  unit_conjugateEquiv_symm
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).comp (AmbientTensorHom.adjunction B U))
    ((AmbientTensorHom.adjunction A U).comp (CategoryTheory.Mod.ExtensionOfScalars.adjunction p))
    (cotensorNatIso p U).inv M

/-- The actual mate preserves the literal original scalar unit and tensoring of that unit. -/
theorem inductionTensorIso_unit_hom (U : C) (M : Mod C A) :
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app ((Mod.AmbientTensor.functor A U).obj M)).hom ≫
        ((inductionTensorIso p U).hom.app M).hom =
      U ◁ ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom := by
  let g : ((induction p).obj ((Mod.AmbientTensor.functor A U).obj M)).X ⟶ U ⊗ ((induction p).obj M).X :=
    ((inductionTensorIso p U).hom.app M).hom
  let e : M.X ⟶ ((induction p).obj M).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom
  let eU : U ⊗ M.X ⟶ ((induction p).obj ((Mod.AmbientTensor.functor A U).obj M)).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app ((Mod.AmbientTensor.functor A U).obj M)).hom
  have h := congrArg Mod.Hom.hom (inductionTensorIso_unit p U M)
  simp only [Adjunction.comp_unit_app, Mod.comp_hom', Functor.comp_map, cotensorNatIso,
    NatIso.ofComponents_inv_app, cotensorIso_inv, Category.assoc] at h
  dsimp only [restriction, Mod.comap, AmbientTensorHom.rightFunctor] at h
  simp only [AmbientTensorHom.cotensorMap_hom, AmbientTensorHom.coevaluation_hom] at h
  change e ≫ (ihom.coev U).app ((induction p).obj M).X ≫ 𝟙 _ =
    (ihom.coev U).app M.X ≫ (ihom U).map eU ≫ (ihom U).map g at h
  have h0 : e ≫ (ihom.coev U).app ((induction p).obj M).X =
      (ihom.coev U).app M.X ≫ (ihom U).map eU ≫ (ihom U).map g :=
    (congrArg (fun f => e ≫ f) (Category.comp_id _)).symm.trans h
  rw [← Functor.map_comp] at h0
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_eq, MonoidalClosed.curry_eq]
  exact h0.symm.trans ((ihom.coev U).naturality e)

/-- The original balanced inverse Hom function reconstructs the whole actual extension/tensor mate. -/
theorem inductionTensorIso_original (U : C) (M : Mod C A) :
    (inductionTensorIso p U).hom.app M = fromRestriction p
      ((Mod.AmbientTensor.functor A U).map ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M) ≫
        (tensorIso p U ((induction p).obj M)).hom) := by
  let X := (Mod.AmbientTensor.functor A U).obj M
  let Y := (Mod.AmbientTensor.functor B U).obj ((induction p).obj M)
  let g : X ⟶ (restriction p).obj Y :=
    (Mod.AmbientTensor.functor A U).map ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M) ≫
      (tensorIso p U ((induction p).obj M)).hom
  let e := (CategoryTheory.Mod.ExtensionOfScalars.adjunction p).homEquiv X Y
  have hg : e (fromRestriction p g) = g :=
    (congrArg (fun f => f (fromRestriction p g))
      (CategoryTheory.Mod.ExtensionOfScalars.adjunction_homEquiv p X Y)).trans
        ((homEquiv p X Y).apply_symm_apply g)
  have he : e ((inductionTensorIso p U).hom.app M) = g := by
    apply Mod.hom_ext
    have hf := congrArg Mod.Hom.hom
      ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).homEquiv_unit X Y
        ((inductionTensorIso p U).hom.app M))
    calc
      (e ((inductionTensorIso p U).hom.app M)).hom =
          ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app X).hom ≫
            ((inductionTensorIso p U).hom.app M).hom := hf
      _ = U ◁ ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom :=
        inductionTensorIso_unit_hom p U M
      _ = g.hom := by
        change _ =
          ((Mod.AmbientTensor.functor A U).map ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M)).hom ≫
            (tensorIso p U ((induction p).obj M)).hom.hom
        rw [Mod.AmbientTensor.functor_map_hom, tensorIso_hom]
        exact (Category.comp_id _).symm
  exact e.injective (he.trans hg.symm)

/-- The literal original free-generator quotient map retains the original scalar/tensor characteristic. -/
theorem inductionTensorIso_projection (U : C) (M : Mod C A) :
    (π p ((Mod.AmbientTensor.functor A U).obj M)).hom ≫ ((inductionTensorIso p U).hom.app M).hom =
      eqToHom (Mod.free_obj B (U ⊗ M.X)) ≫
        (B ◁ (U ◁ ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom)) ≫
          ((Mod.AmbientTensor.functor B U).obj ((induction p).obj M)).mod.smul := by
  rw [inductionTensorIso_original]
  have h := congrArg Mod.Hom.hom (π_fromRestriction p
    ((Mod.AmbientTensor.functor A U).map ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M) ≫
      (tensorIso p U ((induction p).obj M)).hom))
  simp only [Mod.comp_hom'] at h
  let N := (Mod.AmbientTensor.functor B U).obj ((induction p).obj M)
  let g : ((Mod.AmbientTensor.functor A U).obj M) ⟶ (restriction p).obj N :=
    (Mod.AmbientTensor.functor A U).map ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M) ≫
      (tensorIso p U ((induction p).obj M)).hom
  have hg : g.hom = U ◁ ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom := by
    change ((Mod.AmbientTensor.functor A U).map
      ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M)).hom ≫
        (tensorIso p U ((induction p).obj M)).hom.hom = _
    rw [Mod.AmbientTensor.functor_map_hom, tensorIso_hom]
    exact Category.comp_id _
  change _ = (((Mod.freeForgetAdjunction B).homEquiv
    ((Mod.AmbientTensor.functor A U).obj M).X N).symm g.hom).hom at h
  rw [hg] at h
  have hf := Mod.freeForgetAdjunction_homEquiv_symm_apply_hom B N g.hom
  rw [hg] at hf
  exact h.trans hf

omit [BraidedCategory C] [MonoidalClosed C] in
/-- The actual original scalar unit detects equality of whole extension maps. -/
theorem induction_hom_ext {M : Mod C A} {N : Mod C B} (f g : (induction p).obj M ⟶ N)
    (h : ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom ≫ f.hom =
      ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom ≫ g.hom) : f = g := by
  apply ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).homEquiv M N).injective
  apply Mod.hom_ext
  have hf := congrArg Mod.Hom.hom ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).homEquiv_unit M N f)
  have hg := congrArg Mod.Hom.hom ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).homEquiv_unit M N g)
  exact hf.trans (h.trans hg.symm)

/-- Every original tensor-coordinate arrow retains the whole actual scalar/tensor comparison square. -/
theorem inductionTensorIso_coordinate {U V : C} (a : U ⟶ V) (M : Mod C A) :
    (induction p).map ((Mod.AmbientTensor.coefficientNatTrans A a).app M) ≫
        (inductionTensorIso p V).hom.app M =
      (inductionTensorIso p U).hom.app M ≫
        (Mod.AmbientTensor.coefficientNatTrans B a).app ((induction p).obj M) := by
  let aA := (Mod.AmbientTensor.coefficientNatTrans A a).app M
  let aB := (Mod.AmbientTensor.coefficientNatTrans B a).app ((induction p).obj M)
  let e : M.X ⟶ ((induction p).obj M).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom
  let eU : U ⊗ M.X ⟶ ((induction p).obj ((Mod.AmbientTensor.functor A U).obj M)).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app ((Mod.AmbientTensor.functor A U).obj M)).hom
  let eV : V ⊗ M.X ⟶ ((induction p).obj ((Mod.AmbientTensor.functor A V).obj M)).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app ((Mod.AmbientTensor.functor A V).obj M)).hom
  have hn : eU ≫ ((induction p).map aA).hom = aA.hom ≫ eV :=
    (congrArg Mod.Hom.hom ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.naturality aA)).symm
  have hA : aA.hom = a ▷ M.X := by
    change (Mod.AmbientTensor.map A a (𝟙 M)).hom = _
    rw [Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id]
  have hB : aB.hom = a ▷ ((induction p).obj M).X := by
    change (Mod.AmbientTensor.map B a (𝟙 ((induction p).obj M))).hom = _
    rw [Mod.AmbientTensor.map_hom, Mod.id_hom', tensorHom_id]
  apply induction_hom_ext p
  change eU ≫ (((induction p).map aA).hom ≫ ((inductionTensorIso p V).hom.app M).hom) =
    eU ≫ (((inductionTensorIso p U).hom.app M).hom ≫ aB.hom)
  calc
    eU ≫ (((induction p).map aA).hom ≫ ((inductionTensorIso p V).hom.app M).hom) =
        aA.hom ≫ (eV ≫ ((inductionTensorIso p V).hom.app M).hom) := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = (a ▷ M.X) ≫ (V ◁ e) := by rw [inductionTensorIso_unit_hom, hA]
    _ = (U ◁ e) ≫ (a ▷ ((induction p).obj M).X) := (whisker_exchange a e).symm
    _ = eU ≫ (((inductionTensorIso p U).hom.app M).hom ≫ aB.hom) := by
      rw [← Category.assoc, inductionTensorIso_unit_hom, hB]

section Identity

variable [HasCoequalizers (Mod C A)]

/-- The original scalar identity comparison and ambient tensor identity route have the same whole map. -/
theorem inductionTensorIso_id (U : C) (M : Mod C A) :
    (inductionTensorIso (𝟙 A) U).hom.app M ≫
        (Mod.AmbientTensor.functor A U).map ((inductionIdIso (A := A)).hom.app M) =
      (inductionIdIso (A := A)).hom.app ((Mod.AmbientTensor.functor A U).obj M) := by
  let e : M.X ⟶ ((induction (𝟙 A)).obj M).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction (𝟙 A)).unit.app M).hom
  let eU : U ⊗ M.X ⟶ ((induction (𝟙 A)).obj ((Mod.AmbientTensor.functor A U).obj M)).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction (𝟙 A)).unit.app ((Mod.AmbientTensor.functor A U).obj M)).hom
  have hM : e ≫ ((inductionIdIso (A := A)).hom.app M).hom = 𝟙 M.X := by
    simpa only [e, unit_hom] using (inductionIdIso_generator M)
  have hU : eU ≫ ((inductionIdIso (A := A)).hom.app ((Mod.AmbientTensor.functor A U).obj M)).hom =
      𝟙 ((Mod.AmbientTensor.functor A U).obj M).X := by
    simpa only [eU, unit_hom] using (inductionIdIso_generator ((Mod.AmbientTensor.functor A U).obj M))
  apply induction_hom_ext (𝟙 A)
  change eU ≫ (((inductionTensorIso (𝟙 A) U).hom.app M).hom ≫
      ((Mod.AmbientTensor.functor A U).map ((inductionIdIso (A := A)).hom.app M)).hom) = _
  calc
    eU ≫ (((inductionTensorIso (𝟙 A) U).hom.app M).hom ≫
        ((Mod.AmbientTensor.functor A U).map ((inductionIdIso (A := A)).hom.app M)).hom) =
      (U ◁ e) ≫ (U ◁ ((inductionIdIso (A := A)).hom.app M).hom) := by
        rw [← Category.assoc, inductionTensorIso_unit_hom, Mod.AmbientTensor.functor_map_hom]
    _ = U ◁ (e ≫ ((inductionIdIso (A := A)).hom.app M).hom) := (whiskerLeft_comp _ _ _).symm
    _ = 𝟙 (U ⊗ M.X) := by rw [hM, whiskerLeft_id]
    _ = eU ≫ ((inductionIdIso (A := A)).hom.app ((Mod.AmbientTensor.functor A U).obj M)).hom := hU.symm

end Identity

section Composition

variable {D : C} [MonObj D] (q : B ⟶ D) [IsMonHom q] [HasCoequalizers (Mod C D)]

omit [BraidedCategory C] [MonoidalClosed C] in
/-- Both original scalar units detect equality of the whole two-step extension maps. -/
theorem induction_composite_hom_ext {M : Mod C A} {N : Mod C D}
    (f g : (induction q).obj ((induction p).obj M) ⟶ N)
    (h : ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom ≫
        ((CategoryTheory.Mod.ExtensionOfScalars.adjunction q).unit.app ((induction p).obj M)).hom ≫ f.hom =
      ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom ≫
        ((CategoryTheory.Mod.ExtensionOfScalars.adjunction q).unit.app ((induction p).obj M)).hom ≫ g.hom) :
    f = g := by
  let a := (CategoryTheory.Mod.ExtensionOfScalars.adjunction p).comp
    (CategoryTheory.Mod.ExtensionOfScalars.adjunction q)
  apply (a.homEquiv M N).injective
  apply Mod.hom_ext
  have hu : (a.unit.app M).hom =
      ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom ≫
        ((CategoryTheory.Mod.ExtensionOfScalars.adjunction q).unit.app ((induction p).obj M)).hom := by
    rw [Adjunction.comp_unit_app, Mod.comp_hom']
    rfl
  have hf := congrArg Mod.Hom.hom (a.homEquiv_unit M N f)
  have hg := congrArg Mod.Hom.hom (a.homEquiv_unit M N g)
  have hh : (a.unit.app M).hom ≫ f.hom = (a.unit.app M).hom ≫ g.hom := by
    rw [hu, Category.assoc, Category.assoc]
    exact h
  exact hf.trans (hh.trans hg.symm)

/-- The actual scalar compositor and both tensor mates retain the same original complete extension route. -/
theorem inductionTensorIso_comp (U : C) (M : Mod C A) :
    (induction q).map ((inductionTensorIso p U).hom.app M) ≫
        (inductionTensorIso q U).hom.app ((induction p).obj M) ≫
          (Mod.AmbientTensor.functor D U).map ((inductionCompIso p q).hom.app M) =
      (inductionCompIso p q).hom.app ((Mod.AmbientTensor.functor A U).obj M) ≫
        (inductionTensorIso (p ≫ q) U).hom.app M := by
  let X := (Mod.AmbientTensor.functor A U).obj M
  let a := (inductionTensorIso p U).hom.app M
  let eM : M.X ⟶ ((induction p).obj M).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app M).hom
  let eX : X.X ⟶ ((induction p).obj X).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction p).unit.app X).hom
  let fM : ((induction p).obj M).X ⟶ ((induction q).obj ((induction p).obj M)).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction q).unit.app ((induction p).obj M)).hom
  let fX : ((induction p).obj X).X ⟶ ((induction q).obj ((induction p).obj X)).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction q).unit.app ((induction p).obj X)).hom
  let fY : U ⊗ ((induction p).obj M).X ⟶
      ((induction q).obj ((Mod.AmbientTensor.functor B U).obj ((induction p).obj M))).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction q).unit.app
      ((Mod.AmbientTensor.functor B U).obj ((induction p).obj M))).hom
  let eC : M.X ⟶ ((induction (p ≫ q)).obj M).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction (p ≫ q)).unit.app M).hom
  let eCX : X.X ⟶ ((induction (p ≫ q)).obj X).X :=
    ((CategoryTheory.Mod.ExtensionOfScalars.adjunction (p ≫ q)).unit.app X).hom
  have hn : fX ≫ ((induction q).map a).hom = a.hom ≫ fY :=
    (congrArg Mod.Hom.hom ((CategoryTheory.Mod.ExtensionOfScalars.adjunction q).unit.naturality a)).symm
  have hM : eM ≫ fM ≫ ((inductionCompIso p q).hom.app M).hom = eC := by
    dsimp only [eM, fM, eC]
    rw [unit_hom, unit_hom, unit_hom]
    exact inductionCompIso_generator p q M
  have hX : eX ≫ fX ≫ ((inductionCompIso p q).hom.app X).hom = eCX := by
    dsimp only [eX, fX, eCX]
    rw [unit_hom, unit_hom, unit_hom]
    exact inductionCompIso_generator p q X
  have hp : eX ≫ a.hom = U ◁ eM := inductionTensorIso_unit_hom p U M
  have hq : fY ≫ ((inductionTensorIso q U).hom.app ((induction p).obj M)).hom = U ◁ fM :=
    inductionTensorIso_unit_hom q U ((induction p).obj M)
  apply induction_composite_hom_ext p q
  simp only [Mod.comp_hom']
  change eX ≫ fX ≫ (((induction q).map a).hom ≫
      ((inductionTensorIso q U).hom.app ((induction p).obj M)).hom ≫
        ((Mod.AmbientTensor.functor D U).map ((inductionCompIso p q).hom.app M)).hom) =
    eX ≫ fX ≫ (((inductionCompIso p q).hom.app X).hom ≫
      ((inductionTensorIso (p ≫ q) U).hom.app M).hom)
  calc
    eX ≫ fX ≫ (((induction q).map a).hom ≫
        ((inductionTensorIso q U).hom.app ((induction p).obj M)).hom ≫
          ((Mod.AmbientTensor.functor D U).map ((inductionCompIso p q).hom.app M)).hom) =
      (eX ≫ a.hom) ≫
        (fY ≫ ((inductionTensorIso q U).hom.app ((induction p).obj M)).hom) ≫
          ((Mod.AmbientTensor.functor D U).map ((inductionCompIso p q).hom.app M)).hom := by
        rw [← Category.assoc fX, hn]
        simp only [Category.assoc]
    _ = (U ◁ eM) ≫ (U ◁ fM) ≫ (U ◁ ((inductionCompIso p q).hom.app M).hom) := by
      rw [hp, hq, Mod.AmbientTensor.functor_map_hom]
    _ = U ◁ (eM ≫ fM ≫ ((inductionCompIso p q).hom.app M).hom) := by
      rw [whiskerLeft_comp, whiskerLeft_comp]
    _ = U ◁ eC := congrArg (fun f => U ◁ f) hM
    _ = eCX ≫ ((inductionTensorIso (p ≫ q) U).hom.app M).hom :=
      (inductionTensorIso_unit_hom (p ≫ q) U M).symm
    _ = eX ≫ fX ≫ (((inductionCompIso p q).hom.app X).hom ≫
        ((inductionTensorIso (p ≫ q) U).hom.app M).hom) := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ ((inductionTensorIso (p ≫ q) U).hom.app M).hom) hX.symm

end Composition

end CategoryTheory.HomogeneousLocalization.ScalarActionTransport
