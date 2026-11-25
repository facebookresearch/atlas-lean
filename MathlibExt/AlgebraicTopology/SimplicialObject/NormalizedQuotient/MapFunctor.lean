/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedQuotient

/-!
# Additive functors and the actual normalization quotient

The native alternating-complex comparison and the original Dold–Kan
projector formulas earn the quotient comparison. Preservation is local
to the split projector; the functor need not preserve arbitrary kernels,
cokernels, or homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits Opposite Functor
open scoped Simplicial

namespace AlgebraicTopology.NormalizedQuotient

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]

section Projector

variable [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]

/-- The native ambient comparison commutes with the original degenerate projector. -/
@[reassoc]
theorem map_QInfty (X : SimplicialObject C) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (DoldKan.QInfty (X := X)) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom =
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        DoldKan.QInfty (X := ((SimplicialObject.whiskering C D).obj F).obj X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change F.map ((DoldKan.QInfty (X := X)).f n) ≫ 𝟙 _ =
    𝟙 _ ≫ (DoldKan.QInfty
      (X := ((SimplicialObject.whiskering C D).obj F).obj X)).f n
  rw [Category.comp_id, Category.id_comp, DoldKan.QInfty_f, DoldKan.QInfty_f]
  exact DoldKan.map_Q F X n n

/-- The same native ambient comparison retains the original normalized projector. -/
@[reassoc]
theorem map_PInfty (X : SimplicialObject C) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (DoldKan.PInfty (X := X)) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom =
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        DoldKan.PInfty (X := ((SimplicialObject.whiskering C D).obj F).obj X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change F.map ((DoldKan.PInfty (X := X)).f n) ≫ 𝟙 _ =
    𝟙 _ ≫ (DoldKan.PInfty
      (X := ((SimplicialObject.whiskering C D).obj F).obj X)).f n
  rw [Category.comp_id, Category.id_comp]
  exact (DoldKan.map_PInfty_f F X n).symm

end Projector

section Normalization

variable [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]

local notation "Fh" => F.mapHomologicalComplex (ComplexShape.down ℕ)
local notation "Fs" => CategoryTheory.Functor.obj (SimplicialObject.whiskering C D) F

/-- The actual normalization quotient commutes with every additive functor. -/
def objCompMapIso (X : SimplicialObject C) :
    (Fh).obj (obj X) ≅ obj ((Fs).obj X) := by
  letI : PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0) Fh :=
    preservesCokernel_Q X Fh
  let a := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X
  exact PreservesCokernel.iso Fh (DoldKan.QInfty (X := X)) ≪≫
    cokernel.mapIso ((Fh).map (DoldKan.QInfty (X := X)))
      (DoldKan.QInfty (X := (Fs).obj X)) a a (map_QInfty F X)

/-- The comparison retains the actual quotient projection and native ambient map. -/
@[reassoc]
theorem projection_objCompMapIso_hom (X : SimplicialObject C) :
    (Fh).map (projection X) ≫ (objCompMapIso F X).hom =
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        projection ((Fs).obj X) := by
  letI : PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0) Fh :=
    preservesCokernel_Q X Fh
  let a := (alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X
  change (Fh).map (cokernel.π (DoldKan.QInfty (X := X))) ≫
      ((PreservesCokernel.iso Fh (DoldKan.QInfty (X := X))).hom ≫
        cokernel.map ((Fh).map (DoldKan.QInfty (X := X)))
          (DoldKan.QInfty (X := (Fs).obj X)) a.hom a.hom (map_QInfty F X)) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- Actual simplicial maps give naturality of the original quotient comparison. -/
@[reassoc]
theorem objCompMapIso_naturality {X Y : SimplicialObject C} (f : X ⟶ Y) :
    (Fh).map (map f) ≫ (objCompMapIso F Y).hom =
      (objCompMapIso F X).hom ≫ map ((Fs).map f) := by
  letI : PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0) Fh :=
    preservesCokernel_Q X Fh
  letI : Epi ((Fh).map (projection X)) :=
    Cofork.IsColimit.epi
      (isColimitOfHasCokernelOfPreservesColimit Fh (DoldKan.QInfty (X := X)))
  have ha : (Fh).map ((alternatingFaceMapComplex C).map f) ≫
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y).hom =
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
      (alternatingFaceMapComplex D).map ((Fs).map f) :=
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.naturality f
  apply (cancel_epi ((Fh).map (projection X))).1
  calc
    _ = ((Fh).map (projection X) ≫ (Fh).map (map f)) ≫
        (objCompMapIso F Y).hom := (Category.assoc _ _ _).symm
    _ = ((Fh).map ((alternatingFaceMapComplex C).map f) ≫
        (Fh).map (projection Y)) ≫ (objCompMapIso F Y).hom := by
      rw [← (Fh).map_comp, projection_map, (Fh).map_comp]
    _ = (Fh).map ((alternatingFaceMapComplex C).map f) ≫
        (((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y).hom ≫
          projection ((Fs).obj Y)) := by
      rw [Category.assoc, projection_objCompMapIso_hom]
    _ = (((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        (alternatingFaceMapComplex D).map ((Fs).map f)) ≫
          projection ((Fs).obj Y) := by rw [← Category.assoc, ha]
    _ = ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        (projection ((Fs).obj X) ≫ map ((Fs).map f)) := by
      rw [Category.assoc, ← projection_map]
    _ = ((Fh).map (projection X) ≫ (objCompMapIso F X).hom) ≫
        map ((Fs).map f) := by rw [← Category.assoc, projection_objCompMapIso_hom]
    _ = _ := Category.assoc _ _ _

/-- The original quotient comparisons assemble into the actual functor isomorphism. -/
def functorCompMapIso :
    functor C ⋙ Fh ≅ Fs ⋙ functor D :=
  NatIso.ofComponents (fun X => objCompMapIso F X) (by
    intro X Y f
    exact objCompMapIso_naturality F f)

/-- The retained quotient–Moore comparisons give the native Moore functor comparison. -/
def mooreCompMapIso :
    normalizedMooreComplex C ⋙ Fh ≅ Fs ⋙ normalizedMooreComplex D :=
  isoWhiskerRight (mooreNatIso C).symm Fh ≪≫ functorCompMapIso F ≪≫
    isoWhiskerLeft Fs (mooreNatIso D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual Moore functor comparison retains the original Moore inclusion. -/
@[reassoc]
theorem mooreCompMapIso_hom_inclusion (X : SimplicialObject C) :
    ((mooreCompMapIso F).app X).hom ≫ inclusionOfMooreComplexMap ((Fs).obj X) =
      (Fh).map (inclusionOfMooreComplexMap X) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom := by
  simp only [mooreCompMapIso, NatIso.trans_app, Iso.trans_hom,
    Iso.app_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Category.assoc]
  change (Fh).map (mooreIso X).inv ≫ (objCompMapIso F X).hom ≫
      (mooreIso ((Fs).obj X)).hom ≫ inclusionOfMooreComplexMap ((Fs).obj X) = _
  rw [mooreIso_inv, (Fh).map_comp]
  simp only [Category.assoc]
  rw [projection_objCompMapIso_hom_assoc, projection_mooreIso_hom_assoc,
    DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
    ← map_PInfty F X]
  have hI : (Fh).map (inclusionOfMooreComplexMap X) ≫
      (Fh).map (DoldKan.PInfty (X := X)) =
    (Fh).map (inclusionOfMooreComplexMap X) := by
    rw [← (Fh).map_comp, DoldKan.inclusionOfMooreComplexMap_comp_PInfty]
  calc
    _ = ((Fh).map (inclusionOfMooreComplexMap X) ≫
        (Fh).map (DoldKan.PInfty (X := X))) ≫
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom :=
      (Category.assoc _ _ _).symm
    _ = _ := by simp only [hI, Iso.app_hom]

end Normalization

section AmbientFunctorNaturality

variable [Preadditive C] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The native ambient comparisons respect every actual functor transformation. -/
@[reassoc]
theorem ambientCompMapIso_naturality (α : F ⟶ G) (X : SimplicialObject C) :
    (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app
        ((alternatingFaceMapComplex C).obj X) ≫
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso G).app X).hom =
    ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
      (alternatingFaceMapComplex D).map (((SimplicialObject.whiskering C D).map α).app X) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change α.app (X.obj (op ⦋n⦌)) ≫ 𝟙 _ = 𝟙 _ ≫ α.app (X.obj (op ⦋n⦌))
  rw [Category.comp_id, Category.id_comp]

end AmbientFunctorNaturality

section FunctorNaturality

variable [Abelian C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- The actual quotient comparison is natural even for a noninvertible functor transformation. -/
@[reassoc]
theorem objCompMapIso_functor_naturality (α : F ⟶ G) (X : SimplicialObject C) :
    (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app (obj X) ≫
        (objCompMapIso G X).hom =
      (objCompMapIso F X).hom ≫ map (((SimplicialObject.whiskering C D).map α).app X) := by
  letI : PreservesColimit (parallelPair (DoldKan.QInfty (X := X)) 0)
      (F.mapHomologicalComplex (ComplexShape.down ℕ)) :=
    preservesCokernel_Q X (F.mapHomologicalComplex (ComplexShape.down ℕ))
  letI : Epi ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (projection X)) :=
    Cofork.IsColimit.epi (isColimitOfHasCokernelOfPreservesColimit
      (F.mapHomologicalComplex (ComplexShape.down ℕ)) (DoldKan.QInfty (X := X)))
  have hα : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (projection X) ≫
      (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app (obj X) =
    (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app
        ((alternatingFaceMapComplex C).obj X) ≫
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).map (projection X) :=
    NatTrans.mapHomologicalComplex_naturality α (projection X)
  apply (cancel_epi ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (projection X))).1
  calc
    _ = (_ ≫ (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app (obj X)) ≫
        (objCompMapIso G X).hom := (Category.assoc _ _ _).symm
    _ = ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app
          ((alternatingFaceMapComplex C).obj X) ≫
        (G.mapHomologicalComplex (ComplexShape.down ℕ)).map (projection X)) ≫
          (objCompMapIso G X).hom := by rw [hα]
    _ = (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app
        ((alternatingFaceMapComplex C).obj X) ≫
        (((alternatingFaceMapComplexCompMapHomologicalComplexIso G).app X).hom ≫
          projection (((SimplicialObject.whiskering C D).obj G).obj X)) := by
      rw [Category.assoc, projection_objCompMapIso_hom]
    _ = (((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        (alternatingFaceMapComplex D).map
          (((SimplicialObject.whiskering C D).map α).app X)) ≫
        projection (((SimplicialObject.whiskering C D).obj G).obj X) := by
      rw [← Category.assoc, ambientCompMapIso_naturality]
    _ = ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X).hom ≫
        (projection (((SimplicialObject.whiskering C D).obj F).obj X) ≫
          map (((SimplicialObject.whiskering C D).map α).app X)) := by
      rw [Category.assoc, ← projection_map]
    _ = ((_ ≫ (objCompMapIso F X).hom) ≫
        map (((SimplicialObject.whiskering C D).map α).app X)) := by
      rw [← Category.assoc, projection_objCompMapIso_hom]
    _ = _ := Category.assoc _ _ _

/-- The comparison square is an equality of actual natural transformations. -/
@[reassoc]
theorem functorCompMapIso_naturality (α : F ⟶ G) :
    whiskerLeft (functor C) (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)) ≫
        (functorCompMapIso G).hom =
      (functorCompMapIso F).hom ≫
        whiskerRight ((SimplicialObject.whiskering C D).map α) (functor D) := by
  apply NatTrans.ext
  funext X
  exact objCompMapIso_functor_naturality α X

end FunctorNaturality

end AlgebraicTopology.NormalizedQuotient
