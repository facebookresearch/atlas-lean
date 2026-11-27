/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedMappingCylinderBoundary
public import MathlibExt.Algebra.Homology.HomotopyCofiberMapCoordinates
public import MathlibExt.CategoryTheory.Limits.Shapes.BiprodPushoutCorner
public import MathlibExt.CategoryTheory.Waldhausen.FullCylinder

/-!
# Component and relative-corner charts for bounded mapping cylinders

Let `C` be preadditive with binary biproducts. For a bounded cochain arrow `f:K→L`, the
degree-`j` cylinder term is isomorphic to `K^{j+1} ⊞ (K ⊞ L)^j`. A commuting endpoint square
`(u,v):f→g` acts in these coordinates by `u^{j+1} ⊞ (u⊞v)^j`.

With a zero object and pointed cofibration/weak-equivalence data on bounded complexes with pushouts along cofibrations,
the
stock endpoint coproduct and the chosen zero-pushout coproduct compare canonically to the
endpoint biproduct. Under the component charts, the joint cylinder boundary is the second
biproduct injection and is degreewise split monic.

For a pushout of that boundary along an endpoint map, any corner map satisfying the two face
equations has the corresponding biproduct-corner formula. It is monic, or split monic, when
the shifted source component `u^{j+1}` has that property.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v uC vC

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] Waldhausen.waldhausenHasBinaryCoproducts

namespace CochainComplex.Bounded

variable (C : Type uC) [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

/-- For a preadditive category `C` with binary biproducts, `f:K→L` in `Bounded C`, and `j : ℤ`, the isomorphism
`mappingCylinderRawTermIso C f j` identifies the cylinder term with
`K.obj.X (j+1) ⊞ (K.obj ⊞ L.obj).X j`.
It is the cofiber term chart for the arrow `(1,−f.hom.hom)`. -/
def mappingCylinderRawTermIso (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ≅
      f.left.obj.X (j + 1) ⊞ (f.left.obj ⊞ f.right.obj).X j :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod
    (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j (j + 1) rfl

/-- For a preadditive category `C` with binary biproducts, a bounded cochain arrow `f:K→L`, and `j : ℤ`,
`mappingCylinderTermIso C f j = mappingCylinderRawTermIso C f j ≪≫ biprod.mapIso (Iso.refl _)
(HomologicalComplex.biprodXIso K.obj L.obj j)`.
Thus the refined chart has target `K^{j+1} ⊞ (K^j ⊞ L^j)`. -/
theorem mappingCylinderTermIso_eq (f : Arrow (Bounded C)) (j : ℤ) :
    mappingCylinderTermIso C f j = mappingCylinderRawTermIso C f j ≪≫
      biprod.mapIso (Iso.refl _) (HomologicalComplex.biprodXIso f.left.obj f.right.obj j) :=
  rfl

/-- For a preadditive category `C` with binary biproducts, a commuting square `a:f→g` of bounded cochain arrows, and `j
: ℤ`,
`(mappingCylinderRawTermIso C f j).inv ≫ ((mappingCylinderFunctor C).map a).hom.f j ≫ (mappingCylinderRawTermIso C g
j).hom = biprod.map (a.left.hom.f (j+1)) ((biprod.map a.left.hom a.right.hom).f j)`.
The shifted source and endpoint coordinates are mapped separately. -/
theorem mappingCylinderRawTermIso_inv_map_hom {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) :
    (mappingCylinderRawTermIso C f j).inv ≫
        ((mappingCylinderFunctor C).map a).hom.f j ≫
        (mappingCylinderRawTermIso C g j).hom =
      biprod.map (a.left.hom.f (j + 1)) ((biprod.map a.left.hom a.right.hom).f j) := by
  let b := HomologicalComplex.mappingCylinder.arrowMap f.hom.hom g.hom.hom
    ((ι C).mapArrow.map a)
  change (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j (j + 1) rfl).inv ≫
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
        mappingCylinderPredecessors b).f j ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (HomologicalComplex.mappingCylinder.arrow g.hom.hom) j (j + 1) rfl).hom =
      biprod.map (b.left.f (j + 1)) (b.right.f j)
  exact HomologicalComplex.homotopyCofiber.XIsoBiprod_inv_mapArrowHom_hom
    mappingCylinderPredecessors b (j + 1) j rfl

/-- For a preadditive category `C` with binary biproducts, a commuting square `a:f→g` of bounded cochain arrows, and `j
: ℤ`, the component chart satisfies
`((mappingCylinderFunctor C).map a).hom.f j ≫ (mappingCylinderRawTermIso C g j).hom = (mappingCylinderRawTermIso C f
j).hom ≫ biprod.map (a.left.hom.f (j+1)) ((biprod.map a.left.hom a.right.hom).f j)`. -/
theorem mappingCylinderRawTermIso_map_hom {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) :
    ((mappingCylinderFunctor C).map a).hom.f j ≫
        (mappingCylinderRawTermIso C g j).hom =
      (mappingCylinderRawTermIso C f j).hom ≫
        biprod.map (a.left.hom.f (j + 1)) ((biprod.map a.left.hom a.right.hom).f j) := by
  apply (cancel_epi (mappingCylinderRawTermIso C f j).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    mappingCylinderRawTermIso_inv_map_hom C a j

variable [HasZeroObject C] [WaldhausenCategoryWithoutGluing (Bounded C)]

/-- For a preadditive category `C` with a zero object and binary biproducts, and a fixed
cofibration/weak-equivalence structure on `Bounded C` and a bounded arrow `f:K→L`,
`mappingCylinderStockCoproductIso C f : K ⨿ L ≅ K ⊞ L` is the inverse of `biprod.isoCoprod K
L`. It identifies the stock binary coproduct with the selected bounded biproduct. -/
def mappingCylinderStockCoproductIso (f : Arrow (Bounded C)) :
    f.left ⨿ f.right ≅ f.left ⊞ f.right :=
  (biprod.isoCoprod f.left f.right).symm

/-- For a preadditive category `C` with a zero object and binary biproducts, and a fixed cofibration/weak-equivalence
structure on `Bounded C` and a bounded arrow `f:K→L`, there is a canonical isomorphism
`K ⨿ L ≅ (mappingCylinderCoproductCofan C f).pt`.
It compares the two colimiting binary cofans, carrying the stock coproduct injections to the chosen zero-pushout cofan
injections. -/
def mappingCylinderStockCofanIso (f : Arrow (Bounded C)) :
    f.left ⨿ f.right ≅ (mappingCylinderCoproductCofan C f).pt :=
  (coprodIsCoprod f.left f.right).coconePointUniqueUpToIso
    (Waldhausen.binaryCoproductColimitCocone (Bounded C) (pair f.left f.right)).isColimit

/-- For a preadditive category `C` with a zero object and binary biproducts, and a fixed cofibration/weak-equivalence
structure on `Bounded C` and a bounded arrow `f:K→L`,
`coprod.inl ≫ (mappingCylinderStockCofanIso C f).hom = (mappingCylinderCoproductCofan C f).inl`.
The canonical comparison of coproduct cofans preserves the left endpoint injection. -/
theorem mappingCylinderStockCofanIso_inl (f : Arrow (Bounded C)) :
    coprod.inl ≫ (mappingCylinderStockCofanIso C f).hom =
      (mappingCylinderCoproductCofan C f).inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod f.left f.right)
    (Waldhausen.binaryCoproductColimitCocone (Bounded C) (pair f.left f.right)).isColimit
    ⟨WalkingPair.left⟩

/-- For a preadditive category `C` with a zero object and binary biproducts, and a fixed cofibration/weak-equivalence
structure on `Bounded C` and a bounded arrow `f:K→L`,
`coprod.inr ≫ (mappingCylinderStockCofanIso C f).hom = (mappingCylinderCoproductCofan C f).inr`.
The canonical cofan comparison preserves the right endpoint injection. -/
theorem mappingCylinderStockCofanIso_inr (f : Arrow (Bounded C)) :
    coprod.inr ≫ (mappingCylinderStockCofanIso C f).hom =
      (mappingCylinderCoproductCofan C f).inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod f.left f.right)
    (Waldhausen.binaryCoproductColimitCocone (Bounded C) (pair f.left f.right)).isColimit
    ⟨WalkingPair.right⟩

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations and a bounded arrow `f:K→L`,
`(mappingCylinderStockCoproductIso C f).hom = (mappingCylinderStockCofanIso C f).hom ≫
(mappingCylinderCoproductBiproductIso C f).hom`.
The stock coproduct-to-biproduct map is the stock-to-chosen cofan comparison followed by the chosen cofan's biproduct
chart. -/
theorem mappingCylinderStockCoproductIso_hom (f : Arrow (Bounded C)) :
    (mappingCylinderStockCoproductIso C f).hom =
      (mappingCylinderStockCofanIso C f).hom ≫
        (mappingCylinderCoproductBiproductIso C f).hom := by
  apply coprod.hom_ext
  · change coprod.inl ≫ (biprod.isoCoprod f.left f.right).inv = _
    rw [biprod.isoCoprod_inv, coprod.inl_desc, ← Category.assoc,
      mappingCylinderStockCofanIso_inl, mappingCylinderCoproductBiproductIso_hom]
    exact (Waldhausen.binaryCoproductBiproductIso_inl_hom
      (Bounded C) f.left f.right).symm
  · change coprod.inr ≫ (biprod.isoCoprod f.left f.right).inv = _
    rw [biprod.isoCoprod_inv, coprod.inr_desc, ← Category.assoc,
      mappingCylinderStockCofanIso_inr, mappingCylinderCoproductBiproductIso_hom]
    exact (Waldhausen.binaryCoproductBiproductIso_inr_hom
      (Bounded C) f.left f.right).symm

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations and a bounded arrow `f:K→L`, the
joint map from the stock coproduct to the cylinder satisfies
`Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C) (mappingCylinderFront C) (mappingCylinderBack C) f =
(mappingCylinderStockCoproductIso C f).hom ≫ mappingCylinderBoundary C f`. -/
theorem mappingCylinderStockBoundary_eq (f : Arrow (Bounded C)) :
    Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f =
      (mappingCylinderStockCoproductIso C f).hom ≫ mappingCylinderBoundary C f := by
  apply coprod.hom_ext
  · change coprod.inl ≫ _ = coprod.inl ≫
      (biprod.isoCoprod f.left f.right).inv ≫ mappingCylinderBoundary C f
    rw [Waldhausen.cylinderBoundaryMap_inl, biprod.isoCoprod_inv,
      coprod.inl_desc_assoc, mappingCylinderBoundary_inl]
  · change coprod.inr ≫ _ = coprod.inr ≫
      (biprod.isoCoprod f.left f.right).inv ≫ mappingCylinderBoundary C f
    rw [Waldhausen.cylinderBoundaryMap_inr, biprod.isoCoprod_inv,
      coprod.inr_desc_assoc, mappingCylinderBoundary_inr]

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations and a bounded arrow `f:K→L`, the
stock joint cylinder boundary is
`(mappingCylinderStockCofanIso C f).hom ≫ mappingCylinderCoproductBoundary C f`.
The cofan comparison carries the stock endpoint coproduct to the chosen zero-pushout coproduct before applying its
boundary. -/
theorem mappingCylinderStockBoundary_cofan (f : Arrow (Bounded C)) :
    Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f =
      (mappingCylinderStockCofanIso C f).hom ≫ mappingCylinderCoproductBoundary C f := by
  rw [mappingCylinderStockBoundary_eq, mappingCylinderStockCoproductIso_hom]
  exact Category.assoc _ _ _

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations and a bounded arrow `f:K→L`,
there is an isomorphism
`(K ⨿ L : Bounded C).obj ≅ K.obj ⊞ L.obj`.
It applies the bounded inclusion to `mappingCylinderStockCoproductIso C f` and then composes with
`mappingCylinderBoundaryChart C f`. -/
def mappingCylinderStockBoundaryRawIso (f : Arrow (Bounded C)) :
    (f.left ⨿ f.right : Bounded C).obj ≅ f.left.obj ⊞ f.right.obj :=
  (ι C).mapIso (mappingCylinderStockCoproductIso C f) ≪≫ mappingCylinderBoundaryChart C f

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations and a bounded arrow `f:K→L`, put
`χ=(1,−f.hom.hom)`. The underlying map of the joint cylinder boundary equals
`(mappingCylinderStockBoundaryRawIso C f).hom ≫ HomologicalComplex.homotopyCofiber.inr χ`.
The stock endpoint coproduct is first identified with the endpoint cochain biproduct. -/
theorem mappingCylinderStockBoundary_hom (f : Arrow (Bounded C)) :
    (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom =
      (mappingCylinderStockBoundaryRawIso C f).hom ≫
        HomologicalComplex.homotopyCofiber.inr
          (HomologicalComplex.mappingCylinder.arrow f.hom.hom) := by
  rw [mappingCylinderStockBoundary_eq]
  change ((mappingCylinderStockCoproductIso C f).hom).hom ≫
    (mappingCylinderBoundary C f).hom = _
  rw [mappingCylinderBoundary_hom]
  exact (Category.assoc _ _ _).symm

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations, a bounded arrow `f:K→L`, and `j
: ℤ`,
`mappingCylinderStockBoundaryTermIso C f j : (K ⨿ L : Bounded C).obj.X j ≅ (K.obj ⊞ L.obj).X j`
is the degree-`j` component of `mappingCylinderStockBoundaryRawIso C f`. -/
def mappingCylinderStockBoundaryTermIso (f : Arrow (Bounded C)) (j : ℤ) :
    (f.left ⨿ f.right : Bounded C).obj.X j ≅ (f.left.obj ⊞ f.right.obj).X j :=
  HomologicalComplex.Hom.isoApp (mappingCylinderStockBoundaryRawIso C f) j

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations, a bounded arrow `f:K→L`, and `j
: ℤ`, the degree-`j` joint boundary followed by `mappingCylinderRawTermIso C f j` equals
`(mappingCylinderStockBoundaryTermIso C f j).hom ≫ biprod.inr`.
Its target is `K^{j+1} ⊞ (K ⊞ L)^j`, so the endpoint coordinate is included as the second summand. -/
theorem mappingCylinderStockBoundary_term (f : Arrow (Bounded C)) (j : ℤ) :
    (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j ≫
        (mappingCylinderRawTermIso C f j).hom =
      (mappingCylinderStockBoundaryTermIso C f j).hom ≫ biprod.inr := by
  have hj : (ComplexShape.up ℤ).Rel j (j + 1) := rfl
  rw [mappingCylinderStockBoundary_hom]
  change ((mappingCylinderStockBoundaryRawIso C f).hom.f j ≫
    HomologicalComplex.homotopyCofiber.inrX
      (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j) ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j (j + 1) hj).hom = _
  rw [Category.assoc, HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom]
  rfl

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations and a
bounded arrow `f:K→L`, the joint cylinder boundary from the stock coproduct is degreewise
split monic. The biproduct boundary's component retractions are transported through
`mappingCylinderStockCoproductIso C f`, preserving the endpoint map. -/
theorem mappingCylinderStockBoundary_degreewiseSplit (f : Arrow (Bounded C)) :
    degreewiseSplitMonomorphisms C
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f) := by
  intro j
  rw [mappingCylinderStockBoundary_eq]
  let e := HomologicalComplex.Hom.isoApp
    ((ι C).mapIso (mappingCylinderStockCoproductIso C f)) j
  change IsSplitMono (e.hom ≫ (mappingCylinderBoundary C f).hom.f j)
  let _ : IsSplitMono ((mappingCylinderBoundary C f).hom.f j) :=
    mappingCylinderBoundary_degreewiseSplit C f j
  infer_instance

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations, a commuting square `a:f→g` of
bounded arrows, and `j : ℤ`,
`(coprod.map a.left a.right).hom.f j ≫ (mappingCylinderStockBoundaryTermIso C g j).hom =
(mappingCylinderStockBoundaryTermIso C f j).hom ≫ (biprod.map a.left.hom a.right.hom).f j`.
The endpoint coproduct map agrees with the component biproduct map through the stock term charts. -/
theorem mappingCylinderStockCoproductMap_term {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) :
    (coprod.map a.left a.right).hom.f j ≫ (mappingCylinderStockBoundaryTermIso C g j).hom =
      (mappingCylinderStockBoundaryTermIso C f j).hom ≫
        (biprod.map a.left.hom a.right.hom).f j := by
  let bf := Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
    (mappingCylinderFront C) (mappingCylinderBack C) f
  let bg := Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
    (mappingCylinderFront C) (mappingCylinderBack C) g
  have hNat : bf.hom.f j ≫ ((mappingCylinderFunctor C).map a).hom.f j =
      (coprod.map a.left a.right).hom.f j ≫ bg.hom.f j :=
    congrArg (fun t : f.left ⨿ f.right ⟶ (mappingCylinderFunctor C).obj g => t.hom.f j)
      (Waldhausen.cylinderBoundaryMap_naturality (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) a)
  have hf : bf.hom.f j ≫ (mappingCylinderRawTermIso C f j).hom =
      (mappingCylinderStockBoundaryTermIso C f j).hom ≫ biprod.inr :=
    mappingCylinderStockBoundary_term C f j
  have hg : bg.hom.f j ≫ (mappingCylinderRawTermIso C g j).hom =
      (mappingCylinderStockBoundaryTermIso C g j).hom ≫ biprod.inr :=
    mappingCylinderStockBoundary_term C g j
  apply (cancel_mono (biprod.inr : (g.left.obj ⊞ g.right.obj).X j ⟶
    g.left.obj.X (j + 1) ⊞ (g.left.obj ⊞ g.right.obj).X j)).1
  calc
    _ = (coprod.map a.left a.right).hom.f j ≫
        ((mappingCylinderStockBoundaryTermIso C g j).hom ≫ biprod.inr) :=
      Category.assoc _ _ _
    _ = (coprod.map a.left a.right).hom.f j ≫
        (bg.hom.f j ≫ (mappingCylinderRawTermIso C g j).hom) :=
      congrArg (fun t => (coprod.map a.left a.right).hom.f j ≫ t) hg.symm
    _ = ((coprod.map a.left a.right).hom.f j ≫ bg.hom.f j) ≫
        (mappingCylinderRawTermIso C g j).hom := (Category.assoc _ _ _).symm
    _ = (bf.hom.f j ≫ ((mappingCylinderFunctor C).map a).hom.f j) ≫
        (mappingCylinderRawTermIso C g j).hom :=
      congrArg (fun t => t ≫ (mappingCylinderRawTermIso C g j).hom) hNat.symm
    _ = bf.hom.f j ≫ (((mappingCylinderFunctor C).map a).hom.f j ≫
        (mappingCylinderRawTermIso C g j).hom) := Category.assoc _ _ _
    _ = bf.hom.f j ≫ ((mappingCylinderRawTermIso C f j).hom ≫
        biprod.map (a.left.hom.f (j + 1)) ((biprod.map a.left.hom a.right.hom).f j)) :=
      congrArg (fun t => bf.hom.f j ≫ t) (mappingCylinderRawTermIso_map_hom C a j)
    _ = (bf.hom.f j ≫ (mappingCylinderRawTermIso C f j).hom) ≫
        biprod.map (a.left.hom.f (j + 1)) ((biprod.map a.left.hom a.right.hom).f j) :=
      (Category.assoc _ _ _).symm
    _ = ((mappingCylinderStockBoundaryTermIso C f j).hom ≫ biprod.inr) ≫
        biprod.map (a.left.hom.f (j + 1)) ((biprod.map a.left.hom a.right.hom).f j) :=
      congrArg (fun t => t ≫
        biprod.map (a.left.hom.f (j + 1)) ((biprod.map a.left.hom a.right.hom).f j)) hf
    _ = (mappingCylinderStockBoundaryTermIso C f j).hom ≫
        ((biprod.map a.left.hom a.right.hom).f j ≫ biprod.inr) := by
      rw [Category.assoc, biprod.inr_map]
    _ = _ := (Category.assoc _ _ _).symm

private theorem mappingCylinderComponentPushout {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew) :
    IsPushout (biprod.inr : (f.left.obj ⊞ f.right.obj).X j ⟶
      f.left.obj.X (j + 1) ⊞ (f.left.obj ⊞ f.right.obj).X j)
      ((biprod.map a.left.hom a.right.hom).f j)
      ((mappingCylinderRawTermIso C f j).inv ≫ inOld)
      ((mappingCylinderStockBoundaryTermIso C g j).inv ≫ inNew) := by
  apply hP.of_iso (mappingCylinderStockBoundaryTermIso C f j)
    (mappingCylinderRawTermIso C f j) (mappingCylinderStockBoundaryTermIso C g j) (Iso.refl P)
  · exact mappingCylinderStockBoundary_term C f j
  · exact mappingCylinderStockCoproductMap_term C a j
  · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem mappingCylinderCornerComponent_eq {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (d : P ⟶ ((mappingCylinderFunctor C).obj g).obj.X j)
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew)
    (hOld : inOld ≫ d = ((mappingCylinderFunctor C).map a).hom.f j)
    (hNew : inNew ≫ d =
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) g).hom.f j) :
    d = IsPushout.biprodInrCorner (mappingCylinderComponentPushout C a j hP)
        (a.left.hom.f (j + 1)) ≫ (mappingCylinderRawTermIso C g j).inv := by
  let h := mappingCylinderComponentPushout C a j hP
  let k := IsPushout.biprodInrCorner h (a.left.hom.f (j + 1))
  have hd : d ≫ (mappingCylinderRawTermIso C g j).hom = k := by
    apply h.hom_ext
    · calc
        _ = (mappingCylinderRawTermIso C f j).inv ≫
            (inOld ≫ d) ≫ (mappingCylinderRawTermIso C g j).hom := by
          simp only [Category.assoc]
        _ = (mappingCylinderRawTermIso C f j).inv ≫
            ((mappingCylinderFunctor C).map a).hom.f j ≫
            (mappingCylinderRawTermIso C g j).hom := by rw [hOld]
        _ = biprod.map (a.left.hom.f (j + 1))
            ((biprod.map a.left.hom a.right.hom).f j) :=
          mappingCylinderRawTermIso_inv_map_hom C a j
        _ = _ := (IsPushout.inOld_biprodInrCorner h (a.left.hom.f (j + 1))).symm
    · calc
        _ = (mappingCylinderStockBoundaryTermIso C g j).inv ≫
            (inNew ≫ d) ≫ (mappingCylinderRawTermIso C g j).hom := by
          simp only [Category.assoc]
        _ = (mappingCylinderStockBoundaryTermIso C g j).inv ≫
            (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
              (mappingCylinderFront C) (mappingCylinderBack C) g).hom.f j ≫
            (mappingCylinderRawTermIso C g j).hom := by rw [hNew]
        _ = (mappingCylinderStockBoundaryTermIso C g j).inv ≫
            ((mappingCylinderStockBoundaryTermIso C g j).hom ≫ biprod.inr) := by
          rw [mappingCylinderStockBoundary_term]
        _ = biprod.inr := Iso.inv_hom_id_assoc _ _
        _ = _ := (IsPushout.inNew_biprodInrCorner h (a.left.hom.f (j + 1))).symm
  calc
    d = (d ≫ (mappingCylinderRawTermIso C g j).hom) ≫
        (mappingCylinderRawTermIso C g j).inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = k ≫ (mappingCylinderRawTermIso C g j).inv :=
      congrArg (fun t => t ≫ (mappingCylinderRawTermIso C g j).inv) hd

private theorem mono_mappingCylinderCornerComponent {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (d : P ⟶ ((mappingCylinderFunctor C).obj g).obj.X j)
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew)
    (hOld : inOld ≫ d = ((mappingCylinderFunctor C).map a).hom.f j)
    (hNew : inNew ≫ d =
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) g).hom.f j)
    [Mono (a.left.hom.f (j + 1))] : Mono d := by
  rw [mappingCylinderCornerComponent_eq C a j d hP hOld hNew]
  let h := mappingCylinderComponentPushout C a j hP
  let _ : Mono (IsPushout.biprodInrCorner h (a.left.hom.f (j + 1))) :=
    IsPushout.mono_biprodInrCorner h (a.left.hom.f (j + 1))
  infer_instance

private theorem isSplitMono_mappingCylinderCornerComponent
    {f g : Arrow (Bounded C)} (a : f ⟶ g) (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (d : P ⟶ ((mappingCylinderFunctor C).obj g).obj.X j)
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew)
    (hOld : inOld ≫ d = ((mappingCylinderFunctor C).map a).hom.f j)
    (hNew : inNew ≫ d =
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) g).hom.f j)
    [IsSplitMono (a.left.hom.f (j + 1))] : IsSplitMono d := by
  rw [mappingCylinderCornerComponent_eq C a j d hP hOld hNew]
  let h := mappingCylinderComponentPushout C a j hP
  let _ : IsSplitMono (IsPushout.biprodInrCorner h (a.left.hom.f (j + 1))) :=
    IsPushout.isSplitMono_biprodInrCorner h (a.left.hom.f (j + 1))
  infer_instance


/-- Let `C` be preadditive with a zero object and binary biproducts, and fix pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations. Let
`a:f→g` be a commuting square of bounded cochain arrows and `j : ℤ`. Let `P` be the pushout of
the degree-`j` joint boundary `β_f` and the degree-`j` stock endpoint map `σ_a`, with legs
`inOld:Cyl(f)^j→P` and `inNew:(g.left⨿g.right)^j→P`. Suppose `d:P→Cyl(g)^j` satisfies `inOld ≫
d=Cyl(a)^j` and `inNew ≫ d=β_g`. If `a.left.hom.f (j+1)` is monic, then `d` is monic. The
hypothesis concerns the shifted source component in degree `j+1`; the pushout and both
corner-face equations determine the cylinder corner. -/
theorem mappingCylinderCornerComponent_mono {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (d : P ⟶ ((mappingCylinderFunctor C).obj g).obj.X j)
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew)
    (hOld : inOld ≫ d = ((mappingCylinderFunctor C).map a).hom.f j)
    (hNew : inNew ≫ d =
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) g).hom.f j)
    [Mono (a.left.hom.f (j + 1))] : Mono d :=
  mono_mappingCylinderCornerComponent C a j d hP hOld hNew

/-- Let `C` be preadditive with a zero object and binary biproducts, and fix pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations. Let
`a:f→g` be a commuting square of bounded cochain arrows and `j : ℤ`. Let `P` be the pushout of
the degree-`j` joint boundary `β_f` and the degree-`j` stock endpoint map `σ_a`, with legs
`inOld:Cyl(f)^j→P` and `inNew:(g.left⨿g.right)^j→P`. Suppose `d:P→Cyl(g)^j` satisfies `inOld ≫
d=Cyl(a)^j` and `inNew ≫ d=β_g`. If `a.left.hom.f (j+1)` is split monic, then `d` is split
monic. This transports the shifted source splitting through the component pushout chart. -/
theorem mappingCylinderCornerComponent_splitMono
    {f g : Arrow (Bounded C)} (a : f ⟶ g) (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (d : P ⟶ ((mappingCylinderFunctor C).obj g).obj.X j)
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew)
    (hOld : inOld ≫ d = ((mappingCylinderFunctor C).map a).hom.f j)
    (hNew : inNew ≫ d =
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) g).hom.f j)
    [IsSplitMono (a.left.hom.f (j + 1))] : IsSplitMono d :=
  isSplitMono_mappingCylinderCornerComponent C a j d hP hOld hNew

end CochainComplex.Bounded

end

public section
noncomputable section
universe uAmbient vAmbient

open CategoryTheory CategoryTheory.Limits
attribute [local instance] Waldhausen.waldhausenHasBinaryCoproducts

namespace CochainComplex.Bounded

variable (C : Type uAmbient) [Category.{vAmbient} C] [Preadditive C] [HasBinaryBiproducts C]
  [HasZeroObject C] [WaldhausenCategoryWithoutGluing (Bounded C)]

/-- For a preadditive category `C` with a zero object and binary biproducts, with fixed pointed
cofibration/weak-equivalence data on `Bounded C` admitting pushouts along cofibrations, let
`a:f→g` be a commuting square and let `P` be a degree-`j` pushout of the joint boundary of `f`
and the stock endpoint map, with legs `inOld` and `inNew`. Put `γ_f=mappingCylinderRawTermIso
C f j` and `δ_g=mappingCylinderStockBoundaryTermIso C g j`. Then the square with source
`(f.left.obj⊞f.right.obj).X j`, maps `biprod.inr` and `(biprod.map a.left.hom a.right.hom).f
j`, and legs `γ_f.inv ≫ inOld` and `δ_g.inv ≫ inNew` is a pushout in `C`. -/
theorem mappingCylinderComponentPushout_chart {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew) :
    IsPushout (biprod.inr : (f.left.obj ⊞ f.right.obj).X j ⟶
      f.left.obj.X (j + 1) ⊞ (f.left.obj ⊞ f.right.obj).X j)
      ((biprod.map a.left.hom a.right.hom).f j)
      ((mappingCylinderRawTermIso C f j).inv ≫ inOld)
      ((mappingCylinderStockBoundaryTermIso C g j).inv ≫ inNew) :=
  mappingCylinderComponentPushout C a j hP

/-- Let `C` be preadditive with a zero object and binary biproducts, and fix pointed cofibration/weak-equivalence data
on `Bounded C` admitting pushouts along cofibrations. Let `a:f→g` be a commuting square of bounded cochain arrows and `j
: ℤ`. Let `P` be the pushout of the degree-`j` joint boundary `β_f` and the degree-`j` stock endpoint map `σ_a`, with
legs `inOld:Cyl(f)^j→P` and `inNew:(g.left⨿g.right)^j→P`. Suppose `d:P→Cyl(g)^j` satisfies `inOld ≫ d=Cyl(a)^j` and
`inNew ≫ d=β_g`. The corner has the formula
`d = IsPushout.biprodInrCorner (mappingCylinderComponentPushout_chart C a j hP) (a.left.hom.f (j+1)) ≫
(mappingCylinderRawTermIso C g j).inv`.
The biproduct-corner map uses the shifted source component and the identity on the new endpoint coordinate, then returns
through the target cylinder chart. -/
theorem mappingCylinderCornerComponent_chart {f g : Arrow (Bounded C)} (a : f ⟶ g)
    (j : ℤ) {P : C}
    {inOld : ((mappingCylinderFunctor C).obj f).obj.X j ⟶ P}
    {inNew : (g.left ⨿ g.right : Bounded C).obj.X j ⟶ P}
    (d : P ⟶ ((mappingCylinderFunctor C).obj g).obj.X j)
    (hP : IsPushout
      ((Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) f).hom.f j)
      ((coprod.map a.left a.right).hom.f j) inOld inNew)
    (hOld : inOld ≫ d = ((mappingCylinderFunctor C).map a).hom.f j)
    (hNew : inNew ≫ d =
      (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor C)
        (mappingCylinderFront C) (mappingCylinderBack C) g).hom.f j) :
    d = IsPushout.biprodInrCorner (mappingCylinderComponentPushout_chart C a j hP)
        (a.left.hom.f (j + 1)) ≫ (mappingCylinderRawTermIso C g j).inv :=
  mappingCylinderCornerComponent_eq C a j d hP hOld hNew

end CochainComplex.Bounded

end
