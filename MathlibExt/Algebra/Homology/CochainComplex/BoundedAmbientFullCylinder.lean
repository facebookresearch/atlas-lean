/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientWaldhausen
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedMappingCylinderCharts
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedMappingCylinderNormalization
public import MathlibExt.CategoryTheory.ExactCategory.Biproduct

/-!
# Full mapping cylinders in the bounded ambient Waldhausen model

Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Bounded integer cochains have degreewise admissible-mono cofibrations and
weak maps whose F-images are quasi-isomorphisms.

The signed cylinder I(f) has front i_f, back j_f and projection p_f with i_f≫p_f=f and
j_f≫p_f=id. Its joint boundaries and relative corners of arrow cofibrations are cofibrations,
and it preserves arrow cofibrations and weak maps. The projection's raw homotopy equivalence
becomes a quasi-isomorphism after F. Together with the selected zero-arrow normalization, these
maps give a full cylinder satisfying the Cylinder Axiom.

The source and ambient object and Hom universes uE,vE,uA,vA are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

private theorem admissible_biprod_map {X Y X' Y' : E} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : IsAdmissibleMono f) (hg : IsAdmissibleMono g) :
    IsAdmissibleMono (biprod.map f g) := by
  obtain ⟨P, p, w, hS⟩ := hf
  obtain ⟨Q, q, v, hT⟩ := hg
  exact isAdmissibleMono_f (isAdmissibleExact_biprod hS hT)

private theorem admissible_biprod_inr (X B : E) :
    IsAdmissibleMono (biprod.inr : B ⟶ X ⊞ B) := by
  let e := biprod.braiding' B X
  have hLeft : IsAdmissibleMono (biprod.inl : B ⟶ B ⊞ X) :=
    isAdmissibleMono_f (isAdmissibleExact_split B X)
  have hComp : IsAdmissibleMono ((biprod.inl : B ⟶ B ⊞ X) ≫ e.hom) :=
    admissibleMono_comp.comp_mem _ _ hLeft (IsAdmissibleMono.of_isIso e.hom)
  simpa only [e, biprod.braiding'_hom, biprod.inl_desc] using hComp

private theorem admissible_of_chart {X Y X' Y' : E} (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) (m : X' ⟶ Y') (h : eX.inv ≫ f ≫ eY.hom = m)
    (hm : IsAdmissibleMono m) : IsAdmissibleMono f := by
  have hf : f = eX.hom ≫ m ≫ eY.inv := by
    rw [← h]
    simp only [← Category.assoc, eX.hom_inv_id, Category.id_comp]
    rw [Category.assoc, eY.hom_inv_id, Category.comp_id]
  rw [hf]
  exact admissibleMono_comp.comp_mem _ _ (IsAdmissibleMono.of_isIso eX.hom)
    (admissibleMono_comp.comp_mem _ _ hm (IsAdmissibleMono.of_isIso eY.inv))

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.IsExact]

attribute [local instance] Waldhausen.waldhausenHasBinaryCoproducts

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. For every arrow f:X→Y, the joint boundary [i_f,j_f]:X⊔Y→I(f) is a
cofibration. -/
theorem ambientMappingCylinderBoundary_isCofibration (f : Arrow (Bounded E)) :
    letI := ambientWaldhausenCategory F
    IsCofibration (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
      (mappingCylinderFront E) (mappingCylinderBack E) f) := by
  let _ := ambientWaldhausenCategory F
  apply (ambient_isCofibration_iff F _).mpr
  intro j
  let eX := mappingCylinderStockBoundaryTermIso E f j
  let eY := mappingCylinderRawTermIso E f j
  let d := (Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) f).hom.f j
  have h : eX.inv ≫ d ≫ eY.hom = biprod.inr := by
    have hBoundary := mappingCylinderStockBoundary_term E f j
    change d ≫ eY.hom = eX.hom ≫ biprod.inr at hBoundary
    rw [hBoundary, eX.inv_hom_id_assoc]
  exact admissible_of_chart eX eY d biprod.inr h
    (admissible_biprod_inr _ _)

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. If both components of a commuting square α:f→g are cofibrations, then
I(α):I(f)→I(g) is a cofibration. -/
theorem ambientMappingCylinder_map_isCofibration {f g : Arrow (Bounded E)} (α : f ⟶ g) :
    letI := ambientWaldhausenCategory F
    Waldhausen.arrowCofibrations (Bounded E) α →
      IsCofibration ((mappingCylinderFunctor E).map α) := by
  let _ := ambientWaldhausenCategory F
  intro hα
  apply (ambient_isCofibration_iff F _).mpr
  have hLeft := (ambient_isCofibration_iff F α.left).mp hα.1
  have hRight := (ambient_isCofibration_iff F α.right).mp hα.2
  intro j
  have hEndpoint : IsAdmissibleMono ((biprod.map α.left.hom α.right.hom).f j) :=
    admissible_of_chart (HomologicalComplex.biprodXIso f.left.obj f.right.obj j)
      (HomologicalComplex.biprodXIso g.left.obj g.right.obj j)
      ((biprod.map α.left.hom α.right.hom).f j)
      (biprod.map (α.left.hom.f j) (α.right.hom.f j))
      (HomologicalComplex.biprodXIso_inv_map_hom α.left.hom α.right.hom j)
      (admissible_biprod_map _ _ (hLeft j) (hRight j))
  exact admissible_of_chart (mappingCylinderRawTermIso E f j)
    (mappingCylinderRawTermIso E g j) (((mappingCylinderFunctor E).map α).hom.f j)
    (biprod.map (α.left.hom.f (j + 1)) ((biprod.map α.left.hom α.right.hom).f j))
    (mappingCylinderRawTermIso_inv_map_hom E α j)
    (admissible_biprod_map _ _ (hLeft (j + 1)) hEndpoint)

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. Each projection p_f:I(f)→Y is weak, since its raw homotopy equivalence
remains a homotopy equivalence after F. -/
theorem ambientMappingCylinderProjection_isWeakEquivalence (f : Arrow (Bounded E)) :
    letI := ambientWaldhausenCategory F
    IsWeakEquivalence ((mappingCylinderProjection E).app f) := by
  let _ := ambientWaldhausenCategory F
  apply (ambient_isWeakEquivalence_iff F _).mpr
  have h := (F.mapHomotopyEquiv
    (HomologicalComplex.mappingCylinder.homotopyEquiv
      f.hom.hom mappingCylinderPredecessors)).quasiIso_inv
  exact h

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. If both components of α:f→g are weak, then I(α):I(f)→I(g) is weak by
projection naturality and two-of-three. -/
theorem ambientMappingCylinder_map_isWeakEquivalence {f g : Arrow (Bounded E)} (α : f ⟶ g) :
    letI := ambientWaldhausenCategory F
    Waldhausen.arrowWeakEquivalences (Bounded E) α →
      IsWeakEquivalence ((mappingCylinderFunctor E).map α) := by
  let _ := ambientWaldhausenCategory F
  intro hα
  apply (ambient_isWeakEquivalence_iff F _).mpr
  let pf := ((mappingCylinderProjection E).app f).hom
  let pg := ((mappingCylinderProjection E).app g).hom
  let m := ((mappingCylinderFunctor E).map α).hom
  let J := F.mapHomologicalComplex (.up ℤ)
  have hNat : m ≫ pg = pf ≫ α.right.hom :=
    congrArg (fun t : (mappingCylinderFunctor E).obj f ⟶ g.right => t.hom)
      ((mappingCylinderProjection E).naturality α)
  have hMapped : J.map m ≫ J.map pg = J.map pf ≫ J.map α.right.hom := by
    rw [← J.map_comp, hNat, J.map_comp]
  let _ : QuasiIso (J.map pf) := (ambient_isWeakEquivalence_iff F _).mp
    (ambientMappingCylinderProjection_isWeakEquivalence F f)
  let _ : QuasiIso (J.map pg) := (ambient_isWeakEquivalence_iff F _).mp
    (ambientMappingCylinderProjection_isWeakEquivalence F g)
  let _ : QuasiIso (J.map α.right.hom) := (ambient_isWeakEquivalence_iff F _).mp hα.2
  let _ : QuasiIso (J.map m ≫ J.map pg) := by rw [hMapped]; infer_instance
  exact _root_.quasiIso_of_comp_right (J.map m) (J.map pg)

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. For every arrow f:X→Y, the front i_f:X→I(f) is a cofibration. -/
theorem ambientMappingCylinderFront_isCofibration (f : Arrow (Bounded E)) :
    letI := ambientWaldhausenCategory F
    IsCofibration ((mappingCylinderFront E).app f) := by
  let _ := ambientWaldhausenCategory F
  let e := mappingCylinderStockCofanIso E f
  have hChosen : IsCofibration (mappingCylinderCoproductCofan E f).inl :=
    (Waldhausen.binaryCoproductColimitCocone_injections_isCofibration
      (Bounded E) f.left f.right).1
  have hInlEq : (coprod.inl : f.left ⟶ f.left ⨿ f.right) =
      (mappingCylinderCoproductCofan E f).inl ≫ e.inv := by
    rw [← mappingCylinderStockCofanIso_inl E f, Category.assoc,
      e.hom_inv_id, Category.comp_id]
  have hInl : IsCofibration (coprod.inl : f.left ⟶ f.left ⨿ f.right) := by
    rw [hInlEq]
    exact (WaldhausenCategoryWithoutGluing.cofibrations (C := Bounded E)).comp_mem _ _ hChosen
      ((WaldhausenCategoryWithoutGluing.cofibrations (C := Bounded E)).of_isIso e.inv)
  have hComp : IsCofibration ((coprod.inl : f.left ⟶ f.left ⨿ f.right) ≫
      Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
        (mappingCylinderFront E) (mappingCylinderBack E) f) :=
    (WaldhausenCategoryWithoutGluing.cofibrations (C := Bounded E)).comp_mem _ _ hInl
      (ambientMappingCylinderBoundary_isCofibration F f)
  simpa only [Waldhausen.cylinderBoundaryMap_inl] using hComp

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. For an arrow cofibration α:f→g, the map from the selected pushout
I(f)⊔_(X⊔Y)(X'⊔Y') to I(g) is a cofibration. -/
theorem ambientMappingCylinderCorner_isCofibration :
    letI := ambientWaldhausenCategory F
    ∀ {f g : Arrow (Bounded E)} (α : f ⟶ g),
      Waldhausen.arrowCofibrations (Bounded E) α →
      letI := Waldhausen.cylinderCorner_hasPushout (mappingCylinderFunctor E)
        (mappingCylinderFront E) (mappingCylinderBack E)
        (ambientMappingCylinderBoundary_isCofibration F) α
      IsCofibration (Waldhausen.cylinderCornerMap (mappingCylinderFunctor E)
        (mappingCylinderFront E) (mappingCylinderBack E)
        (ambientMappingCylinderBoundary_isCofibration F) α) := by
  let _ := ambientWaldhausenCategory F
  intro f g α hα
  let hBoundary := ambientMappingCylinderBoundary_isCofibration F
  let _ := Waldhausen.cylinderCorner_hasPushout (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) hBoundary α
  let bf := Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) f
  let bg := Waldhausen.cylinderBoundaryMap (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) g
  let u := coprod.map α.left α.right
  let d := Waldhausen.cylinderCornerMap (mappingCylinderFunctor E)
    (mappingCylinderFront E) (mappingCylinderBack E) hBoundary α
  have hP : IsPushout bf u (pushout.inl bf u) (pushout.inr bf u) :=
    IsPushout.of_hasPushout _ _
  have hOld : pushout.inl bf u ≫ d = (mappingCylinderFunctor E).map α :=
    Waldhausen.cylinderCornerMap_inl _ _ _ hBoundary α
  have hNew : pushout.inr bf u ≫ d = bg :=
    Waldhausen.cylinderCornerMap_inr _ _ _ hBoundary α
  have hLeft := (ambient_isCofibration_iff F α.left).mp hα.1
  apply (ambient_isCofibration_iff F _).mpr
  intro j
  have hTerm := admissiblePushout_term E
    ((ambient_isCofibration_iff F bf).mp (hBoundary f)) hP j
  have hOldTerm : (pushout.inl bf u).hom.f j ≫ d.hom.f j =
      ((mappingCylinderFunctor E).map α).hom.f j :=
    congrArg (fun t : (mappingCylinderFunctor E).obj f ⟶
      (mappingCylinderFunctor E).obj g => t.hom.f j) hOld
  have hNewTerm : (pushout.inr bf u).hom.f j ≫ d.hom.f j = bg.hom.f j :=
    congrArg (fun t : g.left ⨿ g.right ⟶ (mappingCylinderFunctor E).obj g => t.hom.f j) hNew
  have hChart := mappingCylinderCornerComponent_chart E α j (d.hom.f j)
    hTerm hOldTerm hNewTerm
  let hPush := mappingCylinderComponentPushout_chart E α j hTerm
  have hCorner : IsAdmissibleMono (IsPushout.biprodInrCorner hPush (α.left.hom.f (j + 1))) := by
    rw [IsPushout.biprodInrCorner_eq]
    exact admissibleMono_comp.comp_mem _ _
      (IsAdmissibleMono.of_isIso (IsPushout.biprodInrIso hPush).hom)
      (admissible_biprod_map _ _ (hLeft (j + 1))
        (IsAdmissibleMono.of_isIso (𝟙 _)))
  rw [hChart]
  exact admissibleMono_comp.comp_mem _ _ hCorner
    (IsAdmissibleMono.of_isIso (mappingCylinderRawTermIso E g j).inv)

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The natural cylinder maps give a mapping-cylinder core with i_f≫p_f=f
and j_f≫p_f=id_Y. -/
def ambientMappingCylinderCore :
    letI := ambientWaldhausenCategory F
    WaldhausenMappingCylinderCore (Bounded E) := by
  let _ := ambientWaldhausenCategory F
  exact
    { functor := mappingCylinderFunctor E
      front := mappingCylinderFront E
      back := mappingCylinderBack E
      projection := mappingCylinderProjection E
      front_projection := mappingCylinderFront_projection E
      back_projection := mappingCylinderBack_projection E
      front_cofibration := ambientMappingCylinderFront_isCofibration F }

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The cylinder preserves arrow cofibrations and weak maps, has
cofibration joint boundaries and relative corners for arrow cofibrations, and has its selected
zero-arrow normalization. These maps define a full cylinder. -/
def ambientFullCylinder :
    letI := ambientWaldhausenCategory F
    Waldhausen.FullCylinder (Bounded E) := by
  let _ := ambientWaldhausenCategory F
  exact
    { toWaldhausenMappingCylinderCore := ambientMappingCylinderCore F
      normalization := mappingCylinderNormalization E
      boundary_cofibration := ambientMappingCylinderBoundary_isCofibration F
      map_weakEquivalence := ambientMappingCylinder_map_isWeakEquivalence F
      map_cofibration := ambientMappingCylinder_map_isCofibration F
      corner_cofibration := ambientMappingCylinderCorner_isCofibration F }

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The full cylinder satisfies the Cylinder Axiom because all its
projections p_f are weak. -/
theorem ambientFullCylinder_satisfiesCylinderAxiom :
    letI := ambientWaldhausenCategory F
    (ambientFullCylinder F).SatisfiesCylinderAxiom := by
  let _ := ambientWaldhausenCategory F
  intro f
  exact ambientMappingCylinderProjection_isWeakEquivalence F f

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The full-cylinder functor is I:Arrow(Bounded(E))→Bounded(E). -/
theorem ambientFullCylinder_functor :
    letI := ambientWaldhausenCategory F
    (ambientFullCylinder F).functor = mappingCylinderFunctor E := rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The full-cylinder front is the natural transformation i:X→I(f) on arrow
sources. -/
theorem ambientFullCylinder_front :
    letI := ambientWaldhausenCategory F
    (ambientFullCylinder F).front = mappingCylinderFront E := rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The full-cylinder back is the natural transformation j:Y→I(f) on arrow
targets. -/
theorem ambientFullCylinder_back :
    letI := ambientWaldhausenCategory F
    (ambientFullCylinder F).back = mappingCylinderBack E := rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The full-cylinder projection is the natural transformation p:I(f)→Y. -/
theorem ambientFullCylinder_projection :
    letI := ambientWaldhausenCategory F
    (ambientFullCylinder F).projection = mappingCylinderProjection E := rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. The normalization on the selected zero arrow 0→Y is the natural
isomorphism I(0→Y)≅Y, with projection and back inclusion as its maps. -/
theorem ambientFullCylinder_normalization :
    letI := ambientWaldhausenCategory F
    (ambientFullCylinder F).normalization = mappingCylinderNormalization E := rfl

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. For every square α:f→g, the relative corner map restricts on the
old-cylinder pushout leg to I(α):I(f)→I(g). -/
theorem ambientFullCylinderCorner_inl {f g : Arrow (Bounded E)} (α : f ⟶ g) :
    letI := ambientWaldhausenCategory F
    let T := ambientFullCylinder F
    letI := Waldhausen.cylinderCorner_hasPushout T.functor T.front T.back
      T.boundary_cofibration α
    pushout.inl (Waldhausen.cylinderBoundaryMap T.functor T.front T.back f)
        (coprod.map α.left α.right) ≫
      Waldhausen.cylinderCornerMap T.functor T.front T.back T.boundary_cofibration α =
        T.functor.map α := by
  let _ := ambientWaldhausenCategory F
  exact Waldhausen.cylinderCornerMap_inl _ _ _ (ambientFullCylinder F).boundary_cofibration α

omit [F.IsExact] in
/-- Let E be an exact preadditive category with zero and binary biproducts, A abelian, and F:E→A
additive and exact. Give bounded E-cochains degreewise admissible-mono cofibrations and F-image
quasi-isomorphisms as weak maps. Write I for the signed bounded mapping cylinder, with front i,
back j and projection p. For every square α:f→g, the relative corner map restricts on the
new-boundary pushout leg to [i_g,j_g]:X'⊔Y'→I(g). -/
theorem ambientFullCylinderCorner_inr {f g : Arrow (Bounded E)} (α : f ⟶ g) :
    letI := ambientWaldhausenCategory F
    let T := ambientFullCylinder F
    letI := Waldhausen.cylinderCorner_hasPushout T.functor T.front T.back
      T.boundary_cofibration α
    pushout.inr (Waldhausen.cylinderBoundaryMap T.functor T.front T.back f)
        (coprod.map α.left α.right) ≫
      Waldhausen.cylinderCornerMap T.functor T.front T.back T.boundary_cofibration α =
        Waldhausen.cylinderBoundaryMap T.functor T.front T.back g := by
  let _ := ambientWaldhausenCategory F
  exact Waldhausen.cylinderCornerMap_inr _ _ _ (ambientFullCylinder F).boundary_cofibration α

end CochainComplex.Bounded

end
