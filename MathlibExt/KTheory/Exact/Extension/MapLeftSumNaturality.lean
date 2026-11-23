/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.MapLeftSumRow
public import MathlibExt.CategoryTheory.Preadditive.MapBiprodNaturality

/-!
# Actual naturality of the original left-sum comparison on quotient-diagram classes

The inverse biproduct square controls the reverse kernel coordinate.
The forward square controls the middle coordinate. Existing complete
object/morphism views retain all endpoint presentations, and the actual
middle-quotient relation gives the full extension morphism equality.
No action square, localized map or equivalence outcome is a premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

variable (F : C ⥤ D) [F.Additive] [F.IsExact]

omit [HasZeroObject D] [ExactCategory D] in
private theorem binaryMapHEq
    {A B A' B' X Y X' Y' : D}
    (hA : A = A') (hB : B = B') (hX : X = X') (hY : Y = Y')
    {f : A ⟶ X} {f' : A' ⟶ X'} {g : B ⟶ Y} {g' : B' ⟶ Y'}
    (hf : HEq f f') (hg : HEq g g') : HEq (biprod.map f g) (biprod.map f' g') := by
  cases hA
  cases hB
  cases hX
  cases hY
  cases hf
  cases hg
  exact HEq.rfl

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  [F.Additive] [F.IsExact] in
private theorem coreObjectView (T : Core C) : (F.core.obj T).of = F.obj T.of := rfl

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  [F.Additive] [F.IsExact] in
private theorem coreMapHomView {T U : Core C} (a : T ⟶ U) :
    HEq (F.core.map a).iso.hom (F.map a.iso.hom) := heq_of_eq rfl

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  [F.Additive] [F.IsExact] in
private theorem coreMapInvView {T U : Core C} (a : T ⟶ U) :
    HEq (F.core.map a).iso.inv (F.map a.iso.inv) := heq_of_eq rfl

private theorem originalLeftSumMapMk {T U : Core C} (a : T ⟶ U)
    {E E' : ExtensionCategory C} (d : ExtensionDiagram E E') :
    ExtensionCategory.leftSumMap a (ExtensionCategory.mkHom d) =
      ExtensionCategory.mkHom (ExtensionDiagram.leftSum a d) := rfl

private theorem leftSumMappedCompositeRel {T U : Core C} (a : T ⟶ U)
    {E E' : ExtensionCategory C} (d : ExtensionDiagram E E') :
    let ds := ExtensionDiagram.map F (ExtensionDiagram.leftSum a d)
    let dt := ExtensionDiagram.leftSum (F.core.map a) (ExtensionDiagram.map F d)
    let cp := ExtensionCategory.mapLeftSumDiagram F T E
    let cq := ExtensionCategory.mapLeftSumDiagram F U E'
    ExtensionDiagram.Rel (ExtensionDiagram.ofNormalization (ds.normalize ≫ cq.normalize))
      (ExtensionDiagram.ofNormalization (cp.normalize ≫ dt.normalize)) := by
  let ds := ExtensionDiagram.map F (ExtensionDiagram.leftSum a d)
  let dt := ExtensionDiagram.leftSum (F.core.map a) (ExtensionDiagram.map F d)
  let cp := ExtensionCategory.mapLeftSumDiagram F T E
  let cq := ExtensionCategory.mapLeftSumDiagram F U E'
  let p := ExtensionCategory.mapLeftSum_object_views F T E
  let q := ExtensionCategory.mapLeftSum_object_views F U E'
  let cd := ExtensionDiagram.map_characteristic F d
  let cs := ExtensionDiagram.map_characteristic F (ExtensionDiagram.leftSum a d)
  let pc := ExtensionCategory.mapLeftSumDiagram_components F T E
  let qc := ExtensionCategory.mapLeftSumDiagram_components F U E'
  have hSA : HEq ds.alpha (F.map (biprod.map a.iso.inv d.alpha)) :=
    cs.1.trans (heq_of_eq (congrArg F.map (ExtensionDiagram.leftSum_alpha a d)))
  have hSB : HEq ds.beta (F.map (biprod.map a.iso.hom d.beta)) :=
    cs.2.1.trans (heq_of_eq (congrArg F.map (ExtensionDiagram.leftSum_beta a d)))
  have hTA : HEq dt.alpha (biprod.map (F.map a.iso.inv) (F.map d.alpha)) :=
    (heq_of_eq (ExtensionDiagram.leftSum_alpha (F.core.map a)
      (ExtensionDiagram.map F d))).trans
        (binaryMapHEq (coreObjectView F U)
          (ExtensionCategory.mapObject_components F E').1 (coreObjectView F T)
          (ExtensionCategory.mapObject_components F E).1 (coreMapInvView F a) cd.1)
  have hTB : HEq dt.beta (biprod.map (F.map a.iso.hom) (F.map d.beta)) :=
    (heq_of_eq (ExtensionDiagram.leftSum_beta (F.core.map a)
      (ExtensionDiagram.map F d))).trans
        (binaryMapHEq (coreObjectView F T)
          (ExtensionCategory.mapObject_components F E).2.1 (coreObjectView F U)
          (ExtensionCategory.mapObject_components F E').2.1 (coreMapHomView F a) cd.2.1)
  have hAlphaLeft : HEq (cq.alpha ≫ ds.alpha)
      ((F.mapBiprod U.of E'.row.X₁).inv ≫ F.map (biprod.map a.iso.inv d.alpha)) :=
    heq_comp q.2.2.2.1 q.1 p.1 qc.1 hSA
  have hAlphaRight : HEq (dt.alpha ≫ cp.alpha)
      (biprod.map (F.map a.iso.inv) (F.map d.alpha) ≫ (F.mapBiprod T.of E.row.X₁).inv) :=
    heq_comp q.2.2.2.1 p.2.2.2.1 p.1 hTA pc.1
  have hAlpha : cq.alpha ≫ ds.alpha = dt.alpha ≫ cp.alpha :=
    eq_of_heq (hAlphaLeft.trans
      ((heq_of_eq (Functor.mapBiprod_additive_inv_naturality F a.iso.inv d.alpha).symm).trans
        hAlphaRight.symm))
  have hBetaLeft : HEq (ds.beta ≫ cq.beta)
      (F.map (biprod.map a.iso.hom d.beta) ≫ (F.mapBiprod U.of E'.row.X₂).hom) :=
    heq_comp p.2.1 q.2.1 q.2.2.2.2.1 hSB qc.2.1
  have hBetaRight : HEq (cp.beta ≫ dt.beta)
      ((F.mapBiprod T.of E.row.X₂).hom ≫ biprod.map (F.map a.iso.hom) (F.map d.beta)) :=
    heq_comp p.2.1 p.2.2.2.2.1 q.2.2.2.2.1 pc.2.1 hTB
  have hBeta : ds.beta ≫ cq.beta = cp.beta ≫ dt.beta :=
    eq_of_heq (hBetaLeft.trans
      ((heq_of_eq (Functor.mapBiprod_additive_naturality F a.iso.hom d.beta).symm).trans
        hBetaRight.symm))
  apply ExtensionDiagram.rel_of_components_eq
  · exact (ExtensionDiagram.ofNormalization_comp_alpha ds cq).trans
      (hAlpha.trans (ExtensionDiagram.ofNormalization_comp_alpha cp dt).symm)
  · exact (ExtensionDiagram.ofNormalization_comp_beta ds cq).trans
      (hBeta.trans (ExtensionDiagram.ofNormalization_comp_beta cp dt).symm)

private theorem leftSumComparisonNaturalityClass {T U : Core C} (a : T ⟶ U)
    {E E' : ExtensionCategory C} (b : E ⟶ E') :
    ExtensionCategory.mapHom F (ExtensionCategory.leftSumMap a b) ≫
        (ExtensionCategory.mapLeftSumIso F U E').hom =
      (ExtensionCategory.mapLeftSumIso F T E).hom ≫
        ExtensionCategory.leftSumMap (F.core.map a) (ExtensionCategory.mapHom F b) := by
  refine Quotient.inductionOn b ?_
  intro d
  let ls := ExtensionDiagram.leftSum a d
  let ds := ExtensionDiagram.map F ls
  let dt := ExtensionDiagram.leftSum (F.core.map a) (ExtensionDiagram.map F d)
  let cp := ExtensionCategory.mapLeftSumDiagram F T E
  let cq := ExtensionCategory.mapLeftSumDiagram F U E'
  have hSource : ExtensionCategory.mapHom F
      (ExtensionCategory.leftSumMap a (ExtensionCategory.mkHom d)) =
        ExtensionCategory.mkHom ds :=
    (congrArg (fun k : ExtensionCategory.leftSumObj T E ⟶
        ExtensionCategory.leftSumObj U E' => ExtensionCategory.mapHom F k)
      (originalLeftSumMapMk a d)).trans (ExtensionCategory.mapHom_mkHom F ls)
  have hTarget : ExtensionCategory.leftSumMap (F.core.map a)
      (ExtensionCategory.mapHom F (ExtensionCategory.mkHom d)) =
        ExtensionCategory.mkHom dt :=
    (congrArg (fun k : ExtensionCategory.mapObject F E ⟶ ExtensionCategory.mapObject F E' =>
      ExtensionCategory.leftSumMap (F.core.map a) k) (ExtensionCategory.mapHom_mkHom F d)).trans
        (originalLeftSumMapMk (F.core.map a) (ExtensionDiagram.map F d))
  have hMiddle : ExtensionCategory.mkHom ds ≫ ExtensionCategory.mkHom cq =
      ExtensionCategory.mkHom cp ≫ ExtensionCategory.mkHom dt :=
    (ExtensionCategory.mkHom_comp ds cq).trans
      (((ExtensionCategory.mkHom_eq_iff _ _).2 (leftSumMappedCompositeRel F a d)).trans
        (ExtensionCategory.mkHom_comp cp dt).symm)
  have hLeft := congrArg₂ (fun x y => x ≫ y) hSource
    (ExtensionCategory.mapLeftSumIso_hom F U E')
  have hRight := congrArg₂ (fun x y => x ≫ y)
    (ExtensionCategory.mapLeftSumIso_hom F T E).symm hTarget.symm
  exact hLeft.trans (hMiddle.trans hRight)

/-- The actual left-sum comparison is natural on every original quotient-diagram class. -/
public theorem ExtensionCategory.mapLeftSumIso_naturality {T U : Core C} (a : T ⟶ U)
    {E E' : ExtensionCategory C} (b : E ⟶ E') :
    ExtensionCategory.mapHom F (ExtensionCategory.leftSumMap a b) ≫
        (ExtensionCategory.mapLeftSumIso F U E').hom =
      (ExtensionCategory.mapLeftSumIso F T E).hom ≫
        ExtensionCategory.leftSumMap (F.core.map a) (ExtensionCategory.mapHom F b) :=
  leftSumComparisonNaturalityClass F a b


private theorem originalLeftSumMapHEq
    {A B A' B' : ExtensionCategory D} (hA : A = A') (hB : B = B')
    {a : A ⟶ B} {b : A' ⟶ B'} (h : HEq a b)
    {T U : Core D} (f : T ⟶ U) :
    HEq (ExtensionCategory.leftSumMap f a) (ExtensionCategory.leftSumMap f b) := by
  cases hA
  cases hB
  cases h
  exact HEq.rfl

private def originalLeftSumNaturalityIsoComputed :
    ExtensionCategory.leftSumFunctor (C := C) ⋙ ExtensionCategory.mapFunctor F ≅
      (F.core.prod (ExtensionCategory.mapFunctor F)) ⋙
        ExtensionCategory.leftSumFunctor (C := D) := by
  let L := ExtensionCategory.leftSumFunctor (C := C) ⋙ ExtensionCategory.mapFunctor F
  let R := (F.core.prod (ExtensionCategory.mapFunctor F)) ⋙
    ExtensionCategory.leftSumFunctor (C := D)
  let A (p : Core C × ExtensionCategory C) :=
    ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj p.1 p.2)
  let B (p : Core C × ExtensionCategory C) :=
    ExtensionCategory.leftSumObj (F.core.obj p.1) (ExtensionCategory.mapObject F p.2)
  have hL (p : Core C × ExtensionCategory C) : L.obj p = A p :=
    ExtensionCategory.mapFunctor_obj F (ExtensionCategory.leftSumObj p.1 p.2)
  have hR (p : Core C × ExtensionCategory C) : R.obj p = B p :=
    congrArg (fun E : ExtensionCategory D => ExtensionCategory.leftSumObj (F.core.obj p.1) E)
      (ExtensionCategory.mapFunctor_obj F p.2)
  let c (p : Core C × ExtensionCategory C) : L.obj p ≅ R.obj p :=
    eqToIso (hL p) ≪≫ ExtensionCategory.mapLeftSumIso F p.1 p.2 ≪≫ (eqToIso (hR p)).symm
  have hc (p : Core C × ExtensionCategory C) :
      HEq (c p).hom (ExtensionCategory.mapLeftSumIso F p.1 p.2).hom :=
    (conj_eqToHom_iff_heq _ _ (hL p) (hR p)).1 rfl
  refine NatIso.ofComponents c ?_
  intro p q f
  have hMapL : HEq (L.map f)
      (ExtensionCategory.mapHom F (ExtensionCategory.leftSumMap f.1 f.2)) :=
    ExtensionCategory.mapFunctor_map_heq F (ExtensionCategory.leftSumMap f.1 f.2)
  have hMapR : HEq (R.map f)
      (ExtensionCategory.leftSumMap (F.core.map f.1) (ExtensionCategory.mapHom F f.2)) :=
    originalLeftSumMapHEq (ExtensionCategory.mapFunctor_obj F p.2)
      (ExtensionCategory.mapFunctor_obj F q.2)
      (ExtensionCategory.mapFunctor_map_heq F f.2) (F.core.map f.1)
  have hLeft : HEq (L.map f ≫ (c q).hom)
      (ExtensionCategory.mapHom F (ExtensionCategory.leftSumMap f.1 f.2) ≫
        (ExtensionCategory.mapLeftSumIso F q.1 q.2).hom) :=
    heq_comp (hL p) (hL q) (hR q) hMapL (hc q)
  have hRight : HEq ((c p).hom ≫ R.map f)
      ((ExtensionCategory.mapLeftSumIso F p.1 p.2).hom ≫
        ExtensionCategory.leftSumMap (F.core.map f.1) (ExtensionCategory.mapHom F f.2)) :=
    heq_comp (hL p) (hR p) (hR q) (hc p) hMapR
  have hActual := ExtensionCategory.mapLeftSumIso_naturality F f.1 f.2
  exact eq_of_heq (hLeft.trans ((heq_of_eq hActual).trans hRight.symm))

/-- The original exact-functor image is coherently natural for the actual left-sum bifunctor. -/
public def ExtensionCategory.mapLeftSumNaturalityIso :
    ExtensionCategory.leftSumFunctor (C := C) ⋙ ExtensionCategory.mapFunctor F ≅
      (F.core.prod (ExtensionCategory.mapFunctor F)) ⋙
        ExtensionCategory.leftSumFunctor (C := D) :=
  originalLeftSumNaturalityIsoComputed F


private theorem originalLeftSumComponentHomComputed
    (T : Core C) (E : ExtensionCategory C) :
    HEq ((ExtensionCategory.mapLeftSumNaturalityIso F).app (T, E)).hom
      (ExtensionCategory.mapLeftSumIso F T E).hom := by
  let hs := ExtensionCategory.mapFunctor_obj F (ExtensionCategory.leftSumObj T E)
  let ht := congrArg (fun M : ExtensionCategory D =>
    ExtensionCategory.leftSumObj (F.core.obj T) M)
      (ExtensionCategory.mapFunctor_obj F E)
  change HEq (eqToHom hs ≫ (ExtensionCategory.mapLeftSumIso F T E).hom ≫
      eqToHom ht.symm) (ExtensionCategory.mapLeftSumIso F T E).hom
  exact (conj_eqToHom_iff_heq _ _ hs ht).1 rfl

/-- The actual action NaturalIso component is the original row Iso with exact endpoint casts. -/
public theorem ExtensionCategory.mapLeftSumNaturalityIso_app_hom_heq
    (T : Core C) (E : ExtensionCategory C) :
    HEq ((ExtensionCategory.mapLeftSumNaturalityIso F).app (T, E)).hom
      (ExtensionCategory.mapLeftSumIso F T E).hom :=
  originalLeftSumComponentHomComputed F T E

private theorem originalLeftSumComponentMiddleComputed
    (T : Core C) (E : ExtensionCategory C) :
    HEq (ExtensionCategory.homNormalization
      ((ExtensionCategory.mapLeftSumNaturalityIso F).app (T, E)).hom).hom.2.hom
      (F.mapBiprod T.of E.row.X₂).hom := by
  have hs := ExtensionCategory.mapFunctor_obj F (ExtensionCategory.leftSumObj T E)
  have ht := congrArg (fun M : ExtensionCategory D =>
    ExtensionCategory.leftSumObj (F.core.obj T) M)
      (ExtensionCategory.mapFunctor_obj F E)
  have hc := ExtensionCategory.homNormalization_middle_heq_of_objects_eq hs ht
    (ExtensionCategory.mapLeftSumNaturalityIso_app_hom_heq F T E)
  have hm : (ExtensionCategory.homNormalization
      (ExtensionCategory.mapLeftSumIso F T E).hom).hom.2.hom =
      (ExtensionCategory.mapLeftSumDiagram F T E).beta := by
    have h := congrArg (fun f :
        ExtensionCategory.mapObject F (ExtensionCategory.leftSumObj T E) ⟶
          ExtensionCategory.leftSumObj (F.core.obj T) (ExtensionCategory.mapObject F E) =>
      (ExtensionCategory.homNormalization f).hom.2.hom)
        (ExtensionCategory.mapLeftSumIso_hom F T E)
    exact h
  exact hc.trans ((heq_of_eq hm).trans
    (ExtensionCategory.mapLeftSumDiagram_components F T E).2.1)

/-- Its original normalized middle map is the canonical mapBiprod forward comparison. -/
public theorem ExtensionCategory.mapLeftSumNaturalityIso_app_middle_hom_heq
    (T : Core C) (E : ExtensionCategory C) :
    HEq (ExtensionCategory.homNormalization
      ((ExtensionCategory.mapLeftSumNaturalityIso F).app (T, E)).hom).hom.2.hom
      (F.mapBiprod T.of E.row.X₂).hom :=
  originalLeftSumComponentMiddleComputed F T E

end AlgebraicKTheory

end
