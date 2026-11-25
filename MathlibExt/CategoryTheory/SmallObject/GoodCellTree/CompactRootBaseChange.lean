/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerRestriction
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RelativePresentability
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.RootChangeColimits
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
public import Mathlib.Order.Extension.Well

/-!
# Compact roots of small original cell trees

The base-change functor is the native `Under.pushout`. Its actual pushout
maps transport the original cell squares and the chosen colimit cocones.
Compact approximation roots are selected from the accessible category's
presentation; the old root is arbitrary.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v uJ vJ

namespace CategoryTheory.SmallObject.CompactRootBaseChange

open Limits LowerSetColimits

variable {C : Type u} [Category.{v} C]

section BaseChange

variable [HasPushouts C] {X Y : C} (r : X ⟶ Y)

/-- The actual unit square for an original object is the chosen native pushout. -/
theorem root_isPushout (U : Under X) :
    IsPushout U.hom r (pushout.inl U.hom r)
      ((Under.pushout r).obj U).hom :=
  IsPushout.of_hasPushout U.hom r

/-- The actual adjunction's Hom bijection retains the original coefficient pushout inclusion. -/
theorem nativePushoutHomEquiv_right (U : Under X) (V : Under Y)
    (f : (Under.pushout r).obj U ⟶ V) :
    ((Under.mapPushoutAdj r).homEquiv U V f).right = pushout.inl U.hom r ≫ f.right := by
  change ((Under.mapPushoutAdj r).unit.app U).right ≫ f.right = _
  exact congrArg (fun m => m.right ≫ f.right) (Under.mapPushoutAdj_unit_app r U)

/-- The native composition isomorphism preserves the two actual original pushout inclusions. -/
theorem pushoutComp_inl {Z : C} (q : Y ⟶ Z) (U : Under X) :
    pushout.inl U.hom (r ≫ q) ≫ ((Under.pushoutComp r q).hom.app U).right =
      pushout.inl U.hom r ≫ pushout.inl ((Under.pushout r).obj U).hom q := by
  have h := unit_conjugateEquiv_symm
    ((Under.mapPushoutAdj r).comp (Under.mapPushoutAdj q))
    (Under.mapPushoutAdj (r ≫ q)) (Under.mapComp r q).inv U
  have hRight := congrArg Under.Hom.right h
  change (((Under.mapPushoutAdj r).comp (Under.mapPushoutAdj q)).unit.app U).right ≫
      ((Under.mapComp r q).inv.app _).right =
    ((Under.mapPushoutAdj (r ≫ q)).unit.app U).right ≫
      ((Under.pushoutComp r q).hom.app U).right at hRight
  have hUnit : (((Under.mapPushoutAdj r).comp (Under.mapPushoutAdj q)).unit.app U).right =
      pushout.inl U.hom r ≫ pushout.inl ((Under.pushout r).obj U).hom q := by
    have hR : ((Under.mapPushoutAdj r).unit.app U).right = pushout.inl U.hom r :=
      congrArg Under.Hom.right (Under.mapPushoutAdj_unit_app r U)
    have hQ : ((Under.mapPushoutAdj q).unit.app ((Under.pushout r).obj U)).right =
        pushout.inl ((Under.pushout r).obj U).hom q :=
      congrArg Under.Hom.right (Under.mapPushoutAdj_unit_app q ((Under.pushout r).obj U))
    rw [Adjunction.comp_unit_app, Under.comp_right, Under.map_map_right]
    exact congrArg₂ (fun f g => f ≫ g) hR hQ
  have hFlat : ((Under.mapPushoutAdj (r ≫ q)).unit.app U).right =
      pushout.inl U.hom (r ≫ q) :=
    congrArg Under.Hom.right (Under.mapPushoutAdj_unit_app (r ≫ q) U)
  rw [RootChangeColimits.compositionIso_inv_right] at hRight
  have hId : (((Under.mapPushoutAdj r).comp (Under.mapPushoutAdj q)).unit.app U).right ≫
      𝟙 ((Under.pushout r ⋙ Under.pushout q).obj U).right =
        (((Under.mapPushoutAdj r).comp (Under.mapPushoutAdj q)).unit.app U).right :=
    Category.comp_id _
  exact (congrArg (fun f => f ≫ ((Under.pushoutComp r q).hom.app U).right) hFlat.symm).trans
    (hRight.symm.trans (hId.trans hUnit))

/-- The native inverse composition returns the original composite-root inclusion. -/
theorem pushoutComp_inl_inv {Z : C} (q : Y ⟶ Z) (U : Under X) :
    (pushout.inl U.hom r ≫ pushout.inl ((Under.pushout r).obj U).hom q) ≫
      ((Under.pushoutComp r q).inv.app U).right = pushout.inl U.hom (r ≫ q) := by
  have hUnit := congrArg (fun f => f ≫ ((Under.pushoutComp r q).inv.app U).right)
    (pushoutComp_inl r q U).symm
  have hAssoc := Category.assoc (pushout.inl U.hom (r ≫ q))
    ((Under.pushoutComp r q).hom.app U).right ((Under.pushoutComp r q).inv.app U).right
  have hInv := congrArg (fun f => pushout.inl U.hom (r ≫ q) ≫ f)
    (Under.hom_right_inv_right ((Under.pushoutComp r q).app U))
  exact hUnit.trans (hAssoc.trans (hInv.trans (Category.comp_id _)))

/-- Equality of actual root arrows transports the original native pushout inclusion. -/
theorem pushout_eqIso_inl {r' : X ⟶ Y} (hr : r = r') (U : Under X) :
    pushout.inl U.hom r ≫
      (eqToIso (congrArg (fun f : X ⟶ Y => (Under.pushout f).obj U) hr)).hom.right =
        pushout.inl U.hom r' := by
  subst r'
  simp only [eqToIso_refl, Iso.refl_hom, Under.id_right]
  exact Category.comp_id _

/-- Native base change retains the original map on the original pushout leg. -/
@[reassoc]
theorem inl_map {U V : Under X} (f : U ⟶ V) :
    pushout.inl U.hom r ≫ ((Under.pushout r).map f).right =
      f.right ≫ pushout.inl V.hom r := by
  change pushout.inl U.hom r ≫
    pushout.desc (f.right ≫ pushout.inl V.hom r) (pushout.inr V.hom r) _ = _
  exact pushout.inl_desc _ _ _

/-- Each original under morphism induces its actual pushout square after root change. -/
theorem map_isPushout {U V : Under X} (f : U ⟶ V) :
    IsPushout f.right (pushout.inl U.hom r) (pushout.inl V.hom r)
      ((Under.pushout r).map f).right := by
  change IsPushout f.right (pushout.inl U.hom r) (pushout.inl V.hom r)
    (pushout.desc (f.right ≫ pushout.inl V.hom r) (pushout.inr V.hom r) _)
  apply IsPushout.of_left _ (pushout.inl_desc _ _ _).symm
    (IsPushout.of_hasPushout U.hom r)
  simpa only [Under.w f, pushout.inr_desc] using IsPushout.of_hasPushout V.hom r

variable {P : Type w} [PartialOrder P] {alpha : Type t}
  {s : alpha → Arrow C} (T : CellTree s X (P := P))

/-- Push the actual predecessor cocone by the native left adjoint, retaining every leg. -/
def pushoutPredecessor (a : P) :
    ColimitCocone (restriction (T.diagram ⋙ Under.pushout r) (LowerSet.Iio a)) where
  cocone := (Under.pushout r).mapCocone (T.predecessor a).cocone
  isColimit := isColimitOfPreserves (Under.pushout r) (T.predecessor a).isColimit

/-- The actual predecessor-to-vertex function is the native image of the old function. -/
theorem pushoutPredecessorMap (a : P) :
    cellTreePredecessorMap (T.diagram ⋙ Under.pushout r) a (pushoutPredecessor r T a) =
      (Under.pushout r).map (T.predecessorMap a) := by
  apply (pushoutPredecessor r T a).isColimit.hom_ext
  intro b
  rw [cellTreePredecessorMap_fac]
  change (Under.pushout r).map (T.diagram.map (homOfLE b.2.le)) =
    (Under.pushout r).map ((T.predecessor a).cocone.ι.app b) ≫
      (Under.pushout r).map (T.predecessorMap a)
  rw [← Functor.map_comp, T.predecessorMap_fac]

/-- A whole cell tree pushed along its actual root arrow, on the literal original label order. -/
def pushoutTree : CellTree s Y (P := P) where
  wellFounded := T.wellFounded
  diagram := T.diagram ⋙ Under.pushout r
  label := T.label
  predecessor := pushoutPredecessor r T
  attaching a := T.attaching a ≫ pushout.inl (T.predecessorObj a).hom r
  cell a := T.cell a ≫ pushout.inl (T.vertex a).hom r
  isPushout a := by
    rw [pushoutPredecessorMap]
    exact ((T.isPushout a).flip.paste_vert
      (map_isPushout r (T.predecessorMap a))).flip
  endpoint :=
    { cocone := (Under.pushout r).mapCocone T.endpoint.cocone
      isColimit := isColimitOfPreserves (Under.pushout r) T.endpoint.isColimit }

/-- Every original generator occurrence retains its original attaching-family label. -/
theorem pushoutTree_label : (pushoutTree r T).label = T.label := rfl

/-- The original generator sources and all original attaching functions remain explicit. -/
theorem pushoutTree_attaching_function :
    (fun a : P => (pushoutTree r T).attaching a) =
      (fun a : P => T.attaching a ≫ pushout.inl (T.predecessorObj a).hom r) := rfl

/-- The whole original cell-target function is retained through its native pushout leg. -/
theorem pushoutTree_cell_function :
    (fun a : P => (pushoutTree r T).cell a) =
      (fun a : P => T.cell a ≫ pushout.inl (T.vertex a).hom r) := rfl

/-- The actual whole endpoint is the native pushout object of the old endpoint. -/
theorem pushoutTree_endpoint :
    (pushoutTree r T).endpointObj = (Under.pushout r).obj T.endpointObj := rfl

/-- The root and both original endpoint maps form the true original pushout. -/
theorem pushoutTree_endpoint_isPushout :
    IsPushout T.hom r (pushout.inl T.hom r) (pushoutTree r T).hom :=
  root_isPushout r T.endpointObj

/-- Root change preserves the same goodness witnesses and actual original predecessor bounds. -/
theorem pushoutTree_good (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (h : T.IsGood chi) : (pushoutTree r T).IsGood chi where
  presentable_source := h.presentable_source
  presentable_target := h.presentable_target
  predecessor_lt := h.predecessor_lt

/-- The same selected lower cocones are mapped by the native left adjoint. -/
def pushoutLowerData (L : LowerSetColimitData T.diagram) :
    LowerSetColimitData (pushoutTree r T).diagram where
  cocone B := (Under.pushout r).mapCocone (L.cocone B)
  isColimit B := isColimitOfPreserves (Under.pushout r) (L.isColimit B)

/-- The entire selected lower-object function uses the actual original choices. -/
theorem pushoutLowerData_obj_function (L : LowerSetColimitData T.diagram) :
    (fun B : LowerSet P => (pushoutLowerData r T L).obj B) =
      (fun B : LowerSet P => (Under.pushout r).obj (L.obj B)) := rfl

/-- Every selected lower-map function is the native image of the same original map. -/
theorem pushoutLowerData_map (L : LowerSetColimitData T.diagram)
    {B D : LowerSet P} (h : B ≤ D) :
    (pushoutLowerData r T L).map h = (Under.pushout r).map (L.map h) := by
  apply (pushoutLowerData r T L).hom_ext
  intro a
  rw [LowerSetColimitData.ι_map]
  change (Under.pushout r).map (L.ι D ⟨a.1, memOfLE h a.2⟩) =
    (Under.pushout r).map (L.ι B a) ≫ (Under.pushout r).map (L.map h)
  rw [← Functor.map_comp, L.ι_map]

/-- The complete native lower-map function retains both its original source and target. -/
theorem pushoutLowerData_map_function (L : LowerSetColimitData T.diagram) :
    (fun (B D : LowerSet P) (h : B ≤ D) => (pushoutLowerData r T L).map h) =
      (fun (B D : LowerSet P) (h : B ≤ D) => (Under.pushout r).map (L.map h)) := by
  funext B D h
  exact pushoutLowerData_map r T L h

end BaseChange

section Approximation

variable (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- Internally chosen compact roots and their actual directed presentation of the old root. -/
structure CompactApproximation (X : C) where
  /-- The actual small directed index. -/
  index : Type w
  /-- Its actual partial-order dictionary. -/
  partialOrder : PartialOrder index
  /-- Its actual cardinal-filtered cone witnesses. -/
  filtered : @IsCardinalFiltered index (@Preorder.smallCategory index partialOrder.toPreorder)
    chi _
  /-- The full presentation with its original-root cocone. -/
  presentation : @ColimitPresentation C _ index
    (@Preorder.smallCategory index partialOrder.toPreorder) X
  /-- Compactness belongs to every approximation object, not to the old root. -/
  presentable (i : index) : IsCardinalPresentable (presentation.diag.obj i) chi

attribute [instance] CompactApproximation.partialOrder CompactApproximation.filtered

variable [IsCardinalAccessibleCategory C chi] (X : C)

/-- The actual accessible-category generator supplies the compact directed approximation. -/
theorem compactApproximation_nonempty : Nonempty (CompactApproximation chi X) := by
  obtain ⟨J, hJ, hFiltered, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C chi).exists_colimitsOfShape X
  obtain ⟨I, hI, hIchi, F, hF⟩ := IsCardinalFiltered.exists_cardinal_directed J chi
  exact ⟨
    { index := I
      partialOrder := hI
      filtered := hIchi
      presentation := p.toColimitPresentation.reindex F
      presentable i := p.prop_diag_obj (F.obj i) }⟩

/-- Choose the actual compact directed approximation of the arbitrary old root internally. -/
def compactApproximation : CompactApproximation chi X :=
  Classical.choice (compactApproximation_nonempty chi X)

end Approximation

section RootPushoutApproximation

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular]
  {X : C} (A : CompactApproximation chi X) (i : A.index)
  (U : Under (A.presentation.diag.obj i))

/-- The actual native base-change objects along all original approximation transitions. -/
abbrev rootPushoutDiagram : Under i ⥤ C where
  obj j := pushout U.hom (A.presentation.diag.map j.hom)
  map {j k} f :=
    pushout.desc (pushout.inl U.hom (A.presentation.diag.map k.hom))
      (A.presentation.diag.map f.right ≫
        pushout.inr U.hom (A.presentation.diag.map k.hom)) (by
      rw [← Category.assoc, ← Functor.map_comp, Under.w f]
      exact pushout.condition)
  map_id j := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, Category.comp_id]
    · simp only [pushout.inr_desc, Under.id_right, Functor.map_id,
        Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply pushout.hom_ext
    · simp only [pushout.inl_desc, pushout.inl_desc_assoc]
    · simp only [Category.assoc, pushout.inr_desc, pushout.inr_desc_assoc,
        Under.comp_right, Functor.map_comp]

/-- The rotated family is the native pushout left adjoint followed by native forget. -/
abbrev reverseRootPushoutDiagram : Under i ⥤ C :=
  Under.post A.presentation.diag ⋙ Under.pushout U.hom ⋙ Under.forget U.right

/-- Native pushout symmetry compares the entire actual family, including every transition map. -/
def rootPushoutSymmetry :
    rootPushoutDiagram chi A i U ≅ reverseRootPushoutDiagram chi A i U :=
  NatIso.ofComponents
    (fun j => pushoutSymmetry U.hom (A.presentation.diag.map j.hom)) (by
      intro j k f
      apply pushout.hom_ext
      · simp [rootPushoutDiagram, reverseRootPushoutDiagram, Under.pushout,
          Under.post]
      · simp [rootPushoutDiagram, reverseRootPushoutDiagram, Under.pushout,
          Under.post, Category.assoc])

/-- The native under-presentation and both left adjoints give the actual rotated colimit. -/
abbrev reverseRootPushoutPresentation :
    ColimitPresentation (Under i) (pushout (A.presentation.ι.app i) U.hom) where
  diag := reverseRootPushoutDiagram chi A i U
  ι := ((Under.forget U.right).mapCocone
    ((Under.pushout U.hom).mapCocone (A.presentation.cocone.underPost i))).ι
  isColimit := by
    let : IsFiltered A.index := isFiltered_of_isCardinalFiltered A.index chi
    let : IsFiltered (Under i) := isFiltered_of_isCardinalFiltered (Under i) chi
    let : IsConnected (Under i) := IsFiltered.isConnected _
    exact isColimitOfPreserves (Under.forget U.right)
      (isColimitOfPreserves (Under.pushout U.hom) (A.presentation.isColimit.underPost i))

/-- The actual base change to the arbitrary old root is the colimit of the native stage objects. -/
abbrev rootPushoutPresentation :
    ColimitPresentation (Under i) (pushout U.hom (A.presentation.ι.app i)) :=
  ((reverseRootPushoutPresentation chi A i U).changeDiag
    (rootPushoutSymmetry chi A i U)).ofIso (pushoutSymmetry (A.presentation.ι.app i) U.hom)

/-- Every original stage leg retains the original coefficient object's pushout inclusion. -/
@[reassoc]
theorem rootPushoutPresentation_inl (j : Under i) :
    pushout.inl U.hom (A.presentation.diag.map j.hom) ≫
      (rootPushoutPresentation chi A i U).ι.app j =
        pushout.inl U.hom (A.presentation.ι.app i) := by
  change pushout.inl U.hom (A.presentation.diag.map j.hom) ≫
    (((rootPushoutSymmetry chi A i U).hom ≫
      (reverseRootPushoutPresentation chi A i U).ι).app j ≫
        (pushoutSymmetry (A.presentation.ι.app i) U.hom).hom) = _
  rw [NatTrans.comp_app (rootPushoutSymmetry chi A i U).hom
    (reverseRootPushoutPresentation chi A i U).ι j]
  have hSym : (rootPushoutSymmetry chi A i U).hom.app j =
      (pushoutSymmetry U.hom (A.presentation.diag.map j.hom)).hom := rfl
  rw [hSym]
  rw [Functor.mapCocone_ι_app (Under.forget U.right),
    Functor.mapCocone_ι_app (Under.pushout U.hom)]
  have hCondition : A.presentation.diag.map j.hom ≫
      (A.presentation.ι.app j.right ≫ pushout.inl (A.presentation.ι.app i) U.hom) =
        U.hom ≫ pushout.inr (A.presentation.ι.app i) U.hom := by
    rw [← Category.assoc, A.presentation.w j.hom]
    exact pushout.condition
  change pushout.inl U.hom (A.presentation.diag.map j.hom) ≫
    (((pushoutSymmetry U.hom (A.presentation.diag.map j.hom)).hom ≫
      pushout.desc (A.presentation.ι.app j.right ≫
        pushout.inl (A.presentation.ι.app i) U.hom)
        (pushout.inr (A.presentation.ι.app i) U.hom) hCondition) ≫
        (pushoutSymmetry (A.presentation.ι.app i) U.hom).hom) = _
  simp only [← Category.assoc, inl_comp_pushoutSymmetry_hom, pushout.inr_desc,
    inr_comp_pushoutSymmetry_hom]

/-- Every original stage leg retains its actual original approximation-to-root map. -/
@[reassoc]
theorem rootPushoutPresentation_inr (j : Under i) :
    pushout.inr U.hom (A.presentation.diag.map j.hom) ≫
      (rootPushoutPresentation chi A i U).ι.app j =
        A.presentation.ι.app j.right ≫ pushout.inr U.hom (A.presentation.ι.app i) := by
  change pushout.inr U.hom (A.presentation.diag.map j.hom) ≫
    (((rootPushoutSymmetry chi A i U).hom ≫
      (reverseRootPushoutPresentation chi A i U).ι).app j ≫
        (pushoutSymmetry (A.presentation.ι.app i) U.hom).hom) = _
  rw [NatTrans.comp_app (rootPushoutSymmetry chi A i U).hom
    (reverseRootPushoutPresentation chi A i U).ι j]
  have hSym : (rootPushoutSymmetry chi A i U).hom.app j =
      (pushoutSymmetry U.hom (A.presentation.diag.map j.hom)).hom := rfl
  rw [hSym]
  rw [Functor.mapCocone_ι_app (Under.forget U.right),
    Functor.mapCocone_ι_app (Under.pushout U.hom)]
  have hCondition : A.presentation.diag.map j.hom ≫
      (A.presentation.ι.app j.right ≫ pushout.inl (A.presentation.ι.app i) U.hom) =
        U.hom ≫ pushout.inr (A.presentation.ι.app i) U.hom := by
    rw [← Category.assoc, A.presentation.w j.hom]
    exact pushout.condition
  change pushout.inr U.hom (A.presentation.diag.map j.hom) ≫
    (((pushoutSymmetry U.hom (A.presentation.diag.map j.hom)).hom ≫
      pushout.desc (A.presentation.ι.app j.right ≫
        pushout.inl (A.presentation.ι.app i) U.hom)
        (pushout.inr (A.presentation.ι.app i) U.hom) hCondition) ≫
        (pushoutSymmetry (A.presentation.ι.app i) U.hom).hom) = _
  simp only [← Category.assoc]
  rw [inr_comp_pushoutSymmetry_hom, pushout.inl_desc, Category.assoc,
    inl_comp_pushoutSymmetry_hom]

/-- Compactness factors an actual original attaching map at a genuine later root stage. -/
theorem exists_rootPushoutFactor {S : C} [IsCardinalPresentable S chi]
    (f : S ⟶ pushout U.hom (A.presentation.ι.app i)) :
    ∃ (j : Under i) (g : S ⟶ pushout U.hom (A.presentation.diag.map j.hom)),
      g ≫ (rootPushoutPresentation chi A i U).ι.app j = f := by
  let : EssentiallySmall.{w} (Under i) := essentiallySmall_of_small_of_locallySmall _
  exact IsCardinalPresentable.exists_hom_of_isColimit chi
    (rootPushoutPresentation chi A i U).isColimit f

/-- Original attaching equations are detected at a genuine common later root stage. -/
theorem exists_rootPushoutEquality {S : C} [IsCardinalPresentable S chi]
    (j : Under i)
    (f g : S ⟶ pushout U.hom (A.presentation.diag.map j.hom))
    (h : f ≫ (rootPushoutPresentation chi A i U).ι.app j =
      g ≫ (rootPushoutPresentation chi A i U).ι.app j) :
    ∃ (k : Under i) (t : j ⟶ k),
      f ≫ (rootPushoutDiagram chi A i U).map t =
        g ≫ (rootPushoutDiagram chi A i U).map t := by
  let : EssentiallySmall.{w} (Under i) := essentiallySmall_of_small_of_locallySmall _
  exact IsCardinalPresentable.exists_eq_of_isColimit' chi
    (rootPushoutPresentation chi A i U).isColimit f g h

end RootPushoutApproximation

section MovingRoots

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular]
  {X : C} (A : CompactApproximation chi X)

/-- The original root cocone and the genuine comma square give the full pushout-map equation. -/
theorem originalBaseChange_condition
    {U V : Comma A.presentation.diag (𝟭 C)} (f : U ⟶ V) :
    U.hom ≫ (f.right ≫ pushout.inl V.hom (A.presentation.ι.app V.left)) =
      A.presentation.ι.app U.left ≫ pushout.inr V.hom (A.presentation.ι.app V.left) := by
  have h : U.hom ≫ f.right = A.presentation.diag.map f.left ≫ V.hom := f.w.symm
  rw [← Category.assoc, h, Category.assoc, pushout.condition,
    ← Category.assoc, A.presentation.w f.left]

/-- Send a diagram with actual moving approximation roots to the same arbitrary old root. -/
abbrev originalBaseChange : Comma A.presentation.diag (𝟭 C) ⥤ Under X where
  obj U := Under.mk (pushout.inr U.hom (A.presentation.ι.app U.left))
  map {U V} f := Under.homMk
    (pushout.desc (f.right ≫ pushout.inl V.hom (A.presentation.ι.app V.left))
      (pushout.inr V.hom (A.presentation.ι.app V.left))
      (originalBaseChange_condition chi A f))
    (pushout.inr_desc _ _ _)
  map_id U := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · simp only [Under.homMk_right, Under.id_right, Under.mk_right, pushout.inl_desc,
        Comma.id_right, Category.comp_id]
      exact Category.id_comp _
    · simp only [Under.homMk_right, Under.id_right, Under.mk_right,
        pushout.inr_desc, Category.comp_id]
  map_comp f g := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · simp only [Under.homMk_right, Under.comp_right, Comma.comp_right,
        Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    · simp only [Under.homMk_right, Under.comp_right,
        pushout.inr_desc, pushout.inr_desc_assoc]

/-- Every moving-root object is sent to its actual native original-root pushout value. -/
theorem originalBaseChange_obj_function :
    (fun U : Comma A.presentation.diag (𝟭 C) => (originalBaseChange chi A).obj U) =
      (fun U : Comma A.presentation.diag (𝟭 C) =>
        (Under.pushout (A.presentation.ι.app U.left)).obj (Under.mk U.hom)) := rfl

/-- The original coefficient leg retains the complete original moving-root comparison map. -/
@[reassoc]
theorem originalBaseChange_inl {U V : Comma A.presentation.diag (𝟭 C)} (f : U ⟶ V) :
    pushout.inl U.hom (A.presentation.ι.app U.left) ≫
      ((originalBaseChange chi A).map f).right =
        f.right ≫ pushout.inl V.hom (A.presentation.ι.app V.left) :=
  pushout.inl_desc _ _ _

/-- The original root leg is the actual root leg after the same moving-root comparison. -/
@[reassoc]
theorem originalBaseChange_inr {U V : Comma A.presentation.diag (𝟭 C)} (f : U ⟶ V) :
    pushout.inr U.hom (A.presentation.ι.app U.left) ≫
      ((originalBaseChange chi A).map f).right =
        pushout.inr V.hom (A.presentation.ι.app V.left) :=
  pushout.inr_desc _ _ _

variable {J : Type uJ} [Category.{vJ} J]
  (D : J ⥤ Comma A.presentation.diag (𝟭 C)) (i : A.index)
  (h : ∀ j, (D.obj j).left ≤ i)

/-- Every actual moving-root comparison commutes with the chosen common receiving root. -/
theorem raised_condition {j k : J} (f : j ⟶ k) :
    (D.obj j).hom ≫ ((D.map f).right ≫
      pushout.inl (D.obj k).hom (A.presentation.diag.map (homOfLE (h k)))) =
    A.presentation.diag.map (homOfLE (h j)) ≫
      pushout.inr (D.obj k).hom (A.presentation.diag.map (homOfLE (h k))) := by
  have hf : (D.obj j).hom ≫ (D.map f).right =
      A.presentation.diag.map (D.map f).left ≫ (D.obj k).hom := (D.map f).w.symm
  rw [← Category.assoc, hf, Category.assoc, pushout.condition,
    ← Category.assoc, ← Functor.map_comp]
  congr 2

/-- The entire original diagram pushed to an actual common compact approximation root. -/
abbrev raisedDiagram : J ⥤ Under (A.presentation.diag.obj i) where
  obj j := Under.mk (pushout.inr (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))))
  map {j k} f := Under.homMk
    (pushout.desc ( (D.map f).right ≫
      pushout.inl (D.obj k).hom (A.presentation.diag.map (homOfLE (h k))))
      (pushout.inr (D.obj k).hom (A.presentation.diag.map (homOfLE (h k))))
      (raised_condition chi A D i h f))
    (pushout.inr_desc _ _ _)
  map_id j := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · simp only [Under.homMk_right, Under.id_right, Under.mk_right, pushout.inl_desc,
        D.map_id, Comma.id_right, Category.comp_id]
      exact Category.id_comp _
    · simp only [Under.homMk_right, Under.id_right, Under.mk_right,
        pushout.inr_desc, Category.comp_id]
  map_comp f g := by
    apply Under.UnderMorphism.ext
    apply pushout.hom_ext
    · simp only [Under.homMk_right, Under.comp_right, D.map_comp, Comma.comp_right,
        Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    · simp only [Under.homMk_right, Under.comp_right,
        pushout.inr_desc, pushout.inr_desc_assoc]

/-- Each new common-root object is the native pushout of its literal original moving-root object. -/
theorem raisedDiagram_obj_function :
    (fun j : J => (raisedDiagram chi A D i h).obj j) =
      (fun j : J =>
        (Under.pushout (A.presentation.diag.map (homOfLE (h j)))).obj
          (Under.mk (D.obj j).hom)) := rfl

/-- The common-root coefficient leg preserves the whole original comparison function. -/
@[reassoc]
theorem raisedDiagram_inl {j k : J} (f : j ⟶ k) :
    pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))) ≫
      ((raisedDiagram chi A D i h).map f).right =
        (D.map f).right ≫
          pushout.inl (D.obj k).hom (A.presentation.diag.map (homOfLE (h k))) :=
  pushout.inl_desc _ _ _

/-- The actual common root is retained by every raised original comparison. -/
@[reassoc]
theorem raisedDiagram_inr {j k : J} (f : j ⟶ k) :
    pushout.inr (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))) ≫
      ((raisedDiagram chi A D i h).map f).right =
        pushout.inr (D.obj k).hom (A.presentation.diag.map (homOfLE (h k))) :=
  pushout.inr_desc _ _ _

/-- The actual native composition comparison at each original moving-root vertex. -/
def raisedComponentIso (j : J) :
    (Under.pushout (A.presentation.ι.app i)).obj ((raisedDiagram chi A D i h).obj j) ≅
      (originalBaseChange chi A).obj (D.obj j) :=
  ((Under.pushoutComp (A.presentation.diag.map (homOfLE (h j)))
    (A.presentation.ι.app i)).app (Under.mk (D.obj j).hom)).symm ≪≫
      eqToIso (congrArg
        (fun f : A.presentation.diag.obj (D.obj j).left ⟶ X =>
          (Under.pushout f).obj (Under.mk (D.obj j).hom))
        (A.presentation.w (homOfLE (h j))))

/-- Both native pushout inclusions return the same original vertex inclusion. -/
@[reassoc]
theorem raisedComponentIso_inl (j : J) :
    (pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))) ≫
      pushout.inl ((raisedDiagram chi A D i h).obj j).hom (A.presentation.ι.app i)) ≫
        (raisedComponentIso chi A D i h j).hom.right =
          pushout.inl (D.obj j).hom (A.presentation.ι.app (D.obj j).left) := by
  have hc := pushoutComp_inl_inv (A.presentation.diag.map (homOfLE (h j)))
    (A.presentation.ι.app i) (Under.mk (D.obj j).hom)
  have he := pushout_eqIso_inl (A.presentation.diag.map (homOfLE (h j)) ≫
    A.presentation.ι.app i) (A.presentation.w (homOfLE (h j))) (Under.mk (D.obj j).hom)
  let e := eqToIso (congrArg
    (fun f : A.presentation.diag.obj (D.obj j).left ⟶ X =>
      (Under.pushout f).obj (Under.mk (D.obj j).hom))
    (A.presentation.w (homOfLE (h j))))
  change (pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))) ≫
    pushout.inl ((raisedDiagram chi A D i h).obj j).hom (A.presentation.ι.app i)) ≫
      (((Under.pushoutComp (A.presentation.diag.map (homOfLE (h j)))
        (A.presentation.ι.app i)).inv.app (Under.mk (D.obj j).hom)).right ≫ e.hom.right) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e.hom.right) hc).trans he)

/-- The complete original vertex inclusion, in the associative form used by all diagram maps. -/
@[reassoc]
theorem raisedComponentIso_inl_flat (j : J) :
    pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))) ≫
      pushout.inl ((raisedDiagram chi A D i h).obj j).hom (A.presentation.ι.app i) ≫
        (raisedComponentIso chi A D i h j).hom.right =
          pushout.inl (D.obj j).hom (A.presentation.ι.app (D.obj j).left) :=
  (Category.assoc _ _ _).symm.trans (raisedComponentIso_inl chi A D i h j)

/-- All native component comparisons form a natural isomorphism to the original-root diagram. -/
def raisedOriginalIso :
    raisedDiagram chi A D i h ⋙ Under.pushout (A.presentation.ι.app i) ≅
      D ⋙ originalBaseChange chi A :=
  NatIso.ofComponents (raisedComponentIso chi A D i h) (by
    intro j k f
    let m₁ := (Under.pushout (A.presentation.ι.app i)).map
      ((raisedDiagram chi A D i h).map f) ≫ (raisedComponentIso chi A D i h k).hom
    let m₂ := (raisedComponentIso chi A D i h j).hom ≫
      (originalBaseChange chi A).map (D.map f)
    have hRoot :
        ((Under.pushout (A.presentation.ι.app i)).obj
          ((raisedDiagram chi A D i h).obj j)).hom ≫ m₁.right =
        ((Under.pushout (A.presentation.ι.app i)).obj
          ((raisedDiagram chi A D i h).obj j)).hom ≫ m₂.right :=
      (Under.w m₁).trans (Under.w m₂).symm
    apply Under.UnderMorphism.ext
    change m₁.right = m₂.right
    apply pushout.hom_ext
    · apply pushout.hom_ext
      · change _ ≫ _ ≫
          (((Under.pushout (A.presentation.ι.app i)).map
            ((raisedDiagram chi A D i h).map f)).right ≫
              (raisedComponentIso chi A D i h k).hom.right) =
          _ ≫ _ ≫ ((raisedComponentIso chi A D i h j).hom.right ≫
            ((originalBaseChange chi A).map (D.map f)).right)
        let a := pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h j)))
        let b := pushout.inl ((raisedDiagram chi A D i h).obj j).hom (A.presentation.ι.app i)
        let a' := pushout.inl (D.obj k).hom (A.presentation.diag.map (homOfLE (h k)))
        let b' := pushout.inl ((raisedDiagram chi A D i h).obj k).hom (A.presentation.ι.app i)
        let v := ((raisedDiagram chi A D i h).map f).right
        let c := ((Under.pushout (A.presentation.ι.app i)).map
          ((raisedDiagram chi A D i h).map f)).right
        let d := (raisedComponentIso chi A D i h k).hom.right
        let e := (raisedComponentIso chi A D i h j).hom.right
        let g := ((originalBaseChange chi A).map (D.map f)).right
        have h₁ : CommSq a (D.map f).right v a' :=
          ⟨raisedDiagram_inl chi A D i h f⟩
        have h₂ : CommSq b v c b' :=
          ⟨inl_map (A.presentation.ι.app i) ((raisedDiagram chi A D i h).map f)⟩
        have hSquare : (a ≫ b) ≫ c = (D.map f).right ≫ (a' ≫ b') :=
          (Category.assoc a b c).trans ((congrArg (fun p => a ≫ p) h₂.w).trans
            ((Category.assoc a v b').symm.trans
              ((congrArg (fun p => p ≫ b') h₁.w).trans (Category.assoc _ _ _))))
        have hLeft := (Category.assoc a b (c ≫ d)).symm.trans
          ((Category.assoc (a ≫ b) c d).symm.trans
            ((congrArg (fun p => p ≫ d) hSquare).trans
              ((Category.assoc (D.map f).right (a' ≫ b') d).trans
                (congrArg (fun p => (D.map f).right ≫ p)
                  (raisedComponentIso_inl chi A D i h k)))))
        have hRight := (Category.assoc a b (e ≫ g)).symm.trans
          ((Category.assoc (a ≫ b) e g).symm.trans
            ((congrArg (fun p => p ≫ g) (raisedComponentIso_inl chi A D i h j)).trans
              (originalBaseChange_inl chi A (D.map f))))
        exact hLeft.trans hRight.symm
      · have e : ((raisedDiagram chi A D i h).obj j).hom ≫
            pushout.inl ((raisedDiagram chi A D i h).obj j).hom (A.presentation.ι.app i) =
          A.presentation.ι.app i ≫
            pushout.inr ((raisedDiagram chi A D i h).obj j).hom (A.presentation.ι.app i) :=
          pushout.condition
        have h₁ := congrArg (fun p => p ≫ m₁.right) e
        have h₂ := congrArg (fun p => p ≫ m₂.right) e
        have hMiddle := h₁.trans ((Category.assoc _ _ _).trans
          ((congrArg (fun p => A.presentation.ι.app i ≫ p) hRoot).trans
            ((Category.assoc _ _ _).symm.trans h₂.symm)))
        exact (Category.assoc _ _ _).symm.trans
          (hMiddle.trans (Category.assoc _ _ _))
    · exact hRoot)

end MovingRoots

section RootAdjoinedDataCongruence

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {J : Type w} [Category.{w} J]
  (D E : J ⥤ Comma A.presentation.diag (𝟭 C)) (i j : A.index)
  (hi : ∀ b, (D.obj b).left ≤ i) (hj : ∀ b, (E.obj b).left ≤ j)

/-- Equal actual birth data and receiving roots give the same entire root-adjoined C diagram. -/
theorem raisedAdjoined_congr (hD : D = E) (hRoot : i = j) :
    UnderColimits.adjoinedDiagram (Y := raisedDiagram chi A D i hi) =
      UnderColimits.adjoinedDiagram (Y := raisedDiagram chi A E j hj) := by
  cases hD
  cases hRoot
  rfl

end RootAdjoinedDataCongruence

section AllOriginalLowerComparisons

variable [HasPushouts C] {P : Type w} [PartialOrder P] {alpha : Type t}
  {s : alpha → Arrow C} {X Y : C} (r : Y ⟶ X)
  (S : CellTree s Y (P := P)) (T : CellTree s X (P := P))
  (LS : LowerSetColimitData S.diagram) (L : LowerSetColimitData T.diagram)
  (eta : S.diagram ⋙ Under.pushout r ≅ T.diagram)

/-- The original chosen lower cocone transported along the actual whole vertex comparison. -/
abbrev originalLowerComparisonCocone (B : LowerSet P) :
    Cocone (restriction (S.diagram ⋙ Under.pushout r) B) :=
  (Cocone.precompose (Functor.isoWhiskerLeft (inclusion (B : Set P)) eta).hom).obj
    (L.cocone B)

/-- The whole original lower comparison has the actual chosen lower colimit UP. -/
def originalLowerComparisonIsColimit (B : LowerSet P) :
    IsColimit (originalLowerComparisonCocone r S T L eta B) :=
  (IsColimit.precomposeHomEquiv (Functor.isoWhiskerLeft (inclusion (B : Set P)) eta)
    (L.cocone B)).symm (L.isColimit B)

/-- Native base change identifies every chosen new lower piece with the same original L piece. -/
def lowerComparison (B : LowerSet P) :
    (Under.pushout r).obj (LS.obj B) ≅ L.obj B :=
  ((pushoutLowerData r S LS).isColimit B).coconePointUniqueUpToIso
    (originalLowerComparisonIsColimit r S T L eta B)

/-- Every original lower vertex leg is retained by the whole native lower comparison. -/
@[reassoc]
theorem lowerComparison_leg (B : LowerSet P) (a : B) :
    (Under.pushout r).map (LS.ι B a) ≫ (lowerComparison r S T LS L eta B).hom =
      eta.hom.app a.1 ≫ L.ι B a := by
  have h := ((pushoutLowerData r S LS).isColimit B).comp_coconePointUniqueUpToIso_hom
    (originalLowerComparisonIsColimit r S T L eta B) a
  change ((Under.pushout r).mapCocone (LS.cocone B)).ι.app a ≫ _ =
    ((Functor.isoWhiskerLeft (inclusion (B : Set P)) eta).hom ≫ (L.cocone B).ι).app a at h
  rw [Functor.mapCocone_ι_app, NatTrans.comp_app] at h
  exact h

/-- Both directions preserve the same original lower vertex function. -/
@[reassoc]
theorem lowerComparison_leg_inv (B : LowerSet P) (a : B) :
    (eta.hom.app a.1 ≫ L.ι B a) ≫ (lowerComparison r S T LS L eta B).inv =
      (Under.pushout r).map (LS.ι B a) := by
  rw [← lowerComparison_leg r S T LS L eta B a, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Every whole original lower inclusion map is retained by the natural family of comparisons. -/
theorem lowerComparison_map {B D : LowerSet P} (h : B ≤ D) :
    (Under.pushout r).map (LS.map h) ≫ (lowerComparison r S T LS L eta D).hom =
      (lowerComparison r S T LS L eta B).hom ≫ L.map h := by
  apply (pushoutLowerData r S LS).hom_ext
  intro a
  change (Under.pushout r).map (LS.ι B a) ≫
    ((Under.pushout r).map (LS.map h) ≫ (lowerComparison r S T LS L eta D).hom) =
      (Under.pushout r).map (LS.ι B a) ≫
        ((lowerComparison r S T LS L eta B).hom ≫ L.map h)
  rw [← Functor.map_comp_assoc, LS.ι_map, lowerComparison_leg,
    lowerComparison_leg_assoc, L.ι_map]

end AllOriginalLowerComparisons

section CommonRootTransitions

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular]
  {X : C} (A : CompactApproximation chi X) (i : A.index)

/-- The actual compact approximation diagram below a given genuine receiving root. -/
abbrev upperRootDiagram : Set.Iic i ⥤ C :=
  inclusion (Set.Iic i) ⋙ A.presentation.diag

/-- The terminal receiving root supplies its actual full compact-object presentation. -/
def upperRootApproximation : CompactApproximation chi (A.presentation.diag.obj i) where
  index := Set.Iic i
  partialOrder := inferInstance
  filtered := isCardinalFiltered_of_hasTerminal _ chi
  presentation :=
    { diag := upperRootDiagram chi A i
      ι :=
        { app b := A.presentation.diag.map (homOfLE b.2)
          naturality b c f := by
            change A.presentation.diag.map (homOfLE (leOfHom f)) ≫
              A.presentation.diag.map (homOfLE c.2) =
                A.presentation.diag.map (homOfLE b.2) ≫ 𝟙 _
            rw [Category.comp_id, ← Functor.map_comp]
            rfl }
      isColimit :=
        { desc c := c.ι.app ⟨i, le_rfl⟩
          fac c b := by
            simpa only [upperRootDiagram, inclusion, Functor.comp_map,
              Category.comp_id] using c.w (homOfLE b.2 : b ⟶ (⟨i, le_rfl⟩ : Set.Iic i))
          uniq c m hm := by
            have h := hm (⟨i, le_rfl⟩ : Set.Iic i)
            change A.presentation.diag.map (𝟙 i) ≫ m = c.ι.app ⟨i, le_rfl⟩ at h
            rw [A.presentation.diag.map_id, Category.id_comp] at h
            exact h } }
  presentable b := A.presentable b.1

variable {J : Type uJ} [Category.{vJ} J]
  (D : J ⥤ Comma A.presentation.diag (𝟭 C))
  (h : ∀ j, (D.obj j).left ≤ i)

/-- Restrict only the moving-root indices, preserving every original coefficient and comparison. -/
def restrictedRootDiagram : J ⥤ Comma (upperRootApproximation chi A i).presentation.diag (𝟭 C) where
  obj j := { left := ⟨(D.obj j).left, h j⟩, right := (D.obj j).right, hom := (D.obj j).hom }
  map {j k} f :=
    { left := homOfLE (show (⟨(D.obj j).left, h j⟩ : Set.Iic i) ≤
          ⟨(D.obj k).left, h k⟩ from leOfHom (D.map f).left)
      right := (D.map f).right
      w := by
        have he : homOfLE (leOfHom (D.map f).left) = (D.map f).left := Subsingleton.elim _ _
        change A.presentation.diag.map (homOfLE (leOfHom (D.map f).left)) ≫
          (D.obj k).hom = (D.obj j).hom ≫ (𝟭 C).map (D.map f).right
        rw [he]
        exact (D.map f).w }
  map_id j := by
    ext
    · exact Subsingleton.elim _ _
    · exact congrArg (fun f => f.right) (D.map_id j)
  map_comp f g := by
    ext
    · exact Subsingleton.elim _ _
    · exact congrArg (fun f => f.right) (D.map_comp f g)

omit [HasPushouts C] in
/-- All original moving-root right objects remain literal after the index restriction. -/
theorem restrictedRootDiagram_right_objects :
    (fun j => ((restrictedRootDiagram chi A i D h).obj j).right) =
      (fun j => (D.obj j).right) := rfl

variable (i₀ : A.index) (h₀ : ∀ j, (D.obj j).left ≤ i₀) (h₀i : i₀ ≤ i)

/-- Two actual common receiving roots give the native coherent comparison of the whole diagram. -/
def raiseCompositionIso :
    raisedDiagram chi A D i₀ h₀ ⋙ Under.pushout (A.presentation.diag.map (homOfLE h₀i)) ≅
      raisedDiagram chi A D i h := by
  let B := upperRootApproximation chi A i
  let E := restrictedRootDiagram chi A i D h
  exact raisedOriginalIso chi B E (⟨i₀, h₀i⟩ : Set.Iic i) h₀

/-- Both original coefficient inclusions are retained when two real receiving roots are compared. -/
@[reassoc]
theorem raiseCompositionIso_inl (j : J) :
    (pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h₀ j))) ≫
      pushout.inl ((raisedDiagram chi A D i₀ h₀).obj j).hom
        (A.presentation.diag.map (homOfLE h₀i))) ≫
      ((raiseCompositionIso chi A i D h i₀ h₀ h₀i).hom.app j).right =
        pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))) := by
  let E := restrictedRootDiagram chi A i D h
  exact raisedComponentIso_inl chi (upperRootApproximation chi A i) E
    (⟨i₀, h₀i⟩ : Set.Iic i) h₀ j

/-- The associative whole coefficient function of the genuine common-root comparison. -/
@[reassoc]
theorem raiseCompositionIso_inl_flat (j : J) :
    pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h₀ j))) ≫
      pushout.inl ((raisedDiagram chi A D i₀ h₀).obj j).hom
        (A.presentation.diag.map (homOfLE h₀i)) ≫
      ((raiseCompositionIso chi A i D h i₀ h₀ h₀i).hom.app j).right =
        pushout.inl (D.obj j).hom (A.presentation.diag.map (homOfLE (h j))) :=
  (Category.assoc _ _ _).symm.trans
    (raiseCompositionIso_inl chi A i D h i₀ h₀ h₀i j)

end CommonRootTransitions

section ExplicitWorkingUnderColimits

variable [HasColimitsOfSize.{w, w} C] {Y : C} {J : Type w} [Category.{w} J]
  (D : J ⥤ Under Y)

/-- Select the actual root-adjoined C colimit through the native cocone equivalence. -/
abbrev workingUnderColimit : ColimitCocone D where
  cocone := WithInitial.coconeEquiv.inverse.obj
    (colimit.cocone (UnderColimits.adjoinedDiagram (Y := D)))
  isColimit := WithInitial.isColimitEquiv
    (IsColimit.ofIsoColimit (colimit.isColimit (UnderColimits.adjoinedDiagram (Y := D)))
      (WithInitial.coconeEquiv.counitIso.app _).symm)

/-- The complete coefficient point is the actual chosen original root-adjoined C colimit. -/
theorem workingUnderColimit_right :
    (workingUnderColimit D).cocone.pt.right =
      colimit (UnderColimits.adjoinedDiagram (Y := D)) := rfl

/-- Equal actual C diagrams retain all chosen colimit legs and both object transports. -/
theorem colimitEquality_leg {F G : J ⥤ C} (h : F = G) (j : J) :
    colimit.ι F j ≫ eqToHom (congrArg (fun E => colimit E) h) =
      eqToHom (Functor.congr_obj h j) ≫ colimit.ι G j := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The entire actual coefficient factor survives equal-diagram and endpoint transports. -/
theorem colimitEquality_factor {F G : J ⥤ C} (h : F = G) {Y Z : C} (hYZ : Y = Z)
    (v : colimit G ⟶ Z) (j : J) (f : F.obj j ⟶ Y)
    (hf : HEq f (colimit.ι G j ≫ v)) :
    colimit.ι F j ≫ eqToHom (congrArg (fun E => colimit E) h) ≫ v ≫ eqToHom hYZ.symm = f := by
  have hFirst := (Category.assoc (colimit.ι F j)
    (eqToHom (congrArg (fun E => colimit E) h)) (v ≫ eqToHom hYZ.symm)).symm
  have hSecond := congrArg (fun m => m ≫ v ≫ eqToHom hYZ.symm) (colimitEquality_leg h j)
  have hThird := (Category.assoc (eqToHom (Functor.congr_obj h j)) (colimit.ι G j)
    (v ≫ eqToHom hYZ.symm)).trans
      (congrArg (fun m => eqToHom (Functor.congr_obj h j) ≫ m)
        (Category.assoc (colimit.ι G j) v (eqToHom hYZ.symm)).symm)
  exact hFirst.trans (hSecond.trans (hThird.trans
    ((conj_eqToHom_iff_heq f (colimit.ι G j ≫ v) (Functor.congr_obj h j) hYZ).mpr hf).symm))

end ExplicitWorkingUnderColimits

section ActualMovingMapTranspose

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X)

/-- Transpose a whole actual moving-root arrow to its receiver's native pushout object. -/
abbrev transposeMovingMap {U V : Comma A.presentation.diag (𝟭 C)} (f : U ⟶ V) :
    (Under.pushout (A.presentation.diag.map (homOfLE (leOfHom f.left)))).obj (Under.mk U.hom) ⟶
      (Under.mk V.hom : Under (A.presentation.diag.obj V.left)) :=
  Under.homMk (pushout.desc f.right V.hom (by
    have h : f.left = homOfLE (leOfHom f.left) := Subsingleton.elim _ _
    exact f.w.symm.trans (congrArg (fun m => A.presentation.diag.map m ≫ V.hom) h)))
    (pushout.inr_desc _ _ _)

/-- Equal original objects and whole maps retain the full transposed coefficient value. -/
theorem transposeMovingMap_heq {U V U' V' : Comma A.presentation.diag (𝟭 C)}
    (hU : U = U') (hV : V = V') {f : U ⟶ V} {f' : U' ⟶ V'} (hf : HEq f f') :
    HEq (transposeMovingMap chi A f).right (transposeMovingMap chi A f').right := by
  cases hU
  cases hV
  cases hf
  rfl

omit [HasPushouts C] in
/-- Equality of actual moving-root objects preserves the entire dependent root morphism. -/
theorem movingHom_heq {U V : Comma A.presentation.diag (𝟭 C)} (h : U = V) : HEq U.hom V.hom := by
  cases h
  rfl

/-- Native functor transport of whole equal arrows retains both actual object values. -/
theorem mapArrow_heq {K : Type uJ} [Category.{vJ} K] {E : Type uJ} [Category.{vJ} E]
    (H : K ⥤ E) {U V U' V' : K} (hU : U = U') (hV : V = V')
    {f : U ⟶ V} {f' : U' ⟶ V'} (hf : HEq f f') : HEq (H.map f) (H.map f') := by
  cases hU
  cases hV
  cases hf
  rfl

end ActualMovingMapTranspose

section OriginalPastComparisonValues

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {J : Type w} [Category.{w} J]
  (D : J ⥤ Comma A.presentation.diag (𝟭 C)) (E : J ⥤ Under X)
  (eta : D ⋙ originalBaseChange chi A ≅ E) (c : ColimitCocone E)
  (i : A.index) (hi : ∀ b, (D.obj b).left ≤ i)

/-- The entire original past comparison uses the actual native common-root composition Iso. -/
abbrev originalPastIso :
    raisedDiagram chi A D i hi ⋙ Under.pushout (A.presentation.ι.app i) ≅ E :=
  raisedOriginalIso chi A D i hi ≪≫ eta

/-- Both actual original colimit UPs identify the full chosen past point after root base change. -/
abbrev originalPastComparison :
    (Under.pushout (A.presentation.ι.app i)).obj
      (workingUnderColimit (raisedDiagram chi A D i hi)).cocone.pt ≅ c.cocone.pt :=
  (isColimitOfPreserves (Under.pushout (A.presentation.ι.app i))
    (workingUnderColimit (raisedDiagram chi A D i hi)).isColimit).coconePointsIsoOfNatIso
      c.isColimit (originalPastIso chi A D E eta i hi)

/-- The actual native Hom bijection retains the full original past map under the selected root. -/
abbrev originalPastMap :
    (workingUnderColimit (raisedDiagram chi A D i hi)).cocone.pt ⟶
      (Under.map (A.presentation.ι.app i)).obj c.cocone.pt :=
  (Under.mapPushoutAdj (A.presentation.ι.app i)).homEquiv _ _
    (originalPastComparison chi A D E eta c i hi).hom

/-- Actual diagram, comparison and root equalities retain the full original coefficient map. -/
theorem originalPastMap_heq
    {D' : J ⥤ Comma A.presentation.diag (𝟭 C)} (hD : D = D')
    {eta' : D' ⋙ originalBaseChange chi A ≅ E} (hEta : HEq eta eta')
    {j : A.index} (hRoot : i = j) {hj : ∀ b, (D'.obj b).left ≤ j} :
    HEq (originalPastMap chi A D E eta c i hi).right
      (originalPastMap chi A D' E eta' c j hj).right := by
  cases hD
  cases hRoot
  cases hEta
  rfl

end OriginalPastComparisonValues

section ActualBirthPredecessors

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P]
  (B : LowerSet P) (D : B ⥤ Comma A.presentation.diag (𝟭 C)) (a : B)

/-- The literal old predecessor labels enter the same original lower prefix. -/
abbrev birthPastInclusion : LowerSet.Iio a.1 ⥤ B where
  obj b := ⟨b.1, B.lower b.2.le a.2⟩
  map f := homOfLE (leOfHom f)

/-- The actual already-built moving-root predecessor diagram uses those original labels. -/
abbrev birthPastDiagram : LowerSet.Iio a.1 ⥤ Comma A.presentation.diag (𝟭 C) :=
  birthPastInclusion B a ⋙ D

/-- The genuine existing diagram supplies every actual predecessor-to-vertex arrow. -/
abbrev birthPastArrow (b : LowerSet.Iio a.1) :
    (birthPastInclusion B a).obj b ⟶ a := homOfLE b.2.le

omit [HasPushouts C] [HasColimitsOfSize.{w, w} C] in
/-- Every old predecessor root has its actual transition to the selected birth root. -/
theorem birthPastRootBound (b : LowerSet.Iio a.1) :
    ((birthPastDiagram chi A B D a).obj b).left ≤ (D.obj a).left :=
  leOfHom (D.map (birthPastArrow B a b)).left

/-- The actual predecessor diagram is pushed to the selected vertex's genuine birth root. -/
abbrev birthPredecessorDiagram :
    LowerSet.Iio a.1 ⥤ Under (A.presentation.diag.obj (D.obj a).left) :=
  raisedDiagram chi A (birthPastDiagram chi A B D a) (D.obj a).left
    (birthPastRootBound chi A B D a)

/-- The native selected birth vertex under its own actual compact approximation root. -/
abbrev birthVertex : Under (A.presentation.diag.obj (D.obj a).left) := Under.mk (D.obj a).hom

omit [HasPushouts C] [HasColimitsOfSize.{w, w} C] in
/-- The original comma square is the entire actual predecessor pushout-leg compatibility. -/
theorem birthPredecessorLegCondition (b : LowerSet.Iio a.1) :
    ((birthPastDiagram chi A B D a).obj b).hom ≫ (D.map (birthPastArrow B a b)).right =
      A.presentation.diag.map (homOfLE (birthPastRootBound chi A B D a b)) ≫ (D.obj a).hom := by
  have he : (D.map (birthPastArrow B a b)).left =
      homOfLE (birthPastRootBound chi A B D a b) := Subsingleton.elim _ _
  exact (D.map (birthPastArrow B a b)).w.symm.trans
    (congrArg (fun f => A.presentation.diag.map f ≫ (D.obj a).hom) he)

/-- The whole actual predecessor leg, including its root equation, is constructed internally. -/
abbrev birthPredecessorLeg (b : LowerSet.Iio a.1) :
    (birthPredecessorDiagram chi A B D a).obj b ⟶ birthVertex chi A B D a :=
  Under.homMk (pushout.desc (D.map (birthPastArrow B a b)).right (D.obj a).hom
    (birthPredecessorLegCondition chi A B D a b)) (pushout.inr_desc _ _ _)

omit [HasColimitsOfSize.{w, w} C] in
/-- The complete actual birth leg retains the original coefficient comparison. -/
@[reassoc]
theorem birthPredecessorLeg_inl (b : LowerSet.Iio a.1) :
    pushout.inl ((birthPastDiagram chi A B D a).obj b).hom
      (A.presentation.diag.map (homOfLE (birthPastRootBound chi A B D a b))) ≫
        (birthPredecessorLeg chi A B D a b).right = (D.map (birthPastArrow B a b)).right :=
  pushout.inl_desc _ _ _

omit [HasColimitsOfSize.{w, w} C] in
/-- The whole actual birth leg keeps the selected original birth-root map. -/
@[reassoc]
theorem birthPredecessorLeg_inr (b : LowerSet.Iio a.1) :
    pushout.inr ((birthPastDiagram chi A B D a).obj b).hom
      (A.presentation.diag.map (homOfLE (birthPastRootBound chi A B D a b))) ≫
        (birthPredecessorLeg chi A B D a b).right = (D.obj a).hom :=
  pushout.inr_desc _ _ _

/-- Both original predecessor comparison paths are the same actual diagram arrow. -/
theorem birthPastArrow_naturality {b c : LowerSet.Iio a.1} (f : b ⟶ c) :
    (birthPastInclusion B a).map f ≫ birthPastArrow B a c = birthPastArrow B a b :=
  Subsingleton.elim _ _

/-- The internally built full predecessor cocone retains every original map and root. -/
abbrev birthPredecessorCocone : Cocone (birthPredecessorDiagram chi A B D a) where
  pt := birthVertex chi A B D a
  ι :=
    { app b := birthPredecessorLeg chi A B D a b
      naturality b c f := by
        have hw : (birthPredecessorDiagram chi A B D a).map f ≫
            birthPredecessorLeg chi A B D a c = birthPredecessorLeg chi A B D a b := by
          apply Under.UnderMorphism.ext
          change ((birthPredecessorDiagram chi A B D a).map f).right ≫
            (birthPredecessorLeg chi A B D a c).right =
              (birthPredecessorLeg chi A B D a b).right
          apply pushout.hom_ext
          · simp only [raisedDiagram_inl_assoc, birthPredecessorLeg_inl]
            have h := D.map_comp ((birthPastInclusion B a).map f) (birthPastArrow B a c)
            rw [birthPastArrow_naturality] at h
            exact congrArg (fun m : (birthPastDiagram chi A B D a).obj b ⟶ D.obj a =>
              m.right) h.symm
          · simp only [raisedDiagram_inr_assoc, birthPredecessorLeg_inr]
        exact hw.trans (Category.comp_id _).symm }

/-- The selected birth predecessor uses actual available working-size colimits. -/
abbrev birthPredecessor : ColimitCocone (birthPredecessorDiagram chi A B D a) where
  cocone := (workingUnderColimit (birthPredecessorDiagram chi A B D a)).cocone
  isColimit := (workingUnderColimit (birthPredecessorDiagram chi A B D a)).isColimit

/-- The genuine birth predecessor-to-vertex morphism is the actual selected colimit descender. -/
abbrev birthPredecessorMap :
    (birthPredecessor chi A B D a).cocone.pt ⟶ birthVertex chi A B D a :=
  (birthPredecessor chi A B D a).isColimit.desc (birthPredecessorCocone chi A B D a)

/-- Each literal old predecessor leg factors through that same full descender. -/
@[reassoc]
theorem birthPredecessorMap_fac (b : LowerSet.Iio a.1) :
    (birthPredecessor chi A B D a).cocone.ι.app b ≫ birthPredecessorMap chi A B D a =
      birthPredecessorLeg chi A B D a b :=
  (birthPredecessor chi A B D a).isColimit.fac (birthPredecessorCocone chi A B D a) b

end ActualBirthPredecessors

section InternalPrefixLifts

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))

/-- The complete actual prefix objects and their original comparisons, before cell witnesses. -/
structure PrefixCore (B : LowerSet P) where
  /-- Every actual birth root, coefficient object and comparison arrow. -/
  diagram : B ⥤ Comma A.presentation.diag (𝟭 C)
  /-- The entire actual native original-root vertex comparison. -/
  comparison : diagram ⋙ originalBaseChange chi A ≅ restriction T.diagram B

/-- Restrict all actual primary data of a prefix core to the same original lower labels. -/
abbrev PrefixCore.restrict {B E : LowerSet P} (S : PrefixCore chi A T B) (h : E ≤ B) :
    PrefixCore chi A T E where
  diagram := lowerInclusion h ⋙ S.diagram
  comparison := Functor.isoWhiskerLeft (lowerInclusion h) S.comparison

omit [HasColimitsOfSize.{w, w} C] in
/-- The literal core is determined by its entire birth diagram and original comparison. -/
theorem PrefixCore.ext {B : LowerSet P} {S R : PrefixCore chi A T B}
    (hD : S.diagram = R.diagram) (hEta : HEq S.comparison R.comparison) : S = R := by
  cases S
  cases R
  cases hD
  cases hEta
  rfl

omit [HasColimitsOfSize.{w, w} C] in
/-- Equality of full original cores retains every actual whiskered comparison and its inverse. -/
theorem PrefixCore.whiskerComparison_heq {B : LowerSet P} {S R : PrefixCore chi A T B}
    (h : S = R) {J : Type w} [Category.{w} J] (H : J ⥤ B) :
    HEq (Functor.isoWhiskerLeft H S.comparison) (Functor.isoWhiskerLeft H R.comparison) := by
  cases h
  rfl

/-- Every actual core keeps its complete original comparison in the native comma diagram. -/
abbrev PrefixCore.comparedDiagram {B : LowerSet P} (S : PrefixCore chi A T B) :
    B ⥤ Comma (originalBaseChange chi A) T.diagram where
  obj a := { left := S.diagram.obj a, right := a.1, hom := S.comparison.hom.app a }
  map {a b} f :=
    { left := S.diagram.map f
      right := homOfLE (leOfHom f)
      w := S.comparison.hom.naturality f }
  map_id a := by
    apply Comma.hom_ext
    · exact S.diagram.map_id a
    · exact Subsingleton.elim _ _
  map_comp f g := by
    apply Comma.hom_ext
    · exact S.diagram.map_comp f g
    · exact Subsingleton.elim _ _

omit [HasColimitsOfSize.{w, w} C] in
/-- The entire core is recovered by its native compared diagram, including all inverse maps. -/
theorem PrefixCore.comparedDiagram_injective {B : LowerSet P} {S R : PrefixCore chi A T B}
    (h : S.comparedDiagram chi A T = R.comparedDiagram chi A T) : S = R := by
  have hD : S.diagram = R.diagram := congrArg
    (fun F => F ⋙ Comma.fst (originalBaseChange chi A) T.diagram) h
  cases S with | mk D eta =>
    cases R with | mk E theta =>
      cases hD
      have hCompare : eta = theta := by
        apply Iso.ext
        apply NatTrans.ext
        funext a
        have hObj := Functor.congr_obj h a
        injection hObj
      cases hCompare
      rfl

/-- The whole true birth-predecessor diagram maps to the original predecessor diagram. -/
abbrev PrefixCore.birthOriginalIso {B : LowerSet P} (S : PrefixCore chi A T B) (a : B) :
    birthPredecessorDiagram chi A B S.diagram a ⋙
      Under.pushout (A.presentation.ι.app (S.diagram.obj a).left) ≅
    restriction T.diagram (LowerSet.Iio a.1) :=
  originalPastIso chi A (birthPastDiagram chi A B S.diagram a)
    (restriction T.diagram (LowerSet.Iio a.1))
    (Functor.isoWhiskerLeft (birthPastInclusion B a) S.comparison) (S.diagram.obj a).left
    (birthPastRootBound chi A B S.diagram a)

/-- The two actual predecessor UPs identify the entire birth predecessor after root change. -/
abbrev PrefixCore.birthOriginalComparison {B : LowerSet P} (S : PrefixCore chi A T B) (a : B) :
    (Under.pushout (A.presentation.ι.app (S.diagram.obj a).left)).obj
      (birthPredecessor chi A B S.diagram a).cocone.pt ≅ T.predecessorObj a.1 :=
  originalPastComparison chi A (birthPastDiagram chi A B S.diagram a)
    (restriction T.diagram (LowerSet.Iio a.1))
    (Functor.isoWhiskerLeft (birthPastInclusion B a) S.comparison) (T.predecessor a.1)
    (S.diagram.obj a).left (birthPastRootBound chi A B S.diagram a)

/-- The complete original predecessor coefficient map retains its actual birth-root equation. -/
abbrev PrefixCore.birthOriginalMap {B : LowerSet P} (S : PrefixCore chi A T B) (a : B) :
    (birthPredecessor chi A B S.diagram a).cocone.pt ⟶
      (Under.map (A.presentation.ι.app (S.diagram.obj a).left)).obj (T.predecessorObj a.1) :=
  originalPastMap chi A (birthPastDiagram chi A B S.diagram a)
    (restriction T.diagram (LowerSet.Iio a.1))
    (Functor.isoWhiskerLeft (birthPastInclusion B a) S.comparison) (T.predecessor a.1)
    (S.diagram.obj a).left (birthPastRootBound chi A B S.diagram a)

/-- Retain both actual original attaching and target-cell functions in each internal witness. -/
def PrefixCore.BirthCell {B : LowerSet P} (S : PrefixCore chi A T B) (a : B) : Prop :=
  ∃ (g : (s (T.label a.1)).left ⟶ (birthPredecessor chi A B S.diagram a).cocone.pt.right)
    (k : (s (T.label a.1)).right ⟶ (S.diagram.obj a).right),
    IsPushout g (s (T.label a.1)).hom (birthPredecessorMap chi A B S.diagram a).right k ∧
    g ≫ (S.birthOriginalMap chi A T a).right = T.attaching a.1 ∧
    k ≫ pushout.inl (S.diagram.obj a).hom (A.presentation.ι.app (S.diagram.obj a).left) ≫
      (S.comparison.hom.app a).right = T.cell a.1

/-- The whole original coefficient map of each native compared object keeps its actual root unit. -/
abbrev PrefixCore.comparedCoefficientMap (U : Comma (originalBaseChange chi A) T.diagram) :
    U.left.right ⟶ (T.diagram.obj U.right).right :=
  pushout.inl U.left.hom (A.presentation.ι.app U.left.left) ≫ U.hom.right

omit [HasColimitsOfSize.{w, w} C] in
/-- Equality of compared objects retains the whole original coefficient function. -/
theorem PrefixCore.comparedCoefficientMap_heq
    {U V : Comma (originalBaseChange chi A) T.diagram} (h : U = V) :
    HEq (PrefixCore.comparedCoefficientMap chi A T U)
      (PrefixCore.comparedCoefficientMap chi A T V) := by
  cases h
  rfl

omit [HasColimitsOfSize.{w, w} C] in
/-- Exact lower restriction retains the whole actual core comparison functor. -/
theorem PrefixCore.comparedDiagram_restrict {B E : LowerSet P} (S : PrefixCore chi A T B)
    (h : E ≤ B) :
    (S.restrict chi A T h).comparedDiagram chi A T = lowerInclusion h ⋙ S.comparedDiagram chi A T :=
  rfl

/-- Every true lower restriction retains the same complete original birth-cell predicate. -/
theorem PrefixCore.birthCell_restrict {B E : LowerSet P} (S : PrefixCore chi A T B)
    (h : E ≤ B) (a : E) :
    (S.restrict chi A T h).BirthCell chi A T a ↔
      S.BirthCell chi A T (⟨a.1, memOfLE h a.2⟩ : B) := Iff.rfl

/-- Every actual original birth-predecessor leg factors through its whole original comparison. -/
@[reassoc]
theorem PrefixCore.birthOriginalComparison_leg {B : LowerSet P} (S : PrefixCore chi A T B)
    (a : B) (b : LowerSet.Iio a.1) :
    (Under.pushout (A.presentation.ι.app (S.diagram.obj a).left)).map
      ((birthPredecessor chi A B S.diagram a).cocone.ι.app b) ≫
      (S.birthOriginalComparison chi A T a).hom =
    (S.birthOriginalIso chi A T a).hom.app b ≫ (T.predecessor a.1).cocone.ι.app b :=
  (isColimitOfPreserves (Under.pushout (A.presentation.ι.app (S.diagram.obj a).left))
    (birthPredecessor chi A B S.diagram a).isColimit).comp_coconePointsIsoOfNatIso_hom
      (T.predecessor a.1).isColimit (S.birthOriginalIso chi A T a) b

/-- The exact native Hom bijection retains the full original coefficient map on each birth leg. -/
@[reassoc]
theorem PrefixCore.birthOriginalMap_leg {B : LowerSet P} (S : PrefixCore chi A T B)
    (a : B) (b : LowerSet.Iio a.1) :
    ((birthPredecessor chi A B S.diagram a).cocone.ι.app b).right ≫
      (S.birthOriginalMap chi A T a).right =
    pushout.inl ((birthPredecessorDiagram chi A B S.diagram a).obj b).hom
      (A.presentation.ι.app (S.diagram.obj a).left) ≫
    ((S.birthOriginalIso chi A T a).hom.app b).right ≫
      ((T.predecessor a.1).cocone.ι.app b).right := by
  let adj := Under.mapPushoutAdj (A.presentation.ι.app (S.diagram.obj a).left)
  have h := (adj.homEquiv_naturality_left
    ((birthPredecessor chi A B S.diagram a).cocone.ι.app b)
    (S.birthOriginalComparison chi A T a).hom).symm.trans
      (congrArg (adj.homEquiv ((birthPredecessorDiagram chi A B S.diagram a).obj b)
        (T.predecessorObj a.1)) (S.birthOriginalComparison_leg chi A T a b))
  exact (congrArg Under.Hom.right h).trans
    (nativePushoutHomEquiv_right (A.presentation.ι.app (S.diagram.obj a).left) _ _ _)

/-- Internal prefix data keep the old labels, real root transitions and actual cell squares. -/
structure PrefixLift (B : LowerSet P) where
  /-- The actual moving-root coefficient diagram on this literal original prefix. -/
  diagram : B ⥤ Comma A.presentation.diag (𝟭 C)
  /-- Native base change returns the same original vertex diagram. -/
  comparison : diagram ⋙ originalBaseChange chi A ≅ restriction T.diagram B
  /-- Each original generator is attached by an actual internally selected birth pushout. -/
  cell (a : B) :
    (PrefixCore.mk diagram comparison : PrefixCore chi A T B).BirthCell chi A T a

/-- Retain the entire actual core of each internally constructed prefix state. -/
abbrev PrefixLift.core {B : LowerSet P} (S : PrefixLift chi A T B) : PrefixCore chi A T B where
  diagram := S.diagram
  comparison := S.comparison

/-- The actual empty moving-root prefix uses no original attaching labels. -/
abbrev emptyBirthDiagram : (⊥ : LowerSet P) ⥤ Comma A.presentation.diag (𝟭 C) where
  obj a := False.elim (LowerSet.notMem_bot a.2)
  map {a} _ := False.elim (LowerSet.notMem_bot a.2)
  map_id a := False.elim (LowerSet.notMem_bot a.2)
  map_comp {a} _ _ := False.elim (LowerSet.notMem_bot a.2)

/-- The first genuine empty-prefix state is constructed without a supplied coherent state. -/
def emptyPrefixLift : PrefixLift chi A T (⊥ : LowerSet P) where
  diagram := emptyBirthDiagram chi A
  comparison := NatIso.ofComponents (fun a => False.elim (LowerSet.notMem_bot a.2)) (by
    intro a b f
    exact False.elim (LowerSet.notMem_bot a.2))
  cell a := False.elim (LowerSet.notMem_bot a.2)

/-- Prefix states retain both the actual diagram and the entire original comparison. -/
theorem PrefixLift.ext {B : LowerSet P} {S R : PrefixLift chi A T B}
    (h : S.diagram = R.diagram) (hCompare : HEq S.comparison R.comparison) : S = R := by
  cases S
  cases R
  cases h
  cases hCompare
  rfl

/-- Restrict the internally built state to literal original labels, retaining every birth cell. -/
def PrefixLift.restrict {B E : LowerSet P} (S : PrefixLift chi A T B) (h : E ≤ B) :
    PrefixLift chi A T E where
  diagram := lowerInclusion h ⋙ S.diagram
  comparison := Functor.isoWhiskerLeft (lowerInclusion h) S.comparison
  cell a := by
    let aB : B := ⟨a.1, memOfLE h a.2⟩
    obtain ⟨g, k, hs⟩ := S.cell aB
    exact ⟨g, k, hs⟩

/-- Restriction to the same actual label set leaves the entire state unchanged. -/
theorem PrefixLift.restrict_id {B : LowerSet P} (S : PrefixLift chi A T B) :
    S.restrict chi A T (le_refl B) = S := by
  cases S
  rfl

/-- All original restriction paths retain the same entire coefficient diagram and birth maps. -/
theorem PrefixLift.restrict_comp {B E F : LowerSet P} (S : PrefixLift chi A T B)
    (hEB : E ≤ B) (hFE : F ≤ E) :
    (S.restrict chi A T hEB).restrict chi A T hFE = S.restrict chi A T (hFE.trans hEB) := by
  cases S
  rfl

/-- Equality of actual label supports transports the full state and its complete restriction. -/
theorem PrefixLift.transport_restrict {B E F : LowerSet P} (h : E = F)
    (S : PrefixLift chi A T E) (hB : B ≤ F) :
    (Eq.mp (congrArg (fun L => PrefixLift chi A T L) h) S).restrict chi A T hB =
      S.restrict chi A T (Eq.mpr (congrArg (fun L => B ≤ L) h) hB) := by
  cases h
  rfl

/-- Keep each actual birth object and its entire original comparison in a native comma diagram. -/
def PrefixLift.comparedDiagram {B : LowerSet P} (S : PrefixLift chi A T B) :
    B ⥤ Comma (originalBaseChange chi A) T.diagram where
  obj a := { left := S.diagram.obj a, right := a.1, hom := S.comparison.hom.app a }
  map {a b} f :=
    { left := S.diagram.map f
      right := homOfLE (leOfHom f)
      w := S.comparison.hom.naturality f }
  map_id a := by
    apply Comma.hom_ext
    · exact S.diagram.map_id a
    · exact Subsingleton.elim _ _
  map_comp f g := by
    apply Comma.hom_ext
    · exact S.diagram.map_comp f g
    · exact Subsingleton.elim _ _

/-- The native comma projection returns the same entire actual birth diagram. -/
theorem PrefixLift.comparedDiagram_fst {B : LowerSet P} (S : PrefixLift chi A T B) :
    S.comparedDiagram chi A T ⋙ Comma.fst (originalBaseChange chi A) T.diagram = S.diagram := rfl

/-- Exact restriction also retains every actual comparison homomorphism and its inverse. -/
theorem PrefixLift.comparedDiagram_restrict {B E : LowerSet P} (S : PrefixLift chi A T B)
    (h : E ≤ B) :
    (S.restrict chi A T h).comparedDiagram chi A T = lowerInclusion h ⋙ S.comparedDiagram chi A T :=
  rfl

/-- The full compared diagram determines both actual primary data of an internal prefix state. -/
theorem PrefixLift.comparedDiagram_injective {B : LowerSet P} {S R : PrefixLift chi A T B}
    (h : S.comparedDiagram chi A T = R.comparedDiagram chi A T) : S = R := by
  have hD : S.diagram = R.diagram := congrArg
    (fun F => F ⋙ Comma.fst (originalBaseChange chi A) T.diagram) h
  cases S with | mk D eta hCell =>
    cases R with | mk E theta hCell' =>
      dsimp only at hD
      cases hD
      have hCompare : eta = theta := by
        apply Iso.ext
        apply NatTrans.ext
        funext a
        have hObj := Functor.congr_obj h a
        have hHom : HEq (eta.hom.app a) (theta.hom.app a) := by
          injection hObj with _ _ hValue
          exact heq_of_eq hValue
        exact eq_of_heq hHom
      cases hCompare
      rfl

/-- The genuine internally built states form the actual inverse restriction system. -/
def prefixLiftRestrictionFunctor : (LowerSet P)ᵒᵖ ⥤ Type (max w u v) where
  obj B := PrefixLift chi A T B.unop
  map f := ↾fun S => S.restrict chi A T (leOfHom f.unop)
  map_id B := by
    ext S
    exact PrefixLift.restrict_id chi A T S
  map_comp f g := by
    ext S
    exact (PrefixLift.restrict_comp chi A T S (leOfHom f.unop) (leOfHom g.unop)).symm

end InternalPrefixLifts

section NormalizedBirthTrees

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))
  (B : LowerSet P) (S : PrefixLift chi A T B) (i : A.index)
  (hi : ∀ a, (S.diagram.obj a).left ≤ i)

/-- The actual transition from each selected birth root to the common compact root. -/
abbrev birthRootTransition (a : B) :
    A.presentation.diag.obj (S.diagram.obj a).left ⟶ A.presentation.diag.obj i :=
  A.presentation.diag.map (homOfLE (hi a))

/-- The whole original predecessor diagram is compared by native successive root change. -/
abbrev birthRaiseIso (a : B) :
    birthPredecessorDiagram chi A B S.diagram a ⋙ Under.pushout
      (birthRootTransition chi A T B S i hi a) ≅
    raisedDiagram chi A (birthPastDiagram chi A B S.diagram a) i
      (fun b => hi ((birthPastInclusion B a).obj b)) :=
  raiseCompositionIso chi A i (birthPastDiagram chi A B S.diagram a)
    (fun b => hi ((birthPastInclusion B a).obj b)) (S.diagram.obj a).left
    (birthPastRootBound chi A B S.diagram a) (hi a)

/-- The comparison keeps both genuine birth and final coefficient inclusions. -/
@[reassoc]
theorem birthRaiseIso_inl (a : B) (b : LowerSet.Iio a.1) :
    pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
      (A.presentation.diag.map (homOfLE (birthPastRootBound chi A B S.diagram a b))) ≫
    pushout.inl ((birthPredecessorDiagram chi A B S.diagram a).obj b).hom
      (birthRootTransition chi A T B S i hi a) ≫
    ((birthRaiseIso chi A T B S i hi a).hom.app b).right =
      pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
        (A.presentation.diag.map (homOfLE (hi ((birthPastInclusion B a).obj b)))) :=
  raiseCompositionIso_inl_flat chi A i (birthPastDiagram chi A B S.diagram a)
    (fun b => hi ((birthPastInclusion B a).obj b)) (S.diagram.obj a).left
    (birthPastRootBound chi A B S.diagram a) (hi a) b

/-- The actual original predecessor-to-vertex leg is retained across the common receiving root. -/
theorem birthRaiseIso_leg (a : B) (b : LowerSet.Iio a.1) :
    (birthRaiseIso chi A T B S i hi a).hom.app b ≫
      (raisedDiagram chi A S.diagram i hi).map (birthPastArrow B a b) =
    (Under.pushout (birthRootTransition chi A T B S i hi a)).map
      (birthPredecessorLeg chi A B S.diagram a b) := by
  let f := (birthRaiseIso chi A T B S i hi a).hom.app b ≫
    (raisedDiagram chi A S.diagram i hi).map (birthPastArrow B a b)
  let g := (Under.pushout (birthRootTransition chi A T B S i hi a)).map
    (birthPredecessorLeg chi A B S.diagram a b)
  have hRoot := (Under.w f).trans (Under.w g).symm
  apply Under.UnderMorphism.ext
  change f.right = g.right
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · change _ ≫ _ ≫ f.right = _ ≫ _ ≫ g.right
      let a₀ := pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
        (A.presentation.diag.map (homOfLE (birthPastRootBound chi A B S.diagram a b)))
      let a₁ := pushout.inl ((birthPredecessorDiagram chi A B S.diagram a).obj b).hom
        (birthRootTransition chi A T B S i hi a)
      let c := ((birthRaiseIso chi A T B S i hi a).hom.app b).right
      let v := ((raisedDiagram chi A S.diagram i hi).map (birthPastArrow B a b)).right
      let l := (birthPredecessorLeg chi A B S.diagram a b).right
      let a' := pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
        (A.presentation.diag.map (homOfLE (hi ((birthPastInclusion B a).obj b))))
      let b' := pushout.inl (S.diagram.obj a).hom (birthRootTransition chi A T B S i hi a)
      have h₁ : a₀ ≫ a₁ ≫ c = a' := birthRaiseIso_inl chi A T B S i hi a b
      have h₂ : a' ≫ v = (S.diagram.map (birthPastArrow B a b)).right ≫ b' :=
        raisedDiagram_inl chi A S.diagram i hi (birthPastArrow B a b)
      have h₃ : a₁ ≫ g.right = l ≫ b' :=
        inl_map (birthRootTransition chi A T B S i hi a)
          (birthPredecessorLeg chi A B S.diagram a b)
      have h₄ : a₀ ≫ l = (S.diagram.map (birthPastArrow B a b)).right :=
        birthPredecessorLeg_inl chi A B S.diagram a b
      have hLeft : a₀ ≫ a₁ ≫ f.right = (S.diagram.map (birthPastArrow B a b)).right ≫ b' := by
        change a₀ ≫ a₁ ≫ (c ≫ v) = _
        calc
          _ = (a₀ ≫ a₁ ≫ c) ≫ v :=
            ((Category.assoc a₀ (a₁ ≫ c) v).trans
              (congrArg (fun p => a₀ ≫ p) (Category.assoc a₁ c v))).symm
          _ = a' ≫ v := congrArg (fun p => p ≫ v) h₁
          _ = _ := h₂
      have hRight : a₀ ≫ a₁ ≫ g.right = (S.diagram.map (birthPastArrow B a b)).right ≫ b' :=
        (congrArg (fun p => a₀ ≫ p) h₃).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ b') h₄))
      exact hLeft.trans hRight.symm
    · have e : ((birthPredecessorDiagram chi A B S.diagram a).obj b).hom ≫
          pushout.inl ((birthPredecessorDiagram chi A B S.diagram a).obj b).hom
            (birthRootTransition chi A T B S i hi a) =
        birthRootTransition chi A T B S i hi a ≫
          pushout.inr ((birthPredecessorDiagram chi A B S.diagram a).obj b).hom
            (birthRootTransition chi A T B S i hi a) := pushout.condition
      have h₁ := congrArg (fun p => p ≫ f.right) e
      have h₂ := congrArg (fun p => p ≫ g.right) e
      exact (Category.assoc _ _ _).symm.trans
        (h₁.trans ((Category.assoc _ _ _).trans
          ((congrArg (fun p => birthRootTransition chi A T B S i hi a ≫ p) hRoot).trans
            ((Category.assoc _ _ _).symm.trans
              (h₂.symm.trans (Category.assoc _ _ _))))))
  · exact hRoot

/-- The genuine inverse comparison retains every actual original predecessor leg. -/
@[reassoc]
theorem birthRaiseIso_inv_leg (a : B) (b : LowerSet.Iio a.1) :
    (birthRaiseIso chi A T B S i hi a).inv.app b ≫
      (Under.pushout (birthRootTransition chi A T B S i hi a)).map
        (birthPredecessorLeg chi A B S.diagram a b) =
      (raisedDiagram chi A S.diagram i hi).map (birthPastArrow B a b) := by
  have h := birthRaiseIso_leg chi A T B S i hi a b
  have h' := congrArg (fun m :
    (birthPredecessorDiagram chi A B S.diagram a ⋙
      Under.pushout (birthRootTransition chi A T B S i hi a)).obj b ⟶
        (raisedDiagram chi A S.diagram i hi).obj a =>
      (birthRaiseIso chi A T B S i hi a).inv.app b ≫ m) h.symm
  exact h'.trans (((birthRaiseIso chi A T B S i hi a).app b).inv_hom_id_assoc _)

/-- The actual birth predecessor cocone is transported by the native left adjoint and comparison. -/
abbrev normalizedBirthPredecessor (a : B) :
    ColimitCocone (raisedDiagram chi A (birthPastDiagram chi A B S.diagram a) i
      (fun b => hi ((birthPastInclusion B a).obj b))) where
  cocone := (Cocone.precompose (birthRaiseIso chi A T B S i hi a).inv).obj
    ((Under.pushout (birthRootTransition chi A T B S i hi a)).mapCocone
      (birthPredecessor chi A B S.diagram a).cocone)
  isColimit := (IsColimit.precomposeInvEquiv (birthRaiseIso chi A T B S i hi a) _).symm
    (isColimitOfPreserves (Under.pushout (birthRootTransition chi A T B S i hi a))
      (birthPredecessor chi A B S.diagram a).isColimit)

/-- The strict original predecessor-label equivalence supplies the full normalized predecessor. -/
abbrev normalizedPredecessor (a : B) :
    ColimitCocone (restriction (raisedDiagram chi A S.diagram i hi) (LowerSet.Iio a)) where
  cocone := (normalizedBirthPredecessor chi A T B S i hi a).cocone.whisker
    (CellTreeLowerRestriction.predecessorOrderIso B a).equivalence.functor
  isColimit := (normalizedBirthPredecessor chi A T B S i hi a).isColimit.whiskerEquivalence
    (CellTreeLowerRestriction.predecessorOrderIso B a).equivalence

/-- All normalized predecessor maps are the native images of the actual birth descenders. -/
theorem normalizedPredecessorMap (a : B) :
    cellTreePredecessorMap (raisedDiagram chi A S.diagram i hi) a
      (normalizedPredecessor chi A T B S i hi a) =
      (Under.pushout (birthRootTransition chi A T B S i hi a)).map
        (birthPredecessorMap chi A B S.diagram a) := by
  apply (normalizedPredecessor chi A T B S i hi a).isColimit.hom_ext
  intro b
  let b' := (CellTreeLowerRestriction.predecessorOrderIso B a) b
  let F := Under.pushout (birthRootTransition chi A T B S i hi a)
  let rho := (birthRaiseIso chi A T B S i hi a).inv.app b'
  have hFactor : (normalizedPredecessor chi A T B S i hi a).cocone.ι.app b ≫
      F.map (birthPredecessorMap chi A B S.diagram a) =
      (raisedDiagram chi A S.diagram i hi).map (homOfLE b.2.le) := by
    have hStart : (normalizedPredecessor chi A T B S i hi a).cocone.ι.app b ≫
        F.map (birthPredecessorMap chi A B S.diagram a) =
        (rho ≫ F.map ((birthPredecessor chi A B S.diagram a).cocone.ι.app b')) ≫
          F.map (birthPredecessorMap chi A B S.diagram a) := rfl
    have hMiddle := (Category.assoc rho
      (F.map ((birthPredecessor chi A B S.diagram a).cocone.ι.app b'))
      (F.map (birthPredecessorMap chi A B S.diagram a))).trans
        (congrArg (fun m => rho ≫ m)
          (F.map_comp ((birthPredecessor chi A B S.diagram a).cocone.ι.app b')
            (birthPredecessorMap chi A B S.diagram a)).symm)
    have hBirth := congrArg (fun m => rho ≫ F.map m)
      (birthPredecessorMap_fac chi A B S.diagram a b')
    have hEnd : rho ≫ F.map (birthPredecessorLeg chi A B S.diagram a b') =
        (raisedDiagram chi A S.diagram i hi).map (homOfLE b.2.le) :=
      birthRaiseIso_inv_leg chi A T B S i hi a b'
    exact hStart.trans (hMiddle.trans (hBirth.trans hEnd))
  exact (cellTreePredecessorMap_fac (raisedDiagram chi A S.diagram i hi) a
    (normalizedPredecessor chi A T B S i hi a) b).trans hFactor.symm

/-- Select the actual birth attaching function and transport it by the genuine root pushout leg. -/
abbrev normalizedAttaching (a : B) :
    (s (T.label a.1)).left ⟶ (normalizedPredecessor chi A T B S i hi a).cocone.pt.right :=
  (S.cell a).choose ≫ pushout.inl (birthPredecessor chi A B S.diagram a).cocone.pt.hom
    (birthRootTransition chi A T B S i hi a)

/-- The same original generator target enters its actual normalized vertex. -/
abbrev normalizedCell (a : B) :
    (s (T.label a.1)).right ⟶ ((raisedDiagram chi A S.diagram i hi).obj a).right :=
  (S.cell a).choose_spec.choose ≫ pushout.inl (S.diagram.obj a).hom
    (birthRootTransition chi A T B S i hi a)

/-- Normalize an internally constructed prefix to a genuine compact root, keeping its old order. -/
def normalizedTree : CellTree s (A.presentation.diag.obj i) (P := B) where
  wellFounded := InvImage.wf (fun a : B => a.1) T.wellFounded
  diagram := raisedDiagram chi A S.diagram i hi
  label a := T.label a.1
  predecessor a := normalizedPredecessor chi A T B S i hi a
  attaching a := normalizedAttaching chi A T B S i hi a
  cell a := normalizedCell chi A T B S i hi a
  isPushout a := by
    rw [normalizedPredecessorMap]
    exact (((S.cell a).choose_spec.choose_spec.1).flip.paste_vert
      (map_isPushout (birthRootTransition chi A T B S i hi a)
        (birthPredecessorMap chi A B S.diagram a))).flip
  endpoint :=
    { cocone := colimit.cocone (raisedDiagram chi A S.diagram i hi)
      isColimit := colimit.isColimit (raisedDiagram chi A S.diagram i hi) }

/-- The full normalized comparison returns the original prefix's actual whole diagram. -/
def normalizedOriginalIso :
    (normalizedTree chi A T B S i hi).diagram ⋙ Under.pushout (A.presentation.ι.app i) ≅
      restriction T.diagram B :=
  raisedOriginalIso chi A S.diagram i hi ≪≫ S.comparison

/-- The actual generator-label function is unchanged on every literal original prefix label. -/
theorem normalizedTree_label_function :
    (normalizedTree chi A T B S i hi).label = (fun a : B => T.label a.1) := rfl

end NormalizedBirthTrees

section OriginalWellOrderPrefixes

variable {P : Type w} [PartialOrder P] [WellFoundedLT P]

/-- The native extension of the actual old well-founded order is genuinely well founded. -/
theorem labelExtensionWellFounded : WellFoundedLT (WellOrderExtension P) :=
  WellFounded.wellOrderExtension.wellFounded_lt (r := ((· < ·) : P → P → Prop))

attribute [local instance] labelExtensionWellFounded

/-- The internal well-ordered stage carrier adds genuine first and last stages to the old labels. -/
abbrev ConstructionIndex (P : Type w) := WithBot (WithTop (WellOrderExtension P))

/-- The entire internally chosen stage order retains its true well-founded recursion dictionary. -/
theorem constructionIndexWellFounded : WellFoundedLT (ConstructionIndex P) := inferInstance

attribute [local instance] constructionIndexWellFounded

/-- The actual well-founded linear stage order supplies its genuine native successor operation. -/
@[instance_reducible]
noncomputable def constructionIndexSuccOrder : SuccOrder (ConstructionIndex P) :=
  SuccOrder.ofLinearWellFoundedLT (ConstructionIndex P)

attribute [local instance] constructionIndexSuccOrder

/-- The actual old label is retained through the native well-order extension and both stage maps. -/
def constructionLabel (a : P) : ConstructionIndex P :=
  WithBot.some (WithTop.some ((toWellOrderExtension : P ≃ WellOrderExtension P) a))

/-- The original partial order is preserved by its internally chosen stage enumeration. -/
theorem constructionLabel_strictMono : StrictMono (constructionLabel (P := P)) :=
  WithBot.coe_strictMono.comp (WithTop.coe_strictMono.comp toWellOrderExtension_strictMono)

omit [PartialOrder P] [WellFoundedLT P] in
/-- The literal old label is retained injectively even when its original order is partial. -/
theorem constructionLabel_injective : Function.Injective (constructionLabel (P := P)) :=
  WithBot.coe_injective.comp (WithTop.coe_injective.comp
    (toWellOrderExtension : P ≃ WellOrderExtension P).injective)

/-- Every stage retains a literal downward-closed subset of the original old label order. -/
def originalPrefix (gamma : ConstructionIndex P) : LowerSet P where
  carrier := {a | constructionLabel a < gamma}
  lower' := fun _ _ hab hb =>
    lt_of_le_of_lt (constructionLabel_strictMono.monotone hab) hb

/-- The whole internal prefix-membership function keeps each actual original label. -/
theorem originalPrefix_membership (gamma : ConstructionIndex P) :
    (fun a : P => a ∈ originalPrefix gamma) =
      (fun a : P => constructionLabel a < gamma) := rfl

/-- Every actual later stage contains the same original earlier labels. -/
theorem originalPrefix_mono : Monotone (originalPrefix (P := P)) := by
  intro gamma delta h a ha
  exact lt_of_lt_of_le ha h

/-- The first genuine stage has no old labels. -/
theorem originalPrefix_bot : originalPrefix (⊥ : ConstructionIndex P) = ⊥ := by
  ext a
  change constructionLabel a < (⊥ : ConstructionIndex P) ↔ False
  simp only [not_lt_bot]

/-- The final genuine stage retains every old label. -/
theorem originalPrefix_top : originalPrefix (⊤ : ConstructionIndex P) = ⊤ := by
  ext a
  change constructionLabel a < (⊤ : ConstructionIndex P) ↔ True
  apply iff_true_intro
  exact WithBot.coe_lt_coe.mpr
    (WithTop.coe_lt_top ((toWellOrderExtension : P ≃ WellOrderExtension P) a))

/-- Every actual old label is strictly before the genuine final stage. -/
theorem constructionLabel_lt_top (a : P) :
    constructionLabel a < (⊤ : ConstructionIndex P) :=
  WithBot.coe_lt_coe.mpr
    (WithTop.coe_lt_top ((toWellOrderExtension : P ≃ WellOrderExtension P) a))

/-- A genuine old-label stage always has a strict successor. -/
theorem constructionLabel_not_isMax (a : P) : ¬IsMax (constructionLabel a) :=
  not_isMax_of_lt (constructionLabel_lt_top a)

/-- All literal original predecessors are already built at the label's birth stage. -/
theorem predecessor_le_originalPrefix (a : P) :
    LowerSet.Iio a ≤ originalPrefix (constructionLabel a) := by
  intro b hb
  exact constructionLabel_strictMono hb

/-- The original birth label itself is absent from its preceding actual prefix. -/
theorem notMem_originalPrefix_label (a : P) :
    a ∉ originalPrefix (constructionLabel a) := by
  change ¬constructionLabel a < constructionLabel a
  exact lt_irrefl _

/-- A successor step adds the actual original cell and all its already-built predecessors. -/
theorem originalPrefix_succ_label (a : P) :
    originalPrefix (Order.succ (constructionLabel a)) =
      originalPrefix (constructionLabel a) ⊔ LowerSet.Iic a := by
  ext b
  change b ∈ originalPrefix (Order.succ (constructionLabel a)) ↔
    b ∈ originalPrefix (constructionLabel a) ⊔ LowerSet.Iic a
  rw [LowerSet.mem_sup_iff]
  change constructionLabel b < Order.succ (constructionLabel a) ↔
    constructionLabel b < constructionLabel a ∨ b ≤ a
  rw [Order.lt_succ_iff_of_not_isMax (constructionLabel_not_isMax a)]
  constructor
  · intro h
    obtain hlt | he := h.lt_or_eq
    · exact Or.inl hlt
    · exact Or.inr (constructionLabel_injective he).le
  · rintro (hlt | hle)
    · exact hlt.le
    · exact constructionLabel_strictMono.monotone hle

/-- The extra initial successor stage still has no old generator label. -/
theorem originalPrefix_succ_bot :
    originalPrefix (Order.succ (⊥ : ConstructionIndex P)) = ⊥ := by
  ext a
  change constructionLabel a < Order.succ (⊥ : ConstructionIndex P) ↔ False
  apply iff_false_intro
  intro h
  have hBot : ¬IsMax (⊥ : ConstructionIndex P) :=
    not_isMax_of_lt (WithBot.bot_lt_coe (⊤ : WithTop (WellOrderExtension P)))
  have hle := (Order.lt_succ_iff_of_not_isMax hBot).mp h
  exact (WithBot.bot_lt_coe
    (WithTop.some ((toWellOrderExtension : P ≃ WellOrderExtension P) a))).not_ge hle

/-- At an actual limit stage each old label belongs to a genuine strictly earlier prefix. -/
theorem originalPrefix_limit_membership (gamma : ConstructionIndex P)
    (hgamma : Order.IsSuccLimit gamma) (a : P) :
    a ∈ originalPrefix gamma ↔
      ∃ delta : Set.Iio gamma, a ∈ originalPrefix delta.1 := by
  constructor
  · intro ha
    refine ⟨⟨Order.succ (constructionLabel a), hgamma.succ_lt ha⟩, ?_⟩
    exact Order.lt_succ_of_not_isMax (constructionLabel_not_isMax a)
  · rintro ⟨delta, ha⟩
    exact lt_trans (show constructionLabel a < delta.1 from ha)
      (show delta.1 < gamma from delta.2)

variable (chi : Cardinal.{w}) [Fact chi.IsRegular]

omit [Fact chi.IsRegular] in
/-- The actual ordinal enumerating the original well-order has length below the chosen cardinal. -/
theorem originalLabelOrdinal_lt (hP : HasCardinalLT P chi) :
    Ordinal.type ((· < ·) : WellOrderExtension P → WellOrderExtension P → Prop) < chi.ord := by
  apply Cardinal.lt_ord.mpr
  simpa only [Ordinal.card_type, WellOrderExtension] using
    (hasCardinalLT_iff_cardinal_mk_lt P chi).mp hP

omit [PartialOrder P] [WellFoundedLT P] in
/-- The actual small original labels bound the entire stage carrier, including both end stages. -/
theorem constructionIndex_bound (hP : HasCardinalLT P chi) :
    HasCardinalLT (ConstructionIndex P) chi := by
  have h := (hasCardinalLT_option_iff P chi (Fact.out : chi.IsRegular).aleph0_le).2 hP
  have h' := (hasCardinalLT_option_iff (Option P) chi
    (Fact.out : chi.IsRegular).aleph0_le).2 h
  exact h'

/-- Every actual stage arrow is bounded; length alone is never used as an arrow bound. -/
theorem constructionIndex_arrow_bound (hP : HasCardinalLT P chi) :
    HasCardinalLT (Arrow (ConstructionIndex P)) chi :=
  (hasCardinalLT_arrow_iff_of_isThin (ConstructionIndex P) chi
    (Fact.out : chi.IsRegular).aleph0_le).2 (constructionIndex_bound chi hP)

end OriginalWellOrderPrefixes

section GenuineLimitPrefixDiagrams

variable {P : Type w} [PartialOrder P] [WellFoundedLT P]

attribute [local instance] labelExtensionWellFounded constructionIndexWellFounded
  constructionIndexSuccOrder

/-- The first genuine stage containing an actual old label is strictly below an actual limit. -/
def prefixStage (gamma : ConstructionIndex P) (hgamma : Order.IsSuccLimit gamma)
    (a : originalPrefix gamma) : Set.Iio gamma :=
  ⟨Order.succ (constructionLabel a.1), hgamma.succ_lt a.2⟩

/-- The original label at its own first containing stage remains literal. -/
abbrev prefixStageObject (gamma : ConstructionIndex P) (hgamma : Order.IsSuccLimit gamma)
    (a : originalPrefix gamma) : originalPrefix (prefixStage gamma hgamma a).1 :=
  ⟨a.1, Order.lt_succ_of_not_isMax (constructionLabel_not_isMax a.1)⟩

/-- Every original lower label already belongs to the later label's first containing stage. -/
theorem prefixStage_contains_le (gamma : ConstructionIndex P)
    (hgamma : Order.IsSuccLimit gamma) {a b : originalPrefix gamma} (hab : a ≤ b) :
    a.1 ∈ originalPrefix (prefixStage gamma hgamma b).1 :=
  lt_of_le_of_lt (constructionLabel_strictMono.monotone (show a.1 ≤ b.1 from hab))
    (Order.lt_succ_of_not_isMax (constructionLabel_not_isMax b.1))

variable {K : Type uJ} [Category.{vJ} K]
  (gamma : ConstructionIndex P) (hgamma : Order.IsSuccLimit gamma)
  (D : ∀ delta : Set.Iio gamma, originalPrefix delta.1 ⥤ K)
  (hD : ∀ (delta epsilon : Set.Iio gamma) (h : delta ≤ epsilon),
    lowerInclusion (originalPrefix_mono (show delta.1 ≤ epsilon.1 from h)) ⋙ D epsilon = D delta)

/-- Each limit object comes from the first actual prefix containing its same original label. -/
abbrev limitPrefixObject (a : originalPrefix gamma) : K :=
  (D (prefixStage gamma hgamma a)).obj (prefixStageObject gamma hgamma a)

include hD in
/-- Compatible actual restriction maps identify that object with every later containing prefix. -/
theorem limitPrefixObject_eq_at (delta : Set.Iio gamma) (a : originalPrefix gamma)
    (ha : a.1 ∈ originalPrefix delta.1) :
    limitPrefixObject gamma hgamma D a = (D delta).obj ⟨a.1, ha⟩ := by
  have hStage : prefixStage gamma hgamma a ≤ delta :=
    Order.succ_le_of_lt (show constructionLabel a.1 < delta.1 from ha)
  exact (Functor.congr_obj (hD (prefixStage gamma hgamma a) delta hStage)
    (prefixStageObject gamma hgamma a)).symm

/-- The whole limit arrow uses the actual earlier object equality and original later-prefix map. -/
abbrev limitPrefixMap {a b : originalPrefix gamma} (f : a ⟶ b) :
    limitPrefixObject gamma hgamma D a ⟶ limitPrefixObject gamma hgamma D b :=
  eqToHom (limitPrefixObject_eq_at gamma hgamma D hD (prefixStage gamma hgamma b) a
    (prefixStage_contains_le gamma hgamma (leOfHom f))) ≫
      (D (prefixStage gamma hgamma b)).map
        (homOfLE (leOfHom f) :
          (⟨a.1, prefixStage_contains_le gamma hgamma (leOfHom f)⟩ :
            originalPrefix (prefixStage gamma hgamma b).1) ⟶ prefixStageObject gamma hgamma b)

include hD hgamma in
/-- Every complete limit Hom value is the same actual map in any prefix containing its target. -/
theorem limitPrefixMap_heq_at {a b : originalPrefix gamma} (f : a ⟶ b)
    (delta : Set.Iio gamma) (hb : b.1 ∈ originalPrefix delta.1) :
    limitPrefixMap gamma hgamma D hD f ≍
      (D delta).map (homOfLE (leOfHom f) :
        (⟨a.1, (originalPrefix delta.1).lower (leOfHom f) hb⟩ : originalPrefix delta.1) ⟶
          ⟨b.1, hb⟩) := by
  let g : (⟨a.1, prefixStage_contains_le gamma hgamma (leOfHom f)⟩ :
      originalPrefix (prefixStage gamma hgamma b).1) ⟶ prefixStageObject gamma hgamma b :=
    homOfLE (leOfHom f)
  have hStage : prefixStage gamma hgamma b ≤ delta :=
    Order.succ_le_of_lt (show constructionLabel b.1 < delta.1 from hb)
  have hMap := Functor.hcongr_hom (hD (prefixStage gamma hgamma b) delta hStage).symm g
  exact (eqToHom_comp_heq ((D (prefixStage gamma hgamma b)).map g)
    (limitPrefixObject_eq_at gamma hgamma D hD (prefixStage gamma hgamma b) a
      (prefixStage_contains_le gamma hgamma (leOfHom f)))).trans hMap

/-- Construct the whole limit functor from real compatible original prefix functions. -/
def limitPrefixDiagram : originalPrefix gamma ⥤ K where
  obj a := limitPrefixObject gamma hgamma D a
  map f := limitPrefixMap gamma hgamma D hD f
  map_id a := by
    have h := limitPrefixMap_heq_at gamma hgamma D hD (𝟙 a)
      (prefixStage gamma hgamma a) (prefixStageObject gamma hgamma a).2
    exact eq_of_heq (h.trans
      (heq_of_eq ((D (prefixStage gamma hgamma a)).map_id (prefixStageObject gamma hgamma a))))
  map_comp {a b c} f g := by
    let delta := prefixStage gamma hgamma c
    have ha : a.1 ∈ originalPrefix delta.1 :=
      prefixStage_contains_le gamma hgamma ((leOfHom f).trans (leOfHom g))
    have hb : b.1 ∈ originalPrefix delta.1 := prefixStage_contains_le gamma hgamma (leOfHom g)
    have hc : c.1 ∈ originalPrefix delta.1 := (prefixStageObject gamma hgamma c).2
    let f' : (⟨a.1, ha⟩ : originalPrefix delta.1) ⟶ ⟨b.1, hb⟩ := homOfLE (leOfHom f)
    let g' : (⟨b.1, hb⟩ : originalPrefix delta.1) ⟶ ⟨c.1, hc⟩ := homOfLE (leOfHom g)
    have hComp := heq_comp
      (limitPrefixObject_eq_at gamma hgamma D hD delta a ha)
      (limitPrefixObject_eq_at gamma hgamma D hD delta b hb)
      (limitPrefixObject_eq_at gamma hgamma D hD delta c hc)
      (limitPrefixMap_heq_at gamma hgamma D hD f delta hb)
      (limitPrefixMap_heq_at gamma hgamma D hD g delta hc)
    have hMap : limitPrefixMap gamma hgamma D hD (f ≫ g) ≍ (D delta).map (f' ≫ g') :=
      limitPrefixMap_heq_at gamma hgamma D hD (f ≫ g) delta hc
    exact eq_of_heq ((hMap.trans (heq_of_eq ((D delta).map_comp f' g'))).trans hComp.symm)

include hD hgamma in
/-- The entire glued limit diagram restricts to the same given original earlier-prefix functor. -/
theorem limitPrefixDiagram_restrict (delta : Set.Iio gamma) :
    lowerInclusion (originalPrefix_mono delta.2.le) ⋙ limitPrefixDiagram gamma hgamma D hD =
      D delta := by
  apply Functor.hext
  · intro a
    exact limitPrefixObject_eq_at gamma hgamma D hD delta
      ⟨a.1, memOfLE (originalPrefix_mono delta.2.le) a.2⟩ a.2
  · intro a b f
    exact limitPrefixMap_heq_at gamma hgamma D hD
      ((lowerInclusion (originalPrefix_mono delta.2.le)).map f) delta b.2

end GenuineLimitPrefixDiagrams

section ActualLimitPrefixStates

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P] [WellFoundedLT P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))

attribute [local instance] labelExtensionWellFounded constructionIndexWellFounded
  constructionIndexSuccOrder

/-- The internally chosen stage order indexes the actual inverse system of complete prefix data. -/
abbrev originalPrefixLiftFunctor : (ConstructionIndex P)ᵒᵖ ⥤ Type (max w u v) :=
  originalPrefix_mono.functor.op ⋙ prefixLiftRestrictionFunctor chi A T

variable (gamma : ConstructionIndex P) (hgamma : Order.IsSuccLimit gamma)
  (x : ((OrderHom.Subtype.val (· ∈ Set.Iio gamma)).monotone.functor.op ⋙
    originalPrefixLiftFunctor chi A T).sections)

/-- The actual compatible earlier states retain exact original restriction equalities. -/
theorem limitFamily_restrict (delta epsilon : Set.Iio gamma) (h : delta ≤ epsilon) :
    (x.val (Opposite.op epsilon)).restrict chi A T
      (originalPrefix_mono (show delta.1 ≤ epsilon.1 from h)) = x.val (Opposite.op delta) :=
  x.property (homOfLE h).op

/-- All whole earlier comparison diagrams are glued on literal original labels and arrows. -/
abbrev limitComparedDiagram : originalPrefix gamma ⥤ Comma (originalBaseChange chi A) T.diagram :=
  limitPrefixDiagram gamma hgamma
    (fun delta => (x.val (Opposite.op delta)).comparedDiagram chi A T)
    (fun delta epsilon h =>
      ((x.val (Opposite.op epsilon)).comparedDiagram_restrict chi A T
        (originalPrefix_mono (show delta.1 ≤ epsilon.1 from h))).symm.trans
        (congrArg (fun S => S.comparedDiagram chi A T)
          (limitFamily_restrict chi A T gamma x delta epsilon h)))

/-- The full original earlier compared functor is recovered by every actual limit restriction. -/
theorem limitComparedDiagram_restrict (delta : Set.Iio gamma) :
    lowerInclusion (originalPrefix_mono delta.2.le) ⋙ limitComparedDiagram chi A T gamma hgamma x =
      (x.val (Opposite.op delta)).comparedDiagram chi A T :=
  limitPrefixDiagram_restrict gamma hgamma _ _ delta

/-- The whole actual birth diagram at a limit is the native projection of its compared diagram. -/
abbrev limitBirthDiagram : originalPrefix gamma ⥤ Comma A.presentation.diag (𝟭 C) :=
  limitComparedDiagram chi A T gamma hgamma x ⋙
    Comma.fst (originalBaseChange chi A) T.diagram

/-- The full birth diagram retains the same earlier states, including all roots and maps. -/
theorem limitBirthDiagram_restrict (delta : Set.Iio gamma) :
    lowerInclusion (originalPrefix_mono delta.2.le) ⋙
      limitBirthDiagram chi A T gamma hgamma x =
      (x.val (Opposite.op delta)).diagram :=
  congrArg (fun F => F ⋙ Comma.fst (originalBaseChange chi A) T.diagram)
    (limitComparedDiagram_restrict chi A T gamma hgamma x delta)

/-- Each limit comparison keeps the actual earlier isomorphism on its same original label. -/
def limitOriginalIso :
    limitBirthDiagram chi A T gamma hgamma x ⋙ originalBaseChange chi A ≅
      restriction T.diagram (originalPrefix gamma) :=
  NatIso.ofComponents
    (fun a => (x.val (Opposite.op (prefixStage gamma hgamma a))).comparison.app
      (prefixStageObject gamma hgamma a)) (by
      intro a b f
      have h := ((limitComparedDiagram chi A T gamma hgamma x).map f).w
      have hArrow : ((limitComparedDiagram chi A T gamma hgamma x).map f).right =
          homOfLE (leOfHom f) := Subsingleton.elim _ _
      exact h.trans (congrArg (fun m =>
        ((limitComparedDiagram chi A T gamma hgamma x).obj a).hom ≫ T.diagram.map m) hArrow))

/-- The actual complete limit core retains its whole birth diagram and original comparison. -/
abbrev limitPrefixCore : PrefixCore chi A T (originalPrefix gamma) where
  diagram := limitBirthDiagram chi A T gamma hgamma x
  comparison := limitOriginalIso chi A T gamma hgamma x

/-- The entire limit core has the actual glued comparison functor on all original labels. -/
theorem limitPrefixCore_comparedDiagram :
    (limitPrefixCore chi A T gamma hgamma x).comparedDiagram chi A T =
      limitComparedDiagram chi A T gamma hgamma x := by
  apply Functor.hext
  · intro a
    rfl
  · intro a b f
    apply heq_of_eq
    apply Comma.hom_ext
    · rfl
    · exact Subsingleton.elim _ _

/-- Every entire earlier core is recovered by the actual limit restriction. -/
theorem limitPrefixCore_restrict (delta : Set.Iio gamma) :
    (limitPrefixCore chi A T gamma hgamma x).restrict chi A T
      (originalPrefix_mono delta.2.le) = (x.val (Opposite.op delta)).core chi A T := by
  apply PrefixCore.comparedDiagram_injective chi A T
  exact ((limitPrefixCore chi A T gamma hgamma x).comparedDiagram_restrict chi A T
    (originalPrefix_mono delta.2.le)).trans
      ((congrArg (fun D => lowerInclusion (originalPrefix_mono delta.2.le) ⋙ D)
        (limitPrefixCore_comparedDiagram chi A T gamma hgamma x)).trans
          (limitComparedDiagram_restrict chi A T gamma hgamma x delta))

/-- Construct the complete limit state, retaining each actual earlier original birth-cell square. -/
def limitPrefixLift : PrefixLift chi A T (originalPrefix gamma) where
  diagram := limitBirthDiagram chi A T gamma hgamma x
  comparison := limitOriginalIso chi A T gamma hgamma x
  cell a := by
    let delta := prefixStage gamma hgamma a
    let S := x.val (Opposite.op delta)
    let a' := prefixStageObject gamma hgamma a
    let hdelta := originalPrefix_mono delta.2.le
    let N := limitPrefixCore chi A T gamma hgamma x
    have hCell : (S.core chi A T).BirthCell chi A T a' := S.cell a'
    have hRestrict := limitPrefixCore_restrict chi A T gamma hgamma x delta
    have hBuilt : (N.restrict chi A T hdelta).BirthCell chi A T a' :=
      Eq.mpr (congrArg (fun R => R.BirthCell chi A T a') hRestrict) hCell
    exact (N.birthCell_restrict chi A T hdelta a').mp hBuilt

/-- The constructed limit state retains the entire glued comparison functor. -/
theorem limitPrefixLift_comparedDiagram :
    (limitPrefixLift chi A T gamma hgamma x).comparedDiagram chi A T =
      limitComparedDiagram chi A T gamma hgamma x := by
  apply Functor.hext
  · intro a
    rfl
  · intro a b f
    apply heq_of_eq
    apply Comma.hom_ext
    · rfl
    · exact Subsingleton.elim _ _

/-- Every full earlier state, including all comparison inverses and cell functions, is retained. -/
theorem limitPrefixLift_restrict (delta : Set.Iio gamma) :
    (limitPrefixLift chi A T gamma hgamma x).restrict chi A T
      (originalPrefix_mono delta.2.le) = x.val (Opposite.op delta) := by
  apply PrefixLift.comparedDiagram_injective chi A T
  exact ((limitPrefixLift chi A T gamma hgamma x).comparedDiagram_restrict chi A T
    (originalPrefix_mono delta.2.le)).trans
      ((congrArg (fun D => lowerInclusion (originalPrefix_mono delta.2.le) ⋙ D)
        (limitPrefixLift_comparedDiagram chi A T gamma hgamma x)).trans
          (limitComparedDiagram_restrict chi A T gamma hgamma x delta))

end ActualLimitPrefixStates

section ActualCommonPrefixRoots

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))
  {B : LowerSet P} (S : PrefixLift chi A T B) (hB : HasCardinalLT B chi)

/-- The genuine chi-filtered compact approximation supplies an actual root receiving every birth. -/
abbrev commonPrefixRootCocone : Cocone (S.diagram ⋙ Comma.fst A.presentation.diag (𝟭 C)) :=
  IsCardinalFiltered.cocone (κ := chi) (S.diagram ⋙ Comma.fst A.presentation.diag (𝟭 C))
    ((hasCardinalLT_arrow_iff_of_isThin B chi (Fact.out : chi.IsRegular).aleph0_le).2 hB)

/-- The selected root is the point of the actual entire root-diagram cone. -/
abbrev commonPrefixRoot : A.index := (commonPrefixRootCocone chi A T S hB).pt

/-- Every actual original birth root has its genuine transition to that selected common root. -/
theorem commonPrefixRoot_bound (a : B) :
    (S.diagram.obj a).left ≤ commonPrefixRoot chi A T S hB :=
  leOfHom ((commonPrefixRootCocone chi A T S hB).ι.app a)

/-- Every actual old root-transition arrow commutes with its real receiving-root cone. -/
theorem commonPrefixRoot_naturality {a b : B} (f : a ⟶ b) :
    (S.diagram.map f).left ≫ (commonPrefixRootCocone chi A T S hB).ι.app b =
      (commonPrefixRootCocone chi A T S hB).ι.app a :=
  (commonPrefixRootCocone chi A T S hB).w f

end ActualCommonPrefixRoots

section ActualSuccessorPredecessors

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))
  (B : LowerSet P) (S : PrefixLift chi A T B) (a : P) (hPast : LowerSet.Iio a ≤ B)
  (i : A.index) (hi : ∀ b, (S.diagram.obj b).left ≤ i)

/-- The genuine old predecessors of the next original label enter the already constructed prefix. -/
abbrev nextPastInclusion : LowerSet.Iio a ⥤ B where
  obj b := ⟨b.1, memOfLE hPast b.2⟩
  map f := homOfLE (leOfHom f)

/-- The entire next predecessor birth diagram retains those same old objects and arrows. -/
abbrev nextPastDiagram : LowerSet.Iio a ⥤ Comma A.presentation.diag (𝟭 C) :=
  nextPastInclusion B a hPast ⋙ S.diagram

/-- The actual next predecessor diagram is pushed to the selected common compact root. -/
abbrev nextPastAtRoot : LowerSet.Iio a ⥤ Under (A.presentation.diag.obj i) :=
  raisedDiagram chi A (nextPastDiagram chi A T B S a hPast) i
    (fun b => hi ((nextPastInclusion B a hPast).obj b))

/-- Its entire predecessor cocone is the actual available working-size colimit. -/
abbrev nextPastColimit : ColimitCocone (nextPastAtRoot chi A T B S a hPast i hi) where
  cocone := (workingUnderColimit (nextPastAtRoot chi A T B S a hPast i hi)).cocone
  isColimit := (workingUnderColimit (nextPastAtRoot chi A T B S a hPast i hi)).isColimit

/-- The original preceding vertex diagram is recovered with its actual whole comparison. -/
def nextPastOriginalIso :
    nextPastAtRoot chi A T B S a hPast i hi ⋙ Under.pushout (A.presentation.ι.app i) ≅
      restriction T.diagram (LowerSet.Iio a) :=
  originalPastIso chi A (nextPastDiagram chi A T B S a hPast)
    (restriction T.diagram (LowerSet.Iio a))
    (Functor.isoWhiskerLeft (nextPastInclusion B a hPast) S.comparison) i
    (fun b => hi ((nextPastInclusion B a hPast).obj b))

/-- Both true predecessor colimits identify the actual common-root predecessor after base change. -/
def nextPastOriginalComparison :
    (Under.pushout (A.presentation.ι.app i)).obj
      (nextPastColimit chi A T B S a hPast i hi).cocone.pt ≅ T.predecessorObj a :=
  originalPastComparison chi A (nextPastDiagram chi A T B S a hPast)
    (restriction T.diagram (LowerSet.Iio a))
    (Functor.isoWhiskerLeft (nextPastInclusion B a hPast) S.comparison) (T.predecessor a) i
    (fun b => hi ((nextPastInclusion B a hPast).obj b))

/-- Every original strict predecessor retains its actual mapped colimit leg and comparison. -/
@[reassoc]
theorem nextPastOriginalComparison_leg (b : LowerSet.Iio a) :
    (Under.pushout (A.presentation.ι.app i)).map
      ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b) ≫
    (nextPastOriginalComparison chi A T B S a hPast i hi).hom =
      (nextPastOriginalIso chi A T B S a hPast i hi).hom.app b ≫
        (T.predecessor a).cocone.ι.app b := by
  exact (isColimitOfPreserves (Under.pushout (A.presentation.ι.app i))
    (nextPastColimit chi A T B S a hPast i hi).isColimit).comp_coconePointsIsoOfNatIso_hom
      (T.predecessor a).isColimit (nextPastOriginalIso chi A T B S a hPast i hi) b

/-- The actual original predecessor coefficient map under the common compact approximation root. -/
abbrev nextPastOriginalMap :
    (nextPastColimit chi A T B S a hPast i hi).cocone.pt ⟶
      (Under.map (A.presentation.ι.app i)).obj (T.predecessorObj a) :=
  originalPastMap chi A (nextPastDiagram chi A T B S a hPast)
    (restriction T.diagram (LowerSet.Iio a))
    (Functor.isoWhiskerLeft (nextPastInclusion B a hPast) S.comparison) (T.predecessor a) i
    (fun b => hi ((nextPastInclusion B a hPast).obj b))

/-- The complete common-root coefficient map retains the actual original pushout inclusion. -/
theorem nextPastOriginalMap_right :
    (nextPastOriginalMap chi A T B S a hPast i hi).right =
      pushout.inl (nextPastColimit chi A T B S a hPast i hi).cocone.pt.hom
        (A.presentation.ι.app i) ≫
      (nextPastOriginalComparison chi A T B S a hPast i hi).hom.right :=
  nativePushoutHomEquiv_right (A.presentation.ι.app i) _ _ _

/-- The original native Hom bijection and complete UP retain each actual predecessor leg. -/
@[reassoc]
theorem nextPastOriginalMap_leg (b : LowerSet.Iio a) :
    ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫
      (nextPastOriginalMap chi A T B S a hPast i hi).right =
    pushout.inl ((nextPastAtRoot chi A T B S a hPast i hi).obj b).hom
      (A.presentation.ι.app i) ≫
    ((nextPastOriginalIso chi A T B S a hPast i hi).hom.app b).right ≫
      ((T.predecessor a).cocone.ι.app b).right := by
  let adj := Under.mapPushoutAdj (A.presentation.ι.app i)
  have h := (adj.homEquiv_naturality_left
    ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b)
    (nextPastOriginalComparison chi A T B S a hPast i hi).hom).symm.trans
      (congrArg (adj.homEquiv ((nextPastAtRoot chi A T B S a hPast i hi).obj b)
        (T.predecessorObj a)) (nextPastOriginalComparison_leg chi A T B S a hPast i hi b))
  exact (congrArg Under.Hom.right h).trans
    (nativePushoutHomEquiv_right (A.presentation.ι.app i) _ _ _)

/-- Each entire next predecessor comparison retains the same original coefficient and vertex leg. -/
@[reassoc]
theorem nextPastOriginalMap_coefficient (b : LowerSet.Iio a) :
    pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b)))) ≫
    ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫
    (nextPastOriginalMap chi A T B S a hPast i hi).right =
    pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.ι.app ((nextPastDiagram chi A T B S a hPast).obj b).left) ≫
    (S.comparison.hom.app ((nextPastInclusion B a hPast).obj b)).right ≫
    ((T.predecessor a).cocone.ι.app b).right := by
  let k := pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
    (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))))
  let l := pushout.inl ((nextPastAtRoot chi A T B S a hPast i hi).obj b).hom
    (A.presentation.ι.app i)
  let c := (raisedComponentIso chi A (nextPastDiagram chi A T B S a hPast) i
    (fun b => hi ((nextPastInclusion B a hPast).obj b)) b).hom.right
  let e := (S.comparison.hom.app ((nextPastInclusion B a hPast).obj b)).right
  let p := ((T.predecessor a).cocone.ι.app b).right
  let k' := pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
    (A.presentation.ι.app ((nextPastDiagram chi A T B S a hPast).obj b).left)
  have h₁ : (k ≫ l) ≫ c = k' :=
    raisedComponentIso_inl chi A (nextPastDiagram chi A T B S a hPast) i
      (fun b => hi ((nextPastInclusion B a hPast).obj b)) b
  have hCompare : k ≫ l ≫ (c ≫ e) = k' ≫ e :=
    (Category.assoc k l (c ≫ e)).symm.trans
      ((Category.assoc (k ≫ l) c e).symm.trans (congrArg (fun m => m ≫ e) h₁))
  have hLeg := congrArg (fun m => k ≫ m)
    (nextPastOriginalMap_leg chi A T B S a hPast i hi b)
  change k ≫ _ ≫ _ = k' ≫ e ≫ p
  have hAssoc : k ≫ l ≫ ((c ≫ e) ≫ p) = (k ≫ l ≫ (c ≫ e)) ≫ p :=
    ((Category.assoc k (l ≫ (c ≫ e)) p).trans
      (congrArg (fun m => k ≫ m) (Category.assoc l (c ≫ e) p))).symm
  exact hLeg.trans (hAssoc.trans
    ((congrArg (fun m => m ≫ p) hCompare).trans (Category.assoc k' e p)))

variable (j : A.index) (hij : i ≤ j)

/-- The full predecessor transition uses the native composition comparison and both actual UPs. -/
def nextPastTransitionIso :
    (Under.pushout (A.presentation.diag.map (homOfLE hij))).obj
      (nextPastColimit chi A T B S a hPast i hi).cocone.pt ≅
    (nextPastColimit chi A T B S a hPast j (fun b => (hi b).trans hij)).cocone.pt :=
  (isColimitOfPreserves (Under.pushout (A.presentation.diag.map (homOfLE hij)))
    (nextPastColimit chi A T B S a hPast i hi).isColimit).coconePointsIsoOfNatIso
      (nextPastColimit chi A T B S a hPast j (fun b => (hi b).trans hij)).isColimit
      (raiseCompositionIso chi A j (nextPastDiagram chi A T B S a hPast)
        (fun b => (hi ((nextPastInclusion B a hPast).obj b)).trans hij) i
        (fun b => hi ((nextPastInclusion B a hPast).obj b)) hij)

/-- Each whole predecessor transition retains the actual old mapped leg and receiving-root Iso. -/
@[reassoc]
theorem nextPastTransitionIso_leg (b : LowerSet.Iio a) :
    (Under.pushout (A.presentation.diag.map (homOfLE hij))).map
      ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b) ≫
    (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom =
    (raiseCompositionIso chi A j (nextPastDiagram chi A T B S a hPast)
      (fun b => (hi ((nextPastInclusion B a hPast).obj b)).trans hij) i
      (fun b => hi ((nextPastInclusion B a hPast).obj b)) hij).hom.app b ≫
    (nextPastColimit chi A T B S a hPast j (fun b => (hi b).trans hij)).cocone.ι.app b :=
  (isColimitOfPreserves (Under.pushout (A.presentation.diag.map (homOfLE hij)))
    (nextPastColimit chi A T B S a hPast i hi).isColimit).comp_coconePointsIsoOfNatIso_hom
      (nextPastColimit chi A T B S a hPast j (fun b => (hi b).trans hij)).isColimit
      (raiseCompositionIso chi A j (nextPastDiagram chi A T B S a hPast)
        (fun b => (hi ((nextPastInclusion B a hPast).obj b)).trans hij) i
        (fun b => hi ((nextPastInclusion B a hPast).obj b)) hij) b

/-- The true predecessor transition retains its complete native original coefficient map. -/
@[reassoc]
theorem nextPastTransitionIso_coefficient (b : LowerSet.Iio a) :
    pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b)))) ≫
    ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫
    pushout.inl (nextPastColimit chi A T B S a hPast i hi).cocone.pt.hom
      (A.presentation.diag.map (homOfLE hij)) ≫
    (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom.right =
    pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.diag.map (homOfLE ((hi ((nextPastInclusion B a hPast).obj b)).trans hij))) ≫
    ((nextPastColimit chi A T B S a hPast j (fun b => (hi b).trans hij)).cocone.ι.app b).right := by
  let adj := Under.mapPushoutAdj (A.presentation.diag.map (homOfLE hij))
  let rho := raiseCompositionIso chi A j (nextPastDiagram chi A T B S a hPast)
    (fun b => (hi ((nextPastInclusion B a hPast).obj b)).trans hij) i
    (fun b => hi ((nextPastInclusion B a hPast).obj b)) hij
  have hLeg := (adj.homEquiv_naturality_left
    ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b)
    (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom).symm.trans
      (congrArg (adj.homEquiv ((nextPastAtRoot chi A T B S a hPast i hi).obj b)
        (nextPastColimit chi A T B S a hPast j (fun b => (hi b).trans hij)).cocone.pt)
        (nextPastTransitionIso_leg chi A T B S a hPast i hi j hij b))
  have hLegRight := (congrArg Under.Hom.right hLeg).trans
    (nativePushoutHomEquiv_right (A.presentation.diag.map (homOfLE hij)) _ _ _)
  let k := pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
    (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))))
  let l := pushout.inl ((nextPastAtRoot chi A T B S a hPast i hi).obj b).hom
    (A.presentation.diag.map (homOfLE hij))
  let c := (rho.hom.app b).right
  let p := ((nextPastColimit chi A T B S a hPast j
    (fun b => (hi b).trans hij)).cocone.ι.app b).right
  let k' := pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
    (A.presentation.diag.map (homOfLE ((hi ((nextPastInclusion B a hPast).obj b)).trans hij)))
  have hCompare : k ≫ l ≫ c = k' :=
    raiseCompositionIso_inl_flat chi A j (nextPastDiagram chi A T B S a hPast)
      (fun b => (hi ((nextPastInclusion B a hPast).obj b)).trans hij) i
      (fun b => hi ((nextPastInclusion B a hPast).obj b)) hij b
  have hUnit := nativePushoutHomEquiv_right (A.presentation.diag.map (homOfLE hij))
    (nextPastColimit chi A T B S a hPast i hi).cocone.pt _
    (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom
  change k ≫ _ ≫ _ ≫ _ = k' ≫ p
  have hStart := congrArg (fun m => k ≫
    ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫ m) hUnit.symm
  have hMiddle := congrArg (fun m => k ≫ m) hLegRight
  have hAssoc : k ≫ l ≫ (c ≫ p) = (k ≫ l ≫ c) ≫ p :=
    ((Category.assoc k (l ≫ c) p).trans
      (congrArg (fun m => k ≫ m) (Category.assoc l c p))).symm
  exact hStart.trans (hMiddle.trans (hAssoc.trans (congrArg (fun m => m ≫ p) hCompare)))

/-- The root-transition Hom bijection retains the original root via its actual cocone equation. -/
abbrev nextPastOriginalThrough :
    (nextPastColimit chi A T B S a hPast i hi).cocone.pt ⟶
      (Under.map (A.presentation.ι.app i)).obj (T.predecessorObj a) :=
  Under.homMk
    ((Under.mapPushoutAdj (A.presentation.diag.map (homOfLE hij))).homEquiv _ _
      ((nextPastTransitionIso chi A T B S a hPast i hi j hij).hom ≫
        nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij))).right (by
      have h := Under.w ((Under.mapPushoutAdj (A.presentation.diag.map (homOfLE hij))).homEquiv
        _ _ ((nextPastTransitionIso chi A T B S a hPast i hi j hij).hom ≫
          nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij)))
      exact h.trans ((Category.assoc (A.presentation.diag.map (homOfLE hij))
        (A.presentation.ι.app j) (T.predecessorObj a).hom).symm.trans
          (congrArg (fun m => m ≫ (T.predecessorObj a).hom)
            (A.presentation.w (homOfLE hij)))))

/-- The full original predecessor function is retained along the selected true root transition. -/
theorem nextPastOriginalThrough_right :
    (nextPastOriginalThrough chi A T B S a hPast i hi j hij).right =
      pushout.inl (nextPastColimit chi A T B S a hPast i hi).cocone.pt.hom
        (A.presentation.diag.map (homOfLE hij)) ≫
      (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom.right ≫
      (nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij)).right :=
  nativePushoutHomEquiv_right (A.presentation.diag.map (homOfLE hij)) _ _ _

/-- The actual whole predecessor UP proves compatibility of every original root-transition map. -/
theorem nextPastOriginalThrough_eq :
    nextPastOriginalThrough chi A T B S a hPast i hi j hij =
      nextPastOriginalMap chi A T B S a hPast i hi := by
  apply (nextPastColimit chi A T B S a hPast i hi).isColimit.hom_ext
  intro b
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · let k := pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))))
    change k ≫ _ ≫ _ = k ≫ _ ≫ _
    have hFirst := congrArg (fun m => k ≫
      ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫ m)
      (nextPastOriginalThrough_right chi A T B S a hPast i hi j hij)
    have hAssoc := congrArg (fun m => k ≫
      ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫ m)
      (Category.assoc
        (pushout.inl (nextPastColimit chi A T B S a hPast i hi).cocone.pt.hom
          (A.presentation.diag.map (homOfLE hij)))
        (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom.right
        (nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij)).right).symm
    exact hFirst.trans
      (hAssoc.trans ((nextPastTransitionIso_coefficient_assoc chi A T B S a hPast i hi j hij b
        (nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij)).right).trans
          ((nextPastOriginalMap_coefficient chi A T B S a hPast j
            (fun b => (hi b).trans hij) b).trans
              (nextPastOriginalMap_coefficient chi A T B S a hPast i hi b).symm)))
  · exact (Under.w ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b ≫
      nextPastOriginalThrough chi A T B S a hPast i hi j hij)).trans
        (Under.w ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b ≫
          nextPastOriginalMap chi A T B S a hPast i hi)).symm

/-- The genuine filtered-presentation leg agrees with the entire canonical next-predecessor map. -/
theorem nextPastTransition_original :
    (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom.right ≫
      (nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij)).right =
    (rootPushoutPresentation chi A i
      (nextPastColimit chi A T B S a hPast i hi).cocone.pt).ι.app
      (Under.mk (homOfLE hij)) ≫
    (nextPastOriginalComparison chi A T B S a hPast i hi).hom.right := by
  let U := (nextPastColimit chi A T B S a hPast i hi).cocone.pt
  let e := nextPastOriginalComparison chi A T B S a hPast i hi
  let f := (nextPastTransitionIso chi A T B S a hPast i hi j hij).hom ≫
    nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij)
  let g : (Under.pushout (A.presentation.diag.map (homOfLE hij))).obj U ⟶
      (Under.map (A.presentation.ι.app j)).obj (T.predecessorObj a) :=
    Under.homMk ((rootPushoutPresentation chi A i U).ι.app (Under.mk (homOfLE hij)) ≫
      e.hom.right) (by
        exact (Category.assoc (pushout.inr U.hom (A.presentation.diag.map (homOfLE hij)))
          ((rootPushoutPresentation chi A i U).ι.app (Under.mk (homOfLE hij)))
          e.hom.right).symm.trans
            ((rootPushoutPresentation_inr_assoc chi A i U (Under.mk (homOfLE hij))
              e.hom.right).trans
                (congrArg (fun m => A.presentation.ι.app j ≫ m) (Under.w e.hom))))
  change f.right = g.right
  apply pushout.hom_ext
  · have hFirst := (nextPastOriginalThrough_right chi A T B S a hPast i hi j hij).symm.trans
      (congrArg Under.Hom.right (nextPastOriginalThrough_eq chi A T B S a hPast i hi j hij))
    have hSecond := (Category.assoc (pushout.inl U.hom (A.presentation.diag.map (homOfLE hij)))
      ((rootPushoutPresentation chi A i U).ι.app (Under.mk (homOfLE hij)))
      e.hom.right).symm.trans
        ((rootPushoutPresentation_inl_assoc chi A i U
          (Under.mk (homOfLE hij)) e.hom.right).trans
            (nextPastOriginalMap_right chi A T B S a hPast i hi).symm)
    exact hFirst.trans hSecond.symm
  · exact (Under.w f).trans (Under.w g).symm

variable [IsCardinalPresentable (s (T.label a)).left chi]

include hi in
/-- Compactness of the actual original source selects a real later compact-root attaching factor. -/
theorem exists_nextAttaching :
    ∃ (j : A.index) (hij : i ≤ j)
      (g : (s (T.label a)).left ⟶
        (nextPastColimit chi A T B S a hPast j (fun b => (hi b).trans hij)).cocone.pt.right),
      g ≫ (nextPastOriginalMap chi A T B S a hPast j (fun b => (hi b).trans hij)).right =
        T.attaching a := by
  let e := nextPastOriginalComparison chi A T B S a hPast i hi
  obtain ⟨j, g, hg⟩ := exists_rootPushoutFactor chi A i
    (nextPastColimit chi A T B S a hPast i hi).cocone.pt (T.attaching a ≫ e.inv.right)
  let hij : i ≤ j.right := leOfHom j.hom
  let p := nextPastTransitionIso chi A T B S a hPast i hi j.right hij
  refine ⟨j.right, hij, g ≫ p.hom.right, ?_⟩
  have h₁ := (Category.assoc g p.hom.right
    (nextPastOriginalMap chi A T B S a hPast j.right (fun b => (hi b).trans hij)).right).trans
      (congrArg (fun m => g ≫ m)
        (nextPastTransition_original chi A T B S a hPast i hi j.right hij))
  have h₂ := (Category.assoc g
    ((rootPushoutPresentation chi A i
      (nextPastColimit chi A T B S a hPast i hi).cocone.pt).ι.app j) e.hom.right).symm.trans
      (congrArg (fun m => m ≫ e.hom.right) hg)
  have h₃ := (Category.assoc (T.attaching a) e.inv.right e.hom.right).trans
    ((congrArg (fun m => T.attaching a ≫ m) (Under.inv_right_hom_right e)).trans
      (Category.comp_id _))
  exact h₁.trans (h₂.trans h₃)

end ActualSuccessorPredecessors

section OriginalSuccessorVertices

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P)) (a : P)
  (i : A.index) (U : Under (A.presentation.diag.obj i))
  (e : (Under.pushout (A.presentation.ι.app i)).obj U ≅ T.predecessorObj a)
  (g : (s (T.label a)).left ⟶ U.right)
  (hg : g ≫ pushout.inl U.hom (A.presentation.ι.app i) ≫ e.hom.right = T.attaching a)

/-- Attach the same actual original generator at the genuinely selected compact root. -/
abbrev newVertex : Under (A.presentation.diag.obj i) :=
  Under.mk (U.hom ≫ pushout.inl g (s (T.label a)).hom)

/-- The whole predecessor map is the actual native generator pushout inclusion. -/
abbrev newVertexMap : U ⟶ newVertex chi A T a i U g :=
  Under.homMk (pushout.inl g (s (T.label a)).hom) rfl

/-- The same original generator target enters the actual new vertex by the other native leg. -/
abbrev newVertexCell : (s (T.label a)).right ⟶ (newVertex chi A T a i U g).right :=
  pushout.inr g (s (T.label a)).hom

/-- Actual root pushout pasting retains the complete newly attached original cell square. -/
theorem newVertex_mapped_isPushout :
    IsPushout (g ≫ pushout.inl U.hom (A.presentation.ι.app i)) (s (T.label a)).hom
      ((Under.pushout (A.presentation.ι.app i)).map (newVertexMap chi A T a i U g)).right
      (newVertexCell chi A T a i U g ≫
        pushout.inl (newVertex chi A T a i U g).hom (A.presentation.ι.app i)) :=
  ((IsPushout.of_hasPushout g (s (T.label a)).hom).flip.paste_vert
    (map_isPushout (A.presentation.ι.app i) (newVertexMap chi A T a i U g))).flip

include hg in
/-- The true original attaching equation aligns the two original-generator pushout spans. -/
theorem newVertex_original_isPushout :
    IsPushout (T.attaching a) (s (T.label a)).hom
      (e.inv.right ≫
        ((Under.pushout (A.presentation.ι.app i)).map (newVertexMap chi A T a i U g)).right)
      (newVertexCell chi A T a i U g ≫
        pushout.inl (newVertex chi A T a i U g).hom (A.presentation.ι.app i)) := by
  apply (newVertex_mapped_isPushout chi A T a i U g).of_iso
    (Iso.refl _) ((Under.forget X).mapIso e) (Iso.refl _) (Iso.refl _)
  · exact (Category.assoc g (pushout.inl U.hom (A.presentation.ι.app i)) e.hom.right).trans
      (hg.trans (Category.id_comp _).symm)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans
      ((Category.assoc e.hom.right e.inv.right _).symm.trans
        ((congrArg (fun m => m ≫ _) (Under.hom_right_inv_right e)).trans
          (Category.id_comp _))).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Both genuine original cell UPs construct the actual whole coefficient-vertex isomorphism. -/
def newVertexUnderlyingIso :
    ((Under.pushout (A.presentation.ι.app i)).obj (newVertex chi A T a i U g)).right ≅
      (T.vertex a).right :=
  (newVertex_original_isPushout chi A T a i U e g hg).isoIsPushout _ _ (T.isPushout a)

/-- The complete original predecessor-to-vertex map is retained through the chosen vertex Iso. -/
@[reassoc]
theorem newVertexUnderlyingIso_predecessor :
    ((Under.pushout (A.presentation.ι.app i)).map (newVertexMap chi A T a i U g)).right ≫
      (newVertexUnderlyingIso chi A T a i U e g hg).hom =
    e.hom.right ≫ (T.predecessorMap a).right := by
  let m := ((Under.pushout (A.presentation.ι.app i)).map (newVertexMap chi A T a i U g)).right
  let z := (newVertexUnderlyingIso chi A T a i U e g hg).hom
  have h := IsPushout.inl_isoIsPushout_hom (T.predecessorObj a).right (s (T.label a)).right
    (newVertex_original_isPushout chi A T a i U e g hg) (T.isPushout a)
  have hAssoc : e.inv.right ≫ (m ≫ z) = (T.predecessorMap a).right :=
    (Category.assoc e.inv.right m z).symm.trans h
  have h' := congrArg (fun m => e.hom.right ≫ m) hAssoc
  have hCancel : e.hom.right ≫ e.inv.right ≫ (m ≫ z) = m ≫ z :=
    (Category.assoc e.hom.right e.inv.right (m ≫ z)).symm.trans
      ((congrArg (fun m' => m' ≫ (m ≫ z)) (Under.hom_right_inv_right e)).trans
        (Category.id_comp _))
  exact hCancel.symm.trans h'

/-- The native original root equation makes the entire coefficient Iso an Iso in Under X. -/
def newVertexOriginalIso :
    (Under.pushout (A.presentation.ι.app i)).obj (newVertex chi A T a i U g) ≅ T.vertex a :=
  Under.isoMk (newVertexUnderlyingIso chi A T a i U e g hg) (by
    have h₁ := Under.w ((Under.pushout (A.presentation.ι.app i)).map
      (newVertexMap chi A T a i U g))
    have h₂ := newVertexUnderlyingIso_predecessor chi A T a i U e g hg
    exact (congrArg (fun m => m ≫ (newVertexUnderlyingIso chi A T a i U e g hg).hom)
      h₁.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (fun m => ((Under.pushout (A.presentation.ι.app i)).obj U).hom ≫ m) h₂).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun m => m ≫ (T.predecessorMap a).right) (Under.w e.hom)).trans
              (Under.w (T.predecessorMap a)))))))

/-- Every actual original generator-target function survives the full native vertex comparison. -/
@[reassoc]
theorem newVertexOriginalIso_cell :
    newVertexCell chi A T a i U g ≫
      pushout.inl (newVertex chi A T a i U g).hom (A.presentation.ι.app i) ≫
      (newVertexOriginalIso chi A T a i U e g hg).hom.right = T.cell a :=
  (Category.assoc _ _ _).symm.trans
    (IsPushout.inr_isoIsPushout_hom (T.predecessorObj a).right (s (T.label a)).right
      (newVertex_original_isPushout chi A T a i U e g hg) (T.isPushout a))

end OriginalSuccessorVertices

section LiteralOneCellExtension

variable {P : Type w} [PartialOrder P] (B : LowerSet P) (a : P)
  (ha : a ∉ B) (hPast : LowerSet.Iio a ≤ B)

include hPast in
/-- Outside the old prefix, its one-cell extension contains exactly the original new label. -/
theorem extension_label {b : ↥(B ⊔ LowerSet.Iic a)} (hb : b.1 ∉ B) : b.1 = a := by
  have hba : b.1 ≤ a := (LowerSet.mem_sup_iff.1 b.2).resolve_left hb
  by_contra hne
  exact hb (memOfLE hPast (lt_of_le_of_ne hba hne))

include ha hPast in
/-- Every old-to-new arrow is a genuine original strict predecessor of the same new cell. -/
theorem extension_old_to_new {b d : ↥(B ⊔ LowerSet.Iic a)} (f : b ⟶ d)
    (hb : b.1 ∈ B) (hd : d.1 ∉ B) : b.1 < a := by
  have hda := extension_label B a hPast hd
  have hbd : b.1 ≤ d.1 := leOfHom f
  have hba : b.1 ≤ a := Eq.mp (congrArg (fun z : P => b.1 ≤ z) hda) hbd
  have hne : b.1 ≠ a := by
    intro he
    exact ha (Eq.mp (congrArg (fun z : P => z ∈ B) he) hb)
  exact lt_of_le_of_ne hba hne

variable {K : Type uJ} [Category.{vJ} K]
  (F : B ⥤ K) (c : Cocone (nextPastInclusion B a hPast ⋙ F))

/-- The old objects stay literal, and the new original label receives the actual cocone point. -/
abbrev extensionObject (b : ↥(B ⊔ LowerSet.Iic a)) : K := by
  classical
  exact if hb : b.1 ∈ B then F.obj ⟨b.1, hb⟩ else c.pt

/-- The actual old coefficient object is retained by its original label. -/
theorem extensionObject_old (b : ↥(B ⊔ LowerSet.Iic a)) (hb : b.1 ∈ B) :
    extensionObject B a hPast F c b = F.obj ⟨b.1, hb⟩ := by
  classical
  exact dite_eq_left hb

/-- The sole new label receives the actual predecessor cocone point. -/
theorem extensionObject_new (b : ↥(B ⊔ LowerSet.Iic a)) (hb : b.1 ∉ B) :
    extensionObject B a hPast F c b = c.pt := by
  classical
  exact dite_eq_right hb

/-- Every actual extension arrow is the original old map or its genuine predecessor cocone leg. -/
abbrev extensionMap {b d : ↥(B ⊔ LowerSet.Iic a)} (f : b ⟶ d) :
    extensionObject B a hPast F c b ⟶ extensionObject B a hPast F c d := by
  classical
  by_cases hb : b.1 ∈ B
  · by_cases hd : d.1 ∈ B
    · exact eqToHom (extensionObject_old B a hPast F c b hb) ≫
        F.map (homOfLE (leOfHom f) : (⟨b.1, hb⟩ : B) ⟶ ⟨d.1, hd⟩) ≫
        eqToHom (extensionObject_old B a hPast F c d hd).symm
    · have leg : F.obj (⟨b.1, hb⟩ : B) ⟶ c.pt :=
        c.ι.app ⟨b.1, extension_old_to_new B a ha hPast f hb hd⟩
      exact eqToHom (extensionObject_old B a hPast F c b hb) ≫ leg ≫
        eqToHom (extensionObject_new B a hPast F c d hd).symm
  · have hd : d.1 ∉ B := fun hd => hb (B.lower (leOfHom f) hd)
    exact eqToHom (extensionObject_new B a hPast F c b hb) ≫ 𝟙 c.pt ≫
      eqToHom (extensionObject_new B a hPast F c d hd).symm

include ha in
/-- The entire old extension map is the actual original old Hom value. -/
theorem extensionMap_old {b d : ↥(B ⊔ LowerSet.Iic a)} (f : b ⟶ d)
    (hb : b.1 ∈ B) (hd : d.1 ∈ B) :
    extensionMap B a ha hPast F c f ≍
      F.map (homOfLE (leOfHom f) : (⟨b.1, hb⟩ : B) ⟶ ⟨d.1, hd⟩) := by
  classical
  simp only [extensionMap, dite_eq_left hb, dite_eq_left hd,
    comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]
  rfl

include ha in
/-- The whole old-to-new map is its actual original strict-predecessor cocone leg. -/
theorem extensionMap_mixed {b d : ↥(B ⊔ LowerSet.Iic a)} (f : b ⟶ d)
    (hb : b.1 ∈ B) (hd : d.1 ∉ B) :
    extensionMap B a ha hPast F c f ≍
      c.ι.app ⟨b.1, extension_old_to_new B a ha hPast f hb hd⟩ := by
  classical
  simp only [extensionMap, dite_eq_left hb, dite_eq_right hd,
    comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]
  rfl

include ha in
/-- Every map whose source is the sole new label retains the actual identity of the new vertex. -/
theorem extensionMap_new {b d : ↥(B ⊔ LowerSet.Iic a)} (f : b ⟶ d) (hb : b.1 ∉ B) :
    extensionMap B a ha hPast F c f ≍ 𝟙 c.pt := by
  classical
  simp only [extensionMap, dite_eq_right hb,
    comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]
  rfl

/-- The full literal one-cell extension is constructed from actual natural predecessor legs. -/
def extensionDiagram : ↥(B ⊔ LowerSet.Iic a) ⥤ K where
  obj b := extensionObject B a hPast F c b
  map f := extensionMap B a ha hPast F c f
  map_id b := by
    classical
    by_cases hb : b.1 ∈ B
    · have hObj := extensionObject_old B a hPast F c b hb
      have hId := (eqToHom_heq_id_dom _ _ hObj).symm.trans (eqToHom_heq_id_cod _ _ hObj)
      exact eq_of_heq ((extensionMap_old B a ha hPast F c (𝟙 b) hb hb).trans
        ((heq_of_eq (F.map_id (⟨b.1, hb⟩ : B))).trans hId.symm))
    · have hObj := extensionObject_new B a hPast F c b hb
      have hId := (eqToHom_heq_id_dom _ _ hObj).symm.trans (eqToHom_heq_id_cod _ _ hObj)
      exact eq_of_heq ((extensionMap_new B a ha hPast F c (𝟙 b) hb).trans hId.symm)
  map_comp {b d e} f g := by
    classical
    by_cases he : e.1 ∈ B
    · have hd : d.1 ∈ B := B.lower (leOfHom g) he
      have hb : b.1 ∈ B := B.lower (leOfHom f) hd
      let f' : (⟨b.1, hb⟩ : B) ⟶ ⟨d.1, hd⟩ := homOfLE (leOfHom f)
      let g' : (⟨d.1, hd⟩ : B) ⟶ ⟨e.1, he⟩ := homOfLE (leOfHom g)
      have hComp := heq_comp
        (extensionObject_old B a hPast F c b hb) (extensionObject_old B a hPast F c d hd)
        (extensionObject_old B a hPast F c e he)
        (extensionMap_old B a ha hPast F c f hb hd) (extensionMap_old B a ha hPast F c g hd he)
      exact eq_of_heq ((extensionMap_old B a ha hPast F c (f ≫ g) hb he).trans
        ((heq_of_eq (F.map_comp f' g')).trans hComp.symm))
    · by_cases hd : d.1 ∈ B
      · have hb : b.1 ∈ B := B.lower (leOfHom f) hd
        have hNat := c.w
          (homOfLE (leOfHom f) :
            (⟨b.1, extension_old_to_new B a ha hPast (f ≫ g) hb he⟩ : LowerSet.Iio a) ⟶
            ⟨d.1, extension_old_to_new B a ha hPast g hd he⟩)
        have hComp := heq_comp
          (extensionObject_old B a hPast F c b hb) (extensionObject_old B a hPast F c d hd)
          (extensionObject_new B a hPast F c e he)
          (extensionMap_old B a ha hPast F c f hb hd)
          (extensionMap_mixed B a ha hPast F c g hd he)
        exact eq_of_heq ((extensionMap_mixed B a ha hPast F c (f ≫ g) hb he).trans
          ((heq_of_eq hNat.symm).trans hComp.symm))
      · by_cases hb : b.1 ∈ B
        · have hComp := heq_comp
            (extensionObject_old B a hPast F c b hb) (extensionObject_new B a hPast F c d hd)
            (extensionObject_new B a hPast F c e he)
            (extensionMap_mixed B a ha hPast F c f hb hd)
            (extensionMap_new B a ha hPast F c g hd)
          exact eq_of_heq ((extensionMap_mixed B a ha hPast F c (f ≫ g) hb he).trans
            ((heq_of_eq (Category.comp_id _)).symm.trans hComp.symm))
        · have hComp := heq_comp
            (extensionObject_new B a hPast F c b hb) (extensionObject_new B a hPast F c d hd)
            (extensionObject_new B a hPast F c e he)
            (extensionMap_new B a ha hPast F c f hb) (extensionMap_new B a ha hPast F c g hd)
          exact eq_of_heq ((extensionMap_new B a ha hPast F c (f ≫ g) hb).trans
            ((heq_of_eq (Category.id_comp (𝟙 c.pt))).symm.trans hComp.symm))

/-- The entire actual old diagram, including every Hom value, is retained by exact restriction. -/
theorem extensionDiagram_restrict :
    lowerInclusion (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) ⋙
      extensionDiagram B a ha hPast F c = F := by
  classical
  apply Functor.hext
  · intro b
    simp only [Functor.comp_obj, extensionDiagram, extensionObject,
      lowerInclusion, dite_eq_left b.2]
  · intro b d f
    exact (extensionMap_old B a ha hPast F c
      ((lowerInclusion (le_sup_left : B ≤ B ⊔ LowerSet.Iic a)).map f) b.2 d.2).trans
        (heq_of_eq (congrArg F.map (Subsingleton.elim _ _)))

end LiteralOneCellExtension

section ActualNewBirthCocones

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))
  (B : LowerSet P) (S : PrefixLift chi A T B) (a : P) (hPast : LowerSet.Iio a ≤ B)
  (i : A.index) (hi : ∀ b, (S.diagram.obj b).left ≤ i)
  (g : (s (T.label a)).left ⟶ (nextPastColimit chi A T B S a hPast i hi).cocone.pt.right)
  (hg : g ≫ (nextPastOriginalMap chi A T B S a hPast i hi).right = T.attaching a)

include hg in
/-- The actual factor equation keeps both native root-change inclusions and the original Iso. -/
theorem nextBirthFactorEquation :
    g ≫ pushout.inl (nextPastColimit chi A T B S a hPast i hi).cocone.pt.hom
      (A.presentation.ι.app i) ≫
    (nextPastOriginalComparison chi A T B S a hPast i hi).hom.right = T.attaching a :=
  (congrArg (fun m => g ≫ m) (nextPastOriginalMap_right chi A T B S a hPast i hi)).symm.trans hg

/-- The next actual moving-root vertex is the original generator's genuine native pushout. -/
abbrev nextBirthVertex : Comma A.presentation.diag (𝟭 C) where
  left := i
  right := (newVertex chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right
  hom := (newVertex chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).hom

/-- Every actual strict predecessor maps to the new birth vertex through its full colimit leg. -/
abbrev nextBirthLeg (b : LowerSet.Iio a) :
    (nextPastDiagram chi A T B S a hPast).obj b ⟶ nextBirthVertex chi A T B S a hPast i hi g where
  left := homOfLE (hi ((nextPastInclusion B a hPast).obj b))
  right :=
    pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b)))) ≫
    ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫
    (newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right
  w := by
    let D := nextPastDiagram chi A T B S a hPast
    let k := pushout.inl (D.obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))))
    let m := ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫
      (newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right
    have h₁ : (D.obj b).hom ≫ k =
        A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))) ≫
          ((nextPastAtRoot chi A T B S a hPast i hi).obj b).hom := pushout.condition
    have h₂ : ((nextPastAtRoot chi A T B S a hPast i hi).obj b).hom ≫ m =
        (nextBirthVertex chi A T B S a hPast i hi g).hom :=
      Under.w ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b ≫
        newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g)
    exact ((Category.assoc (D.obj b).hom k m).symm.trans
      ((congrArg (fun m' => m' ≫ m) h₁).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun m' =>
            A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))) ≫ m')
              h₂)))).symm

/-- All birth comparisons are natural on the literal original strict-predecessor order. -/
theorem nextBirthLeg_naturality {b d : LowerSet.Iio a} (f : b ⟶ d) :
    (nextPastDiagram chi A T B S a hPast).map f ≫ nextBirthLeg chi A T B S a hPast i hi g d =
      nextBirthLeg chi A T B S a hPast i hi g b := by
  apply Comma.hom_ext
  · exact Subsingleton.elim _ _
  · let D := nextPastDiagram chi A T B S a hPast
    let k₀ := pushout.inl (D.obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))))
    let k₁ := pushout.inl (D.obj d).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj d))))
    let m := ((nextPastAtRoot chi A T B S a hPast i hi).map f).right
    let p₀ := ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right
    let p₁ := ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app d).right
    let k := (newVertexMap chi A T a i
      (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right
    have h₁ : k₀ ≫ m = (D.map f).right ≫ k₁ :=
      raisedDiagram_inl chi A D i (fun b => hi ((nextPastInclusion B a hPast).obj b)) f
    have h₂ : m ≫ p₁ = p₀ := congrArg Under.Hom.right
      ((nextPastColimit chi A T B S a hPast i hi).cocone.w f)
    change (D.map f).right ≫ k₁ ≫ p₁ ≫ k = k₀ ≫ p₀ ≫ k
    exact (Category.assoc (D.map f).right k₁ (p₁ ≫ k)).symm.trans
      ((congrArg (fun m' => m' ≫ p₁ ≫ k) h₁.symm).trans
        ((Category.assoc k₀ m (p₁ ≫ k)).trans
          ((congrArg (fun m' => k₀ ≫ m') (Category.assoc m p₁ k).symm).trans
            (congrArg (fun m' => k₀ ≫ m' ≫ k) h₂))))

/-- The full actual moving-root predecessor cocone is built from every original comparison map. -/
abbrev nextBirthCocone : Cocone (nextPastDiagram chi A T B S a hPast) where
  pt := nextBirthVertex chi A T B S a hPast i hi g
  ι :=
    { app b := nextBirthLeg chi A T B S a hPast i hi g b
      naturality b d f :=
        (nextBirthLeg_naturality chi A T B S a hPast i hi g (b := b) (d := d) f).trans
        (Category.comp_id _).symm }

/-- The native new-vertex comparison retains the complete actual original cell value. -/
abbrev nextBirthVertexIso :
    (originalBaseChange chi A).obj (nextBirthVertex chi A T B S a hPast i hi g) ≅ T.vertex a :=
  newVertexOriginalIso chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt
    (nextPastOriginalComparison chi A T B S a hPast i hi) g
      (nextBirthFactorEquation chi A T B S a hPast i hi g hg)

/-- The whole actual new-cell map returns the same original structural predecessor map. -/
theorem nextBirthVertexIso_map :
    (newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right ≫
    pushout.inl (nextBirthVertex chi A T B S a hPast i hi g).hom (A.presentation.ι.app i) ≫
    (nextBirthVertexIso chi A T B S a hPast i hi g hg).hom.right =
    (nextPastOriginalMap chi A T B S a hPast i hi).right ≫ (T.predecessorMap a).right := by
  let U := (nextPastColimit chi A T B S a hPast i hi).cocone.pt
  let e := nextPastOriginalComparison chi A T B S a hPast i hi
  let v := newVertexMap chi A T a i U g
  let z := (nextBirthVertexIso chi A T B S a hPast i hi g hg).hom.right
  have hSquare := inl_map (A.presentation.ι.app i) v
  have h₁ := (Category.assoc v.right
    (pushout.inl (nextBirthVertex chi A T B S a hPast i hi g).hom (A.presentation.ι.app i))
    z).symm.trans
      ((congrArg (fun m => m ≫ z) hSquare.symm).trans (Category.assoc _ _ _))
  have h₂ := congrArg (fun m => pushout.inl U.hom (A.presentation.ι.app i) ≫ m)
    (newVertexUnderlyingIso_predecessor chi A T a i U e g
      (nextBirthFactorEquation chi A T B S a hPast i hi g hg))
  have h₃ := (Category.assoc (pushout.inl U.hom (A.presentation.ι.app i)) e.hom.right
    (T.predecessorMap a).right).symm.trans
      (congrArg (fun m => m ≫ (T.predecessorMap a).right)
        (nextPastOriginalMap_right chi A T B S a hPast i hi).symm)
  exact h₁.trans (h₂.trans h₃)

/-- Every old predecessor-to-new vertex comparison keeps the complete original diagram arrow. -/
theorem nextBirthLeg_original (b : LowerSet.Iio a) :
    (originalBaseChange chi A).map (nextBirthLeg chi A T B S a hPast i hi g b) ≫
      (nextBirthVertexIso chi A T B S a hPast i hi g hg).hom =
    S.comparison.hom.app ((nextPastInclusion B a hPast).obj b) ≫
      T.diagram.map (homOfLE b.2.le) := by
  let l := nextBirthLeg chi A T B S a hPast i hi g b
  let eta := nextBirthVertexIso chi A T B S a hPast i hi g hg
  let old := S.comparison.hom.app ((nextPastInclusion B a hPast).obj b)
  let f := T.diagram.map (homOfLE b.2.le)
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · let k := pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((nextPastInclusion B a hPast).obj b))))
    let p := ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right
    let v := (newVertexMap chi A T a i
      (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right
    let u := pushout.inl (nextBirthVertex chi A T B S a hPast i hi g).hom (A.presentation.ι.app i)
    let q := (nextPastOriginalMap chi A T B S a hPast i hi).right
    let t := (T.predecessorMap a).right
    let p' := ((T.predecessor a).cocone.ι.app b).right
    let k' := pushout.inl ((nextPastDiagram chi A T B S a hPast).obj b).hom
      (A.presentation.ι.app ((nextPastDiagram chi A T B S a hPast).obj b).left)
    have hFirst : k' ≫ ((originalBaseChange chi A).map l).right ≫ eta.hom.right =
        l.right ≫ u ≫ eta.hom.right :=
      (Category.assoc k' ((originalBaseChange chi A).map l).right eta.hom.right).symm.trans
        ((congrArg (fun m => m ≫ eta.hom.right) (originalBaseChange_inl chi A l)).trans
          (Category.assoc _ _ _))
    have hSplit : l.right ≫ u ≫ eta.hom.right = k ≫ p ≫ (v ≫ u ≫ eta.hom.right) :=
      (Category.assoc k (p ≫ v) (u ≫ eta.hom.right)).trans
        (congrArg (fun m => k ≫ m) (Category.assoc p v (u ≫ eta.hom.right)))
    have hCell := congrArg (fun m => k ≫ p ≫ m)
      (nextBirthVertexIso_map chi A T B S a hPast i hi g hg)
    have hAssoc := ((Category.assoc k (p ≫ q) t).trans
      (congrArg (fun m => k ≫ m) (Category.assoc p q t))).symm
    have hOriginal := congrArg (fun m => m ≫ t)
      (nextPastOriginalMap_coefficient chi A T B S a hPast i hi b)
    have hEnd : (k' ≫ old.right ≫ p') ≫ t = k' ≫ old.right ≫ f.right :=
      (Category.assoc k' (old.right ≫ p') t).trans
        ((congrArg (fun m => k' ≫ m) (Category.assoc old.right p' t)).trans
          (congrArg (fun m => k' ≫ old.right ≫ m)
            (congrArg Under.Hom.right (T.predecessorMap_fac a b))))
    change k' ≫ ((originalBaseChange chi A).map l).right ≫ eta.hom.right =
      k' ≫ old.right ≫ f.right
    exact hFirst.trans (hSplit.trans (hCell.trans (hAssoc.trans (hOriginal.trans hEnd))))
  · exact (Under.w ((originalBaseChange chi A).map l ≫ eta.hom)).trans
      (Under.w (old ≫ f)).symm

/-- The actual new birth vertex and its whole original comparison form a native comma object. -/
abbrev nextBirthComparedPoint : Comma (originalBaseChange chi A) T.diagram where
  left := nextBirthVertex chi A T B S a hPast i hi g
  right := a
  hom := (nextBirthVertexIso chi A T B S a hPast i hi g hg).hom

/-- Each actual original strict predecessor retains its whole compared birth arrow. -/
abbrev nextBirthComparedLeg (b : LowerSet.Iio a) :
    (nextPastInclusion B a hPast ⋙ S.comparedDiagram chi A T).obj b ⟶
      nextBirthComparedPoint chi A T B S a hPast i hi g hg where
  left := nextBirthLeg chi A T B S a hPast i hi g b
  right := homOfLE b.2.le
  w := nextBirthLeg_original chi A T B S a hPast i hi g hg b

/-- The complete compared birth arrows are natural on the same original predecessor order. -/
theorem nextBirthComparedLeg_naturality {b d : LowerSet.Iio a} (f : b ⟶ d) :
    (nextPastInclusion B a hPast ⋙ S.comparedDiagram chi A T).map f ≫
      nextBirthComparedLeg chi A T B S a hPast i hi g hg d =
    nextBirthComparedLeg chi A T B S a hPast i hi g hg b := by
  apply Comma.hom_ext
  · exact nextBirthLeg_naturality chi A T B S a hPast i hi g f
  · exact Subsingleton.elim _ _

/-- The actual predecessor cocone retains each birth map and original comparison in native Comma. -/
abbrev nextBirthComparedCocone :
    Cocone (nextPastInclusion B a hPast ⋙ S.comparedDiagram chi A T) where
  pt := nextBirthComparedPoint chi A T B S a hPast i hi g hg
  ι :=
    { app b := nextBirthComparedLeg chi A T B S a hPast i hi g hg b
      naturality b d f :=
        (nextBirthComparedLeg_naturality chi A T B S a hPast i hi g hg (b := b) (d := d) f).trans
          (Category.comp_id _).symm }

variable (ha : a ∉ B)

/-- The entire next compared prefix keeps all old birth data and adjoins the same original cell. -/
abbrev nextComparedDiagram : ↥(B ⊔ LowerSet.Iic a) ⥤ Comma (originalBaseChange chi A) T.diagram :=
  extensionDiagram B a ha hPast (S.comparedDiagram chi A T)
    (nextBirthComparedCocone chi A T B S a hPast i hi g hg)

/-- The complete original old compared diagram is recovered by exact next-prefix restriction. -/
theorem nextComparedDiagram_restrict :
    lowerInclusion (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) ⋙
      nextComparedDiagram chi A T B S a hPast i hi g hg ha = S.comparedDiagram chi A T :=
  extensionDiagram_restrict B a ha hPast (S.comparedDiagram chi A T)
    (nextBirthComparedCocone chi A T B S a hPast i hi g hg)

/-- The entire actual label functor is the same literal original lower inclusion. -/
theorem nextComparedDiagram_labels :
    nextComparedDiagram chi A T B S a hPast i hi g hg ha ⋙
      Comma.snd (originalBaseChange chi A) T.diagram =
        inclusion ((B ⊔ LowerSet.Iic a) : Set P) := by
  classical
  refine Functor.ext (fun b => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  by_cases hb : b.1 ∈ B
  · simp only [nextComparedDiagram, extensionDiagram, extensionObject, dite_eq_left hb,
      PrefixLift.comparedDiagram, Comma.snd_obj, Functor.comp_obj]
  · simp only [nextComparedDiagram, extensionDiagram, extensionObject, dite_eq_right hb,
      nextBirthComparedCocone, nextBirthComparedPoint, Comma.snd_obj, Functor.comp_obj]
    exact (extension_label B a hPast hb).symm

/-- Each whole next-prefix comparison is an actual isomorphism, including the new generator cell. -/
theorem nextComparedDiagram_isIso (b : ↥(B ⊔ LowerSet.Iic a)) :
    IsIso ((nextComparedDiagram chi A T B S a hPast i hi g hg ha).obj b).hom := by
  classical
  let R (V : Comma (originalBaseChange chi A) T.diagram) : Prop := IsIso V.hom
  by_cases hb : b.1 ∈ B
  · have h := extensionObject_old B a hPast (S.comparedDiagram chi A T)
      (nextBirthComparedCocone chi A T B S a hPast i hi g hg) b hb
    exact Eq.mpr (congrArg R h)
      (inferInstance : IsIso (S.comparison.hom.app ⟨b.1, hb⟩))
  · have h := extensionObject_new B a hPast (S.comparedDiagram chi A T)
      (nextBirthComparedCocone chi A T B S a hPast i hi g hg) b hb
    exact Eq.mpr (congrArg R h)
      (inferInstance : IsIso (nextBirthVertexIso chi A T B S a hPast i hi g hg).hom)

/-- The complete next birth diagram is the native projection of its actual original comparisons. -/
abbrev nextPrefixBirthDiagram : ↥(B ⊔ LowerSet.Iic a) ⥤ Comma A.presentation.diag (𝟭 C) :=
  nextComparedDiagram chi A T B S a hPast i hi g hg ha ⋙
    Comma.fst (originalBaseChange chi A) T.diagram

/-- Exact original labels transport the actual compared isomorphisms to the entire next prefix. -/
abbrev nextPrefixOriginalIso :
    nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha ⋙ originalBaseChange chi A ≅
      restriction T.diagram (B ⊔ LowerSet.Iic a) := by
  let Q := nextComparedDiagram chi A T B S a hPast i hi g hg ha
  letI (b : ↥(B ⊔ LowerSet.Iic a)) : IsIso (Q.obj b).hom :=
    nextComparedDiagram_isIso chi A T B S a hPast i hi g hg ha b
  let F := Q ⋙ Comma.fst (originalBaseChange chi A) T.diagram ⋙ originalBaseChange chi A
  let G := Q ⋙ Comma.snd (originalBaseChange chi A) T.diagram ⋙ T.diagram
  let eta : F ≅ G := NatIso.ofComponents (fun b => asIso (Q.obj b).hom)
    (fun {b d} (f : b ⟶ d) => (Q.map f).w)
  exact eta ≪≫
      eqToIso (congrArg (fun F => F ⋙ T.diagram)
        (nextComparedDiagram_labels chi A T B S a hPast i hi g hg ha))

/-- Every old birth object and Hom value is retained by the next prefix's full restriction. -/
theorem nextPrefixBirthDiagram_restrict :
    lowerInclusion (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) ⋙
      nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha = S.diagram :=
  congrArg (fun F => F ⋙ Comma.fst (originalBaseChange chi A) T.diagram)
    (nextComparedDiagram_restrict chi A T B S a hPast i hi g hg ha)

/-- The same original new label lies in the literal one-cell extension. -/
abbrev nextPrefixLabel : ↥(B ⊔ LowerSet.Iic a) :=
  ⟨a, LowerSet.mem_sup_iff.2 (Or.inr le_rfl)⟩

/-- The actual new birth vertex retains its selected compact root and both coefficient maps. -/
theorem nextPrefixBirthDiagram_vertex :
    (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha).obj (nextPrefixLabel B a) =
      nextBirthVertex chi A T B S a hPast i hi g := by
  classical
  simp only [nextPrefixBirthDiagram, nextComparedDiagram, extensionDiagram, extensionObject,
    nextPrefixLabel, dite_eq_right ha, Functor.comp_obj, Comma.fst_obj,
    nextBirthComparedCocone, nextBirthComparedPoint]

/-- The entire actual strict-predecessor birth diagram remains the same given old prefix. -/
theorem nextPrefixBirthDiagram_past :
    birthPastDiagram chi A (B ⊔ LowerSet.Iic a)
      (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha) (nextPrefixLabel B a) =
      nextPastDiagram chi A T B S a hPast :=
  congrArg (fun D => nextPastInclusion B a hPast ⋙ D)
    (nextPrefixBirthDiagram_restrict chi A T B S a hPast i hi g hg ha)

/-- The whole root-adjoined next predecessor is the same actual C diagram at the selected root. -/
theorem nextPrefixBirthAdjoined :
    UnderColimits.adjoinedDiagram (Y := birthPredecessorDiagram chi A (B ⊔ LowerSet.Iic a)
      (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha) (nextPrefixLabel B a)) =
    UnderColimits.adjoinedDiagram (Y := nextPastAtRoot chi A T B S a hPast i hi) :=
  raisedAdjoined_congr chi A _ _ _ _ _ _
    (nextPrefixBirthDiagram_past chi A T B S a hPast i hi g hg ha)
    (congrArg Comma.left (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha))

/-- The actual next predecessor coefficient is the same selected root-adjoined C colimit. -/
theorem nextPrefixBirthPredecessor_right :
    (birthPredecessor chi A (B ⊔ LowerSet.Iic a)
      (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha)
      (nextPrefixLabel B a)).cocone.pt.right =
    (nextPastColimit chi A T B S a hPast i hi).cocone.pt.right :=
  congrArg (fun D => colimit D) (nextPrefixBirthAdjoined chi A T B S a hPast i hi g hg ha)

/-- The actual old-to-new arrow retains every coefficient and root map from its original leg. -/
theorem nextPrefixBirthMap_heq (b : LowerSet.Iio a) :
    HEq
      ((nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha).map
        (birthPastArrow (B ⊔ LowerSet.Iic a) (nextPrefixLabel B a) b))
      (nextBirthLeg chi A T B S a hPast i hi g b) := by
  let Q := nextComparedDiagram chi A T B S a hPast i hi g hg ha
  let x := (birthPastInclusion (B ⊔ LowerSet.Iic a) (nextPrefixLabel B a)).obj b
  let y := nextPrefixLabel B a
  let f : x ⟶ y := birthPastArrow (B ⊔ LowerSet.Iic a) (nextPrefixLabel B a) b
  have hx := extensionObject_old B a hPast (S.comparedDiagram chi A T)
    (nextBirthComparedCocone chi A T B S a hPast i hi g hg) x (memOfLE hPast b.2)
  have hy := extensionObject_new B a hPast (S.comparedDiagram chi A T)
    (nextBirthComparedCocone chi A T B S a hPast i hi g hg) y ha
  have hf := extensionMap_mixed B a ha hPast (S.comparedDiagram chi A T)
    (nextBirthComparedCocone chi A T B S a hPast i hi g hg) f (memOfLE hPast b.2) ha
  exact mapArrow_heq (Comma.fst (originalBaseChange chi A) T.diagram) hx hy hf

/-- Transposing the actual selected birth leg gives the same full colimit-to-cell factor. -/
theorem nextBirthLeg_transpose (b : LowerSet.Iio a) :
    (transposeMovingMap chi A (nextBirthLeg chi A T B S a hPast i hi g b)).right =
      ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫
      (newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right := by
  apply pushout.hom_ext
  · exact pushout.inl_desc _ _ _
  · have h := Under.w ((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b ≫
      newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g)
    exact (pushout.inr_desc _ _ _).trans h.symm

/-- The entire new structural leg equals the actual old colimit leg and original cell factor. -/
theorem nextPrefixBirthLeg_heq (b : LowerSet.Iio a) :
    HEq
      (birthPredecessorLeg chi A (B ⊔ LowerSet.Iic a)
        (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha)
        (nextPrefixLabel B a) b).right
      (((nextPastColimit chi A T B S a hPast i hi).cocone.ι.app b).right ≫
        (newVertexMap chi A T a i
          (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right) := by
  have hU := Functor.congr_obj
    (nextPrefixBirthDiagram_past chi A T B S a hPast i hi g hg ha) b
  have hV := nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha
  have hf := nextPrefixBirthMap_heq chi A T B S a hPast i hi g hg ha b
  have h := transposeMovingMap_heq chi A hU hV hf
  exact h.trans (heq_of_eq (nextBirthLeg_transpose chi A T B S a hPast i hi g b))

/-- The full structural predecessor map is the constructed cell map after true transports. -/
theorem nextPrefixBirthPredecessorMap_right :
    (birthPredecessorMap chi A (B ⊔ LowerSet.Iic a)
      (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha)
      (nextPrefixLabel B a)).right =
    eqToHom (nextPrefixBirthPredecessor_right chi A T B S a hPast i hi g hg ha) ≫
      (newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g).right ≫
    eqToHom (congrArg Comma.right
      (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha)).symm := by
  let D := nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha
  let a' := nextPrefixLabel B a
  let F := UnderColimits.adjoinedDiagram
    (Y := birthPredecessorDiagram chi A (B ⊔ LowerSet.Iic a) D a')
  let G := UnderColimits.adjoinedDiagram (Y := nextPastAtRoot chi A T B S a hPast i hi)
  let v := newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g
  let hF : F = G := nextPrefixBirthAdjoined chi A T B S a hPast i hi g hg ha
  let hV := nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha
  apply (colimit.isColimit F).hom_ext
  intro j
  cases j with
  | star =>
      have hActual : colimit.ι F WithInitial.star ≫
          (birthPredecessorMap chi A (B ⊔ LowerSet.Iic a) D a').right = (D.obj a').hom :=
        Under.w (birthPredecessorMap chi A (B ⊔ LowerSet.Iic a) D a')
      have hOld : colimit.ι G WithInitial.star ≫ v.right =
          (nextBirthVertex chi A T B S a hPast i hi g).hom := Under.w v
      have hHom : HEq (D.obj a').hom
          (nextBirthVertex chi A T B S a hPast i hi g).hom := movingHom_heq chi A hV
      exact hActual.trans (colimitEquality_factor hF (congrArg Comma.right hV) v.right
        WithInitial.star (D.obj a').hom (hHom.trans (heq_of_eq hOld.symm))).symm
  | of b =>
      have hActual : colimit.ι F (WithInitial.of b) ≫
          (birthPredecessorMap chi A (B ⊔ LowerSet.Iic a) D a').right =
          (birthPredecessorLeg chi A (B ⊔ LowerSet.Iic a) D a' b).right :=
        congrArg Under.Hom.right (birthPredecessorMap_fac chi A (B ⊔ LowerSet.Iic a) D a' b)
      have hHom := nextPrefixBirthLeg_heq chi A T B S a hPast i hi g hg ha b
      exact hActual.trans (colimitEquality_factor hF (congrArg Comma.right hV) v.right
        (WithInitial.of b) (birthPredecessorLeg chi A (B ⊔ LowerSet.Iic a) D a' b).right hHom).symm

/-- The entire actual newly attached birth cell has its full derived pushout square. -/
theorem nextPrefixBirthCell :
    ∃ (g' : (s (T.label a)).left ⟶
        (birthPredecessor chi A (B ⊔ LowerSet.Iic a)
          (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha)
          (nextPrefixLabel B a)).cocone.pt.right)
      (k' : (s (T.label a)).right ⟶
        ((nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha).obj
          (nextPrefixLabel B a)).right),
      IsPushout g' (s (T.label a)).hom
        (birthPredecessorMap chi A (B ⊔ LowerSet.Iic a)
          (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha)
          (nextPrefixLabel B a)).right k' := by
  let e := eqToIso (nextPrefixBirthPredecessor_right chi A T B S a hPast i hi g hg ha)
  let z := eqToIso (congrArg Comma.right
    (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha)).symm
  let v := newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g
  let k := newVertexCell chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g
  refine ⟨g ≫ e.inv, k ≫ z.hom, ?_⟩
  apply (IsPushout.of_hasPushout g (s (T.label a)).hom).of_iso
    (Iso.refl _) e.symm (Iso.refl _) z
  · exact (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have h : (birthPredecessorMap chi A (B ⊔ LowerSet.Iic a)
        (nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha) (nextPrefixLabel B a)).right =
        e.hom ≫ v.right ≫ z.hom :=
          nextPrefixBirthPredecessorMap_right chi A T B S a hPast i hi g hg ha
    exact ((congrArg (fun m => e.inv ≫ m) h).trans (e.inv_hom_id_assoc _)).symm
  · exact (Category.id_comp _).symm

omit [HasColimitsOfSize.{w, w} C] in
/-- Transporting an actual compared object to its equal original label retains the entire object. -/
theorem comparedLabelObject_eq (U : Comma (originalBaseChange chi A) T.diagram) (b : P)
    (h : U.right = b) :
    ({ left := U.left, right := b,
        hom := U.hom ≫ eqToHom (congrArg T.diagram.obj h) } :
      Comma (originalBaseChange chi A) T.diagram) = U := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

/-- The entire actual successor core is constructed with its same original vertex comparison. -/
abbrev nextPrefixCore : PrefixCore chi A T (B ⊔ LowerSet.Iic a) where
  diagram := nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha
  comparison := nextPrefixOriginalIso chi A T B S a hPast i hi g hg ha

/-- The successor core retains the complete actual old and new compared diagram. -/
theorem nextPrefixCore_comparedDiagram :
    (nextPrefixCore chi A T B S a hPast i hi g hg ha).comparedDiagram chi A T =
      nextComparedDiagram chi A T B S a hPast i hi g hg ha := by
  let Q := nextComparedDiagram chi A T B S a hPast i hi g hg ha
  let hLabels := nextComparedDiagram_labels chi A T B S a hPast i hi g hg ha
  have hObj : ∀ b,
      ((nextPrefixCore chi A T B S a hPast i hi g hg ha).comparedDiagram chi A T).obj b =
        Q.obj b := by
    intro b
    let hLabel : (Q.obj b).right = b.1 := Functor.congr_obj hLabels b
    have hComponent :
        (nextPrefixOriginalIso chi A T B S a hPast i hi g hg ha).hom.app b =
        (Q.obj b).hom ≫ eqToHom (congrArg T.diagram.obj hLabel) := by
      change (Q.obj b).hom ≫
        (eqToHom (congrArg (fun F => F ⋙ T.diagram) hLabels)).app b = _
      rw [eqToHom_app]
    exact (congrArg (fun m : (originalBaseChange chi A).obj (Q.obj b).left ⟶ T.diagram.obj b.1 =>
      (Comma.mk (Q.obj b).left b.1 m : Comma (originalBaseChange chi A) T.diagram))
      hComponent).trans (comparedLabelObject_eq chi A T (Q.obj b) b.1 hLabel)
  refine Functor.ext hObj (fun b d f => ?_)
  have hb : (eqToHom (hObj b)).left = 𝟙 (Q.obj b).left :=
    (Comma.eqToHom_left _ _ _ _ (hObj b)).trans (eqToHom_refl _ _)
  have hd : (eqToHom (hObj d).symm).left = 𝟙 (Q.obj d).left :=
    (Comma.eqToHom_left _ _ _ _ (hObj d).symm).trans (eqToHom_refl _ _)
  apply Comma.hom_ext
  · have h : 𝟙 (Q.obj b).left ≫ (Q.map f).left ≫ 𝟙 (Q.obj d).left = (Q.map f).left :=
      (Category.id_comp _).trans (Category.comp_id _)
    exact h.symm.trans (congrArg₂ (fun l r => l ≫ (Q.map f).left ≫ r) hb hd).symm
  · exact Subsingleton.elim _ _

/-- The complete original preceding core is retained by the actual successor restriction. -/
theorem nextPrefixCore_restrict :
    (nextPrefixCore chi A T B S a hPast i hi g hg ha).restrict chi A T
      (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) = S.core chi A T := by
  apply PrefixCore.comparedDiagram_injective chi A T
  exact ((nextPrefixCore chi A T B S a hPast i hi g hg ha).comparedDiagram_restrict chi A T
    (le_sup_left : B ≤ B ⊔ LowerSet.Iic a)).trans
      ((congrArg (fun F => lowerInclusion (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) ⋙ F)
        (nextPrefixCore_comparedDiagram chi A T B S a hPast i hi g hg ha)).trans
          (nextComparedDiagram_restrict chi A T B S a hPast i hi g hg ha))

/-- The complete canonical original birth map is the same actual old original past map. -/
theorem nextPrefixCore_birthOriginalMap_heq :
    HEq
      ((nextPrefixCore chi A T B S a hPast i hi g hg ha).birthOriginalMap chi A T
        (nextPrefixLabel B a)).right
      (nextPastOriginalMap chi A T B S a hPast i hi).right := by
  let N := nextPrefixCore chi A T B S a hPast i hi g hg ha
  let a' := nextPrefixLabel B a
  have hData := nextPrefixBirthDiagram_past chi A T B S a hPast i hi g hg ha
  have hEta := PrefixCore.whiskerComparison_heq chi A T
    (nextPrefixCore_restrict chi A T B S a hPast i hi g hg ha) (nextPastInclusion B a hPast)
  have hRoot := congrArg Comma.left
    (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha)
  exact originalPastMap_heq chi A (birthPastDiagram chi A (B ⊔ LowerSet.Iic a) N.diagram a')
    (restriction T.diagram (LowerSet.Iio a))
    (Functor.isoWhiskerLeft (birthPastInclusion (B ⊔ LowerSet.Iic a) a') N.comparison)
    (T.predecessor a) (N.diagram.obj a').left
    (birthPastRootBound chi A (B ⊔ LowerSet.Iic a) N.diagram a') hData hEta hRoot

/-- The full canonical new original birth map is retained after actual point equality. -/
theorem nextPrefixCore_birthOriginalMap_right :
    ((nextPrefixCore chi A T B S a hPast i hi g hg ha).birthOriginalMap chi A T
      (nextPrefixLabel B a)).right =
    eqToHom (nextPrefixBirthPredecessor_right chi A T B S a hPast i hi g hg ha) ≫
      (nextPastOriginalMap chi A T B S a hPast i hi).right := by
  have h := (conj_eqToHom_iff_heq
    ((nextPrefixCore chi A T B S a hPast i hi g hg ha).birthOriginalMap chi A T
      (nextPrefixLabel B a)).right
    (nextPastOriginalMap chi A T B S a hPast i hi).right
    (nextPrefixBirthPredecessor_right chi A T B S a hPast i hi g hg ha) rfl).mpr
      (nextPrefixCore_birthOriginalMap_heq chi A T B S a hPast i hi g hg ha)
  exact h.trans (congrArg
    (fun m => eqToHom (nextPrefixBirthPredecessor_right chi A T B S a hPast i hi g hg ha) ≫ m)
    (Category.comp_id (nextPastOriginalMap chi A T B S a hPast i hi).right))

/-- The actual complete compared object at the original new label is retained verbatim. -/
theorem nextPrefixCore_comparedPoint :
    ((nextPrefixCore chi A T B S a hPast i hi g hg ha).comparedDiagram chi A T).obj
      (nextPrefixLabel B a) = nextBirthComparedPoint chi A T B S a hPast i hi g hg :=
  (Functor.congr_obj (nextPrefixCore_comparedDiagram chi A T B S a hPast i hi g hg ha)
    (nextPrefixLabel B a)).trans
      (extensionObject_new B a hPast (S.comparedDiagram chi A T)
        (nextBirthComparedCocone chi A T B S a hPast i hi g hg) (nextPrefixLabel B a) ha)

/-- Both new-vertex coefficient functions retain the same original function after true transport. -/
theorem nextPrefixCore_comparedCoefficientMap :
    PrefixCore.comparedCoefficientMap chi A T
      (((nextPrefixCore chi A T B S a hPast i hi g hg ha).comparedDiagram chi A T).obj
        (nextPrefixLabel B a)) =
    eqToHom (congrArg Comma.right
      (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha)) ≫
      PrefixCore.comparedCoefficientMap chi A T
        (nextBirthComparedPoint chi A T B S a hPast i hi g hg) := by
  have h := (conj_eqToHom_iff_heq
    (PrefixCore.comparedCoefficientMap chi A T
      (((nextPrefixCore chi A T B S a hPast i hi g hg ha).comparedDiagram chi A T).obj
        (nextPrefixLabel B a)))
    (PrefixCore.comparedCoefficientMap chi A T
      (nextBirthComparedPoint chi A T B S a hPast i hi g hg))
    (congrArg Comma.right (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha)) rfl).mpr
      (PrefixCore.comparedCoefficientMap_heq chi A T
        (nextPrefixCore_comparedPoint chi A T B S a hPast i hi g hg ha))
  exact h.trans (congrArg
    (fun m => eqToHom (congrArg Comma.right
      (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha)) ≫ m)
    (Category.comp_id (PrefixCore.comparedCoefficientMap chi A T
      (nextBirthComparedPoint chi A T B S a hPast i hi g hg))))

/-- The successor retains its same generator, full pushout and both original cell functions. -/
theorem nextPrefixCore_birthCell :
    (nextPrefixCore chi A T B S a hPast i hi g hg ha).BirthCell chi A T (nextPrefixLabel B a) := by
  let N := nextPrefixCore chi A T B S a hPast i hi g hg ha
  let e := eqToIso (nextPrefixBirthPredecessor_right chi A T B S a hPast i hi g hg ha)
  let z := eqToIso (congrArg Comma.right
    (nextPrefixBirthDiagram_vertex chi A T B S a hPast i hi g hg ha)).symm
  let v := newVertexMap chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g
  let k := newVertexCell chi A T a i (nextPastColimit chi A T B S a hPast i hi).cocone.pt g
  refine ⟨g ≫ e.inv, k ≫ z.hom, ?_, ?_, ?_⟩
  · apply (IsPushout.of_hasPushout g (s (T.label a)).hom).of_iso
      (Iso.refl _) e.symm (Iso.refl _) z
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · have h : (birthPredecessorMap chi A (B ⊔ LowerSet.Iic a) N.diagram
          (nextPrefixLabel B a)).right = e.hom ≫ v.right ≫ z.hom :=
        nextPrefixBirthPredecessorMap_right chi A T B S a hPast i hi g hg ha
      exact ((congrArg (fun m => e.inv ≫ m) h).trans (e.inv_hom_id_assoc _)).symm
    · exact (Category.id_comp _).symm
  · have h₁ := (Category.assoc g e.inv
      (N.birthOriginalMap chi A T (nextPrefixLabel B a)).right).trans
        (congrArg (fun m => g ≫ m)
          (congrArg (fun m => e.inv ≫ m)
            (nextPrefixCore_birthOriginalMap_right chi A T B S a hPast i hi g hg ha)))
    have h₂ := congrArg (fun m => g ≫ m)
      (e.inv_hom_id_assoc (nextPastOriginalMap chi A T B S a hPast i hi).right)
    exact h₁.trans (h₂.trans hg)
  · let m := PrefixCore.comparedCoefficientMap chi A T
      (nextBirthComparedPoint chi A T B S a hPast i hi g hg)
    have h₁ := (Category.assoc k z.hom
      (PrefixCore.comparedCoefficientMap chi A T
        ((N.comparedDiagram chi A T).obj (nextPrefixLabel B a)))).trans
          (congrArg (fun m' => k ≫ m')
            (congrArg (fun m' => z.hom ≫ m')
              (nextPrefixCore_comparedCoefficientMap chi A T B S a hPast i hi g hg ha)))
    have h₂ := congrArg (fun m' => k ≫ m') (z.hom_inv_id_assoc m)
    have h₃ : k ≫ m = T.cell a :=
      newVertexOriginalIso_cell chi A T a i
        (nextPastColimit chi A T B S a hPast i hi).cocone.pt
        (nextPastOriginalComparison chi A T B S a hPast i hi) g
        (nextBirthFactorEquation chi A T B S a hPast i hi g hg)
    exact h₁.trans (h₂.trans h₃)

/-- Internally construct the entire next prefix, deriving each old and new birth-cell square. -/
abbrev nextPrefixLift : PrefixLift chi A T (B ⊔ LowerSet.Iic a) where
  diagram := nextPrefixBirthDiagram chi A T B S a hPast i hi g hg ha
  comparison := nextPrefixOriginalIso chi A T B S a hPast i hi g hg ha
  cell b := by
    classical
    let N := nextPrefixCore chi A T B S a hPast i hi g hg ha
    by_cases hb : b.1 ∈ B
    · let b' : B := ⟨b.1, hb⟩
      have hOld : (S.core chi A T).BirthCell chi A T b' := S.cell b'
      have hRestrict := nextPrefixCore_restrict chi A T B S a hPast i hi g hg ha
      have hBuilt : (N.restrict chi A T
          (le_sup_left : B ≤ B ⊔ LowerSet.Iic a)).BirthCell chi A T b' :=
        Eq.mpr (congrArg (fun R => R.BirthCell chi A T b') hRestrict) hOld
      exact (N.birthCell_restrict chi A T (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) b').mp hBuilt
    · have hLabel : b = nextPrefixLabel B a := Subtype.ext (extension_label B a hPast hb)
      subst b
      exact nextPrefixCore_birthCell chi A T B S a hPast i hi g hg ha

/-- The whole constructed successor state retains every actual old and new original comparison. -/
theorem nextPrefixLift_comparedDiagram :
    (nextPrefixLift chi A T B S a hPast i hi g hg ha).comparedDiagram chi A T =
      nextComparedDiagram chi A T B S a hPast i hi g hg ha := by
  let Q := nextComparedDiagram chi A T B S a hPast i hi g hg ha
  let hLabels := nextComparedDiagram_labels chi A T B S a hPast i hi g hg ha
  have hObj : ∀ b,
      ((nextPrefixLift chi A T B S a hPast i hi g hg ha).comparedDiagram chi A T).obj b =
        Q.obj b := by
    intro b
    let hLabel : (Q.obj b).right = b.1 := Functor.congr_obj hLabels b
    have hComponent :
        (nextPrefixOriginalIso chi A T B S a hPast i hi g hg ha).hom.app b =
        (Q.obj b).hom ≫ eqToHom (congrArg T.diagram.obj hLabel) := by
      change (Q.obj b).hom ≫
        (eqToHom (congrArg (fun F => F ⋙ T.diagram) hLabels)).app b = _
      rw [eqToHom_app]
    exact (congrArg (fun m : (originalBaseChange chi A).obj (Q.obj b).left ⟶ T.diagram.obj b.1 =>
      (Comma.mk (Q.obj b).left b.1 m : Comma (originalBaseChange chi A) T.diagram))
      hComponent).trans
        (comparedLabelObject_eq chi A T (Q.obj b) b.1 hLabel)
  refine Functor.ext hObj (fun b d f => ?_)
  have hb : (eqToHom (hObj b)).left = 𝟙 (Q.obj b).left :=
    (Comma.eqToHom_left _ _ _ _ (hObj b)).trans (eqToHom_refl _ _)
  have hd : (eqToHom (hObj d).symm).left = 𝟙 (Q.obj d).left :=
    (Comma.eqToHom_left _ _ _ _ (hObj d).symm).trans (eqToHom_refl _ _)
  apply Comma.hom_ext
  · have h : 𝟙 (Q.obj b).left ≫ (Q.map f).left ≫ 𝟙 (Q.obj d).left = (Q.map f).left :=
      (Category.id_comp _).trans (Category.comp_id _)
    have hRight := congrArg₂ (fun l r => l ≫ (Q.map f).left ≫ r) hb hd
    exact h.symm.trans hRight.symm
  · exact Subsingleton.elim _ _

/-- Exact successor restriction retains the complete preceding state, including all inverse maps. -/
theorem nextPrefixLift_restrict :
    (nextPrefixLift chi A T B S a hPast i hi g hg ha).restrict chi A T
      (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) = S := by
  apply PrefixLift.comparedDiagram_injective chi A T
  exact ((nextPrefixLift chi A T B S a hPast i hi g hg ha).comparedDiagram_restrict chi A T
    (le_sup_left : B ≤ B ⊔ LowerSet.Iic a)).trans
      ((congrArg (fun F => lowerInclusion (le_sup_left : B ≤ B ⊔ LowerSet.Iic a) ⋙ F)
        (nextPrefixLift_comparedDiagram chi A T B S a hPast i hi g hg ha)).trans
          (nextComparedDiagram_restrict chi A T B S a hPast i hi g hg ha))

end ActualNewBirthCocones

section InternallyConstructedWholeLift

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {P : Type w} [PartialOrder P] [WellFoundedLT P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))
  (hP : HasCardinalLT P chi)
  (hSource : ∀ a : P, IsCardinalPresentable (s (T.label a)).left chi)

attribute [local instance] labelExtensionWellFounded constructionIndexWellFounded
  constructionIndexSuccOrder

include hP in
omit [Fact chi.IsRegular] in
/-- Every actual original prefix is bounded by its injection into the same old label carrier. -/
theorem originalPrefix_bound (gamma : ConstructionIndex P) :
    HasCardinalLT (originalPrefix gamma) chi :=
  hP.of_injective Subtype.val Subtype.val_injective

include hP hSource in
/-- A true original birth stage extends by the same generator, preserving its complete old state. -/
theorem originalPrefix_label_extension (a : P)
    (S : PrefixLift chi A T (originalPrefix (constructionLabel a))) :
    ∃ R : PrefixLift chi A T (originalPrefix (Order.succ (constructionLabel a))),
      R.restrict chi A T (originalPrefix_mono (Order.le_succ (constructionLabel a))) = S := by
  let B := originalPrefix (constructionLabel a)
  let i := commonPrefixRoot chi A T S (originalPrefix_bound chi hP (constructionLabel a))
  let hi := commonPrefixRoot_bound chi A T S (originalPrefix_bound chi hP (constructionLabel a))
  let hPast := predecessor_le_originalPrefix a
  let : IsCardinalPresentable (s (T.label a)).left chi := hSource a
  obtain ⟨j, hij, g, hg⟩ := exists_nextAttaching chi A T B S a hPast i hi
  let R := nextPrefixLift chi A T B S a hPast j (fun b => (hi b).trans hij) g hg
    (notMem_originalPrefix_label a)
  let hEq := (originalPrefix_succ_label a).symm
  refine ⟨Eq.mp (congrArg (fun E => PrefixLift chi A T E) hEq) R, ?_⟩
  exact (PrefixLift.transport_restrict chi A T hEq R
    (originalPrefix_mono (Order.le_succ (constructionLabel a)))).trans
      (nextPrefixLift_restrict chi A T B S a hPast j (fun b => (hi b).trans hij) g hg
        (notMem_originalPrefix_label a))

omit [PartialOrder P] [WellFoundedLT P] in
/-- The actual stage carrier consists of its two end stages and the same literal old labels. -/
theorem constructionIndex_cases (gamma : ConstructionIndex P) :
    gamma = ⊥ ∨ gamma = ⊤ ∨ ∃ a : P, gamma = constructionLabel a := by
  cases gamma with
  | none => exact Or.inl rfl
  | some gamma =>
    cases gamma with
    | top => exact Or.inr (Or.inl rfl)
    | coe q =>
      refine Or.inr (Or.inr ⟨(toWellOrderExtension : P ≃ WellOrderExtension P).symm q, ?_⟩)
      simp only [constructionLabel, Equiv.apply_symm_apply,
        WithBot.some_eq_coe]

include hP hSource in
/-- Each actual nonmaximal stage has a full internally constructed successor lift. -/
theorem originalPrefix_successor_extension (gamma : ConstructionIndex P) (hgamma : ¬IsMax gamma)
    (S : PrefixLift chi A T (originalPrefix gamma)) :
    ∃ R : PrefixLift chi A T (originalPrefix (Order.succ gamma)),
      R.restrict chi A T (originalPrefix_mono (Order.le_succ gamma)) = S := by
  rcases constructionIndex_cases gamma with rfl | rfl | ⟨a, rfl⟩
  · let hEq : originalPrefix (⊥ : ConstructionIndex P) = originalPrefix (Order.succ ⊥) :=
      originalPrefix_bot.trans originalPrefix_succ_bot.symm
    refine ⟨Eq.mp (congrArg (fun E => PrefixLift chi A T E) hEq) S, ?_⟩
    exact (PrefixLift.transport_restrict chi A T hEq S
      (originalPrefix_mono (Order.le_succ (⊥ : ConstructionIndex P)))).trans
        (PrefixLift.restrict_id chi A T S)
  · exact False.elim (hgamma isMax_top)
  · exact originalPrefix_label_extension chi A T hP hSource a S

/-- The entire successor and limit programme supplies the native well-order induction data. -/
abbrev originalPrefixInductionData :
    (originalPrefixLiftFunctor chi A T).WellOrderInductionData :=
  Functor.WellOrderInductionData.ofExists
    (fun gamma hgamma S => originalPrefix_successor_extension chi A T hP hSource gamma hgamma S)
    (fun gamma hgamma x =>
      ⟨limitPrefixLift chi A T gamma hgamma x,
        fun delta hdelta => limitPrefixLift_restrict chi A T gamma hgamma x ⟨delta, hdelta⟩⟩)

/-- The genuine first stage is the actual empty-prefix state, with no supplied coherent lift. -/
abbrev originalPrefixSeed :
    (originalPrefixLiftFunctor chi A T).obj (Opposite.op (⊥ : ConstructionIndex P)) :=
  Eq.mpr (congrArg (fun B => PrefixLift chi A T B) originalPrefix_bot) (emptyPrefixLift chi A T)

/-- Internally construct the compatible original-prefix section by native well-order recursion. -/
def originalPrefixSection : (originalPrefixLiftFunctor chi A T).sections :=
  (originalPrefixInductionData chi A T hP hSource).sectionsMk (originalPrefixSeed chi A T)

/-- The final internally constructed state retains every original label and original comparison. -/
abbrev wholeOriginalLift : PrefixLift chi A T (⊤ : LowerSet P) :=
  Eq.mp (congrArg (fun B => PrefixLift chi A T B) originalPrefix_top)
    ((originalPrefixSection chi A T hP hSource).val (Opposite.op (⊤ : ConstructionIndex P)))

end InternallyConstructedWholeLift

section LiteralTopLabelTransport

variable {P : Type w} [PartialOrder P]

/-- The actual full lower subtype has exactly the original label order. -/
def topLabelOrderIso : P ≃o (⊤ : LowerSet P) where
  toFun a := ⟨a, by trivial⟩
  invFun a := a.1
  left_inv a := rfl
  right_inv a := by apply Subtype.ext; rfl
  map_rel_iff' := by intro a b; rfl

/-- Strict predecessors retain the same original labels in the full lower subtype. -/
def topPredecessorOrderIso (a : P) :
    LowerSet.Iio a ≃o LowerSet.Iio (topLabelOrderIso a) where
  toFun b := ⟨topLabelOrderIso b.1, b.2⟩
  invFun b := ⟨b.1.1, b.2⟩
  left_inv b := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; apply Subtype.ext; rfl
  map_rel_iff' := by intro b c; rfl

variable {Y : C} {alpha : Type t} {s : alpha → Arrow C}
  (R : CellTree s Y (P := (⊤ : LowerSet P)))

/-- Reindex the whole actual compact-root diagram on literal original labels. -/
abbrev literalTopDiagram : P ⥤ Under Y :=
  topLabelOrderIso.equivalence.functor ⋙ R.diagram

/-- Whisker each true predecessor cocone by the actual strict-predecessor equivalence. -/
abbrev literalTopPredecessor (a : P) :
    ColimitCocone (restriction (literalTopDiagram R) (LowerSet.Iio a)) where
  cocone := (R.predecessor (topLabelOrderIso a)).cocone.whisker
    (topPredecessorOrderIso a).equivalence.functor
  isColimit := (R.predecessor (topLabelOrderIso a)).isColimit.whiskerEquivalence
    (topPredecessorOrderIso a).equivalence

/-- The true predecessor UP preserves the entire original structural map after reindexing. -/
theorem literalTopPredecessorMap (a : P) :
    cellTreePredecessorMap (literalTopDiagram R) a (literalTopPredecessor R a) =
      R.predecessorMap (topLabelOrderIso a) := by
  apply (R.predecessor (topLabelOrderIso a)).isColimit.hom_ext
  intro b
  obtain ⟨b', rfl⟩ := (topPredecessorOrderIso a).surjective b
  exact (cellTreePredecessorMap_fac (literalTopDiagram R) a
    (literalTopPredecessor R a) b').trans
      (R.predecessorMap_fac (topLabelOrderIso a) ((topPredecessorOrderIso a) b')).symm

/-- The entire compact-root tree on the literal original partial order, with actual cocones. -/
def literalTopTree : CellTree s Y (P := P) where
  wellFounded := InvImage.wf (fun a : P => topLabelOrderIso a) R.wellFounded
  diagram := literalTopDiagram R
  label a := R.label (topLabelOrderIso a)
  predecessor a := literalTopPredecessor R a
  attaching a := R.attaching (topLabelOrderIso a)
  cell a := R.cell (topLabelOrderIso a)
  isPushout a := by
    rw [literalTopPredecessorMap]
    exact R.isPushout (topLabelOrderIso a)
  endpoint :=
    { cocone := R.endpoint.cocone.whisker topLabelOrderIso.equivalence.functor
      isColimit := R.endpoint.isColimit.whiskerEquivalence topLabelOrderIso.equivalence }

/-- Every literal vertex keeps its entire actual Under object. -/
theorem literalTopTree_vertex_function :
    (fun a : P => (literalTopTree R).vertex a) =
      (fun a : P => R.vertex (topLabelOrderIso a)) := rfl

/-- The full original Hom function is transported by the actual label equivalence. -/
theorem literalTopTree_map_function :
    (fun (a b : P) (f : a ⟶ b) => (literalTopTree R).diagram.map f) =
      (fun (a b : P) (f : a ⟶ b) =>
        R.diagram.map (topLabelOrderIso.equivalence.functor.map f)) := rfl

/-- The complete predecessor point function retains its actual selected objects and roots. -/
theorem literalTopTree_predecessor_function :
    (fun a : P => (literalTopTree R).predecessorObj a) =
      (fun a : P => R.predecessorObj (topLabelOrderIso a)) := rfl

/-- Every original strict-predecessor leg retains its whole actual Under morphism. -/
theorem literalTopTree_predecessor_leg_function (a : P) :
    (fun b : LowerSet.Iio a => ((literalTopTree R).predecessor a).cocone.ι.app b) =
      (fun b : LowerSet.Iio a =>
        (R.predecessor (topLabelOrderIso a)).cocone.ι.app ((topPredecessorOrderIso a) b)) := rfl

/-- The whole attaching function is retained on its actual original dependent source types. -/
theorem literalTopTree_attaching_function :
    (fun a : P => (literalTopTree R).attaching a) =
      (fun a : P => R.attaching (topLabelOrderIso a)) := rfl

/-- The whole target-cell function is retained on its actual original dependent target types. -/
theorem literalTopTree_cell_function :
    (fun a : P => (literalTopTree R).cell a) =
      (fun a : P => R.cell (topLabelOrderIso a)) := rfl

/-- Whiskering the true full cocone preserves the actual endpoint and root map. -/
theorem literalTopTree_endpoint : (literalTopTree R).endpointObj = R.endpointObj := rfl

/-- All actual original endpoint legs survive the literal-label transport. -/
theorem literalTopTree_endpoint_leg_function :
    (fun a : P => (literalTopTree R).inclusion a) =
      (fun a : P => R.inclusion (topLabelOrderIso a)) := rfl

variable {K : Type uJ} [Category.{vJ} K]

/-- The full lower subtype and its actual label equivalence recover the entire original functor. -/
theorem topRestrictionIdentity (F : P ⥤ K) :
    topLabelOrderIso.equivalence.functor ⋙ restriction F (⊤ : LowerSet P) = F := by
  apply Functor.hext
  · intro a
    rfl
  · intro a b f
    exact heq_of_eq (congrArg F.map (Subsingleton.elim _ _))

variable [HasPushouts C] {X : C} (r : Y ⟶ X) (T : CellTree s X (P := P))
  (eta : R.diagram ⋙ Under.pushout r ≅ restriction T.diagram (⊤ : LowerSet P))

/-- The whole original comparison, including its inverse, on the literal original carrier. -/
def literalTopOriginalIso : (literalTopTree R).diagram ⋙ Under.pushout r ≅ T.diagram := by
  change (topLabelOrderIso (P := P)).equivalence.functor ⋙
    (R.diagram ⋙ Under.pushout r) ≅ T.diagram
  exact Functor.isoWhiskerLeft (topLabelOrderIso (P := P)).equivalence.functor eta ≪≫
    eqToIso (topRestrictionIdentity T.diagram)

/-- The whole original forward comparison is retained at every literal label. -/
theorem literalTopOriginalIso_hom (a : P) :
    (literalTopOriginalIso R r T eta).hom.app a = eta.hom.app (topLabelOrderIso a) := by
  change eta.hom.app (topLabelOrderIso a) ≫
    (eqToHom (topRestrictionIdentity T.diagram)).app a = _
  rw [eqToHom_app]
  exact Category.comp_id _

/-- The entire original inverse comparison is retained at every literal label. -/
theorem literalTopOriginalIso_inv (a : P) :
    (literalTopOriginalIso R r T eta).inv.app a = eta.inv.app (topLabelOrderIso a) := by
  change (eqToHom (topRestrictionIdentity T.diagram).symm).app a ≫
    eta.inv.app (topLabelOrderIso a) = _
  rw [eqToHom_app]
  exact Category.id_comp _

end LiteralTopLabelTransport

section CompactRootAbsolutePresentability

variable (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- Adjoining the genuine root adds exactly one object to the actual small diagram carrier. -/
theorem rootAdjoinedObject_bound (J : Type w) (hJ : HasCardinalLT J chi) :
    HasCardinalLT (WithInitial J) chi := by
  let e : WithInitial J ≃ Option J :=
    { toFun j := match j with | .of a => some a | .star => none
      invFun j := match j with | some a => .of a | none => .star
      left_inv j := by cases j <;> rfl
      right_inv j := by cases j <;> rfl }
  exact ((hasCardinalLT_option_iff J chi (Fact.out : chi.IsRegular).aleph0_le).2 hJ).of_injective
    e e.injective

/-- The real root-adjoined arrow carrier is bounded using every one of its actual Hom types. -/
theorem rootAdjoinedArrow_bound (J : Type w) [Category.{w} J] [Quiver.IsThin J]
    (hJ : HasCardinalLT J chi) : HasCardinalLT (Arrow (WithInitial J)) chi := by
  let : Quiver.IsThin (WithInitial J) := fun a b => by
    cases a with
    | of a =>
      cases b with
      | of b => change Subsingleton (a ⟶ b); infer_instance
      | star => change Subsingleton PEmpty; infer_instance
    | star =>
      cases b with
      | of b => change Subsingleton PUnit; infer_instance
      | star => change Subsingleton PUnit; infer_instance
  exact (hasCardinalLT_arrow_iff_of_isThin (WithInitial J) chi
    (Fact.out : chi.IsRegular).aleph0_le).2 (rootAdjoinedObject_bound chi J hJ)

variable [LocallySmall.{w} C]

/-- The actual root-adjoined C colimit is compact from its compact root and every coefficient. -/
theorem compactRootColimit {Y : C} [IsCardinalPresentable Y chi]
    {J : Type w} [Category.{w} J] [Quiver.IsThin J] (D : J ⥤ Under Y)
    (c : ColimitCocone D) (hJ : HasCardinalLT J chi)
    (hObj : ∀ j : J, IsCardinalPresentable (D.obj j).right chi) :
    IsCardinalPresentable c.cocone.pt.right chi := by
  have (j : WithInitial J) :
      IsCardinalPresentable ((UnderColimits.adjoinedDiagram (Y := D)).obj j) chi := by
    cases j with
    | star => exact ‹IsCardinalPresentable Y chi›
    | of j => exact hObj j
  exact isCardinalPresentable_of_isColimit (UnderColimits.adjoinedColimit c).cocone
    (UnderColimits.adjoinedColimit c).isColimit chi (rootAdjoinedArrow_bound chi J hJ)

variable {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  {Y : C} [IsCardinalPresentable Y chi] (R : CellTree s Y (P := P))
  (hSource : ∀ a : P, IsCardinalPresentable (s (R.label a)).left chi)
  (hTarget : ∀ a : P, IsCardinalPresentable (s (R.label a)).right chi)
  (hPred : ∀ a : P, HasCardinalLT (LowerSet.Iio a) chi)

include hSource hTarget hPred in
/-- Original well-founded recursion proves absolute compactness of the new compact-root vertices. -/
theorem compactRootVertex (a : P) : IsCardinalPresentable (R.vertex a).right chi := by
  refine R.wellFounded.induction
    (C := fun b : P => IsCardinalPresentable (R.vertex b).right chi) a ?_
  intro a ih
  have hPredecessor : IsCardinalPresentable (R.predecessorObj a).right chi :=
    compactRootColimit chi (restriction R.diagram (LowerSet.Iio a)) (R.predecessor a) (hPred a)
      (fun b => ih b.1 b.2)
  let : IsCardinalPresentable (R.predecessorObj a).right chi := hPredecessor
  let : IsCardinalPresentable (s (R.label a)).left chi := hSource a
  let : IsCardinalPresentable (s (R.label a)).right chi := hTarget a
  exact RelativeCellPresentability.ofPushout chi (R.isPushout a)

include hSource hTarget hPred in
/-- Every genuine new predecessor keeps its actual compact C point and original root-adjoined UP. -/
theorem compactRootPredecessor (a : P) :
    IsCardinalPresentable (R.predecessorObj a).right chi :=
  compactRootColimit chi (restriction R.diagram (LowerSet.Iio a)) (R.predecessor a) (hPred a)
    (fun b => compactRootVertex chi R hSource hTarget hPred b.1)

include hSource hTarget hPred in
/-- Every selected new lower piece is compact by its full root-adjoined C diagram. -/
theorem compactRootLower (L : LowerSetColimitData R.diagram) (B : LowerSet P)
    (hB : HasCardinalLT B chi) : IsCardinalPresentable (L.obj B).right chi :=
  compactRootColimit chi (restriction R.diagram B) ⟨L.cocone B, L.isColimit B⟩ hB
    (fun a => compactRootVertex chi R hSource hTarget hPred a.1)

include hSource hTarget hPred in
/-- The whole actual new endpoint is compact when the original total label carrier is bounded. -/
theorem compactRootEndpoint (hP : HasCardinalLT P chi) :
    IsCardinalPresentable R.endpointObj.right chi :=
  compactRootColimit chi R.diagram R.endpoint hP
    (compactRootVertex chi R hSource hTarget hPred)

end CompactRootAbsolutePresentability

section NativeRootPushoutComparisons

variable [HasPushouts C] {Y X : C} (r : Y ⟶ X)

/-- The actual native root pushout retains both legs after its constructed Under isomorphism. -/
theorem rootComparison_isPushout (U : Under Y) (V : Under X)
    (e : (Under.pushout r).obj U ≅ V) :
    IsPushout U.hom r (pushout.inl U.hom r ≫ e.hom.right) V.hom := by
  apply (root_isPushout r U).of_iso (Iso.refl Y) (Iso.refl U.right) (Iso.refl X)
    ((Under.forget X).mapIso e)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Functor.mapIso_hom, Under.forget_map, Category.id_comp]
  · change ((Under.pushout r).obj U).hom ≫ e.hom.right = 𝟙 X ≫ V.hom
    exact (Under.w e.hom).trans (Category.id_comp _).symm

variable {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (R : CellTree s Y (P := P)) (T : CellTree s X (P := P))
  (eta : R.diagram ⋙ Under.pushout r ≅ T.diagram)

/-- Both actual whole endpoint colimits construct the full original endpoint comparison. -/
def endpointComparison : (Under.pushout r).obj R.endpointObj ≅ T.endpointObj :=
  (isColimitOfPreserves (Under.pushout r) R.endpoint.isColimit).coconePointsIsoOfNatIso
    T.endpoint.isColimit eta

/-- Every endpoint leg is retained by the actual original comparison. -/
@[reassoc]
theorem endpointComparison_leg (a : P) :
    (Under.pushout r).map (R.inclusion a) ≫ (endpointComparison r R T eta).hom =
      eta.hom.app a ≫ T.inclusion a :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves (Under.pushout r) R.endpoint.isColimit) T.endpoint.isColimit eta a

/-- The full inverse comparison also retains every original endpoint leg. -/
@[reassoc]
theorem endpointComparison_leg_inv (a : P) :
    T.inclusion a ≫ (endpointComparison r R T eta).inv =
      eta.inv.app a ≫ (Under.pushout r).map (R.inclusion a) :=
  IsColimit.comp_coconePointsIsoOfNatIso_inv
    (isColimitOfPreserves (Under.pushout r) R.endpoint.isColimit) T.endpoint.isColimit eta a

/-- The endpoint comparison and both actual root maps form the original whole pushout. -/
theorem endpointComparison_isPushout :
    IsPushout R.hom r
      (pushout.inl R.hom r ≫ (endpointComparison r R T eta).hom.right) T.hom :=
  rootComparison_isPushout r R.endpointObj T.endpointObj (endpointComparison r R T eta)

variable (LR : LowerSetColimitData R.diagram) (L : LowerSetColimitData T.diagram)

/-- Every lower comparison and every actual B-to-D map form a whole natural isomorphism. -/
def allLowerComparison : LR.functor ⋙ Under.pushout r ≅ L.functor :=
  NatIso.ofComponents (lowerComparison r R T LR L eta)
    (fun f => lowerComparison_map r R T LR L eta (leOfHom f))

/-- The actual inverse all-lower comparison retains every map for every pair B less than D. -/
theorem lowerComparison_map_inv {B D : LowerSet P} (h : B ≤ D) :
    L.map h ≫ (lowerComparison r R T LR L eta D).inv =
      (lowerComparison r R T LR L eta B).inv ≫ (Under.pushout r).map (LR.map h) :=
  (allLowerComparison r R T eta LR L).inv.naturality (homOfLE h)

/-- The complete all-lower map function includes every original lower subset pair. -/
theorem allLowerComparison_map_function :
    (fun (B D : LowerSet P) (h : B ≤ D) =>
      (Under.pushout r).map (LR.map h) ≫ (lowerComparison r R T LR L eta D).hom) =
    (fun (B D : LowerSet P) (h : B ≤ D) =>
      (lowerComparison r R T LR L eta B).hom ≫ L.map h) := by
  funext B D h
  exact lowerComparison_map r R T LR L eta h

/-- Every actual selected lower root and its whole coefficient map form the true root pushout. -/
theorem lowerComparison_isPushout (B : LowerSet P) :
    IsPushout (LR.obj B).hom r
      (pushout.inl (LR.obj B).hom r ≫ (lowerComparison r R T LR L eta B).hom.right)
      (L.obj B).hom :=
  rootComparison_isPushout r (LR.obj B) (L.obj B) (lowerComparison r R T LR L eta B)

/-- The all-lower comparison retains the exact entire function of original root maps. -/
theorem lowerComparison_root_function :
    (fun B : LowerSet P =>
      pushout.inr (LR.obj B).hom r ≫ (lowerComparison r R T LR L eta B).hom.right) =
    (fun B : LowerSet P => (L.obj B).hom) := by
  funext B
  exact Under.w (lowerComparison r R T LR L eta B).hom

/-- Both directions preserve the complete original function of all lower root maps. -/
theorem lowerComparison_root_inv_function :
    (fun B : LowerSet P =>
      (L.obj B).hom ≫ (lowerComparison r R T LR L eta B).inv.right) =
    (fun B : LowerSet P => pushout.inr (LR.obj B).hom r) := by
  funext B
  exact Under.w (lowerComparison r R T LR L eta B).inv

/-- The actual all-lower and whole-endpoint comparisons retain the same full endpoint map. -/
theorem lowerComparison_endpoint :
    (Under.pushout r).map (R.endpointIso LR).hom ≫ (endpointComparison r R T eta).hom =
      (lowerComparison r R T LR L eta ⊤).hom ≫ (T.endpointIso L).hom := by
  let F := Under.pushout r
  apply (isColimitOfPreserves F LR.isColimitFullCocone).hom_ext
  intro a
  let b : (⊤ : LowerSet P) := ⟨a, by trivial⟩
  let l := LR.ι ⊤ b
  have hFactor : F.map l ≫ F.map (R.endpointIso LR).hom = F.map (R.inclusion a) :=
    (F.map_comp l (R.endpointIso LR).hom).symm.trans
      (congrArg F.map (R.ι_endpointIso_hom LR a))
  have hLeg : F.map l ≫ (lowerComparison r R T LR L eta ⊤).hom = eta.hom.app a ≫ L.ι ⊤ b :=
    lowerComparison_leg r R T LR L eta ⊤ b
  change F.map l ≫ (F.map (R.endpointIso LR).hom ≫ (endpointComparison r R T eta).hom) =
    F.map l ≫ ((lowerComparison r R T LR L eta ⊤).hom ≫ (T.endpointIso L).hom)
  have hLeft := (Category.assoc (F.map l) (F.map (R.endpointIso LR).hom)
    (endpointComparison r R T eta).hom).symm.trans
      ((congrArg (fun f => f ≫ (endpointComparison r R T eta).hom) hFactor).trans
        (endpointComparison_leg r R T eta a))
  have hRight := (Category.assoc (F.map l) (lowerComparison r R T LR L eta ⊤).hom
    (T.endpointIso L).hom).symm.trans
      ((congrArg (fun f => f ≫ (T.endpointIso L).hom) hLeg).trans
        ((Category.assoc (eta.hom.app a) (L.ι ⊤ b) (T.endpointIso L).hom).trans
          (congrArg (fun f => eta.hom.app a ≫ f) (T.ι_endpointIso_hom L a))))
  exact hLeft.trans hRight.symm

/-- Both directions of the entire all-lower endpoint Iso agree with the actual endpoint Iso. -/
theorem lowerComparison_endpoint_iso :
    (Under.pushout r).mapIso (R.endpointIso LR) ≪≫ endpointComparison r R T eta =
      lowerComparison r R T LR L eta ⊤ ≪≫ T.endpointIso L := by
  apply Iso.ext
  exact lowerComparison_endpoint r R T eta LR L

end NativeRootPushoutComparisons

section NativeOriginalPastCoefficientEquations

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) {J : Type w} [Category.{w} J]
  (D : J ⥤ Comma A.presentation.diag (𝟭 C)) (E : J ⥤ Under X)
  (eta : D ⋙ originalBaseChange chi A ≅ E) (c : ColimitCocone E)
  (i : A.index) (hi : ∀ b, (D.obj b).left ≤ i)

/-- Each actual past colimit leg retains its entire original comparison in Under X. -/
@[reassoc]
theorem originalPastComparison_leg (b : J) :
    (Under.pushout (A.presentation.ι.app i)).map
      ((workingUnderColimit (raisedDiagram chi A D i hi)).cocone.ι.app b) ≫
      (originalPastComparison chi A D E eta c i hi).hom =
    (originalPastIso chi A D E eta i hi).hom.app b ≫ c.cocone.ι.app b :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves (Under.pushout (A.presentation.ι.app i))
      (workingUnderColimit (raisedDiagram chi A D i hi)).isColimit)
    c.isColimit (originalPastIso chi A D E eta i hi) b

/-- Native transposition and the actual UP preserve every whole original coefficient leg. -/
@[reassoc]
theorem originalPastMap_leg (b : J) :
    ((workingUnderColimit (raisedDiagram chi A D i hi)).cocone.ι.app b).right ≫
      (originalPastMap chi A D E eta c i hi).right =
    pushout.inl ((raisedDiagram chi A D i hi).obj b).hom (A.presentation.ι.app i) ≫
      ((originalPastIso chi A D E eta i hi).hom.app b).right ≫ (c.cocone.ι.app b).right := by
  let adj := Under.mapPushoutAdj (A.presentation.ι.app i)
  have h := (adj.homEquiv_naturality_left
    ((workingUnderColimit (raisedDiagram chi A D i hi)).cocone.ι.app b)
    (originalPastComparison chi A D E eta c i hi).hom).symm.trans
      (congrArg (adj.homEquiv ((raisedDiagram chi A D i hi).obj b) c.cocone.pt)
        (originalPastComparison_leg chi A D E eta c i hi b))
  exact (congrArg Under.Hom.right h).trans
    (nativePushoutHomEquiv_right (A.presentation.ι.app i) _ _ _)

/-- Every original moving-root coefficient survives the actual past colimit and root changes. -/
@[reassoc]
theorem originalPastMap_coefficient (b : J) :
    pushout.inl (D.obj b).hom (A.presentation.diag.map (homOfLE (hi b))) ≫
      ((workingUnderColimit (raisedDiagram chi A D i hi)).cocone.ι.app b).right ≫
      (originalPastMap chi A D E eta c i hi).right =
    pushout.inl (D.obj b).hom (A.presentation.ι.app (D.obj b).left) ≫
      (eta.hom.app b).right ≫ (c.cocone.ι.app b).right := by
  let k := pushout.inl (D.obj b).hom (A.presentation.diag.map (homOfLE (hi b)))
  let l := pushout.inl ((raisedDiagram chi A D i hi).obj b).hom (A.presentation.ι.app i)
  let z := (raisedComponentIso chi A D i hi b).hom.right
  let e := (eta.hom.app b).right
  let p := (c.cocone.ι.app b).right
  let k' := pushout.inl (D.obj b).hom (A.presentation.ι.app (D.obj b).left)
  have h₁ : (k ≫ l) ≫ z = k' := raisedComponentIso_inl chi A D i hi b
  have hCompare : k ≫ l ≫ (z ≫ e) = k' ≫ e :=
    (Category.assoc k l (z ≫ e)).symm.trans
      ((Category.assoc (k ≫ l) z e).symm.trans (congrArg (fun m => m ≫ e) h₁))
  have hLeg := congrArg (fun m => k ≫ m) (originalPastMap_leg chi A D E eta c i hi b)
  change k ≫ _ ≫ _ = k' ≫ e ≫ p
  have hAssoc : k ≫ l ≫ ((z ≫ e) ≫ p) = (k ≫ l ≫ (z ≫ e)) ≫ p :=
    ((Category.assoc k (l ≫ (z ≫ e)) p).trans
      (congrArg (fun m => k ≫ m) (Category.assoc l (z ≫ e) p))).symm
  exact hLeg.trans (hAssoc.trans
    ((congrArg (fun m => m ≫ p) hCompare).trans (Category.assoc k' e p)))

end NativeOriginalPastCoefficientEquations

section NativeFlatOriginalCellComparisons

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular] {X : C}
  (A : CompactApproximation chi X) (i₀ i : A.index) (h : i₀ ≤ i)

/-- Flatten the actual birth-to-final-to-original root pushouts by the native composition Iso. -/
def approximationFlatIso (U : Under (A.presentation.diag.obj i₀)) :
    (Under.pushout (A.presentation.ι.app i)).obj
      ((Under.pushout (A.presentation.diag.map (homOfLE h))).obj U) ≅
    (Under.pushout (A.presentation.ι.app i₀)).obj U :=
  ((Under.pushoutComp (A.presentation.diag.map (homOfLE h))
    (A.presentation.ι.app i)).app U).symm ≪≫
    eqToIso (congrArg
      (fun f : A.presentation.diag.obj i₀ ⟶ X => (Under.pushout f).obj U)
      (A.presentation.w (homOfLE h)))

/-- Both actual native coefficient inclusions flatten to the original inclusion. -/
@[reassoc]
theorem approximationFlatIso_inl (U : Under (A.presentation.diag.obj i₀)) :
    (pushout.inl U.hom (A.presentation.diag.map (homOfLE h)) ≫
      pushout.inl ((Under.pushout (A.presentation.diag.map (homOfLE h))).obj U).hom
        (A.presentation.ι.app i)) ≫
      (approximationFlatIso chi A i₀ i h U).hom.right =
        pushout.inl U.hom (A.presentation.ι.app i₀) := by
  let q := A.presentation.diag.map (homOfLE h)
  let r := A.presentation.ι.app i
  let e := eqToIso (congrArg
    (fun f : A.presentation.diag.obj i₀ ⟶ X => (Under.pushout f).obj U)
    (A.presentation.w (homOfLE h)))
  have hc := pushoutComp_inl_inv q r U
  have he := pushout_eqIso_inl (q ≫ r) (A.presentation.w (homOfLE h)) U
  change (_ ≫ _) ≫ (((Under.pushoutComp q r).inv.app U).right ≫ e.hom.right) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e.hom.right) hc).trans he)

/-- The associative form retains the complete actual coefficient function. -/
@[reassoc]
theorem approximationFlatIso_inl_flat (U : Under (A.presentation.diag.obj i₀)) :
    pushout.inl U.hom (A.presentation.diag.map (homOfLE h)) ≫
      pushout.inl ((Under.pushout (A.presentation.diag.map (homOfLE h))).obj U).hom
        (A.presentation.ι.app i) ≫
      (approximationFlatIso chi A i₀ i h U).hom.right =
        pushout.inl U.hom (A.presentation.ι.app i₀) :=
  (Category.assoc _ _ _).symm.trans (approximationFlatIso_inl chi A i₀ i h U)

variable [HasColimitsOfSize.{w, w} C] {P : Type w} [PartialOrder P]
  {alpha : Type t} {s : alpha → Arrow C} (T : CellTree s X (P := P))
  (B : LowerSet P) (S : PrefixLift chi A T B) (hi : ∀ a, (S.diagram.obj a).left ≤ i)

/-- The final actual predecessor comparison uses native flat composition and the birth UP. -/
abbrev normalizedPredecessorOriginalComparison (a : B) :
    (Under.pushout (A.presentation.ι.app i)).obj
      ((normalizedTree chi A T B S i hi).predecessorObj a) ≅ T.predecessorObj a.1 :=
  approximationFlatIso chi A (S.diagram.obj a).left i (hi a)
    (birthPredecessor chi A B S.diagram a).cocone.pt ≪≫
      (S.core chi A T).birthOriginalComparison chi A T a

/-- Both final predecessor coefficient inclusions retain the actual whole original birth map. -/
theorem normalizedPredecessorOriginalComparison_unit (a : B) :
    pushout.inl (birthPredecessor chi A B S.diagram a).cocone.pt.hom
      (birthRootTransition chi A T B S i hi a) ≫
    pushout.inl ((normalizedTree chi A T B S i hi).predecessorObj a).hom
      (A.presentation.ι.app i) ≫
    (normalizedPredecessorOriginalComparison chi A i T B S hi a).hom.right =
      ((S.core chi A T).birthOriginalMap chi A T a).right := by
  let U := (birthPredecessor chi A B S.diagram a).cocone.pt
  let q := birthRootTransition chi A T B S i hi a
  let e₀ := approximationFlatIso chi A (S.diagram.obj a).left i (hi a) U
  let e := (S.core chi A T).birthOriginalComparison chi A T a
  let u₁ := pushout.inl U.hom q
  let u₂ := pushout.inl ((Under.pushout q).obj U).hom (A.presentation.ι.app i)
  have hFlat₀ : u₁ ≫ u₂ ≫ e₀.hom.right =
      pushout.inl U.hom (A.presentation.ι.app (S.diagram.obj a).left) :=
    approximationFlatIso_inl_flat chi A (S.diagram.obj a).left i (hi a) U
  have hFlat : u₁ ≫ u₂ ≫ e₀.hom.right ≫ e.hom.right =
      pushout.inl U.hom (A.presentation.ι.app (S.diagram.obj a).left) ≫ e.hom.right :=
    ((Category.assoc u₁ (u₂ ≫ e₀.hom.right) e.hom.right).trans
      (congrArg (fun f => u₁ ≫ f) (Category.assoc u₂ e₀.hom.right e.hom.right))).symm.trans
        (congrArg (fun f => f ≫ e.hom.right) hFlat₀)
  change u₁ ≫ u₂ ≫ (e₀.hom.right ≫ e.hom.right) = _
  exact hFlat.trans (nativePushoutHomEquiv_right
    (A.presentation.ι.app (S.diagram.obj a).left) U (T.predecessorObj a.1) e.hom).symm

/-- The whole normalized vertex comparison retains both actual coefficient inclusions. -/
theorem normalizedOriginalIso_coefficient (a : B) :
    pushout.inl (S.diagram.obj a).hom (birthRootTransition chi A T B S i hi a) ≫
      pushout.inl ((normalizedTree chi A T B S i hi).vertex a).hom (A.presentation.ι.app i) ≫
      ((normalizedOriginalIso chi A T B S i hi).hom.app a).right =
    pushout.inl (S.diagram.obj a).hom (A.presentation.ι.app (S.diagram.obj a).left) ≫
      (S.comparison.hom.app a).right := by
  let k := pushout.inl (S.diagram.obj a).hom (birthRootTransition chi A T B S i hi a)
  let l := pushout.inl ((normalizedTree chi A T B S i hi).vertex a).hom (A.presentation.ι.app i)
  let z := (raisedComponentIso chi A S.diagram i hi a).hom.right
  let e := (S.comparison.hom.app a).right
  have h : (k ≫ l) ≫ z =
      pushout.inl (S.diagram.obj a).hom (A.presentation.ι.app (S.diagram.obj a).left) :=
    raisedComponentIso_inl chi A S.diagram i hi a
  change k ≫ l ≫ (z ≫ e) = _
  exact (Category.assoc k l (z ≫ e)).symm.trans
    ((Category.assoc (k ≫ l) z e).symm.trans (congrArg (fun m => m ≫ e) h))

/-- Every normalized predecessor coefficient leg retains its actual birth leg and root unit. -/
theorem normalizedPredecessor_coefficient (a : B) (b : LowerSet.Iio a.1) :
    pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((birthPastInclusion B a).obj b)))) ≫
      ((normalizedBirthPredecessor chi A T B S i hi a).cocone.ι.app b).right =
    pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
      (A.presentation.diag.map (homOfLE (birthPastRootBound chi A B S.diagram a b))) ≫
      ((birthPredecessor chi A B S.diagram a).cocone.ι.app b).right ≫
      pushout.inl (birthPredecessor chi A B S.diagram a).cocone.pt.hom
        (birthRootTransition chi A T B S i hi a) := by
  let u₀ := pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
    (A.presentation.diag.map (homOfLE (birthPastRootBound chi A B S.diagram a b)))
  let u₁ := pushout.inl ((birthPredecessorDiagram chi A B S.diagram a).obj b).hom
    (birthRootTransition chi A T B S i hi a)
  let u := pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
    (A.presentation.diag.map (homOfLE (hi ((birthPastInclusion B a).obj b))))
  let e := (birthRaiseIso chi A T B S i hi a).app b
  let l := (birthPredecessor chi A B S.diagram a).cocone.ι.app b
  let m := ((Under.pushout (birthRootTransition chi A T B S i hi a)).map l).right
  have hChar : (u₀ ≫ u₁) ≫ e.hom.right = u :=
    (Category.assoc u₀ u₁ e.hom.right).trans (birthRaiseIso_inl chi A T B S i hi a b)
  have hInv : u ≫ e.inv.right = u₀ ≫ u₁ :=
    (congrArg (fun f => f ≫ e.inv.right) hChar.symm).trans
      ((Category.assoc (u₀ ≫ u₁) e.hom.right e.inv.right).trans
        ((congrArg (fun f => (u₀ ≫ u₁) ≫ f) (Under.hom_right_inv_right e)).trans
          (Category.comp_id _)))
  change u ≫ (e.inv.right ≫ m) = _
  exact (Category.assoc u e.inv.right m).symm.trans
    ((congrArg (fun f => f ≫ m) hInv).trans
      ((Category.assoc u₀ u₁ m).trans
        (congrArg (fun f => u₀ ≫ f)
          (inl_map (birthRootTransition chi A T B S i hi a) l))))

/-- Every whole normalized predecessor leg retains its actual original coefficient function. -/
theorem normalizedPredecessorOriginalComparison_coefficient (a : B) (b : LowerSet.Iio a.1) :
    pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
      (A.presentation.diag.map (homOfLE (hi ((birthPastInclusion B a).obj b)))) ≫
      ((normalizedBirthPredecessor chi A T B S i hi a).cocone.ι.app b).right ≫
      pushout.inl ((normalizedTree chi A T B S i hi).predecessorObj a).hom
        (A.presentation.ι.app i) ≫
      (normalizedPredecessorOriginalComparison chi A i T B S hi a).hom.right =
    pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
      (A.presentation.ι.app ((birthPastDiagram chi A B S.diagram a).obj b).left) ≫
      (S.comparison.hom.app ((birthPastInclusion B a).obj b)).right ≫
      ((T.predecessor a.1).cocone.ι.app b).right := by
  let u := pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
    (A.presentation.diag.map (homOfLE (hi ((birthPastInclusion B a).obj b))))
  let l := ((normalizedBirthPredecessor chi A T B S i hi a).cocone.ι.app b).right
  let v := pushout.inl ((normalizedTree chi A T B S i hi).predecessorObj a).hom
    (A.presentation.ι.app i)
  let e := (normalizedPredecessorOriginalComparison chi A i T B S hi a).hom.right
  let u₀ := pushout.inl ((birthPastDiagram chi A B S.diagram a).obj b).hom
    (A.presentation.diag.map (homOfLE (birthPastRootBound chi A B S.diagram a b)))
  let l₀ := ((birthPredecessor chi A B S.diagram a).cocone.ι.app b).right
  let u₁ := pushout.inl (birthPredecessor chi A B S.diagram a).cocone.pt.hom
    (birthRootTransition chi A T B S i hi a)
  have hLeg : u ≫ l = u₀ ≫ l₀ ≫ u₁ :=
    normalizedPredecessor_coefficient chi A i T B S hi a b
  have hUnit : u₁ ≫ v ≫ e = ((S.core chi A T).birthOriginalMap chi A T a).right :=
    normalizedPredecessorOriginalComparison_unit chi A i T B S hi a
  have hBirth := originalPastMap_coefficient chi A (birthPastDiagram chi A B S.diagram a)
    (restriction T.diagram (LowerSet.Iio a.1))
    (Functor.isoWhiskerLeft (birthPastInclusion B a) S.comparison) (T.predecessor a.1)
    (S.diagram.obj a).left (birthPastRootBound chi A B S.diagram a) b
  change u ≫ l ≫ v ≫ e = _
  have hStart : u ≫ l ≫ v ≫ e = u₀ ≫ l₀ ≫ (u₁ ≫ v ≫ e) :=
    (Category.assoc u l (v ≫ e)).symm.trans
      ((congrArg (fun f => f ≫ v ≫ e) hLeg).trans
        ((Category.assoc u₀ (l₀ ≫ u₁) (v ≫ e)).trans
          (congrArg (fun f => u₀ ≫ f) (Category.assoc l₀ u₁ (v ≫ e)))))
  exact hStart.trans ((congrArg (fun f => u₀ ≫ l₀ ≫ f) hUnit).trans hBirth)

/-- The native flat predecessor comparison retains every whole original predecessor leg. -/
@[reassoc]
theorem normalizedPredecessorOriginalComparison_leg (a : B) (b : LowerSet.Iio a) :
    (Under.pushout (A.presentation.ι.app i)).map
      (((normalizedTree chi A T B S i hi).predecessor a).cocone.ι.app b) ≫
      (normalizedPredecessorOriginalComparison chi A i T B S hi a).hom =
    (normalizedOriginalIso chi A T B S i hi).hom.app b.1 ≫
      (T.predecessor a.1).cocone.ι.app ((CellTreeLowerRestriction.predecessorOrderIso B a) b) := by
  let R := normalizedTree chi A T B S i hi
  let F := Under.pushout (A.presentation.ι.app i)
  let b' := (CellTreeLowerRestriction.predecessorOrderIso B a) b
  let l := (R.predecessor a).cocone.ι.app b
  let e := normalizedPredecessorOriginalComparison chi A i T B S hi a
  let eta := normalizedOriginalIso chi A T B S i hi
  let f := F.map l ≫ e.hom
  let g := eta.hom.app b.1 ≫ (T.predecessor a.1).cocone.ι.app b'
  have hRoot := (Under.w f).trans (Under.w g).symm
  apply Under.UnderMorphism.ext
  change f.right = g.right
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · let u := pushout.inl (S.diagram.obj b.1).hom
        (birthRootTransition chi A T B S i hi b.1)
      let v := pushout.inl (R.vertex b.1).hom (A.presentation.ι.app i)
      let p := pushout.inl (R.predecessorObj a).hom (A.presentation.ι.app i)
      let z := (eta.hom.app b.1).right
      let t := ((T.predecessor a.1).cocone.ι.app b').right
      let u' := pushout.inl (S.diagram.obj b.1).hom
        (A.presentation.ι.app (S.diagram.obj b.1).left)
      let m := (F.map l).right
      have hSquare : v ≫ m = l.right ≫ p := inl_map (A.presentation.ι.app i) l
      have hLeft : u ≫ v ≫ f.right = u ≫ l.right ≫ p ≫ e.hom.right := by
        change u ≫ v ≫ (m ≫ e.hom.right) = _
        exact (congrArg (fun q => u ≫ q) (Category.assoc v m e.hom.right).symm).trans
          ((congrArg (fun q => u ≫ q ≫ e.hom.right) hSquare).trans
            (congrArg (fun q => u ≫ q) (Category.assoc l.right p e.hom.right)))
      have hCoefficient : u ≫ l.right ≫ p ≫ e.hom.right =
          u' ≫ (S.comparison.hom.app b.1).right ≫ t :=
        normalizedPredecessorOriginalComparison_coefficient chi A i T B S hi a b'
      have hVertex : u ≫ v ≫ z = u' ≫ (S.comparison.hom.app b.1).right :=
        normalizedOriginalIso_coefficient chi A i T B S hi b.1
      have hRight : u ≫ v ≫ g.right = u' ≫ (S.comparison.hom.app b.1).right ≫ t := by
        change u ≫ v ≫ (z ≫ t) = _
        have hAssoc : u ≫ v ≫ (z ≫ t) = (u ≫ v ≫ z) ≫ t :=
          ((Category.assoc u (v ≫ z) t).trans
            (congrArg (fun q => u ≫ q) (Category.assoc v z t))).symm
        exact hAssoc.trans ((congrArg (fun q => q ≫ t) hVertex).trans
          (Category.assoc u' (S.comparison.hom.app b.1).right t))
      exact hLeft.trans (hCoefficient.trans hRight.symm)
    · let v := pushout.inl (R.vertex b.1).hom (A.presentation.ι.app i)
      let p := pushout.inr (R.vertex b.1).hom (A.presentation.ι.app i)
      have hCondition : (R.vertex b.1).hom ≫ v = A.presentation.ι.app i ≫ p :=
        pushout.condition
      have h₁ := congrArg (fun q => q ≫ f.right) hCondition
      have h₂ := congrArg (fun q => q ≫ g.right) hCondition
      change (R.vertex b.1).hom ≫ v ≫ f.right = (R.vertex b.1).hom ≫ v ≫ g.right
      exact (Category.assoc (R.vertex b.1).hom v f.right).symm.trans
        (h₁.trans ((Category.assoc (A.presentation.ι.app i) p f.right).trans
          ((congrArg (fun q => A.presentation.ι.app i ≫ q) hRoot).trans
            ((Category.assoc (A.presentation.ι.app i) p g.right).symm.trans
              (h₂.symm.trans (Category.assoc (R.vertex b.1).hom v g.right))))))
  · exact hRoot

/-- The two genuine predecessor UPs construct the comparison on every actual predecessor label. -/
abbrev normalizedPredecessorUPComparison (a : B) :
    (Under.pushout (A.presentation.ι.app i)).obj
      ((normalizedTree chi A T B S i hi).predecessorObj a) ≅ T.predecessorObj a.1 :=
  (isColimitOfPreserves (Under.pushout (A.presentation.ι.app i))
    ((normalizedTree chi A T B S i hi).predecessor a).isColimit).coconePointsIsoOfNatIso
    (CellTreeLowerRestriction.predecessor T B a).isColimit
    (Functor.isoWhiskerLeft (inclusion ((LowerSet.Iio a) : Set B))
      (normalizedOriginalIso chi A T B S i hi))

/-- The actual native predecessor UP comparison retains every original predecessor leg. -/
@[reassoc]
theorem normalizedPredecessorUPComparison_leg (a : B) (b : LowerSet.Iio a) :
    (Under.pushout (A.presentation.ι.app i)).map
      (((normalizedTree chi A T B S i hi).predecessor a).cocone.ι.app b) ≫
      (normalizedPredecessorUPComparison chi A i T B S hi a).hom =
    (normalizedOriginalIso chi A T B S i hi).hom.app b.1 ≫
      (T.predecessor a.1).cocone.ι.app ((CellTreeLowerRestriction.predecessorOrderIso B a) b) :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves (Under.pushout (A.presentation.ι.app i))
      ((normalizedTree chi A T B S i hi).predecessor a).isColimit)
    (CellTreeLowerRestriction.predecessor T B a).isColimit
    (Functor.isoWhiskerLeft (inclusion ((LowerSet.Iio a) : Set B))
      (normalizedOriginalIso chi A T B S i hi)) b

/-- All legs prove equality of the entire flat Iso and the actual predecessor UP Iso. -/
theorem normalizedPredecessorOriginalComparison_eq_UP (a : B) :
    normalizedPredecessorOriginalComparison chi A i T B S hi a =
      normalizedPredecessorUPComparison chi A i T B S hi a := by
  apply Iso.ext
  apply (isColimitOfPreserves (Under.pushout (A.presentation.ι.app i))
    ((normalizedTree chi A T B S i hi).predecessor a).isColimit).hom_ext
  intro b
  exact (normalizedPredecessorOriginalComparison_leg chi A i T B S hi a b).trans
    (normalizedPredecessorUPComparison_leg chi A i T B S hi a b).symm

/-- The full inverse flat comparison retains every original predecessor leg through the true UP. -/
@[reassoc]
theorem normalizedPredecessorOriginalComparison_leg_inv (a : B) (b : LowerSet.Iio a) :
    (T.predecessor a.1).cocone.ι.app ((CellTreeLowerRestriction.predecessorOrderIso B a) b) ≫
      (normalizedPredecessorOriginalComparison chi A i T B S hi a).inv =
    (normalizedOriginalIso chi A T B S i hi).inv.app b.1 ≫
      (Under.pushout (A.presentation.ι.app i)).map
        (((normalizedTree chi A T B S i hi).predecessor a).cocone.ι.app b) := by
  rw [normalizedPredecessorOriginalComparison_eq_UP]
  exact IsColimit.comp_coconePointsIsoOfNatIso_inv
    (isColimitOfPreserves (Under.pushout (A.presentation.ι.app i))
      ((normalizedTree chi A T B S i hi).predecessor a).isColimit)
    (CellTreeLowerRestriction.predecessor T B a).isColimit
    (Functor.isoWhiskerLeft (inclusion ((LowerSet.Iio a) : Set B))
      (normalizedOriginalIso chi A T B S i hi)) b

/-- The whole actual structural predecessor map is retained by its original colimit UP. -/
theorem normalizedPredecessorOriginalComparison_map (a : B) :
    (Under.pushout (A.presentation.ι.app i)).map
      ((normalizedTree chi A T B S i hi).predecessorMap a) ≫
      (normalizedOriginalIso chi A T B S i hi).hom.app a =
    (normalizedPredecessorOriginalComparison chi A i T B S hi a).hom ≫
      T.predecessorMap a.1 := by
  let R := normalizedTree chi A T B S i hi
  let F := Under.pushout (A.presentation.ι.app i)
  let eta := normalizedOriginalIso chi A T B S i hi
  let e := normalizedPredecessorOriginalComparison chi A i T B S hi a
  apply (isColimitOfPreserves F (R.predecessor a).isColimit).hom_ext
  intro b
  let l := (R.predecessor a).cocone.ι.app b
  let b' := (CellTreeLowerRestriction.predecessorOrderIso B a) b
  let h : b.1 ⟶ a := homOfLE b.2.le
  have hFactor : F.map l ≫ F.map (R.predecessorMap a) = F.map (R.diagram.map h) :=
    (F.map_comp l (R.predecessorMap a)).symm.trans
      (congrArg F.map (R.predecessorMap_fac a b))
  have hNat : F.map (R.diagram.map h) ≫ eta.hom.app a =
      eta.hom.app b.1 ≫ T.diagram.map (homOfLE b.2.le) := eta.hom.naturality h
  have hLeg : F.map l ≫ e.hom =
      eta.hom.app b.1 ≫ (T.predecessor a.1).cocone.ι.app b' :=
    normalizedPredecessorOriginalComparison_leg chi A i T B S hi a b
  change F.map l ≫ (F.map (R.predecessorMap a) ≫ eta.hom.app a) =
    F.map l ≫ (e.hom ≫ T.predecessorMap a.1)
  have hLeft := (Category.assoc (F.map l) (F.map (R.predecessorMap a)) (eta.hom.app a)).symm.trans
    ((congrArg (fun q => q ≫ eta.hom.app a) hFactor).trans hNat)
  have hRight := (Category.assoc (F.map l) e.hom (T.predecessorMap a.1)).symm.trans
    ((congrArg (fun q => q ≫ T.predecessorMap a.1) hLeg).trans
      ((Category.assoc (eta.hom.app b.1) ((T.predecessor a.1).cocone.ι.app b')
        (T.predecessorMap a.1)).trans
          (congrArg (fun q => eta.hom.app b.1 ≫ q) (T.predecessorMap_fac a.1 b'))))
  exact hLeft.trans hRight.symm

/-- The same selected original attaching function survives both actual native root changes. -/
theorem normalizedAttaching_original (a : B) :
    (normalizedTree chi A T B S i hi).attaching a ≫
      pushout.inl ((normalizedTree chi A T B S i hi).predecessorObj a).hom
        (A.presentation.ι.app i) ≫
      (normalizedPredecessorOriginalComparison chi A i T B S hi a).hom.right =
        T.attaching a.1 := by
  let U := (birthPredecessor chi A B S.diagram a).cocone.pt
  let q := birthRootTransition chi A T B S i hi a
  let e₀ := approximationFlatIso chi A (S.diagram.obj a).left i (hi a) U
  let e := (S.core chi A T).birthOriginalComparison chi A T a
  let g := (S.cell a).choose
  let u₁ := pushout.inl U.hom q
  let u₂ := pushout.inl ((Under.pushout q).obj U).hom (A.presentation.ι.app i)
  have hFlat₀ : u₁ ≫ u₂ ≫ e₀.hom.right =
      pushout.inl U.hom (A.presentation.ι.app (S.diagram.obj a).left) :=
    approximationFlatIso_inl_flat chi A (S.diagram.obj a).left i (hi a) U
  have hFlat : u₁ ≫ u₂ ≫ e₀.hom.right ≫ e.hom.right =
      pushout.inl U.hom (A.presentation.ι.app (S.diagram.obj a).left) ≫ e.hom.right :=
    ((Category.assoc u₁ (u₂ ≫ e₀.hom.right) e.hom.right).trans
      (congrArg (fun f => u₁ ≫ f) (Category.assoc u₂ e₀.hom.right e.hom.right))).symm.trans
        (congrArg (fun f => f ≫ e.hom.right) hFlat₀)
  have hUnit := nativePushoutHomEquiv_right (A.presentation.ι.app (S.diagram.obj a).left)
    U (T.predecessorObj a.1) e.hom
  change (g ≫ pushout.inl U.hom q) ≫
    pushout.inl ((Under.pushout q).obj U).hom (A.presentation.ι.app i) ≫
    (e₀.hom.right ≫ e.hom.right) = T.attaching a.1
  calc
    _ = g ≫ (pushout.inl U.hom q ≫
        pushout.inl ((Under.pushout q).obj U).hom (A.presentation.ι.app i) ≫
        e₀.hom.right ≫ e.hom.right) := by simp only [Category.assoc]
    _ = g ≫ (pushout.inl U.hom (A.presentation.ι.app (S.diagram.obj a).left) ≫
        e.hom.right) := congrArg (fun f => g ≫ f) hFlat
    _ = g ≫ ((S.core chi A T).birthOriginalMap chi A T a).right :=
      congrArg (fun f => g ≫ f) hUnit.symm
    _ = T.attaching a.1 := (S.cell a).choose_spec.choose_spec.2.1

/-- The same selected original target-cell function survives both actual native root changes. -/
theorem normalizedCell_original (a : B) :
    (normalizedTree chi A T B S i hi).cell a ≫
      pushout.inl ((normalizedTree chi A T B S i hi).vertex a).hom
        (A.presentation.ι.app i) ≫
      ((normalizedOriginalIso chi A T B S i hi).hom.app a).right = T.cell a.1 := by
  let U := S.diagram.obj a
  let q := birthRootTransition chi A T B S i hi a
  let e₀ := raisedComponentIso chi A S.diagram i hi a
  let e := S.comparison.app a
  let k := (S.cell a).choose_spec.choose
  let u₁ := pushout.inl U.hom q
  let u₂ := pushout.inl ((Under.pushout q).obj (Under.mk U.hom)).hom (A.presentation.ι.app i)
  have hFlat₀ : u₁ ≫ u₂ ≫ e₀.hom.right = pushout.inl U.hom (A.presentation.ι.app U.left) :=
    raisedComponentIso_inl_flat chi A S.diagram i hi a
  have hFlat : u₁ ≫ u₂ ≫ e₀.hom.right ≫ e.hom.right =
      pushout.inl U.hom (A.presentation.ι.app U.left) ≫ e.hom.right :=
    ((Category.assoc u₁ (u₂ ≫ e₀.hom.right) e.hom.right).trans
      (congrArg (fun f => u₁ ≫ f) (Category.assoc u₂ e₀.hom.right e.hom.right))).symm.trans
        (congrArg (fun f => f ≫ e.hom.right) hFlat₀)
  change (k ≫ pushout.inl U.hom q) ≫
    pushout.inl ((Under.pushout q).obj (Under.mk U.hom)).hom (A.presentation.ι.app i) ≫
    (e₀.hom.right ≫ e.hom.right) = T.cell a.1
  calc
    _ = k ≫ (pushout.inl U.hom q ≫
        pushout.inl ((Under.pushout q).obj (Under.mk U.hom)).hom (A.presentation.ι.app i) ≫
        e₀.hom.right ≫ e.hom.right) := by simp only [Category.assoc]
    _ = k ≫ (pushout.inl U.hom (A.presentation.ι.app U.left) ≫ e.hom.right) :=
      congrArg (fun f => k ≫ f) hFlat
    _ = T.cell a.1 := (S.cell a).choose_spec.choose_spec.2.2

end NativeFlatOriginalCellComparisons

section OriginalCompactRootPresentationData

variable [HasPushouts C] (chi : Cardinal.{w}) [Fact chi.IsRegular]
  {X : C} {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P))

/-- Full compact-root presentation data on the same actual original cell carrier. -/
structure CompactRootPresentation where
  /-- The internally selected new root object. -/
  root : C
  /-- The actual new-root-to-original-root function. -/
  rootMap : root ⟶ X
  /-- The selected new root is presentable at the original cardinal. -/
  root_presentable : IsCardinalPresentable root chi
  /-- The actual new tree on the literal original partial order. -/
  tree : CellTree s root (P := P)
  /-- The whole original attaching-family label function. -/
  label_eq : tree.label = T.label
  /-- The full original vertex comparison and its actual inverse. -/
  comparison : tree.diagram ⋙ Under.pushout rootMap ≅ T.diagram
  /-- Each entire actual original predecessor comparison. -/
  predecessorComparison (a : P) :
    (Under.pushout rootMap).obj (tree.predecessorObj a) ≅ T.predecessorObj a
  /-- Every actual original predecessor leg. -/
  predecessor_leg (a : P) (b : LowerSet.Iio a) :
    (Under.pushout rootMap).map ((tree.predecessor a).cocone.ι.app b) ≫
      (predecessorComparison a).hom = comparison.hom.app b.1 ≫ (T.predecessor a).cocone.ι.app b
  /-- Every actual original predecessor leg in the inverse direction. -/
  predecessor_leg_inv (a : P) (b : LowerSet.Iio a) :
    (T.predecessor a).cocone.ι.app b ≫ (predecessorComparison a).inv =
      comparison.inv.app b.1 ≫ (Under.pushout rootMap).map ((tree.predecessor a).cocone.ι.app b)
  /-- The full actual structural predecessor map. -/
  predecessor_map (a : P) :
    (Under.pushout rootMap).map (tree.predecessorMap a) ≫ comparison.hom.app a =
      (predecessorComparison a).hom ≫ T.predecessorMap a
  /-- The full actual structural predecessor map in the inverse direction. -/
  predecessor_map_inv (a : P) :
    T.predecessorMap a ≫ comparison.inv.app a =
      (predecessorComparison a).inv ≫ (Under.pushout rootMap).map (tree.predecessorMap a)
  /-- The actual whole endpoint comparison, including its inverse. -/
  endpointComparison : (Under.pushout rootMap).obj tree.endpointObj ≅ T.endpointObj
  /-- Every actual original endpoint vertex leg. -/
  endpoint_leg (a : P) :
    (Under.pushout rootMap).map (tree.inclusion a) ≫ endpointComparison.hom =
      comparison.hom.app a ≫ T.inclusion a
  /-- Every actual original endpoint vertex leg in the inverse direction. -/
  endpoint_leg_inv (a : P) :
    T.inclusion a ≫ endpointComparison.inv =
      comparison.inv.app a ≫ (Under.pushout rootMap).map (tree.inclusion a)
  /-- The original whole endpoint and both root maps form the actual pushout. -/
  endpoint_isPushout :
    IsPushout tree.hom rootMap (pushout.inl tree.hom rootMap ≫ endpointComparison.hom.right) T.hom
  /-- The actual internally selected new cocones for every original lower set. -/
  lower : LowerSetColimitData tree.diagram
  /-- All actual lower comparisons and their inverses, including every B-to-D map. -/
  lowerComparison (L : LowerSetColimitData T.diagram) :
    lower.functor ⋙ Under.pushout rootMap ≅ L.functor
  /-- Every actual original lower vertex leg. -/
  lower_leg (L : LowerSetColimitData T.diagram) (B : LowerSet P) (a : B) :
    (Under.pushout rootMap).map (lower.ι B a) ≫ (lowerComparison L).hom.app B =
      comparison.hom.app a.1 ≫ L.ι B a
  /-- Both directions of the whole lower-to-endpoint comparison retain the same values. -/
  lower_endpoint_iso (L : LowerSetColimitData T.diagram) :
    (Under.pushout rootMap).mapIso (tree.endpointIso lower) ≪≫ endpointComparison =
      (lowerComparison L).app ⊤ ≪≫ T.endpointIso L
  /-- Both directions of every lower-to-predecessor comparison retain the same native values. -/
  lower_predecessor_iso (L : LowerSetColimitData T.diagram) (a : P) :
    (Under.pushout rootMap).mapIso (tree.predecessorIso lower a) ≪≫ predecessorComparison a =
      (lowerComparison L).app (LowerSet.Iio a) ≪≫ T.predecessorIso L a
  /-- The whole actual original attaching function, with explicit dependent label transport. -/
  attaching_function :
    (fun a : P => tree.attaching a ≫ pushout.inl (tree.predecessorObj a).hom rootMap ≫
      (predecessorComparison a).hom.right) =
    (fun a : P => eqToHom (congrArg (fun l : alpha => (s l).left) (congrFun label_eq a)) ≫
      T.attaching a)
  /-- The whole actual original target-cell function, with explicit dependent label transport. -/
  cell_function :
    (fun a : P => tree.cell a ≫ pushout.inl (tree.vertex a).hom rootMap ≫
      (comparison.hom.app a).right) =
    (fun a : P => eqToHom (congrArg (fun l : alpha => (s l).right) (congrFun label_eq a)) ≫
      T.cell a)
  /-- The new tree derives the original generator endpoint and predecessor goodness bounds. -/
  good : tree.IsGood chi
  /-- Every actual new coefficient vertex is presentable. -/
  vertex_presentable (a : P) : IsCardinalPresentable (tree.vertex a).right chi
  /-- Every actual new predecessor coefficient point is presentable. -/
  predecessor_presentable (a : P) : IsCardinalPresentable (tree.predecessorObj a).right chi
  /-- Every actual selected new lower coefficient point is presentable. -/
  lower_presentable (B : LowerSet P) : IsCardinalPresentable (lower.obj B).right chi
  /-- The actual whole new endpoint coefficient point is presentable. -/
  endpoint_presentable : IsCardinalPresentable tree.endpointObj.right chi

end OriginalCompactRootPresentationData

section ChosenWholeCompactRoot

variable [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalAccessibleCategory C chi]
  {X : C} {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (hP : HasCardinalLT P chi)
  (hSource : ∀ a : P, IsCardinalPresentable (s (T.label a)).left chi)

/-- The actual chi-accessible presentation of the arbitrary original root is chosen internally. -/
abbrev finalApproximation : CompactApproximation chi X := compactApproximation chi X

/-- The entire final state is built from the recorded original well-founded order internally. -/
abbrev finalLift : PrefixLift chi (finalApproximation chi (X := X)) T (⊤ : LowerSet P) := by
  let : WellFoundedLT P := T.wellFoundedLT
  exact wholeOriginalLift chi (finalApproximation chi (X := X)) T hP hSource

/-- The genuine full cone receives every internally built birth root and root-transition map. -/
abbrev finalRootCone : Cocone
    ((finalLift chi T hP hSource).diagram ⋙
      Comma.fst (finalApproximation chi (X := X)).presentation.diag (𝟭 C)) :=
  commonPrefixRootCocone chi (finalApproximation chi (X := X)) T
    (finalLift chi T hP hSource) (hP.of_injective Subtype.val Subtype.val_injective)

/-- Select the common compact root from the point of that actual whole cone. -/
abbrev finalRootIndex : (finalApproximation chi (X := X)).index :=
  (finalRootCone chi T hP hSource).pt

/-- Every original birth root has its actual arrow to the selected final compact root. -/
theorem finalRootBound (a : (⊤ : LowerSet P)) :
    ((finalLift chi T hP hSource).diagram.obj a).left ≤ finalRootIndex chi T hP hSource :=
  leOfHom ((finalRootCone chi T hP hSource).ι.app a)

/-- The full actual root-transition function is natural at the selected final root. -/
theorem finalRootCone_naturality {a b : (⊤ : LowerSet P)} (f : a ⟶ b) :
    ((finalLift chi T hP hSource).diagram.map f).left ≫
      (finalRootCone chi T hP hSource).ι.app b = (finalRootCone chi T hP hSource).ι.app a :=
  (finalRootCone chi T hP hSource).w f

/-- The new root is the actual compact approximation object at the selected common index. -/
abbrev finalRoot : C :=
  (finalApproximation chi (X := X)).presentation.diag.obj (finalRootIndex chi T hP hSource)

/-- Its original root map is the exact chosen presentation leg, with arbitrary target X. -/
abbrev finalRootArrow : finalRoot chi T hP hSource ⟶ X :=
  (finalApproximation chi (X := X)).presentation.ι.app (finalRootIndex chi T hP hSource)

/-- Compactness belongs to the actual newly chosen root object. -/
theorem finalRoot_presentable : IsCardinalPresentable (finalRoot chi T hP hSource) chi :=
  (finalApproximation chi (X := X)).presentable (finalRootIndex chi T hP hSource)

/-- Normalize the complete internally built state at its actual common compact root. -/
abbrev finalNormalizedTree : CellTree s (finalRoot chi T hP hSource)
    (P := (⊤ : LowerSet P)) :=
  normalizedTree chi (finalApproximation chi (X := X)) T (⊤ : LowerSet P)
    (finalLift chi T hP hSource) (finalRootIndex chi T hP hSource)
    (finalRootBound chi T hP hSource)

/-- The final compact-root tree retains the literal original partial order and label carrier. -/
abbrev finalTree : CellTree s (finalRoot chi T hP hSource) (P := P) :=
  literalTopTree (finalNormalizedTree chi T hP hSource)

/-- Every final cell label is exactly the same original attaching-family value. -/
theorem finalTree_label_function : (finalTree chi T hP hSource).label = T.label := rfl

/-- Native base change at the actual final root map recovers the whole original vertex functor. -/
abbrev finalOriginalIso :
    (finalTree chi T hP hSource).diagram ⋙ Under.pushout (finalRootArrow chi T hP hSource) ≅
      T.diagram :=
  literalTopOriginalIso (finalNormalizedTree chi T hP hSource)
    (finalRootArrow chi T hP hSource) T
    (normalizedOriginalIso chi (finalApproximation chi (X := X)) T (⊤ : LowerSet P)
      (finalLift chi T hP hSource) (finalRootIndex chi T hP hSource)
      (finalRootBound chi T hP hSource))

/-- The final comparison is the actual whole endpoint isomorphism from both genuine UPs. -/
abbrev finalEndpointComparison :
    (Under.pushout (finalRootArrow chi T hP hSource)).obj
      (finalTree chi T hP hSource).endpointObj ≅ T.endpointObj :=
  endpointComparison (finalRootArrow chi T hP hSource) (finalTree chi T hP hSource) T
    (finalOriginalIso chi T hP hSource)

/-- The actual selected compact root and original endpoint form the entire original pushout. -/
theorem finalEndpoint_isPushout :
    IsPushout (finalTree chi T hP hSource).hom (finalRootArrow chi T hP hSource)
      (pushout.inl (finalTree chi T hP hSource).hom (finalRootArrow chi T hP hSource) ≫
        (finalEndpointComparison chi T hP hSource).hom.right) T.hom :=
  endpointComparison_isPushout (finalRootArrow chi T hP hSource)
    (finalTree chi T hP hSource) T (finalOriginalIso chi T hP hSource)

/-- Every whole final endpoint inclusion retains its same original vertex and original leg. -/
theorem finalEndpoint_leg (a : P) :
    (Under.pushout (finalRootArrow chi T hP hSource)).map
      ((finalTree chi T hP hSource).inclusion a) ≫
      (finalEndpointComparison chi T hP hSource).hom =
        (finalOriginalIso chi T hP hSource).hom.app a ≫ T.inclusion a :=
  endpointComparison_leg (finalRootArrow chi T hP hSource)
    (finalTree chi T hP hSource) T (finalOriginalIso chi T hP hSource) a

/-- Every actual final predecessor uses the native flat comparison and its original birth UP. -/
abbrev finalPredecessorComparison (a : P) :
    (Under.pushout (finalRootArrow chi T hP hSource)).obj
      ((finalTree chi T hP hSource).predecessorObj a) ≅ T.predecessorObj a :=
  normalizedPredecessorOriginalComparison chi (finalApproximation chi (X := X))
    (finalRootIndex chi T hP hSource) T (⊤ : LowerSet P) (finalLift chi T hP hSource)
    (finalRootBound chi T hP hSource) (topLabelOrderIso a)

/-- Every final original attaching map is retained through the actual predecessor comparison. -/
theorem finalAttaching_original (a : P) :
    (finalTree chi T hP hSource).attaching a ≫
      pushout.inl ((finalTree chi T hP hSource).predecessorObj a).hom
        (finalRootArrow chi T hP hSource) ≫
      (finalPredecessorComparison chi T hP hSource a).hom.right = T.attaching a :=
  normalizedAttaching_original chi (finalApproximation chi (X := X))
    (finalRootIndex chi T hP hSource) T (⊤ : LowerSet P) (finalLift chi T hP hSource)
    (finalRootBound chi T hP hSource) (topLabelOrderIso a)

/-- Every final original generator-target map is retained through the whole vertex comparison. -/
theorem finalCell_original (a : P) :
    (finalTree chi T hP hSource).cell a ≫
      pushout.inl ((finalTree chi T hP hSource).vertex a).hom
        (finalRootArrow chi T hP hSource) ≫
      ((finalOriginalIso chi T hP hSource).hom.app a).right = T.cell a := by
  simp only [finalOriginalIso, literalTopOriginalIso_hom]
  exact normalizedCell_original chi (finalApproximation chi (X := X))
    (finalRootIndex chi T hP hSource) T (⊤ : LowerSet P) (finalLift chi T hP hSource)
    (finalRootBound chi T hP hSource) (topLabelOrderIso a)

/-- The entire actual original attaching function is retained on its original dependent types. -/
theorem finalAttaching_original_function :
    (fun a : P => (finalTree chi T hP hSource).attaching a ≫
      pushout.inl ((finalTree chi T hP hSource).predecessorObj a).hom
        (finalRootArrow chi T hP hSource) ≫
      (finalPredecessorComparison chi T hP hSource a).hom.right) = T.attaching := by
  funext a
  exact finalAttaching_original chi T hP hSource a

/-- The entire actual original target-cell function is retained on its original dependent types. -/
theorem finalCell_original_function :
    (fun a : P => (finalTree chi T hP hSource).cell a ≫
      pushout.inl ((finalTree chi T hP hSource).vertex a).hom
        (finalRootArrow chi T hP hSource) ≫
      ((finalOriginalIso chi T hP hSource).hom.app a).right) = T.cell := by
  funext a
  exact finalCell_original chi T hP hSource a

/-- Every final predecessor leg retains its exact original literal label and whole morphism. -/
@[reassoc]
theorem finalPredecessor_leg (a : P) (b : LowerSet.Iio a) :
    (Under.pushout (finalRootArrow chi T hP hSource)).map
      (((finalTree chi T hP hSource).predecessor a).cocone.ι.app b) ≫
      (finalPredecessorComparison chi T hP hSource a).hom =
    (finalOriginalIso chi T hP hSource).hom.app b.1 ≫ (T.predecessor a).cocone.ι.app b := by
  simp only [finalOriginalIso, literalTopOriginalIso_hom]
  exact normalizedPredecessorOriginalComparison_leg chi (finalApproximation chi (X := X))
    (finalRootIndex chi T hP hSource) T (⊤ : LowerSet P) (finalLift chi T hP hSource)
    (finalRootBound chi T hP hSource) (topLabelOrderIso a) ((topPredecessorOrderIso a) b)

/-- The actual inverse final predecessor comparison retains every original leg. -/
@[reassoc]
theorem finalPredecessor_leg_inv (a : P) (b : LowerSet.Iio a) :
    (T.predecessor a).cocone.ι.app b ≫ (finalPredecessorComparison chi T hP hSource a).inv =
    (finalOriginalIso chi T hP hSource).inv.app b.1 ≫
      (Under.pushout (finalRootArrow chi T hP hSource)).map
        (((finalTree chi T hP hSource).predecessor a).cocone.ι.app b) := by
  simp only [finalOriginalIso, literalTopOriginalIso_inv]
  exact normalizedPredecessorOriginalComparison_leg_inv chi (finalApproximation chi (X := X))
    (finalRootIndex chi T hP hSource) T (⊤ : LowerSet P) (finalLift chi T hP hSource)
    (finalRootBound chi T hP hSource) (topLabelOrderIso a) ((topPredecessorOrderIso a) b)

/-- The literal-P predecessor structural map is retained by the actual whole original comparison. -/
theorem finalPredecessor_map (a : P) :
    (Under.pushout (finalRootArrow chi T hP hSource)).map
      ((finalTree chi T hP hSource).predecessorMap a) ≫
      (finalOriginalIso chi T hP hSource).hom.app a =
    (finalPredecessorComparison chi T hP hSource a).hom ≫ T.predecessorMap a := by
  let R := finalNormalizedTree chi T hP hSource
  let r := finalRootArrow chi T hP hSource
  let eta := normalizedOriginalIso chi (finalApproximation chi (X := X)) T (⊤ : LowerSet P)
    (finalLift chi T hP hSource) (finalRootIndex chi T hP hSource)
    (finalRootBound chi T hP hSource)
  change (Under.pushout r).map
    (cellTreePredecessorMap (literalTopDiagram R) a (literalTopPredecessor R a)) ≫
    (literalTopOriginalIso R r T eta).hom.app a = _
  rw [literalTopPredecessorMap, literalTopOriginalIso_hom]
  exact normalizedPredecessorOriginalComparison_map chi (finalApproximation chi (X := X))
    (finalRootIndex chi T hP hSource) T (⊤ : LowerSet P) (finalLift chi T hP hSource)
    (finalRootBound chi T hP hSource) (topLabelOrderIso a)

/-- The actual inverse comparisons retain the full original structural predecessor function. -/
theorem finalPredecessor_map_inv (a : P) :
    T.predecessorMap a ≫ (finalOriginalIso chi T hP hSource).inv.app a =
    (finalPredecessorComparison chi T hP hSource a).inv ≫
      (Under.pushout (finalRootArrow chi T hP hSource)).map
        ((finalTree chi T hP hSource).predecessorMap a) := by
  let e := finalPredecessorComparison chi T hP hSource a
  let z := (finalOriginalIso chi T hP hSource).app a
  let f := (Under.pushout (finalRootArrow chi T hP hSource)).map
    ((finalTree chi T hP hSource).predecessorMap a)
  let g := T.predecessorMap a
  have h : f ≫ z.hom = e.hom ≫ g := finalPredecessor_map chi T hP hSource a
  have h₁ : e.inv ≫ f ≫ z.hom = g :=
    (congrArg (fun m => e.inv ≫ m) h).trans (e.inv_hom_id_assoc g)
  have h₂ : (e.inv ≫ f ≫ z.hom) ≫ z.inv = e.inv ≫ f :=
    (Category.assoc e.inv (f ≫ z.hom) z.inv).trans
      (congrArg (fun m => e.inv ≫ m)
        ((Category.assoc f z.hom z.inv).trans
          ((congrArg (fun m => f ≫ m) z.hom_inv_id).trans (Category.comp_id f))))
  exact (congrArg (fun m => m ≫ z.inv) h₁).symm.trans h₂

/-- The full original predecessor Arrow Iso retains both actual underlying component maps. -/
def finalPredecessorArrowIso (a : P) :
    Arrow.mk ((Under.pushout (finalRootArrow chi T hP hSource)).map
      ((finalTree chi T hP hSource).predecessorMap a)).right ≅
    Arrow.mk (T.predecessorMap a).right :=
  Arrow.isoMk ((Under.forget X).mapIso (finalPredecessorComparison chi T hP hSource a))
    ((Under.forget X).mapIso ((finalOriginalIso chi T hP hSource).app a)) (by
      change (finalPredecessorComparison chi T hP hSource a).hom.right ≫
        (T.predecessorMap a).right =
      ((Under.pushout (finalRootArrow chi T hP hSource)).map
        ((finalTree chi T hP hSource).predecessorMap a)).right ≫
        ((finalOriginalIso chi T hP hSource).hom.app a).right
      exact (congrArg Under.Hom.right (finalPredecessor_map chi T hP hSource a)).symm)

/-- The actual whole endpoint Arrow Iso retains the same original source X and root map. -/
def finalEndpointArrowIso :
    Arrow.mk (((Under.pushout (finalRootArrow chi T hP hSource)).obj
      (finalTree chi T hP hSource).endpointObj).hom) ≅ Arrow.mk T.hom :=
  Arrow.isoMk (Iso.refl X) ((Under.forget X).mapIso (finalEndpointComparison chi T hP hSource))
    (by
      change 𝟙 X ≫ T.hom = ((Under.pushout (finalRootArrow chi T hP hSource)).obj
        (finalTree chi T hP hSource).endpointObj).hom ≫
        (finalEndpointComparison chi T hP hSource).hom.right
      exact (Category.id_comp _).trans
        (Under.w (finalEndpointComparison chi T hP hSource).hom).symm)

/-- Every forward vertex comparison retains the exact function of original root maps. -/
theorem finalVertex_root_function :
    (fun a : P => pushout.inr ((finalTree chi T hP hSource).vertex a).hom
      (finalRootArrow chi T hP hSource) ≫ ((finalOriginalIso chi T hP hSource).hom.app a).right) =
    (fun a : P => (T.vertex a).hom) := by
  funext a
  exact Under.w ((finalOriginalIso chi T hP hSource).hom.app a)

/-- Every inverse vertex comparison retains the exact function of original root maps. -/
theorem finalVertex_root_inv_function :
    (fun a : P => (T.vertex a).hom ≫ ((finalOriginalIso chi T hP hSource).inv.app a).right) =
    (fun a : P => pushout.inr ((finalTree chi T hP hSource).vertex a).hom
      (finalRootArrow chi T hP hSource)) := by
  funext a
  exact Under.w ((finalOriginalIso chi T hP hSource).inv.app a)

/-- Every forward predecessor comparison retains the full original function of root maps. -/
theorem finalPredecessor_root_function :
    (fun a : P => pushout.inr ((finalTree chi T hP hSource).predecessorObj a).hom
      (finalRootArrow chi T hP hSource) ≫
      (finalPredecessorComparison chi T hP hSource a).hom.right) =
    (fun a : P => (T.predecessorObj a).hom) := by
  funext a
  exact Under.w (finalPredecessorComparison chi T hP hSource a).hom

/-- Every inverse predecessor comparison retains the full original function of root maps. -/
theorem finalPredecessor_root_inv_function :
    (fun a : P => (T.predecessorObj a).hom ≫
      (finalPredecessorComparison chi T hP hSource a).inv.right) =
    (fun a : P => pushout.inr ((finalTree chi T hP hSource).predecessorObj a).hom
      (finalRootArrow chi T hP hSource)) := by
  funext a
  exact Under.w (finalPredecessorComparison chi T hP hSource a).inv

/-- The original root map at every vertex forms its actual whole native pushout. -/
theorem finalVertex_isPushout (a : P) :
    IsPushout ((finalTree chi T hP hSource).vertex a).hom (finalRootArrow chi T hP hSource)
      (pushout.inl ((finalTree chi T hP hSource).vertex a).hom
        (finalRootArrow chi T hP hSource) ≫
      ((finalOriginalIso chi T hP hSource).hom.app a).right) (T.vertex a).hom :=
  rootComparison_isPushout (finalRootArrow chi T hP hSource)
    ((finalTree chi T hP hSource).vertex a) (T.vertex a) ((finalOriginalIso chi T hP hSource).app a)

/-- The original root map at every predecessor forms its actual whole native pushout. -/
theorem finalPredecessor_isPushout (a : P) :
    IsPushout ((finalTree chi T hP hSource).predecessorObj a).hom
      (finalRootArrow chi T hP hSource)
      (pushout.inl ((finalTree chi T hP hSource).predecessorObj a).hom
        (finalRootArrow chi T hP hSource) ≫
      (finalPredecessorComparison chi T hP hSource a).hom.right) (T.predecessorObj a).hom :=
  rootComparison_isPushout (finalRootArrow chi T hP hSource)
    ((finalTree chi T hP hSource).predecessorObj a) (T.predecessorObj a)
    (finalPredecessorComparison chi T hP hSource a)

/-- The final all-lower isomorphism uses the actual internally selected new lower cocones. -/
abbrev finalAllLowerComparison (L : LowerSetColimitData T.diagram) :
    (finalTree chi T hP hSource).lowerData.functor ⋙
      Under.pushout (finalRootArrow chi T hP hSource) ≅ L.functor :=
  allLowerComparison (finalRootArrow chi T hP hSource) (finalTree chi T hP hSource) T
    (finalOriginalIso chi T hP hSource) (finalTree chi T hP hSource).lowerData L

/-- Every selected new lower piece retains every whole original vertex leg. -/
@[reassoc]
theorem finalAllLower_leg (L : LowerSetColimitData T.diagram) (B : LowerSet P) (a : B) :
    (Under.pushout (finalRootArrow chi T hP hSource)).map
      ((finalTree chi T hP hSource).lowerData.ι B a) ≫
      (finalAllLowerComparison chi T hP hSource L).hom.app B =
    (finalOriginalIso chi T hP hSource).hom.app a.1 ≫ L.ι B a :=
  lowerComparison_leg (finalRootArrow chi T hP hSource) (finalTree chi T hP hSource) T
    (finalTree chi T hP hSource).lowerData L (finalOriginalIso chi T hP hSource) B a

/-- The entire all-lower endpoint Iso has the same actual whole endpoint value. -/
theorem finalAllLower_endpoint_iso (L : LowerSetColimitData T.diagram) :
    (Under.pushout (finalRootArrow chi T hP hSource)).mapIso
      ((finalTree chi T hP hSource).endpointIso (finalTree chi T hP hSource).lowerData) ≪≫
      finalEndpointComparison chi T hP hSource =
    (finalAllLowerComparison chi T hP hSource L).app ⊤ ≪≫ T.endpointIso L :=
  lowerComparison_endpoint_iso (finalRootArrow chi T hP hSource)
    (finalTree chi T hP hSource) T (finalOriginalIso chi T hP hSource)
    (finalTree chi T hP hSource).lowerData L

/-- The entire selected-lower predecessor Iso has the same native flat predecessor value. -/
theorem finalAllLower_predecessor_iso (L : LowerSetColimitData T.diagram) (a : P) :
    (Under.pushout (finalRootArrow chi T hP hSource)).mapIso
      ((finalTree chi T hP hSource).predecessorIso (finalTree chi T hP hSource).lowerData a) ≪≫
      finalPredecessorComparison chi T hP hSource a =
    (finalAllLowerComparison chi T hP hSource L).app (LowerSet.Iio a) ≪≫ T.predecessorIso L a := by
  let R := finalTree chi T hP hSource
  let F := Under.pushout (finalRootArrow chi T hP hSource)
  let LR := R.lowerData
  let eta := finalOriginalIso chi T hP hSource
  let e := finalPredecessorComparison chi T hP hSource a
  let tau := finalAllLowerComparison chi T hP hSource L
  apply Iso.ext
  apply (isColimitOfPreserves F (LR.isColimit (LowerSet.Iio a))).hom_ext
  intro b
  let l := LR.ι (LowerSet.Iio a) b
  have hFactor : F.map l ≫ F.map (R.predecessorIso LR a).hom =
      F.map ((R.predecessor a).cocone.ι.app b) :=
    (F.map_comp l (R.predecessorIso LR a).hom).symm.trans
      (congrArg F.map (R.ι_predecessorIso_hom LR a b))
  have hLeg : F.map l ≫ tau.hom.app (LowerSet.Iio a) = eta.hom.app b.1 ≫ L.ι (LowerSet.Iio a) b :=
    finalAllLower_leg chi T hP hSource L (LowerSet.Iio a) b
  change F.map l ≫ (F.map (R.predecessorIso LR a).hom ≫ e.hom) =
    F.map l ≫ (tau.hom.app (LowerSet.Iio a) ≫ (T.predecessorIso L a).hom)
  have hLeft := (Category.assoc (F.map l) (F.map (R.predecessorIso LR a).hom) e.hom).symm.trans
    ((congrArg (fun f => f ≫ e.hom) hFactor).trans (finalPredecessor_leg chi T hP hSource a b))
  have hRight := (Category.assoc (F.map l) (tau.hom.app (LowerSet.Iio a))
    (T.predecessorIso L a).hom).symm.trans
      ((congrArg (fun f => f ≫ (T.predecessorIso L a).hom) hLeg).trans
        ((Category.assoc (eta.hom.app b.1) (L.ι (LowerSet.Iio a) b)
          (T.predecessorIso L a).hom).trans
            (congrArg (fun f => eta.hom.app b.1 ≫ f) (T.ι_predecessorIso_hom L a b))))
  exact hLeft.trans hRight.symm

variable (hTarget : ∀ a : P, IsCardinalPresentable (s (T.label a)).right chi)

include hTarget

/-- The final tree derives its full goodness from the original endpoint bounds and small labels. -/
theorem finalTree_good : (finalTree chi T hP hSource).IsGood chi where
  presentable_source := hSource
  presentable_target := hTarget
  predecessor_lt a := hP.of_injective (fun b : Set.Iio a => b.1) Subtype.val_injective

/-- Every new coefficient vertex is compact by the actual original well-founded recursion. -/
theorem finalTree_vertex_presentable (a : P) :
    IsCardinalPresentable ((finalTree chi T hP hSource).vertex a).right chi := by
  let : IsCardinalPresentable (finalRoot chi T hP hSource) chi :=
    finalRoot_presentable chi T hP hSource
  exact compactRootVertex chi (finalTree chi T hP hSource) hSource hTarget
    (fun _ => hP.of_injective Subtype.val Subtype.val_injective) a

/-- Every new predecessor is compact through its actual root-adjoined C colimit. -/
theorem finalTree_predecessor_presentable (a : P) :
    IsCardinalPresentable ((finalTree chi T hP hSource).predecessorObj a).right chi := by
  let : IsCardinalPresentable (finalRoot chi T hP hSource) chi :=
    finalRoot_presentable chi T hP hSource
  exact compactRootPredecessor chi (finalTree chi T hP hSource) hSource hTarget
    (fun _ => hP.of_injective Subtype.val Subtype.val_injective) a

/-- All actual selected new lower pieces are compact at this same cardinal. -/
theorem finalTree_lower_presentable
    (L : LowerSetColimitData (finalTree chi T hP hSource).diagram) (B : LowerSet P) :
    IsCardinalPresentable (L.obj B).right chi := by
  let : IsCardinalPresentable (finalRoot chi T hP hSource) chi :=
    finalRoot_presentable chi T hP hSource
  exact compactRootLower chi (finalTree chi T hP hSource) hSource hTarget
    (fun _ => hP.of_injective Subtype.val Subtype.val_injective) L B
    (hP.of_injective Subtype.val Subtype.val_injective)

/-- The actual whole new endpoint is compact, with arbitrary original endpoint and original X. -/
theorem finalTree_endpoint_presentable :
    IsCardinalPresentable (finalTree chi T hP hSource).endpointObj.right chi := by
  let : IsCardinalPresentable (finalRoot chi T hP hSource) chi :=
    finalRoot_presentable chi T hP hSource
  exact compactRootEndpoint chi (finalTree chi T hP hSource) hSource hTarget
    (fun _ => hP.of_injective Subtype.val Subtype.val_injective) hP

/-- Construct every compact-root tree, UP, comparison and whole original function internally. -/
def compactRootPresentation : CompactRootPresentation chi T where
  root := finalRoot chi T hP hSource
  rootMap := finalRootArrow chi T hP hSource
  root_presentable := finalRoot_presentable chi T hP hSource
  tree := finalTree chi T hP hSource
  label_eq := finalTree_label_function chi T hP hSource
  comparison := finalOriginalIso chi T hP hSource
  predecessorComparison := finalPredecessorComparison chi T hP hSource
  predecessor_leg := finalPredecessor_leg chi T hP hSource
  predecessor_leg_inv := finalPredecessor_leg_inv chi T hP hSource
  predecessor_map := finalPredecessor_map chi T hP hSource
  predecessor_map_inv := finalPredecessor_map_inv chi T hP hSource
  endpointComparison := finalEndpointComparison chi T hP hSource
  endpoint_leg := finalEndpoint_leg chi T hP hSource
  endpoint_leg_inv := endpointComparison_leg_inv (finalRootArrow chi T hP hSource)
    (finalTree chi T hP hSource) T (finalOriginalIso chi T hP hSource)
  endpoint_isPushout := finalEndpoint_isPushout chi T hP hSource
  lower := (finalTree chi T hP hSource).lowerData
  lowerComparison := finalAllLowerComparison chi T hP hSource
  lower_leg := finalAllLower_leg chi T hP hSource
  lower_endpoint_iso := finalAllLower_endpoint_iso chi T hP hSource
  lower_predecessor_iso := finalAllLower_predecessor_iso chi T hP hSource
  attaching_function := by
    funext a
    change (finalTree chi T hP hSource).attaching a ≫
      pushout.inl ((finalTree chi T hP hSource).predecessorObj a).hom
        (finalRootArrow chi T hP hSource) ≫
      (finalPredecessorComparison chi T hP hSource a).hom.right = 𝟙 _ ≫ T.attaching a
    exact (finalAttaching_original chi T hP hSource a).trans (Category.id_comp _).symm
  cell_function := by
    funext a
    change (finalTree chi T hP hSource).cell a ≫
      pushout.inl ((finalTree chi T hP hSource).vertex a).hom
        (finalRootArrow chi T hP hSource) ≫
      ((finalOriginalIso chi T hP hSource).hom.app a).right = 𝟙 _ ≫ T.cell a
    exact (finalCell_original chi T hP hSource a).trans (Category.id_comp _).symm
  good := finalTree_good chi T hP hSource hTarget
  vertex_presentable := finalTree_vertex_presentable chi T hP hSource hTarget
  predecessor_presentable := finalTree_predecessor_presentable chi T hP hSource hTarget
  lower_presentable := finalTree_lower_presentable chi T hP hSource hTarget
    (finalTree chi T hP hSource).lowerData
  endpoint_presentable := finalTree_endpoint_presentable chi T hP hSource hTarget

end ChosenWholeCompactRoot

end CategoryTheory.SmallObject.CompactRootBaseChange
