/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceExhaustion
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Filtered unions of compatible original slices

The union uses the actual chosen lower-colimit objects of the original component
trees. Its actions, units, compositions and every inclusion are derived from
those same colimit cocones. Original roots, endpoints and arbitrary unbounded
supports are retained.

This is the limit-union infrastructure for the ordinary specialization of Jacob
Lurie's *Higher Topos Theory*, proof of Lemma A.3.3.3 and Lemma A.3.3.16, author
PDF dated April 9, 2017. A compatible indexed family is an intermediate input
here; the original filtration constructs its family by well-founded induction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w t uD vD uC vC uI vI

namespace CategoryTheory.SmallObject.OriginalSliceFilteredUnion

open Limits DiagramSliceExhaustion DiagramActionCapture

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  {theta : PointwiseCellTreePresentation (s := s) f P}
  {L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram}

/-- Every original inclusion has its actual whole source-root square. -/
theorem inclusion_root {A B : OriginalSlice theta L} (p : OriginalSlice.Inclusion A B) :
    A.root ≫ p.toNatTrans = B.root := by
  apply NatTrans.ext
  funext d
  exact Under.w ((L d).map (p.le d))

/-- Every original inclusion retains the whole target leg into the same original G. -/
theorem inclusion_target {A B : OriginalSlice theta L} (p : OriginalSlice.Inclusion A B) :
    p.toNatTrans ≫ B.target = A.target := by
  apply NatTrans.ext
  funext d
  exact inclusion_leg theta L d (p.le d)


/-- The actual empty chosen component is compared with the same original identity root. -/
def emptyComponentIso (d : D) : (L d).obj ⊥ ≅ Under.mk (𝟙 (F.obj d)) :=
  (theta.component d).tree.emptyLowerIso (L d)

/-- Both actual empty-component comparison maps in the coefficient category. -/
abbrev emptyCoefficientIso (d : D) : ((L d).obj ⊥).right ≅ F.obj d :=
  (Under.forget (F.obj d)).mapIso (emptyComponentIso (theta := theta) (L := L) d)

/-- The actual empty source comparison retains its original identity arrow. -/
theorem empty_root_hom (d : D) :
    ((L d).obj ⊥).hom ≫ (emptyCoefficientIso (theta := theta) (L := L) d).hom = 𝟙 _ :=
  Under.w (emptyComponentIso (theta := theta) (L := L) d).hom

/-- The actual inverse empty comparison is the same original empty source arrow. -/
theorem empty_root_inv (d : D) :
    (emptyCoefficientIso (theta := theta) (L := L) d).inv = ((L d).obj ⊥).hom := by
  simpa only [emptyCoefficientIso, Functor.mapIso_inv, Under.forget_map,
    Under.mk_hom, Category.id_comp] using
    Under.w (emptyComponentIso (theta := theta) (L := L) d).inv

/-- The actual empty lower leg recovers the original component f under its original root. -/
theorem empty_leg_inv (d : D) :
    (emptyCoefficientIso (theta := theta) (L := L) d).inv ≫
      DiagramActionCapture.leg theta L d ⊥ = f.app d := by
  have h := Under.w ((emptyComponentIso (theta := theta) (L := L) d).inv ≫
    DiagramActionCapture.legUnder theta L d ⊥)
  simpa only [emptyCoefficientIso, Functor.mapIso_inv, Under.forget_map,
    Under.comp_right, Under.mk_hom, Category.id_comp] using h

/-- The actual forward comparison identifies the same original empty endpoint leg. -/
theorem empty_leg_hom (d : D) :
    (emptyCoefficientIso (theta := theta) (L := L) d).hom ≫ f.app d =
      DiagramActionCapture.leg theta L d ⊥ := by
  calc
    _ = (emptyCoefficientIso (theta := theta) (L := L) d).hom ≫
        ((emptyCoefficientIso (theta := theta) (L := L) d).inv ≫
          DiagramActionCapture.leg theta L d ⊥) :=
      congrArg (fun k => (emptyCoefficientIso (theta := theta) (L := L) d).hom ≫ k)
        (empty_leg_inv (theta := theta) (L := L) d).symm
    _ = _ := Iso.hom_inv_id_assoc _ _

/-- The empty slice carries the original F actions through its actual empty comparisons. -/
abbrev emptyAction {d e : D} (g : d ⟶ e) :
    ((L d).obj ⊥).right ⟶ ((L e).obj ⊥).right :=
  (emptyCoefficientIso (theta := theta) (L := L) d).hom ≫ F.map g ≫
    (emptyCoefficientIso (theta := theta) (L := L) e).inv

/-- All original empty-support actions are unital. -/
theorem emptyAction_id (d : D) : emptyAction (theta := theta) (L := L) (𝟙 d) = 𝟙 _ := by
  simp only [emptyAction, Functor.map_id, Category.id_comp, Iso.hom_inv_id]

/-- All original empty-support actions retain the same full composition law. -/
theorem emptyAction_comp {d e k : D} (g : d ⟶ e) (h : e ⟶ k) :
    emptyAction (theta := theta) (L := L) (g ≫ h) =
      emptyAction (theta := theta) (L := L) g ≫
        emptyAction (theta := theta) (L := L) h := by
  simp only [emptyAction, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- Empty-support actions retain each actual original root square. -/
theorem emptyAction_root {d e : D} (g : d ⟶ e) :
    ((L d).obj ⊥).hom ≫ emptyAction (theta := theta) (L := L) g =
      F.map g ≫ ((L e).obj ⊥).hom := by
  simp only [emptyAction, ← Category.assoc, empty_root_hom, Category.id_comp, empty_root_inv]

/-- Empty-support actions retain the full original endpoint naturality square. -/
theorem emptyAction_endpoint {d e : D} (g : d ⟶ e) :
    emptyAction (theta := theta) (L := L) g ≫ DiagramActionCapture.leg theta L e ⊥ =
      DiagramActionCapture.leg theta L d ⊥ ≫ G.map g := by
  simp only [emptyAction, Category.assoc, empty_leg_inv]
  calc
    _ = (emptyCoefficientIso (theta := theta) (L := L) d).hom ≫
        (f.app d ≫ G.map g) :=
      congrArg (fun k => (emptyCoefficientIso (theta := theta) (L := L) d).hom ≫ k)
        (f.naturality g)
    _ = ((emptyCoefficientIso (theta := theta) (L := L) d).hom ≫ f.app d) ≫
        G.map g := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k => k ≫ G.map g) (empty_leg_hom (theta := theta) (L := L) d)

/-- The actual empty original slice is constructed with all original roots and actions. -/
def empty : OriginalSlice theta L where
  supports _ := ⊥
  map g := emptyAction (theta := theta) (L := L) g
  map_id := emptyAction_id (theta := theta) (L := L)
  map_comp := emptyAction_comp (theta := theta) (L := L)
  map_root := emptyAction_root (theta := theta) (L := L)
  map_endpoint := emptyAction_endpoint (theta := theta) (L := L)

/-- The whole actual empty-support functor retains both original F comparison maps. -/
def emptyFunctorIso : (empty (theta := theta) (L := L)).toFunctor ≅ F :=
  NatIso.ofComponents (fun d => emptyCoefficientIso (theta := theta) (L := L) d) (by
    intro d e g
    change emptyAction (theta := theta) (L := L) g ≫
        (emptyCoefficientIso (theta := theta) (L := L) e).hom =
      (emptyCoefficientIso (theta := theta) (L := L) d).hom ≫ F.map g
    simp only [emptyAction, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The empty slice's source object is isomorphic to the same original identity under F. -/
def emptyUnderIso : Under.mk (empty (theta := theta) (L := L)).root ≅ Under.mk (𝟙 F) :=
  Under.isoMk (emptyFunctorIso (theta := theta) (L := L)) (by
    apply NatTrans.ext
    funext d
    exact empty_root_hom (theta := theta) (L := L) d)

/-- The chosen empty original support has the actual original source initial UP. -/
def emptyIsInitial : IsInitial (Under.mk (empty (theta := theta) (L := L)).root) :=
  Under.mkIdInitial.ofIso (emptyUnderIso (theta := theta) (L := L)).symm


variable {I : Type uI} [Category.{vI} I] [IsFiltered I]
  (A : I → OriginalSlice theta L)
  (hA : ∀ {i j : I}, (i ⟶ j) → OriginalSlice.Inclusion (A i) (A j))

/-- The compatible original supports form a functor on every original index morphism. -/
abbrev supportFunctor (d : D) : I ⥤ LowerSet (P d) where
  obj i := (A i).supports d
  map h := homOfLE ((hA h).le d)

/-- The literal union support is the original supremum of all original lower supports. -/
abbrev support (d : D) : LowerSet (P d) :=
  LowerSetColimitData.filteredUnion (supportFunctor A hA d)

/-- The union component is the same chosen lower-colimit object under F(d). -/
abbrev component (d : D) : Under (F.obj d) := (L d).obj (support A hA d)

/-- The compatible original component diagram retains every chosen lower map. -/
abbrev componentDiagram (d : D) : I ⥤ Under (F.obj d) :=
  (L d).filteredDiagram (supportFunctor A hA d)

/-- The union cocone retains every original lower comparison leg. -/
abbrev componentCocone (d : D) : Cocone (componentDiagram A hA d) :=
  (L d).filteredCocone (supportFunctor A hA d)

/-- The original lower-colimit data constructs the actual component union UP. -/
def componentIsColimit (d : D) : IsColimit (componentCocone A hA d) :=
  (L d).isColimitFilteredCocone (B := supportFunctor A hA d)

/-- The original leg from a member component into the same chosen union component. -/
abbrev leg (i : I) (d : D) : (L d).obj ((A i).supports d) ⟶ component A hA d :=
  (componentCocone A hA d).ι.app i

omit [IsFiltered I] in
/-- Each original index morphism retains the compatible original lower-leg equation. -/
theorem map_leg {i j : I} (h : i ⟶ j) (d : D) :
    (L d).map ((hA h).le d) ≫ leg A hA j d = leg A hA i d := by
  change (L d).map _ ≫ (L d).map _ = (L d).map _
  rw [(L d).map_comp]

/-- Connected original union cocones retain their UP after forgetting the fixed root. -/
def coefficientIsColimit (d : D) :
    IsColimit ((Under.forget (F.obj d)).mapCocone (componentCocone A hA d)) := by
  letI : IsConnected I := IsFiltered.isConnected I
  letI : PreservesColimitsOfShape I (Under.forget (F.obj d)) := inferInstance
  exact isColimitOfPreserves (Under.forget (F.obj d)) (componentIsColimit A hA d)

/-- Original union legs detect equality of coefficient arrows without cancellation. -/
theorem coefficient_hom_ext (d : D) {Z : C} {p q : (component A hA d).right ⟶ Z}
    (h : ∀ i, (leg A hA i d).right ≫ p = (leg A hA i d).right ≫ q) : p = q :=
  (coefficientIsColimit A hA d).hom_ext h

/-- Compatible original action legs give an actual cocone under the correct F(d). -/
abbrev actionCocone {d e : D} (g : d ⟶ e) : Cocone (componentDiagram A hA d) where
  pt := (Under.map (F.map g)).obj (component A hA e)
  ι :=
    { app i := Under.homMk ((A i).map g ≫ (leg A hA i e).right) (by
        change ((L d).obj ((A i).supports d)).hom ≫
            ((A i).map g ≫ (leg A hA i e).right) =
          F.map g ≫ (component A hA e).hom
        rw [← Category.assoc, (A i).map_root, Category.assoc, Under.w])
      naturality i j h := by
        apply Under.UnderMorphism.ext
        change ((L d).map ((hA h).le d)).right ≫
            ((A j).map g ≫ (leg A hA j e).right) =
          ((A i).map g ≫ (leg A hA i e).right) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, (hA h).naturality,
          Category.assoc, ← Under.comp_right, map_leg A hA h e] }

/-- The union action is the actual original source-side colimit descender. -/
def actionUnder {d e : D} (g : d ⟶ e) :
    component A hA d ⟶ (Under.map (F.map g)).obj (component A hA e) :=
  (componentIsColimit A hA d).desc (actionCocone A hA g)

/-- The full original coefficient action retains that same actual descender. -/
abbrev action {d e : D} (g : d ⟶ e) :
    (component A hA d).right ⟶ (component A hA e).right := (actionUnder A hA g).right

/-- Every original action leg commutes with the original union comparison maps. -/
theorem action_fac {d e : D} (g : d ⟶ e) (i : I) :
    (leg A hA i d).right ≫ action A hA g = (A i).map g ≫ (leg A hA i e).right :=
  congrArg Under.Hom.right ((componentIsColimit A hA d).fac (actionCocone A hA g) i)

/-- The actual union action is unital on every original component. -/
theorem action_id (d : D) : action A hA (𝟙 d) = 𝟙 (component A hA d).right := by
  apply coefficient_hom_ext A hA d
  intro i
  rw [action_fac, (A i).map_id, Category.id_comp, Category.comp_id]

/-- Each original composable pair retains its full union action composition law. -/
theorem action_comp {d e k : D} (g : d ⟶ e) (h : e ⟶ k) :
    action A hA (g ≫ h) = action A hA g ≫ action A hA h := by
  apply coefficient_hom_ext A hA d
  intro i
  rw [action_fac A hA (g ≫ h) i, (A i).map_comp]
  conv_rhs =>
    rw [← Category.assoc, action_fac A hA g i, Category.assoc, action_fac A hA h i]
  exact Category.assoc _ _ _

/-- The full original source-root square holds for every union action. -/
theorem action_root {d e : D} (g : d ⟶ e) :
    (component A hA d).hom ≫ action A hA g = F.map g ≫ (component A hA e).hom :=
  Under.w (actionUnder A hA g)

omit [IsFiltered I] in
/-- Every original union leg retains its actual original endpoint comparison. -/
theorem leg_endpoint (i : I) (d : D) :
    (leg A hA i d).right ≫ DiagramActionCapture.leg theta L d (support A hA d) =
      DiagramActionCapture.leg theta L d ((A i).supports d) :=
  inclusion_leg theta L d (le_iSup (fun j => (A j).supports d) i)

/-- The target square follows from actual union cocone legs and original member actions. -/
theorem action_endpoint {d e : D} (g : d ⟶ e) :
    action A hA g ≫ DiagramActionCapture.leg theta L e (support A hA e) =
      DiagramActionCapture.leg theta L d (support A hA d) ≫ G.map g := by
  apply coefficient_hom_ext A hA d
  intro i
  rw [← Category.assoc, action_fac A hA g i, Category.assoc, leg_endpoint,
    (A i).map_endpoint]
  conv_rhs => rw [← Category.assoc, leg_endpoint A hA i d]

/-- The genuine original filtered union constructs all slice fields and complete actions. -/
def union : OriginalSlice theta L where
  supports := support A hA
  map g := action A hA g
  map_id := action_id A hA
  map_comp := action_comp A hA
  map_root := action_root A hA
  map_endpoint := action_endpoint A hA

/-- Each original member has its full natural inclusion into the constructed union. -/
def inclusion (i : I) : OriginalSlice.Inclusion (A i) (union A hA) where
  le d := le_iSup (fun j => (A j).supports d) i
  naturality g := action_fac A hA g i

/-- The whole original union retains the strict original arrow f. -/
theorem factor : (union A hA).root ≫ (union A hA).target = f :=
  OriginalSlice.factor (union A hA)

/-- All original member roots and maps form the actual diagram under unchanged F. -/
abbrev diagram : I ⥤ Under F where
  obj i := Under.mk (A i).root
  map h := Under.homMk (hA h).toNatTrans (inclusion_root (hA h))
  map_id i := by
    apply Under.UnderMorphism.ext
    apply NatTrans.ext
    funext d
    change ((L d).map (le_refl ((A i).supports d))).right = 𝟙 _
    exact congrArg Under.Hom.right ((L d).map_id ((A i).supports d))
  map_comp h k := by
    apply Under.UnderMorphism.ext
    apply NatTrans.ext
    funext d
    change ((L d).map _).right = ((L d).map ((hA h).le d)).right ≫
      ((L d).map ((hA k).le d)).right
    exact congrArg Under.Hom.right ((L d).map_comp ((hA h).le d) ((hA k).le d)).symm

/-- The full original union cocone retains its actual original member inclusions. -/
abbrev cocone : Cocone (diagram A hA) where
  pt := Under.mk (union A hA).root
  ι :=
    { app i := Under.homMk (inclusion A hA i).toNatTrans
        (inclusion_root (inclusion A hA i))
      naturality i j h := by
        apply Under.UnderMorphism.ext
        apply NatTrans.ext
        funext d
        change ((L d).map ((hA h).le d)).right ≫ (leg A hA j d).right =
          (leg A hA i d).right ≫ 𝟙 _
        rw [Category.comp_id, ← Under.comp_right, map_leg A hA h d] }


section UniversalProperty

variable (t : Cocone (diagram A hA))

/-- Evaluate the actual whole original cocone at the original root F(d). -/
abbrev evaluatedCocone (d : D) : Cocone (componentDiagram A hA d) where
  pt := Under.mk (t.pt.hom.app d)
  ι :=
    { app i := Under.homMk ((t.ι.app i).right.app d) (by
        exact congrArg (fun k : F ⟶ t.pt.right => k.app d) (Under.w (t.ι.app i)))
      naturality i j h := by
        apply Under.UnderMorphism.ext
        have ht := congrArg
          (fun k : (diagram A hA).obj i ⟶ t.pt => k.right.app d) (t.w h)
        change ((L d).map ((hA h).le d)).right ≫ (t.ι.app j).right.app d =
          (t.ι.app i).right.app d ≫ 𝟙 _
        rw [Category.comp_id]
        change ((L d).map ((hA h).le d)).right ≫ (t.ι.app j).right.app d =
          (t.ι.app i).right.app d at ht
        exact ht }

/-- The whole original member cocone gives the same actual component descender. -/
abbrev componentDesc (d : D) : component A hA d ⟶ Under.mk (t.pt.hom.app d) :=
  (componentIsColimit A hA d).desc (evaluatedCocone A hA t d)

/-- Every actual original member leg retains its full evaluated descender equation. -/
theorem componentDesc_fac (d : D) (i : I) :
    (leg A hA i d).right ≫ (componentDesc A hA t d).right = (t.ι.app i).right.app d :=
  congrArg Under.Hom.right
    ((componentIsColimit A hA d).fac (evaluatedCocone A hA t d) i)

/-- Original member naturalities derive the full union descender naturality. -/
theorem componentDesc_naturality {d e : D} (g : d ⟶ e) :
    action A hA g ≫ (componentDesc A hA t e).right =
      (componentDesc A hA t d).right ≫ t.pt.right.map g := by
  apply coefficient_hom_ext A hA d
  intro i
  rw [← Category.assoc, action_fac A hA g i, Category.assoc, componentDesc_fac,
    ← Category.assoc, componentDesc_fac]
  exact (t.ι.app i).right.naturality g

/-- The actual component descenders form the complete original natural transformation. -/
def wholeDesc : (union A hA).toFunctor ⟶ t.pt.right where
  app d := (componentDesc A hA t d).right
  naturality _ _ g := componentDesc_naturality A hA t g

/-- Its original root square is derived from the same component descenders. -/
theorem wholeDesc_root : (union A hA).root ≫ wholeDesc A hA t = t.pt.hom := by
  apply NatTrans.ext
  funext d
  exact Under.w (componentDesc A hA t d)

/-- The full original descender is a morphism under the same original F. -/
def underDesc : (cocone A hA).pt ⟶ t.pt :=
  Under.homMk (wholeDesc A hA t) (wholeDesc_root A hA t)

/-- Every full original member inclusion retains the original whole cocone leg. -/
theorem underDesc_fac (i : I) :
    (cocone A hA).ι.app i ≫ underDesc A hA t = t.ι.app i := by
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext d
  exact componentDesc_fac A hA t d i

/-- The original member legs determine the whole natural descender uniquely. -/
theorem underDesc_uniq (m : (cocone A hA).pt ⟶ t.pt)
    (hm : ∀ i, (cocone A hA).ι.app i ≫ m = t.ι.app i) :
    m = underDesc A hA t := by
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext d
  apply coefficient_hom_ext A hA d
  intro i
  have hi := congrArg
    (fun k : (diagram A hA).obj i ⟶ t.pt => k.right.app d) (hm i)
  exact hi.trans (componentDesc_fac A hA t d i).symm

end UniversalProperty

/-- The same chosen original union objects and all actions give the whole original colimit UP. -/
def isColimit : IsColimit (cocone A hA) where
  desc t := underDesc A hA t
  fac t i := underDesc_fac A hA t i
  uniq t m hm := underDesc_uniq A hA t m hm


section LinearFamilies

variable {J : Type uI} [LinearOrder J] (B : J → OriginalSlice theta L)

/-- Compatibility means the actual original natural inclusion on every ordered pair. -/
def Compatible : Prop :=
  ∀ i j : J, i ≤ j → Nonempty (OriginalSlice.Inclusion (B i) (B j))

/-- The actual original identity inclusion. -/
def identityInclusion (S : OriginalSlice theta L) : OriginalSlice.Inclusion S S where
  le d := le_refl (S.supports d)
  naturality g := by
    simp only [(L _).map_id, Under.id_right, Category.id_comp, Category.comp_id]

/-- Compose actual original support inclusions and their full naturality squares. -/
def composeInclusion {R S T : OriginalSlice theta L}
    (p : OriginalSlice.Inclusion R S) (q : OriginalSlice.Inclusion S T) :
    OriginalSlice.Inclusion R T where
  le d := (p.le d).trans (q.le d)
  naturality {d e} g := by
    rw [← (L d).map_comp (p.le d) (q.le d), Under.comp_right, Category.assoc,
      q.naturality g, ← Category.assoc, p.naturality g, Category.assoc,
      ← Under.comp_right, (L e).map_comp (p.le e) (q.le e)]

/-- The actual compatible linear family supplies its original morphism inclusions. -/
def familyInclusion (hB : Compatible B) {i j : J} (h : i ⟶ j) :
    OriginalSlice.Inclusion (B i) (B j) := Classical.choice (hB i j (leOfHom h))

/-- Totalize union on recursion inputs, using the original empty slice for incompatible inputs. -/
def familyBefore : OriginalSlice theta L := by
  classical
  exact if h : Nonempty J ∧ Compatible B then
    letI : Nonempty J := h.1
    union B (familyInclusion B h.2)
  else empty (theta := theta) (L := L)

/-- Actual compatible families retain their literal support union, including empty families. -/
theorem familyBefore_support (hB : Compatible B) (d : D) :
    (familyBefore B).supports d = ⨆ j : J, (B j).supports d := by
  classical
  by_cases hn : Nonempty J
  · simp only [familyBefore, dite_eq_left (And.intro hn hB)]
    rfl
  · have he : ¬(Nonempty J ∧ Compatible B) := fun h => hn h.1
    simp only [familyBefore, dite_eq_right he]
    change (⊥ : LowerSet (P d)) = ⨆ j : J, (B j).supports d
    apply le_antisymm bot_le
    apply iSup_le
    intro j
    exact False.elim (hn ⟨j⟩)

/-- Every actual earlier original slice has its full natural inclusion into BEFORE. -/
def familyBeforeInclusion (hB : Compatible B) (j : J) :
    OriginalSlice.Inclusion (B j) (familyBefore B) := by
  classical
  letI : Nonempty J := ⟨j⟩
  have h : Nonempty J ∧ Compatible B := ⟨⟨j⟩, hB⟩
  simp only [familyBefore, dite_eq_left h]
  exact inclusion B (familyInclusion B hB) j

/-- The original linear family diagram retains all actual member roots and lower maps. -/
abbrev familyDiagram (hB : Compatible B) : J ⥤ Under F :=
  diagram B (familyInclusion B hB)

/-- The actual BEFORE cocone uses the same original member inclusion transformations. -/
abbrev familyBeforeCocone (hB : Compatible B) : Cocone (familyDiagram B hB) where
  pt := Under.mk (familyBefore B).root
  ι :=
    { app j := Under.homMk (familyBeforeInclusion B hB j).toNatTrans
        (inclusion_root (familyBeforeInclusion B hB j))
      naturality i j h := by
        apply Under.UnderMorphism.ext
        apply NatTrans.ext
        funext d
        change ((L d).map _).right ≫ ((L d).map _).right =
          ((L d).map _).right ≫ 𝟙 _
        rw [Category.comp_id, ← Under.comp_right, (L d).map_comp] }

/-- Actual compatibility derives the BEFORE union UP; no union UP is supplied. -/
abbrev familyComponentCocone (hB : Compatible B) (d : D) :
    Cocone (componentDiagram B (familyInclusion B hB) d) where
  pt := (L d).obj ((familyBefore B).supports d)
  ι :=
    { app j := (L d).map ((familyBeforeInclusion B hB j).le d)
      naturality i j h := by
        change (L d).map _ ≫ (L d).map _ = (L d).map _ ≫ 𝟙 _
        rw [(L d).map_comp, Category.comp_id] }

/-- The actual linear BEFORE component UP follows from the original lower union UP. -/
def familyComponentIsColimit (hB : Compatible B) (d : D) :
    IsColimit (familyComponentCocone B hB d) := by
  classical
  by_cases hn : Nonempty J
  · letI : Nonempty J := hn
    refine IsColimit.ofIsoColimit
      ((L d).isColimitFilteredCocone (B := supportFunctor B (familyInclusion B hB) d))
      (Cocone.ext ((L d).functor.mapIso
        (eqToIso (familyBefore_support B hB d).symm)) ?_)
    intro j
    change (L d).map _ ≫ (L d).map _ = (L d).map _
    rw [(L d).map_comp]
  · letI : IsEmpty J := ⟨fun j => hn ⟨j⟩⟩
    have hi : IsInitial (familyComponentCocone B hB d).pt := by
      change IsInitial ((L d).obj ((familyBefore B).supports d))
      rw [familyBefore_support B hB d]
      simpa using (L d).isInitialObjBot
    exact
      { desc := fun t => hi.to t.pt
        fac := fun _ j => False.elim (hn ⟨j⟩)
        uniq := fun _ _ _ => hi.hom_ext _ _ }

/-- Actual compatibility derives the whole original BEFORE colimit, including the empty history. -/
def familyBeforeIsColimit (hB : Compatible B) : IsColimit (familyBeforeCocone B hB) := by
  classical
  by_cases hn : Nonempty J
  · letI : Nonempty J := hn
    letI : IsConnected J := IsFiltered.isConnected J
    apply isColimitOfReflects (Under.forget F)
    apply evaluationJointlyReflectsColimits
    intro d
    exact isColimitOfPreserves (Under.forget (F.obj d)) (familyComponentIsColimit B hB d)
  · letI : IsEmpty J := ⟨fun j => hn ⟨j⟩⟩
    have he : ¬(Nonempty J ∧ Compatible B) := fun h => hn h.1
    have hb : familyBefore B = empty (theta := theta) (L := L) := by
      unfold familyBefore
      rw [dite_eq_right he]
    have hi : IsInitial (familyBeforeCocone B hB).pt := by
      change IsInitial (Under.mk (familyBefore B).root)
      rw [hb]
      exact emptyIsInitial (theta := theta) (L := L)
    exact
      { desc := fun t => hi.to t.pt
        fac := fun _ j => False.elim (hn ⟨j⟩)
        uniq := fun _ _ _ => hi.hom_ext _ _ }

end LinearFamilies

end CategoryTheory.SmallObject.OriginalSliceFilteredUnion
