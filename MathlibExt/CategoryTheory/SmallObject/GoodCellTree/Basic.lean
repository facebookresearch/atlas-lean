/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# Labelled cell trees over arbitrary roots

A cell tree retains its actual well-founded partial order, original attaching
labels, predecessor colimit cocones, pushout maps, and whole endpoint cocone.
Only the vertex carrier is in the working universe. Attaching labels retain
their independent original universe. No compactness of the root is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t v u vD uD

namespace CategoryTheory.SmallObject

open CategoryTheory.Limits LowerSetColimits

variable {C : Type u} [Category.{v} C] {P : Type w} [PartialOrder P]
  {α : Type t} (s : α → Arrow C) (X : C)

variable {X}

/-- The original strict-predecessor cocone into a vertex under the same root. -/
abbrev cellTreePredecessorCocone (Y : P ⥤ Under X) (a : P) :
    Cocone (restriction Y (LowerSet.Iio a)) where
  pt := Y.obj a
  ι :=
    { app b := Y.map (homOfLE b.2.le)
      naturality b c f := by
        change Y.map (homOfLE (leOfHom f)) ≫ Y.map (homOfLE c.2.le) =
          Y.map (homOfLE b.2.le) ≫ 𝟙 _
        rw [Category.comp_id, ← Y.map_comp]
        rfl }

/-- The actual selected predecessor-to-vertex map. -/
abbrev cellTreePredecessorMap (Y : P ⥤ Under X) (a : P)
    (p : ColimitCocone (restriction Y (LowerSet.Iio a))) :
    p.cocone.pt ⟶ Y.obj a :=
  p.isColimit.desc (cellTreePredecessorCocone Y a)

@[reassoc]
theorem cellTreePredecessorMap_fac (Y : P ⥤ Under X) (a : P)
    (p : ColimitCocone (restriction Y (LowerSet.Iio a))) (b : LowerSet.Iio a) :
    p.cocone.ι.app b ≫ cellTreePredecessorMap Y a p = Y.map (homOfLE b.2.le) :=
  p.isColimit.fac (cellTreePredecessorCocone Y a) b

variable (X)

/-- A labelled cell tree on a vertex carrier `P` over a root `X`.

The strict order on `P` is well founded; it is not required to be linear, and
strict-predecessor sets are not assumed discrete. The data is a diagram
`P ⥤ Under X`, a label `P → α` naming the attaching arrow `s (label a)` of
each vertex `a`, a chosen colimit cocone of the diagram restricted to
`LowerSet.Iio a` at every `a`, an attaching map from `(s (label a)).left` into
the underlying object of that predecessor colimit, and a cell map from
`(s (label a)).right` into the underlying object of the vertex. At every `a`
those exhibit the vertex as the pushout of `s (label a)` along the attaching
map, over the predecessor-to-vertex map. A chosen colimit cocone of the whole
diagram is part of the data. -/
structure CellTree where
  /-- The strict order of the actual vertex carrier is well founded. -/
  wellFounded : WellFounded ((· < ·) : P → P → Prop)
  /-- The actual diagram under the original root. -/
  diagram : P ⥤ Under X
  /-- Every cell occurrence keeps its original attaching-family label. -/
  label : P → α
  /-- The actual chosen strict-predecessor colimit cocone. -/
  predecessor (a : P) : ColimitCocone (restriction diagram (LowerSet.Iio a))
  /-- The original attaching map from the selected cell source. -/
  attaching (a : P) : (s (label a)).left ⟶ (predecessor a).cocone.pt.right
  /-- The original cell-target inclusion into this vertex. -/
  cell (a : P) : (s (label a)).right ⟶ (diagram.obj a).right
  /-- The actual square attaching that original cell over its predecessor colimit. -/
  isPushout (a : P) :
    IsPushout (attaching a) (s (label a)).hom
      (cellTreePredecessorMap diagram a (predecessor a)).right (cell a)
  /-- The actual whole endpoint colimit on the original vertex carrier. -/
  endpoint : ColimitCocone diagram

namespace CellTree

variable {s X} (T : CellTree s X (P := P))

include T in
/-- The actual well-founded-order dictionary from the recorded proof. -/
theorem wellFoundedLT : WellFoundedLT P := T.wellFounded

/-- The original under-object at a vertex. -/
abbrev vertex (a : P) : Under X := T.diagram.obj a

/-- The actual predecessor under-object. -/
abbrev predecessorObj (a : P) : Under X := (T.predecessor a).cocone.pt

/-- The actual whole endpoint under the original root. -/
abbrev endpointObj : Under X := T.endpoint.cocone.pt

/-- The original root-to-endpoint arrow. -/
abbrev hom : X ⟶ T.endpointObj.right := T.endpointObj.hom

/-- The selected predecessor inclusion, with its original colimit choice. -/
abbrev predecessorMap (a : P) : T.predecessorObj a ⟶ T.vertex a :=
  cellTreePredecessorMap T.diagram a (T.predecessor a)

/-- The original vertex inclusion into the endpoint. -/
abbrev inclusion (a : P) : T.vertex a ⟶ T.endpointObj :=
  T.endpoint.cocone.ι.app a

@[reassoc]
theorem predecessorMap_fac (a : P) (b : LowerSet.Iio a) :
    (T.predecessor a).cocone.ι.app b ≫ T.predecessorMap a =
      T.diagram.map (homOfLE b.2.le) :=
  cellTreePredecessorMap_fac T.diagram a (T.predecessor a) b

@[reassoc]
theorem root_predecessorMap (a : P) :
    (T.predecessorObj a).hom ≫ (T.predecessorMap a).right = (T.vertex a).hom :=
  Under.w (T.predecessorMap a)

@[reassoc]
theorem root_inclusion (a : P) :
    (T.vertex a).hom ≫ (T.inclusion a).right = T.hom :=
  Under.w (T.inclusion a)

@[reassoc]
theorem inclusion_naturality {a b : P} (f : a ⟶ b) :
    T.diagram.map f ≫ T.inclusion b = T.inclusion a :=
  T.endpoint.cocone.w f

/-- The original attaching cell commutes with both recorded output maps. -/
theorem attaching_square (a : P) :
    T.attaching a ≫ (T.predecessorMap a).right =
      (s (T.label a)).hom ≫ T.cell a :=
  (T.isPushout a).w

/-- The whole endpoint maps are determined by every original vertex inclusion. -/
theorem endpoint_hom_ext {Z : Under X} {f g : T.endpointObj ⟶ Z}
    (h : ∀ a, T.inclusion a ≫ f = T.inclusion a ≫ g) : f = g :=
  T.endpoint.isColimit.hom_ext h

/-- Choose lower pieces from existing working-size colimits, preserving the root. -/
abbrev lowerData [HasColimitsOfSize.{w, w} C] : LowerSetColimitData T.diagram :=
  LowerSetColimitData.ofHasColimits T.diagram

/-- Every empty lower-colimit choice is isomorphic to the ORIGINAL identity under X. -/
def emptyLowerIso (L : LowerSetColimitData T.diagram) :
    L.obj ⊥ ≅ Under.mk (𝟙 X) :=
  L.isInitialObjBot.uniqueUpToIso Under.mkIdInitial

/-- The chosen lower predecessor and the recorded predecessor have their actual comparison. -/
def predecessorIso (L : LowerSetColimitData T.diagram) (a : P) :
    L.obj (LowerSet.Iio a) ≅ T.predecessorObj a :=
  (L.isColimit (LowerSet.Iio a)).coconePointUniqueUpToIso (T.predecessor a).isColimit

@[reassoc]
theorem ι_predecessorIso_hom (L : LowerSetColimitData T.diagram)
    (a : P) (b : LowerSet.Iio a) :
    L.ι (LowerSet.Iio a) b ≫ (T.predecessorIso L a).hom =
      (T.predecessor a).cocone.ι.app b := by
  exact (L.isColimit (LowerSet.Iio a)).comp_coconePointUniqueUpToIso_hom
    (T.predecessor a).isColimit b

/-- The whole original endpoint comparison preserves the original carrier and root. -/
def endpointIso (L : LowerSetColimitData T.diagram) :
    L.obj ⊤ ≅ T.endpointObj :=
  L.isColimitFullCocone.coconePointUniqueUpToIso T.endpoint.isColimit

@[reassoc]
theorem ι_endpointIso_hom (L : LowerSetColimitData T.diagram) (a : P) :
    L.ι ⊤ ⟨a, by simp⟩ ≫ (T.endpointIso L).hom = T.inclusion a :=
  L.isColimitFullCocone.comp_coconePointUniqueUpToIso_hom T.endpoint.isColimit a

/-- A literal new increment carrier; it is not bundled LowerSet.sdiff. -/
def Increment (B D : LowerSet P) : Type w :=
  {a : P // a ∈ D ∧ a ∉ B}

instance incrementPartialOrder (B D : LowerSet P) : PartialOrder (Increment B D) :=
  inferInstanceAs (PartialOrder {a : P // a ∈ D ∧ a ∉ B})

include T in
/-- The actual increment still has the original inherited well-founded strict order. -/
theorem incrementWellFoundedLT (B D : LowerSet P) : WellFoundedLT (Increment B D) := by
  exact InvImage.wf (fun a : Increment B D => a.1) T.wellFounded

/-- The original attaching label of every literal increment occurrence. -/
def incrementLabel (B D : LowerSet P) (a : Increment B D) : α := T.label a.1

/-- The exact local bounds defining a good tree; the root and total carrier are unconstrained. -/
structure IsGood (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  /-- Every selected original attaching source is κ-presentable. -/
  presentable_source (a : P) : IsCardinalPresentable (s (T.label a)).left κ
  /-- Every selected original attaching target is κ-presentable. -/
  presentable_target (a : P) : IsCardinalPresentable (s (T.label a)).right κ
  /-- Each individual strict predecessor carrier has cardinal below κ. -/
  predecessor_lt (a : P) : HasCardinalLT (Set.Iio a) κ

/-- The actual thin predecessor-arrow bound needed by presentability colimit closure. -/
theorem IsGood.predecessor_arrow_lt {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (h : T.IsGood κ) (a : P) :
    HasCardinalLT (Arrow (Set.Iio a)) κ :=
  (hasCardinalLT_arrow_iff_of_isThin (Set.Iio a) κ
    (Fact.out : κ.IsRegular).aleph0_le).2 (h.predecessor_lt a)

/-- Original endpoint data for a particular arrow, with an actual Under-root isomorphism. -/
structure Presentation {Y : C} (f : X ⟶ Y) where
  /-- The genuine original cell tree. -/
  tree : CellTree s X (P := P)
  /-- Both original endpoint maps, retaining the source as an Under object. -/
  endpointIso : tree.endpointObj ≅ Under.mk f

namespace Presentation

variable {Y : C} {f : X ⟶ Y} (h : Presentation (s := s) (P := P) f)

@[reassoc]
theorem hom_endpointIso_hom : h.tree.hom ≫ h.endpointIso.hom.right = f :=
  Under.w h.endpointIso.hom

@[reassoc]
theorem hom_endpointIso_inv : f ≫ h.endpointIso.inv.right = h.tree.hom :=
  Under.w h.endpointIso.inv

/-- The original arrow comparison is the identity on its source. -/
def arrowIso : Arrow.mk h.tree.hom ≅ Arrow.mk f :=
  Arrow.isoMk (Iso.refl X) ((Under.forget X).mapIso h.endpointIso)
    (by simp)

end Presentation

section Empty

variable [IsEmpty P]

/-- The actual empty-index endpoint cocone with identity under the arbitrary root. -/
abbrev emptyEndpoint (X : C) : ColimitCocone ((Functor.const P).obj (Under.mk (𝟙 X))) where
  cocone :=
    { pt := Under.mk (𝟙 X)
      ι := { app a := isEmptyElim a
             naturality a _ _ := by exact False.elim (IsEmpty.false a) } }
  isColimit :=
    { desc c := Under.mkIdInitial.to c.pt
      fac c a := isEmptyElim a
      uniq c m _ := Under.mkIdInitial.hom_ext m (Under.mkIdInitial.to c.pt) }

/-- The empty labelled tree uses no attaching labels and keeps the original root. -/
def empty (s : α → Arrow C) (X : C) : CellTree s X (P := P) where
  wellFounded := ⟨fun a => isEmptyElim a⟩
  diagram := (Functor.const P).obj (Under.mk (𝟙 X))
  label a := isEmptyElim a
  predecessor a := isEmptyElim a
  attaching a := isEmptyElim a
  cell a := isEmptyElim a
  isPushout a := isEmptyElim a
  endpoint := emptyEndpoint X

@[simp]
theorem empty_hom : (empty s X (P := P)).hom = 𝟙 X := rfl

/-- An empty tree is good at every actual regular cardinal, regardless of its root. -/
theorem emptyIsGood (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (empty s X (P := P)).IsGood κ where
  presentable_source a := isEmptyElim a
  presentable_target a := isEmptyElim a
  predecessor_lt a := isEmptyElim a

end Empty

section Singleton

variable [Unique P] (i : α)
  {Y : C} (a : (s i).left ⟶ X) (f : X ⟶ Y) (b : (s i).right ⟶ Y)
  (hs : IsPushout a (s i).hom f b)

/-- A singleton vertex's strict predecessor carrier is genuinely empty. -/
theorem singleton_predecessors_empty (p : P) : IsEmpty (LowerSet.Iio p) := by
  refine ⟨fun q => ?_⟩
  have hq : q.1 < p := q.2
  have he : q.1 = p := Subsingleton.elim _ _
  rw [he] at hq
  exact False.elim ((lt_irrefl p) hq)

/-- The actual empty predecessor cocone for a one-cell tree. -/
abbrev singletonPredecessor (p : P) :
    ColimitCocone (restriction ((Functor.const P).obj (Under.mk f)) (LowerSet.Iio p)) := by
  letI := singleton_predecessors_empty (P := P) p
  exact
    { cocone :=
        { pt := Under.mk (𝟙 X)
          ι := { app q := isEmptyElim q
                 naturality q _ _ := by exact False.elim (IsEmpty.false q) } }
      isColimit :=
        { desc c := Under.mkIdInitial.to c.pt
          fac c q := isEmptyElim q
          uniq c m _ := Under.mkIdInitial.hom_ext m (Under.mkIdInitial.to c.pt) } }

/-- The original singleton endpoint is the selected vertex itself. -/
abbrev singletonEndpoint : ColimitCocone ((Functor.const P).obj (Under.mk f)) where
  cocone := { pt := Under.mk f, ι := 𝟙 _ }
  isColimit :=
    { desc c := c.ι.app (default : P)
      fac c p := by
        have hp : p = (default : P) := Subsingleton.elim _ _
        subst p
        simp
      uniq c m hm := by simpa using hm (default : P) }

/-- Every ACTUAL pushout square gives a genuine labelled one-cell tree. -/
abbrev ofPushout (s : α → Arrow C) (X : C) (i : α)
    {Y : C} (a : (s i).left ⟶ X) (f : X ⟶ Y) (b : (s i).right ⟶ Y)
    (hs : IsPushout a (s i).hom f b) : CellTree s X (P := P) where
  wellFounded := ⟨fun p => Acc.intro p (fun q h => by
    have he : q = p := Subsingleton.elim _ _
    exact False.elim ((lt_irrefl p) (he ▸ h)))⟩
  diagram := (Functor.const P).obj (Under.mk f)
  label _ := i
  predecessor p := singletonPredecessor f p
  attaching _ := a
  cell _ := b
  isPushout p := by
    have hp :
        cellTreePredecessorMap ((Functor.const P).obj (Under.mk f)) p
          (singletonPredecessor f p) = Under.mkIdInitial.to (Under.mk f) :=
      Under.mkIdInitial.hom_ext _ _
    have hr :
        (cellTreePredecessorMap ((Functor.const P).obj (Under.mk f)) p
          (singletonPredecessor f p)).right = f := by
      simpa only [Under.mkIdInitial_to_right, Under.mk_hom] using
        congrArg (fun k => k.right) hp
    rw [hr]
    exact hs
  endpoint := singletonEndpoint f

@[simp]
theorem ofPushout_label (p : P) : (ofPushout s X i a f b hs (P := P)).label p = i := rfl

@[simp]
theorem ofPushout_hom : (ofPushout s X i a f b hs (P := P)).hom = f := rfl

/-- The chosen one-cell endpoint gives a whole original-arrow presentation. -/
def presentationOfPushout : Presentation (s := s) (P := P) f where
  tree := ofPushout s X i a f b hs
  endpointIso := Iso.refl _

/-- A one-cell tree is good from its actual endpoint bounds, without a bound on X. -/
theorem ofPushoutIsGood (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable (s i).left κ] [IsCardinalPresentable (s i).right κ] :
    (ofPushout s X i a f b hs (P := P)).IsGood κ where
  presentable_source _ := inferInstance
  presentable_target _ := inferInstance
  predecessor_lt p := by
    have : IsEmpty (Set.Iio p) := by
      refine ⟨fun q => ?_⟩
      have hq : q.1 < p := q.2
      have he : q.1 = p := Subsingleton.elim _ _
      rw [he] at hq
      exact False.elim ((lt_irrefl p) hq)
    exact hasCardinalLT_of_finite _ κ (Fact.out : κ.IsRegular).aleph0_le

end Singleton

end CellTree

/-- A labelled tree with genuine local presentability and predecessor bounds. -/
structure GoodCellTree (κ : Cardinal.{w}) [Fact κ.IsRegular] extends CellTree s X (P := P) where
  /-- Its original local goodness witnesses. -/
  good : toCellTree.IsGood κ

/-- Genuine component tree presentations on an arbitrary original ordinary category. -/
structure PointwiseCellTreePresentation
    {D : Type uD} [Category.{vD} D]
    {F G : D ⥤ C} (f : F ⟶ G)
    (A : D → Type w) [∀ d, PartialOrder (A d)] where
  /-- Every original component keeps its actual root and endpoint maps. -/
  component (d : D) : CellTree.Presentation (s := s) (P := A d) (f.app d)

end CategoryTheory.SmallObject
