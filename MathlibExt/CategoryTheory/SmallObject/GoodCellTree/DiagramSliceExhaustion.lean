/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramSliceExtensions
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeIncrement

/-!
# The whole original diagram is exhausted by its actual bounded slices

The index arrows are the action-preserving selected lower comparisons. The
endpoint cocone has the literal original natural transformation F to G.
Its universal property is proved from the given component tree colimits,
including all original index actions and the arbitrary original root. The
main results assume that the regular rank `chi` is uncountable
(`Cardinal.aleph0 < chi`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t uD vD uC vC

namespace CategoryTheory.SmallObject.DiagramSliceExhaustion

open Limits BoundedLowerSupport DiagramActionCapture DiagramActionRefinement
  DiagramSliceExtensions

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- Every selected slice is evaluated at the same original component and root. -/
abbrev componentDiagram (d : D) : Slice theta L chi ⥤ Under (F.obj d) where
  obj A := (L d).obj (A.supports d).1
  map p := (L d).map (p.support_le d)
  map_id A := (L d).map_id (A.supports d).1
  map_comp p q := ((L d).map_comp (p.support_le d) (q.support_le d)).symm

/-- The component comparison keeps both given original endpoint isomorphisms. -/
abbrev componentCocone (d : D) : Cocone (componentDiagram theta L chi d) where
  pt := Under.mk (f.app d)
  ι :=
    { app A := legUnder theta L d (A.supports d).1
      naturality A B p := by
        apply Under.UnderMorphism.ext
        change ((L d).map (p.support_le d)).right ≫ leg theta L d (B.supports d).1 =
          leg theta L d (A.supports d).1 ≫ 𝟙 _
        rw [Category.comp_id]
        exact inclusion_leg theta L d (p.support_le d) }

/-- Every original vertex leg retains its entire endpoint comparison function. -/
theorem vertex_endpoint (d : D) (A : Slice theta L chi) (a : (A.supports d).1) :
    (L d).ι (A.supports d).1 a ≫
        (componentCocone theta L chi d).ι.app A ≫
          (theta.component d).endpointIso.inv =
      (theta.component d).tree.inclusion a.1 := by
  dsimp only [componentCocone, legUnder, EndpointDiagramTransport.lowerLeg]
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Category.assoc, (L d).ι_map, (theta.component d).tree.ι_endpointIso_hom]

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)
  (hUncountable : Cardinal.aleph0 < chi)

/-- A seed that contains one actual original vertex and all of its predecessors. -/
def seedFor (d : D) (a : P d) : Supports (P := P) chi := by
  classical
  exact fun e => if h : e = d then
    h.symm ▸ principal chi (good d).predecessor_lt a else empty chi

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
@[simp]
theorem seedFor_same (d : D) (a : P d) :
    seedFor theta chi good d a d = principal chi (good d).predecessor_lt a := by
  classical
  simp [seedFor]

/-- An actual internally chosen bounded slice containing the original vertex. -/
def sliceFor (d : D) (a : P d) : Slice theta L chi :=
  extension theta L chi hArrow good
    (hasCardinalLT_of_finite Empty chi (Fact.out : chi.IsRegular).aleph0_le)
    (fun i : Empty => i.elim) hUncountable (seedFor theta chi good d a)

theorem mem_sliceFor (d : D) (a : P d) :
    a ∈ ((sliceFor theta L chi hArrow good hUncountable d a).supports d).1 := by
  have h := seed_le_extension theta L chi hArrow good
    (hasCardinalLT_of_finite Empty chi (Fact.out : chi.IsRegular).aleph0_le)
    (fun i : Empty => i.elim) hUncountable (seedFor theta chi good d a) d
  rw [seedFor_same] at h
  apply LowerSetColimits.memOfLE h
  exact le_rfl

section ComponentColimit

variable (d : D) (c : Cocone (componentDiagram theta L chi d))

/-- The original vertex function through its actual chosen containing slice. -/
def vertexApp (a : P d) : (theta.component d).tree.vertex a ⟶ c.pt :=
  (L d).ι ((sliceFor theta L chi hArrow good hUncountable d a).supports d).1
      ⟨a, mem_sliceFor theta L chi hArrow good hUncountable d a⟩ ≫
    c.ι.app (sliceFor theta L chi hArrow good hUncountable d a)

/-- A vertex has the same function through every actual containing slice.

The comparison uses two actual inclusion arrows to one larger compatible
slice. An upper bound on labels without their action squares is insufficient.
-/
theorem vertexApp_through (a : P d) (A : Slice theta L chi)
    (ha : a ∈ (A.supports d).1) :
    vertexApp theta L chi hArrow good hUncountable d c a =
      (L d).ι (A.supports d).1 ⟨a, ha⟩ ≫ c.ι.app A := by
  let : IsCardinalFiltered (Slice theta L chi) chi :=
    DiagramSliceExtensions.cardinalFiltered theta L chi hArrow good hUncountable
  let : IsFiltered (Slice theta L chi) :=
    isFiltered_of_isCardinalFiltered (Slice theta L chi) chi
  let B := sliceFor theta L chi hArrow good hUncountable d a
  let E := IsFiltered.max B A
  let b := IsFiltered.leftToMax B A
  let p := IsFiltered.rightToMax B A
  have hb := c.w b
  have hp := c.w p
  change (L d).map (b.support_le d) ≫ c.ι.app E = c.ι.app B at hb
  change (L d).map (p.support_le d) ≫ c.ι.app E = c.ι.app A at hp
  change (L d).ι (B.supports d).1 _ ≫ c.ι.app B = _
  rw [← hb, ← hp, ← Category.assoc, (L d).ι_map, ← Category.assoc, (L d).ι_map]

/-- All original vertex functions form a cocone on the original component tree. -/
def vertexCocone : Cocone (theta.component d).tree.diagram where
  pt := c.pt
  ι :=
    { app a := vertexApp theta L chi hArrow good hUncountable d c a
      naturality a b g := by
        let A := sliceFor theta L chi hArrow good hUncountable d b
        have hb := mem_sliceFor theta L chi hArrow good hUncountable d b
        have ha := ((A.supports d).1).lower (leOfHom g) hb
        change (theta.component d).tree.diagram.map g ≫
            vertexApp theta L chi hArrow good hUncountable d c b =
          vertexApp theta L chi hArrow good hUncountable d c a ≫ 𝟙 _
        rw [Category.comp_id, vertexApp_through theta L chi hArrow good hUncountable d c b A hb,
          vertexApp_through theta L chi hArrow good hUncountable d c a A ha,
          ← Category.assoc]
        have hg : g = homOfLE (leOfHom g) := Subsingleton.elim _ _
        rw [hg]
        exact congrArg (· ≫ c.ι.app A)
          (((L d).cocone (A.supports d).1).w
            (homOfLE (leOfHom g) :
              (⟨a, ha⟩ : (A.supports d).1) ⟶ ⟨b, hb⟩)) }

/-- The same given original tree endpoint descends this whole vertex cocone. -/
abbrev treeDesc : (theta.component d).tree.endpointObj ⟶ c.pt :=
  (theta.component d).tree.endpoint.isColimit.desc
    (vertexCocone theta L chi hArrow good hUncountable d c)

@[reassoc]
theorem treeDesc_fac (a : P d) :
    (theta.component d).tree.inclusion a ≫
      treeDesc theta L chi hArrow good hUncountable d c =
        vertexApp theta L chi hArrow good hUncountable d c a :=
  (theta.component d).tree.endpoint.isColimit.fac
    (vertexCocone theta L chi hArrow good hUncountable d c) a

/-- Descend from the literal original G component using its given inverse comparison. -/
def componentDesc : Under.mk (f.app d) ⟶ c.pt :=
  (theta.component d).endpointIso.inv ≫ treeDesc theta L chi hArrow good hUncountable d c

theorem componentDesc_fac (A : Slice theta L chi) :
    (componentCocone theta L chi d).ι.app A ≫
      componentDesc theta L chi hArrow good hUncountable d c = c.ι.app A := by
  apply (L d).hom_ext
  intro a
  change (L d).ι (A.supports d).1 a ≫
      ((componentCocone theta L chi d).ι.app A ≫
        ((theta.component d).endpointIso.inv ≫
          treeDesc theta L chi hArrow good hUncountable d c)) = _
  calc
    _ = ((L d).ι (A.supports d).1 a ≫
          ((componentCocone theta L chi d).ι.app A ≫ (theta.component d).endpointIso.inv)) ≫
            treeDesc theta L chi hArrow good hUncountable d c := by simp only [Category.assoc]
    _ = (theta.component d).tree.inclusion a.1 ≫
        treeDesc theta L chi hArrow good hUncountable d c := by rw [vertex_endpoint]
    _ = _ := (treeDesc_fac theta L chi hArrow good hUncountable d c a.1).trans
      (vertexApp_through theta L chi hArrow good hUncountable d c a.1 A a.2)

/-- All selected slices detect the unique map out of the original component endpoint. -/
theorem componentDesc_uniq (m : Under.mk (f.app d) ⟶ c.pt)
    (hm : ∀ A : Slice theta L chi,
      (componentCocone theta L chi d).ι.app A ≫ m = c.ι.app A) :
    m = componentDesc theta L chi hArrow good hUncountable d c := by
  apply (cancel_epi (theta.component d).endpointIso.hom).1
  change (theta.component d).endpointIso.hom ≫ m =
    (theta.component d).endpointIso.hom ≫
      ((theta.component d).endpointIso.inv ≫
        treeDesc theta L chi hArrow good hUncountable d c)
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  apply (theta.component d).tree.endpoint.isColimit.hom_ext
  intro a
  let A := sliceFor theta L chi hArrow good hUncountable d a
  have ha := mem_sliceFor theta L chi hArrow good hUncountable d a
  have hv := vertex_endpoint theta L chi d A ⟨a, ha⟩
  have hv' :
      (theta.component d).tree.inclusion a ≫ (theta.component d).endpointIso.hom =
        (L d).ι (A.supports d).1 ⟨a, ha⟩ ≫
          (componentCocone theta L chi d).ι.app A := by
    have h := congrArg (fun k => k ≫ (theta.component d).endpointIso.hom) hv
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm
  rw [← Category.assoc, hv', Category.assoc, hm A, treeDesc_fac]
  exact (vertexApp_through theta L chi hArrow good hUncountable d c a A ha).symm

/-- The endpoint comparison is the actual colimit of all action-preserving slices. -/
def componentIsColimit : IsColimit (componentCocone theta L chi d) where
  desc c := componentDesc theta L chi hArrow good hUncountable d c
  fac c A := componentDesc_fac theta L chi hArrow good hUncountable d c A
  uniq c m hm := componentDesc_uniq theta L chi hArrow good hUncountable d c m hm

end ComponentColimit

section WholeColimit

variable (c : Cocone (Slice.underDiagram (theta := theta) (L := L) (chi := chi)))

/-- Evaluate this entire under-functor cocone, retaining its actual root equations. -/
abbrev evaluatedCocone (d : D) : Cocone (componentDiagram theta L chi d) where
  pt := Under.mk (c.pt.hom.app d)
  ι :=
    { app A := Under.homMk ((c.ι.app A).right.app d) (by
        have h := congrArg (fun p : F ⟶ c.pt.right => p.app d) (Under.w (c.ι.app A))
        exact h)
      naturality A B p := by
        apply Under.UnderMorphism.ext
        change ((L d).map (p.support_le d)).right ≫ (c.ι.app B).right.app d =
          (c.ι.app A).right.app d ≫ 𝟙 _
        rw [Category.comp_id]
        have h := congrArg (fun q : A.toFunctor theta L chi ⟶ c.pt.right => q.app d)
          (congrArg Under.Hom.right (c.w p))
        change ((L d).map (p.support_le d)).right ≫ (c.ι.app B).right.app d =
          (c.ι.app A).right.app d at h
        exact h }

/-- Its actual component descender, including the original G root. -/
abbrev evaluatedDesc (d : D) : Under.mk (f.app d) ⟶ Under.mk (c.pt.hom.app d) :=
  componentDesc theta L chi hArrow good hUncountable d (evaluatedCocone theta L chi c d)

/-- Both descender functions commute with every original D action. -/
theorem desc_naturality {d e : D} (g : d ⟶ e) :
    G.map g ≫ (evaluatedDesc theta L chi hArrow good hUncountable c e).right =
      (evaluatedDesc theta L chi hArrow good hUncountable c d).right ≫ c.pt.right.map g := by
  let Z : Under (F.obj d) := Under.mk (F.map g ≫ c.pt.hom.app e)
  let p : Under.mk (f.app d) ⟶ Z :=
    Under.homMk
      (G.map g ≫ (evaluatedDesc theta L chi hArrow good hUncountable c e).right) (by
        change f.app d ≫
          (G.map g ≫ (evaluatedDesc theta L chi hArrow good hUncountable c e).right) =
            F.map g ≫ c.pt.hom.app e
        rw [← Category.assoc, ← f.naturality g, Category.assoc]
        exact congrArg (fun k => F.map g ≫ k)
          (Under.w (evaluatedDesc theta L chi hArrow good hUncountable c e)))
  let q : Under.mk (f.app d) ⟶ Z :=
    Under.homMk
      ((evaluatedDesc theta L chi hArrow good hUncountable c d).right ≫ c.pt.right.map g) (by
        change f.app d ≫
          ((evaluatedDesc theta L chi hArrow good hUncountable c d).right ≫ c.pt.right.map g) =
            F.map g ≫ c.pt.hom.app e
        have hroot : f.app d ≫
            (evaluatedDesc theta L chi hArrow good hUncountable c d).right = c.pt.hom.app d :=
          Under.w (evaluatedDesc theta L chi hArrow good hUncountable c d)
        rw [← Category.assoc, hroot]
        exact (c.pt.hom.naturality g).symm)
  have hpq : p = q := (componentIsColimit theta L chi hArrow good hUncountable d).hom_ext
    (fun A => by
      apply Under.UnderMorphism.ext
      change leg theta L d (A.supports d).1 ≫
          (G.map g ≫ (evaluatedDesc theta L chi hArrow good hUncountable c e).right) =
        leg theta L d (A.supports d).1 ≫
          ((evaluatedDesc theta L chi hArrow good hUncountable c d).right ≫ c.pt.right.map g)
      rw [← Category.assoc, ← A.map_endpoint g, Category.assoc]
      have he := congrArg Under.Hom.right
        (componentDesc_fac theta L chi hArrow good hUncountable e
          (evaluatedCocone theta L chi c e) A)
      have hd := congrArg Under.Hom.right
        (componentDesc_fac theta L chi hArrow good hUncountable d
          (evaluatedCocone theta L chi c d) A)
      change leg theta L e (A.supports e).1 ≫
        (evaluatedDesc theta L chi hArrow good hUncountable c e).right =
          (c.ι.app A).right.app e at he
      change leg theta L d (A.supports d).1 ≫
        (evaluatedDesc theta L chi hArrow good hUncountable c d).right =
          (c.ι.app A).right.app d at hd
      rw [he, ← Category.assoc, hd]
      exact (c.ι.app A).right.naturality g)
  exact congrArg Under.Hom.right hpq

/-- The original G component descenders form one entire natural transformation. -/
def wholeDesc : G ⟶ c.pt.right where
  app d := (evaluatedDesc theta L chi hArrow good hUncountable c d).right
  naturality _ _ g := desc_naturality theta L chi hArrow good hUncountable c g

/-- Its entire root equation belongs to the same actual descender. -/
theorem wholeDesc_root : f ≫ wholeDesc theta L chi hArrow good hUncountable c = c.pt.hom := by
  apply NatTrans.ext
  funext d
  exact Under.w (evaluatedDesc theta L chi hArrow good hUncountable c d)

/-- Promote that exact whole natural transformation under the original F. -/
def underDesc : Under.mk f ⟶ c.pt :=
  Under.homMk (wholeDesc theta L chi hArrow good hUncountable c)
    (wholeDesc_root theta L chi hArrow good hUncountable c)

theorem underDesc_fac (A : Slice theta L chi) :
    (Slice.endpointCocone (theta := theta) (L := L) (chi := chi)).ι.app A ≫
      underDesc theta L chi hArrow good hUncountable c = c.ι.app A := by
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext d
  change leg theta L d (A.supports d).1 ≫
      (evaluatedDesc theta L chi hArrow good hUncountable c d).right =
    (c.ι.app A).right.app d
  have h := congrArg Under.Hom.right
    (componentDesc_fac theta L chi hArrow good hUncountable d
      (evaluatedCocone theta L chi c d) A)
  change leg theta L d (A.supports d).1 ≫
      (evaluatedDesc theta L chi hArrow good hUncountable c d).right =
    (c.ι.app A).right.app d at h
  exact h

theorem underDesc_uniq (m : Under.mk f ⟶ c.pt)
    (hm : ∀ A : Slice theta L chi,
      (Slice.endpointCocone (theta := theta) (L := L) (chi := chi)).ι.app A ≫ m = c.ι.app A) :
    m = underDesc theta L chi hArrow good hUncountable c := by
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext d
  let md : Under.mk (f.app d) ⟶ Under.mk (c.pt.hom.app d) :=
    Under.homMk (m.right.app d) (by
      exact congrArg (fun p : F ⟶ c.pt.right => p.app d) (Under.w m))
  have hd : md = evaluatedDesc theta L chi hArrow good hUncountable c d :=
    componentDesc_uniq theta L chi hArrow good hUncountable d
      (evaluatedCocone theta L chi c d) md (fun A => by
        apply Under.UnderMorphism.ext
        exact congrArg (fun p : A.toFunctor theta L chi ⟶ c.pt.right => p.app d)
          (congrArg Under.Hom.right (hm A)))
  exact congrArg Under.Hom.right hd

/-- The actual full original arrow is the colimit of its action-preserving bounded slices. -/
def isColimit : IsColimit (Slice.endpointCocone (theta := theta) (L := L) (chi := chi)) where
  desc c := underDesc theta L chi hArrow good hUncountable c
  fac c A := underDesc_fac theta L chi hArrow good hUncountable c A
  uniq c m hm := underDesc_uniq theta L chi hArrow good hUncountable c m hm

end WholeColimit

include hArrow good hUncountable in
/-- Every original component label occurs in the bounded slice exhaustion. -/
theorem labels_exhausted (d : D) :
    (⨆ A : Slice theta L chi, (A.supports d).1) = (⊤ : LowerSet (P d)) := by
  ext a
  constructor
  · intro _
    trivial
  · intro _
    exact LowerSet.mem_iSup_iff.2
      ⟨sliceFor theta L chi hArrow good hUncountable d a,
        mem_sliceFor theta L chi hArrow good hUncountable d a⟩

/-- An inclusion of actual diagram slices has the literal relative tree at every object. -/
def inclusionTree {A B : Slice theta L chi} (p : A ⟶ B) (d : D) :
    CellTree s ((L d).obj (A.supports d).1).right
      (P := CellTree.Increment (A.supports d).1 (B.supports d).1) :=
  CellTreeIncrement.tree (theta.component d).tree (L d)
    (A.supports d).1 (B.supports d).1 (p.support_le d)

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- These literal relative component trees represent the actual entire inclusion transformation. -/
theorem inclusionTree_hom {A B : Slice theta L chi} (p : A ⟶ B) (d : D) :
    (inclusionTree theta L chi p d).hom = p.toNatTrans.app d := rfl

section OriginalUnboundedSlices

/-- An actual existing slice, whose accumulated original labels need not be bounded. -/
structure OriginalSlice where
  /-- The original lower cell labels retained at every component. -/
  supports (d : D) : LowerSet (P d)
  /-- The original action on the selected component colimits. -/
  map {d e : D} (g : d ⟶ e) :
    ((L d).obj (supports d)).right ⟶ ((L e).obj (supports e)).right
  map_id (d : D) : map (𝟙 d) = 𝟙 _
  map_comp {d m e : D} (g : d ⟶ m) (h : m ⟶ e) : map (g ≫ h) = map g ≫ map h
  map_root {d e : D} (g : d ⟶ e) :
    ((L d).obj (supports d)).hom ≫ map g =
      F.map g ≫ ((L e).obj (supports e)).hom
  map_endpoint {d e : D} (g : d ⟶ e) :
    map g ≫ leg theta L e (supports e) = leg theta L d (supports d) ≫ G.map g

namespace OriginalSlice

variable {theta L}

/-- Keep every map of the given bounded slice when forgetting its bound. -/
def ofBounded (A : Slice theta L chi) : OriginalSlice theta L where
  supports d := (A.supports d).1
  map g := A.map g
  map_id := A.map_id
  map_comp := A.map_comp
  map_root := A.map_root
  map_endpoint := A.map_endpoint

/-- The whole original functor of an existing slice. -/
def toFunctor (A : OriginalSlice theta L) : D ⥤ C where
  obj d := ((L d).obj (A.supports d)).right
  map g := A.map g
  map_id := A.map_id
  map_comp := A.map_comp

/-- The original root functions with all original naturality squares. -/
def root (A : OriginalSlice theta L) : F ⟶ A.toFunctor where
  app d := ((L d).obj (A.supports d)).hom
  naturality _ _ g := (A.map_root g).symm

/-- The original target functions with all original naturality squares. -/
def target (A : OriginalSlice theta L) : A.toFunctor ⟶ G where
  app d := leg theta L d (A.supports d)
  naturality _ _ g := A.map_endpoint g

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- Both natural transformations retain the strict original whole factor equation. -/
theorem factor (A : OriginalSlice theta L) : A.root ≫ A.target = f := by
  apply NatTrans.ext
  funext d
  exact leg_root theta L d (A.supports d)

/-- The original comparison carrier, kept in `Type` as for bounded-slice morphisms. -/
@[nolint structureInType]
structure Inclusion (A B : OriginalSlice theta L) : Type where
  le (d : D) : A.supports d ≤ B.supports d
  naturality {d e : D} (g : d ⟶ e) :
    ((L d).map (le d)).right ≫ B.map g = A.map g ≫ ((L e).map (le e)).right

/-- The same component comparisons form the entire original natural transformation. -/
def Inclusion.toNatTrans {A B : OriginalSlice theta L} (p : Inclusion A B) :
    A.toFunctor ⟶ B.toFunctor where
  app d := ((L d).map (p.le d)).right
  naturality _ _ g := (p.naturality g).symm

end OriginalSlice

section Union

variable (A B : OriginalSlice theta L)
  (t : ∀ {d e : D} (_g : d ⟶ e),
    ((L d).obj (A.supports d ⊓ B.supports d)).right ⟶
      ((L e).obj (A.supports e ⊓ B.supports e)).right)
  (htA : ∀ {d e : D} (g : d ⟶ e),
    ((L d).map (inf_le_left : A.supports d ⊓ B.supports d ≤ A.supports d)).right ≫
        A.map g = t g ≫
      ((L e).map (inf_le_left : A.supports e ⊓ B.supports e ≤ A.supports e)).right)
  (htB : ∀ {d e : D} (g : d ⟶ e),
    ((L d).map (inf_le_right : A.supports d ⊓ B.supports d ≤ B.supports d)).right ≫
        B.map g = t g ≫
      ((L e).map (inf_le_right : A.supports e ⊓ B.supports e ≤ B.supports e)).right)

/-- The same original union object, under its original component root. -/
abbrev unionObject (d : D) : Under (F.obj d) := (L d).obj (A.supports d ⊔ B.supports d)

/-- The first original slice action into the selected target union. -/
def leftUnionAction {d e : D} (g : d ⟶ e) :
    (L d).obj (A.supports d) ⟶ (Under.map (F.map g)).obj (unionObject theta L A B e) :=
  Under.homMk
    (A.map g ≫ ((L e).map (le_sup_left : A.supports e ≤ A.supports e ⊔ B.supports e)).right)
    (by
      change ((L d).obj (A.supports d)).hom ≫
        (A.map g ≫ ((L e).map le_sup_left).right) =
          F.map g ≫ ((L e).obj (A.supports e ⊔ B.supports e)).hom
      rw [← Category.assoc, A.map_root, Category.assoc, Under.w])

/-- The second original slice action into that same selected target union. -/
def rightUnionAction {d e : D} (g : d ⟶ e) :
    (L d).obj (B.supports d) ⟶ (Under.map (F.map g)).obj (unionObject theta L A B e) :=
  Under.homMk
    (B.map g ≫ ((L e).map (le_sup_right : B.supports e ≤ A.supports e ⊔ B.supports e)).right)
    (by
      change ((L d).obj (B.supports d)).hom ≫
        (B.map g ≫ ((L e).map le_sup_right).right) =
          F.map g ≫ ((L e).obj (A.supports e ⊔ B.supports e)).hom
      rw [← Category.assoc, B.map_root, Category.assoc, Under.w])

include t htA htB in
omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- Agreement is proved from the actual intersection action, retaining both inclusions. -/
theorem unionAction_agreement {d e : D} (g : d ⟶ e) :
    (L d).map (inf_le_left : A.supports d ⊓ B.supports d ≤ A.supports d) ≫
        leftUnionAction theta L A B g =
      (L d).map (inf_le_right : A.supports d ⊓ B.supports d ≤ B.supports d) ≫
        rightUnionAction theta L A B g := by
  apply Under.UnderMorphism.ext
  change ((L d).map _).right ≫ (A.map g ≫ ((L e).map _).right) =
    ((L d).map _).right ≫ (B.map g ≫ ((L e).map _).right)
  rw [← Category.assoc, htA g, ← Category.assoc, htB g,
    Category.assoc, Category.assoc, ← Under.comp_right, ← Under.comp_right,
    (L e).map_comp, (L e).map_comp]

/-- The action is the original source-union descender, under its correct original root. -/
def unionActionUnder {d e : D} (g : d ⟶ e) :
    unionObject theta L A B d ⟶ (Under.map (F.map g)).obj (unionObject theta L A B e) :=
  (L d).unionDesc (leftUnionAction theta L A B g) (rightUnionAction theta L A B g)
    (unionAction_agreement theta L A B t htA htB g)

/-- The raw union action retains that exact original descender. -/
abbrev unionAction {d e : D} (g : d ⟶ e) :=
  (unionActionUnder theta L A B t htA htB g).right

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem unionAction_left {d e : D} (g : d ⟶ e) :
    ((L d).map (le_sup_left : A.supports d ≤ A.supports d ⊔ B.supports d)).right ≫
        unionAction theta L A B t htA htB g =
      A.map g ≫ ((L e).map (le_sup_left : A.supports e ≤ A.supports e ⊔ B.supports e)).right :=
  congrArg Under.Hom.right ((L d).map_left_unionDesc _ _ _)

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem unionAction_right {d e : D} (g : d ⟶ e) :
    ((L d).map (le_sup_right : B.supports d ≤ A.supports d ⊔ B.supports d)).right ≫
        unionAction theta L A B t htA htB g =
      B.map g ≫ ((L e).map (le_sup_right : B.supports e ≤ A.supports e ⊔ B.supports e)).right :=
  congrArg Under.Hom.right ((L d).map_right_unionDesc _ _ _)

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- These are the two genuine pushout legs, with no monomorphism hypothesis. -/
theorem unionCoefficientIsPushout (d : D) :
    IsPushout
      ((L d).map (inf_le_left : A.supports d ⊓ B.supports d ≤ A.supports d)).right
      ((L d).map (inf_le_right : A.supports d ⊓ B.supports d ≤ B.supports d)).right
      ((L d).map (le_sup_left : A.supports d ≤ A.supports d ⊔ B.supports d)).right
      ((L d).map (le_sup_right : B.supports d ≤ A.supports d ⊔ B.supports d)).right :=
  ((L d).union_isPushout (A.supports d) (B.supports d)).map (Under.forget (F.obj d))

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem unionAction_id (d : D) :
    unionAction theta L A B t htA htB (𝟙 d) = 𝟙 (unionObject theta L A B d).right := by
  apply (unionCoefficientIsPushout theta L A B d).hom_ext
  · rw [unionAction_left, A.map_id, Category.id_comp, Category.comp_id]
  · rw [unionAction_right, B.map_id, Category.id_comp, Category.comp_id]

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem unionAction_comp {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    unionAction theta L A B t htA htB (g ≫ h) =
      unionAction theta L A B t htA htB g ≫ unionAction theta L A B t htA htB h := by
  apply (unionCoefficientIsPushout theta L A B d).hom_ext
  · rw [unionAction_left, A.map_comp, Category.assoc, ← unionAction_left theta L A B t htA htB h,
      ← Category.assoc, ← unionAction_left theta L A B t htA htB g, Category.assoc]
  · rw [unionAction_right, B.map_comp, Category.assoc, ← unionAction_right theta L A B t htA htB h,
      ← Category.assoc, ← unionAction_right theta L A B t htA htB g, Category.assoc]

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem unionAction_endpoint {d e : D} (g : d ⟶ e) :
    unionAction theta L A B t htA htB g ≫ leg theta L e (A.supports e ⊔ B.supports e) =
      leg theta L d (A.supports d ⊔ B.supports d) ≫ G.map g := by
  apply (unionCoefficientIsPushout theta L A B d).hom_ext
  · rw [← Category.assoc, unionAction_left, Category.assoc, inclusion_leg,
      A.map_endpoint, ← Category.assoc, inclusion_leg]
  · rw [← Category.assoc, unionAction_right, Category.assoc, inclusion_leg,
      B.map_endpoint, ← Category.assoc, inclusion_leg]

/-- The actual union of existing slices, with its whole original actions. -/
def unionSlice : OriginalSlice theta L where
  supports d := A.supports d ⊔ B.supports d
  map g := unionAction theta L A B t htA htB g
  map_id := unionAction_id theta L A B t htA htB
  map_comp := unionAction_comp theta L A B t htA htB
  map_root g := Under.w (unionActionUnder theta L A B t htA htB g)
  map_endpoint := unionAction_endpoint theta L A B t htA htB

/-- The first original lower inclusion remains a natural transformation of whole slices. -/
def leftUnionInclusion : OriginalSlice.Inclusion A (unionSlice theta L A B t htA htB) where
  le _d := le_sup_left
  naturality g := unionAction_left theta L A B t htA htB g

/-- The second original lower inclusion remains a natural transformation of whole slices. -/
def rightUnionInclusion : OriginalSlice.Inclusion B (unionSlice theta L A B t htA htB) where
  le _d := le_sup_right
  naturality g := unionAction_right theta L A B t htA htB g

end Union

end OriginalUnboundedSlices

section Interleaving

variable {Q : Type w} [PartialOrder Q]
  (A : LowerSet Q) (B C : ℕ → LowerSet Q)
  (hBC : ∀ n, C n ≤ A ⊓ B n)
  (hCB : ∀ n, A ⊓ B n ≤ C (n + 1))

include hBC hCB in
/-- The two actual alternating label unions have precisely the required intersection. -/
theorem interleaved_intersection : (⨆ n, C n) = A ⊓ (⨆ n, B n) := by
  ext a
  constructor
  · intro ha
    rcases LowerSet.mem_iSup_iff.1 ha with ⟨n, han⟩
    have hh := LowerSetColimits.memOfLE (hBC n) han
    exact ⟨hh.1, LowerSet.mem_iSup_iff.2 ⟨n, hh.2⟩⟩
  · intro ha
    rcases LowerSet.mem_iSup_iff.1 ha.2 with ⟨n, han⟩
    exact LowerSet.mem_iSup_iff.2
      ⟨n + 1, LowerSetColimits.memOfLE (hCB n) ⟨ha.1, han⟩⟩

include A hBC hCB hUncountable in
/-- A bounded first lane gives a bounded actual intersection, at the same original rank. -/
theorem interleaved_intersection_small (hB : ∀ n, HasCardinalLT (B n : Set Q) chi) :
    HasCardinalLT ((⨆ n, C n : LowerSet Q) : Set Q) chi := by
  rw [interleaved_intersection A B C hBC hCB]
  exact (GoodOrderBounds.indexedUnionLt chi B
      (GoodOrderBounds.natLt chi hUncountable) hB).of_injective
    (fun a : ((A ⊓ (⨆ n, B n) : LowerSet Q) : Set Q) =>
      (⟨a.1, a.2.2⟩ : ((⨆ n, B n : LowerSet Q) : Set Q)))
    (by
      intro a b h
      exact Subtype.ext (congrArg
        (fun z : ((⨆ n, B n : LowerSet Q) : Set Q) => z.1) h))

end Interleaving

end CategoryTheory.SmallObject.DiagramSliceExhaustion
