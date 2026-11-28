/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ThetaQuotientSources
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Actual stack-source mapping groupoids and modification restrictions

Maps are strong transformations between the actual Cat-valued source
and target pseudofunctors. Their arrows are native modifications, not
isomorphism classes. Evaluation and restriction act on those exact
transformations and modifications. Parameter pullback retains every
component and every base-change comparison of the original map.

The independent lifting predicate is equivalence of the actual
groupoid of fillers with the terminal groupoid; in particular, it
includes uniqueness of the compatible 2-isomorphism.

References: Alper–Halpern-Leistner–Heinloth, arXiv:1812.01128v5,
§2.3, Definitions 3.10, 3.36 and 3.38.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StackSourceFiltrations

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open scoped Pseudofunctor.StrongTrans

universe u v w
variable {S : Scheme.{u}}

/-- Literal restriction to schemes over the parameter, through Over.map. -/
def parameter (X : RelativeStack S) (T : Over S) :
    Pseudofunctor (LocallyDiscrete (Over T)ᵒᵖ) Cat.{u, u+1} :=
  ((Over.forget T).op.toPseudofunctor).comp X.toPseudofunctor

/-- The actual stack-source family of based maps on the whole parameter site. -/
abbrev Maps (Y X : RelativeStack S) (T : Over S) :=
  parameter Y T ⟶ parameter X T

/-- Actual transformations and their native modification arrows form a groupoid. -/
instance maps_isGroupoid (Y X : RelativeStack S) (T : Over S) :
    IsGroupoid (Maps Y X T) where
  all_isIso {F G} a := by
    have groupoid (V : LocallyDiscrete (Over T)ᵒᵖ) : IsGroupoid ((parameter X T).obj V) :=
      X.isGroupoid ((Over.forget T).obj V.as.unop)
    have iso (V : LocallyDiscrete (Over T)ᵒᵖ) : IsIso ((a.as.app V).toNatTrans) := by
      let _ := groupoid V
      exact NatIso.isIso_of_isIso_app _
    let e : F ≅ G := Pseudofunctor.StrongTrans.isoMk
      (fun V => by
        let _ := iso V
        exact Cat.Hom.isoMk (asIso ((a.as.app V).toNatTrans)))
      (fun f => a.as.naturality f)
    have he : e.hom = a := by
      apply Pseudofunctor.StrongTrans.homCategory.ext
      intro V
      rfl
    rw [← he]
    infer_instance

/-- Evaluation acts on the same source point and all modification components. -/
def evaluate (Y X : RelativeStack S) (T : Over S)
    (y : (parameter Y T).obj (.mk (op (Over.mk (𝟙 T))))) :
    Maps Y X T ⥤ (parameter X T).obj (.mk (op (Over.mk (𝟙 T)))) where
  obj F := (F.app (.mk (op (Over.mk (𝟙 T))))).toFunctor.obj y
  map a := (a.as.app (.mk (op (Over.mk (𝟙 T))))).toNatTrans.app y
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Precomposition is native bicategorical whiskering, on objects and all arrows. -/
def restrict {A B C : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1}}
    (f : A ⟶ B) : (B ⟶ C) ⥤ (A ⟶ C) where
  obj q := Pseudofunctor.StrongTrans.vcomp f q
  map a := Pseudofunctor.StrongTrans.whiskerLeft f a
  map_id q := whiskerLeft_id f q
  map_comp a b := whiskerLeft_comp f a b

/-- Every restriction component is the literal composed source functor. -/
theorem restrict_component
    {A B C : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1}}
    (f : A ⟶ B) (q : B ⟶ C)
    (V : Over S) :
    (((restrict f).obj q).app (.mk (op V))).toFunctor =
      (f.app (.mk (op V))).toFunctor ⋙ (q.app (.mk (op V))).toFunctor := rfl

/-- Postcomposition uses the same target map on every source component. -/
def postcompose {A B C : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1}}
    (f : B ⟶ C) : (A ⟶ B) ⥤ (A ⟶ C) where
  obj q := Pseudofunctor.StrongTrans.vcomp q f
  map a := Pseudofunctor.StrongTrans.whiskerRight a f
  map_id q := id_whiskerRight q f
  map_comp a b := comp_whiskerRight a b f

/-- The actual comparison to a commutative lifting diagram keeps both
legs and the native associator 2-cell. -/
def liftingComparison
    {A B X Z : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1}}
    (i : A ⟶ B) (f : X ⟶ Z) :
    (B ⟶ X) ⥤ IsoFibre (postcompose (A := A) f) (restrict (C := Z) i) :=
  (CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (postcompose (A := A) f) (restrict (C := Z) i) _).obj
      ⟨restrict (C := X) i, postcompose (A := B) f,
        NatIso.ofComponents (fun q => Pseudofunctor.StrongTrans.associator i q f)
      (fun a => by exact associator_naturality_middle i a f)⟩

/-- Unique lifting for all actual diagrams is an equivalence of these
groupoids, retaining the compatible 2-isomorphisms. -/
def HasUniqueDiagramLifts
    {A B X Z : Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat.{u, u + 1}}
    (i : A ⟶ B) (f : X ⟶ Z) : Prop := (liftingComparison i f).IsEquivalence

/-- An actual parameter restriction retains the entire original strong map.
The comparison includes every object and every modification, not just evaluations. -/
structure ParameterReindex (Y X : RelativeStack S) {T V : Over S} (f : V ⟶ T) where
  functor : Maps Y X T ⥤ Maps Y X V
  component : ∀ (q : Maps Y X T) (U : Over V),
    ((functor.obj q).app (.mk (op U))).toFunctor ≅
      (q.app (.mk (op ((Over.map f).obj U)))).toFunctor
  arrow : ∀ {q r : Maps Y X T} (a : q ⟶ r) (U : Over V),
    ((functor.map a).as.app (.mk (op U))).toNatTrans ≫ (component r U).hom =
      (component q U).hom ≫
        (a.as.app (.mk (op ((Over.map f).obj U)))).toNatTrans
  comparison : ∀ (q : Maps Y X T) {U W : Over V} (a : W ⟶ U),
    Functor.whiskerLeft
        ((parameter Y V).map a.op.toLoc).toFunctor (component q W).hom ≫
      (Cat.Hom.toNatIso (q.naturality ((Over.map f).map a).op.toLoc)).hom =
      (Cat.Hom.toNatIso ((functor.obj q).naturality a.op.toLoc)).hom ≫
        Functor.whiskerRight (component q U).hom
          ((parameter X T).map ((Over.map f).map a).op.toLoc).toFunctor

def toUnit (T : Over S) : T ⟶ Over.mk (𝟙 S) := Over.homMk T.hom (by simp)

theorem comp_toUnit {T V : Over S} (f : V ⟶ T) : f ≫ toUnit T = toUnit V := by
  apply Over.OverMorphism.ext
  exact Over.w f

/-- A source point's entire family is its native reindexing from the base. -/
structure SourceSection (Y : RelativeStack S) where
  origin : Y.Fibre (Over.mk (𝟙 S))

def SourceSection.point {Y : RelativeStack S} (D : SourceSection Y) (T : Over S) :
    Y.Fibre T := (Y.toPseudofunctor.map (toUnit T).op.toLoc).toFunctor.obj D.origin

def SourceSection.comparison {Y : RelativeStack S} (D : SourceSection Y)
    {T V : Over S} (f : V ⟶ T) :
    (Y.toPseudofunctor.map f.op.toLoc).toFunctor.obj (D.point T) ≅ D.point V :=
  ((Cat.Hom.toNatIso (Y.toPseudofunctor.mapComp (toUnit T).op.toLoc f.op.toLoc)).app
    D.origin).symm ≪≫
    (Cat.Hom.toNatIso (Y.toPseudofunctor.map₂Iso (eqToIso (by
      change (f ≫ toUnit T).op.toLoc = (toUnit V).op.toLoc
      rw [comp_toUnit])))).app D.origin

/-- Two trait charts and their genuine common generic-fibre 2-isomorphism. -/
structure ModificationSource {Y : RelativeStack S}
    (R K : Over S) (generic : K ⟶ R) where
  first : SourceSection Y
  second : SourceSection Y
  genericIso : first.point K ≅ second.point K

/-- Applying one actual surface map computes both restrictions and their comparison. -/
def modificationFirst {Y X : RelativeStack S} {R K : Over S}
    {generic : K ⟶ R} (D : ModificationSource (Y := Y) R K generic)
    (q : Pseudofunctor.StrongTrans Y.toPseudofunctor X.toPseudofunctor) :
    X.Fibre R := (q.app (.mk (op R))).toFunctor.obj (D.first.point R)

def modificationSecond {Y X : RelativeStack S} {R K : Over S}
    {generic : K ⟶ R} (D : ModificationSource (Y := Y) R K generic)
    (q : Pseudofunctor.StrongTrans Y.toPseudofunctor X.toPseudofunctor) :
    X.Fibre R := (q.app (.mk (op R))).toFunctor.obj (D.second.point R)

/-- The generic comparison is the same q applied to the source comparison,
transported through its actual strong base-change cells. -/
def modificationGenericIso {Y X : RelativeStack S} {R K : Over S}
    {generic : K ⟶ R} (D : ModificationSource (Y := Y) R K generic)
    (q : Pseudofunctor.StrongTrans Y.toPseudofunctor X.toPseudofunctor) :
    (X.toPseudofunctor.map generic.op.toLoc).toFunctor.obj (modificationFirst D q) ≅
      (X.toPseudofunctor.map generic.op.toLoc).toFunctor.obj (modificationSecond D q) :=
  ((Cat.Hom.toNatIso (q.naturality generic.op.toLoc)).app (D.first.point R)).symm ≪≫
    (q.app (.mk (op K))).toFunctor.mapIso (D.first.comparison generic) ≪≫
    (q.app (.mk (op K))).toFunctor.mapIso D.genericIso ≪≫
    ((q.app (.mk (op K))).toFunctor.mapIso (D.second.comparison generic)).symm ≪≫
    (Cat.Hom.toNatIso (q.naturality generic.op.toLoc)).app (D.second.point R)

/-- A unique compatible groupoid filler means equivalence with one point,
including every arrow. It makes no moduli-space assumption. -/
def HasUniqueGroupoidFiller {A : Type v} [Category.{w} A] [IsGroupoid A] : Prop :=
  Nonempty (A ≌ Discrete PUnit.{1})

end MathlibExt.AlgebraicGeometry.StackSourceFiltrations
