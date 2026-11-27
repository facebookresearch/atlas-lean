/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapAssociatedFamilies
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry

/-!
# Whole universal quasimap families and associated-bundle reindexing

The parameter stack represents the actual marked curve/torsor/map
groupoids. Its reindexing is fixed by actual Cartesian curves, torsor
pullbacks, full fibre arrows and the native identity/composition cells.
The universal associated bundle is that of the same actual quotient
point; all its reindexing maps preserve the actual quotient and section.

This records native integrations of existing torsor, Hom-stack and
marked-curve family machinery. It asserts no quasimap stability, finite
type, properness or perfect obstruction theory for arbitrary inputs.

Reference: Ciocan-Fontanine–Kim–Maulik, arXiv:1106.3724v2,
§2.3 and Definition 3.1.6. Generic source category integrations:
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b and
TauCeti 62bbc0596dc3539d488232e4e924a338548ea0a9.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasimapUniversalFamilies

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open GroupTorsorGeometry QuasimapAssociatedFamilies

variable {S : Scheme} (G W : Over S) [GrpObj G] [ModObj G W]
variable (n g : ℕ)

/-- A whole parameter reindex functor is fixed against literal curve and torsor pullbacks. -/
structure FamilyReindex {T V : Over S} (f : V ⟶ T) where
  functor : Family G W n g T ⥤ Family G W n g V
  curve : ∀ F : Family G W n g T, CurveReindex F f
  torsor : ∀ F : Family G W n g T, Reindex G F.quotient.torsor (curve F).overMap
  comparison : ∀ F : Family G W n g T,
    FamilyIso (functor.obj F) (reindexFamily F f (curve F) (torsor F))
  arrow_curve : ∀ {F H : Family G W n g T} (a : F ⟶ H),
    (functor.map a).curve.hom ≫ (comparison H).curve.hom ≫ (curve H).map =
      (comparison F).curve.hom ≫ (curve F).map ≫ a.curve.hom
  arrow_torsor : ∀ {F H : Family G W n g T} (a : F ⟶ H),
    (functor.map a).total.hom ≫ (comparison H).total.hom ≫ (torsor H).original G =
      (comparison F).total.hom ≫ (torsor F).original G ≫ a.total.hom

variable {G W n g}

def FamilyReindex.originalCurve {T V : Over S} {f : V ⟶ T}
    (R : FamilyReindex G W n g f) (F : Family G W n g T) :
    (R.functor.obj F).curve.X ⟶ F.curve.X :=
  (R.comparison F).curve.hom ≫ (R.curve F).map

def FamilyReindex.originalTorsor {T V : Over S} {f : V ⟶ T}
    (R : FamilyReindex G W n g f) (F : Family G W n g T) :
    (R.functor.obj F).quotient.torsor.total ⟶ F.quotient.torsor.total :=
  (R.comparison F).total.hom ≫ (R.torsor F).original G

/-- The actual source moduli stack, with whole based family functors. -/
structure FamilyStack (G W : Over S) [GrpObj G] [ModObj G W] (n g : ℕ) where
  stack : RelativeStack S
  fibre : ∀ T : Over S, stack.Fibre T ≌ Family G W n g T
  reindex : ∀ {T V : Over S} (f : V ⟶ T), FamilyReindex G W n g f
  comparison : ∀ {T V : Over S} (f : V ⟶ T),
    (stack.toPseudofunctor.map f.op.toLoc).toFunctor ⋙ (fibre V).functor ≅
      (fibre T).functor ⋙ (reindex f).functor

def FamilyStack.family (M : FamilyStack G W n g) (T : Over S) (x : M.stack.Fibre T) :
    Family G W n g T := (M.fibre T).functor.obj x

def FamilyStack.originalCurve (M : FamilyStack G W n g)
    {T V : Over S} (f : V ⟶ T) (x : M.stack.Fibre T) :
    (M.family V ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).curve.X ⟶
      (M.family T x).curve.X :=
  ((M.comparison f).hom.app x).curve.hom ≫
    (M.reindex f).originalCurve (M.family T x)

def FamilyStack.originalTorsor (M : FamilyStack G W n g)
    {T V : Over S} (f : V ⟶ T) (x : M.stack.Fibre T) :
    (M.family V ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).quotient.torsor.total ⟶
      (M.family T x).quotient.torsor.total :=
  ((M.comparison f).hom.app x).total.hom ≫
    (M.reindex f).originalTorsor (M.family T x)

/-- Full identity and composition normalization on both actual source maps.
These fix every native 2-cell through the curve/torsor family groupoid. -/
structure FamilyCoherence (M : FamilyStack G W n g) where
  identity_curve : ∀ (T : Over S) (x : M.stack.Fibre T),
    ((M.fibre T).functor.map
      ((Cat.Hom.toNatIso (M.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app x)).curve.hom =
      M.originalCurve (𝟙 T) x
  identity_torsor : ∀ (T : Over S) (x : M.stack.Fibre T),
    ((M.fibre T).functor.map
      ((Cat.Hom.toNatIso (M.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app x)).total.hom =
      M.originalTorsor (𝟙 T) x
  composition_curve : ∀ {T V U : Over S} (f : V ⟶ T) (g : U ⟶ V) (x : M.stack.Fibre T),
    M.originalCurve (g ≫ f) x =
      ((M.fibre U).functor.map
        ((Cat.Hom.toNatIso
          (M.stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app x)).curve.hom ≫
      M.originalCurve g ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x) ≫
      M.originalCurve f x
  composition_torsor : ∀ {T V U : Over S} (f : V ⟶ T) (g : U ⟶ V) (x : M.stack.Fibre T),
    M.originalTorsor (g ≫ f) x =
      ((M.fibre U).functor.map
        ((Cat.Hom.toNatIso
          (M.stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app x)).total.hom ≫
      M.originalTorsor g ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x) ≫
      M.originalTorsor f x

/-- The actual universal associated bundle and its normalized parameter maps. -/
structure UniversalAssociatedFamily (M : FamilyStack G W n g) where
  bundle : ∀ (T : Over S) (x : M.stack.Fibre T), AssociatedFamily (M.family T x)
  arrow : ∀ (T : Over S) {x y : M.stack.Fibre T} (_a : x ⟶ y),
    (bundle T x).bundle ⟶ (bundle T y).bundle
  arrow_over : ∀ (T : Over S) {x y : M.stack.Fibre T} (a : x ⟶ y),
    (arrow T a).left ≫ (bundle T y).projection.left =
      (bundle T x).projection.left ≫ ((M.fibre T).functor.map a).curve.hom
  arrow_quotient : ∀ (T : Over S) {x y : M.stack.Fibre T} (a : x ⟶ y),
    (bundle T x).quotient ≫ arrow T a =
      tensorHom ((M.fibre T).functor.map a).total.hom (𝟙 W) ≫ (bundle T y).quotient
  arrow_section : ∀ (T : Over S) {x y : M.stack.Fibre T} (a : x ⟶ y),
    (bundle T x).sectionMap.left ≫ (arrow T a).left =
      ((M.fibre T).functor.map a).curve.hom ≫ (bundle T y).sectionMap.left
  arrow_identity : ∀ (T : Over S) (x : M.stack.Fibre T), arrow T (𝟙 x) = 𝟙 _
  arrow_composition : ∀ (T : Over S) {x y z : M.stack.Fibre T}
    (a : x ⟶ y) (b : y ⟶ z), arrow T (a ≫ b) = arrow T a ≫ arrow T b
  map : ∀ {T V : Over S} (f : V ⟶ T) (x : M.stack.Fibre T),
    (bundle V ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).bundle ⟶
      (bundle T x).bundle
  square : ∀ {T V : Over S} (f : V ⟶ T) (x : M.stack.Fibre T),
    IsPullback (map f x).left
      (bundle V ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).projection.left
      (bundle T x).projection.left (M.originalCurve f x)
  quotient : ∀ {T V : Over S} (f : V ⟶ T) (x : M.stack.Fibre T),
    (bundle V ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).quotient ≫ map f x =
      tensorHom (M.originalTorsor f x) (𝟙 W) ≫ (bundle T x).quotient
  section_normalized : ∀ {T V : Over S} (f : V ⟶ T) (x : M.stack.Fibre T),
    (bundle V ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).sectionMap.left ≫
      (map f x).left = M.originalCurve f x ≫ (bundle T x).sectionMap.left
  base_naturality : ∀ {T V : Over S} (f : V ⟶ T)
    {x y : M.stack.Fibre T} (a : x ⟶ y),
    arrow V ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.map a) ≫ map f y =
      map f x ≫ arrow T a
  /-- Base change along an identity is the fibre arrow of the stack's unit cell. -/
  map_identity : ∀ (T : Over S) (x : M.stack.Fibre T),
    map (𝟙 T) x =
      arrow T ((Cat.Hom.toNatIso (M.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app x)
  /-- Base change along a composite is the composite of base changes, through the
  fibre arrow of the stack's composition cell. -/
  map_composition : ∀ {T V U : Over S} (f : V ⟶ T) (g : U ⟶ V) (x : M.stack.Fibre T),
    map (g ≫ f) x =
      arrow U ((Cat.Hom.toNatIso
        (M.stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app x) ≫
      map g ((M.stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x) ≫ map f x

end MathlibExt.AlgebraicGeometry.QuasimapUniversalFamilies
