/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FramedRubberFamilies

/-!
# Actual moduli of framed rubber families

The stack represents the full groupoid of actual standard-target frames
and their coordinate-preserving arrows on every scheme. Every reindex,
unit/composition cell and the forgetful map is pinned to its actual
source/target Cartesian maps. Source: Jun Li arXiv:math/0009097v1,
Section4; JPPZ arXiv:1602.04705v2, Section0.2.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.FramedRubberModuliModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels RubberMapFamilies RubberModuliStackModels
open StackCycleGeometry StackCycleRelations

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  (m : ℕ) {g n : ℕ} (a : Fin n → ℤ)

structure Model where
  stack : Stack (Spec (.of k))
  family : ∀ T : Over (Spec (.of k)),
    stack.Fibre T ⥤ FramedRubberFamilies.StableFamily O P D R S m (g := g) a T
  equivalence : ∀ T : Over (Spec (.of k)), (family T).IsEquivalence
  dm : stack.IsDeligneMumfordStack
  finiteType : FiniteTypeArtin k stack
  reindex : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U) (x : stack.Fibre U),
    FramedRubberFamilies.BaseChange O P D R S m a h
      ((family T).obj ((pull stack h).obj x)).obj ((family U).obj x).obj
  target_naturality : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U)
    {x y : stack.Fibre U} (e : x ⟶ y),
    ((family T).map ((pull stack h).map e)).hom.iso.target.iso.hom ≫ (reindex h y).rubber.target =
      (reindex h x).rubber.target ≫ ((family U).map e).hom.iso.target.iso.hom
  source_naturality : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U)
    {x y : stack.Fibre U} (e : x ⟶ y),
    ((family T).map ((pull stack h).map e)).hom.iso.source.hom ≫ (reindex h y).rubber.source =
      (reindex h x).rubber.source ≫ ((family U).map e).hom.iso.source.hom
  target_unit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.iso.target.iso.hom =
      (reindex (𝟙 T) x).rubber.target
  source_unit : ∀ (T : Over (Spec (.of k))) (x : stack.Fibre T),
    ((family T).map ((stack.toPseudofunctor.mapId (.mk (op T))).hom.toNatTrans.app x)).hom.iso.source.hom =
      (reindex (𝟙 T) x).rubber.source
  target_comp : ∀ {T U V : Over (Spec (.of k))} (h : T ⟶ U) (f : U ⟶ V) (x : stack.Fibre V),
    ((family T).map ((stack.toPseudofunctor.mapComp f.op.toLoc h.op.toLoc).inv.toNatTrans.app x)).hom.iso.target.iso.hom ≫
        (reindex (h ≫ f) x).rubber.target = (reindex h ((pull stack f).obj x)).rubber.target ≫ (reindex f x).rubber.target
  source_comp : ∀ {T U V : Over (Spec (.of k))} (h : T ⟶ U) (f : U ⟶ V) (x : stack.Fibre V),
    ((family T).map ((stack.toPseudofunctor.mapComp f.op.toLoc h.op.toLoc).inv.toNatTrans.app x)).hom.iso.source.hom ≫
        (reindex (h ≫ f) x).rubber.source = (reindex h ((pull stack f).obj x)).rubber.source ≫ (reindex f x).rubber.source

def stableForget (T : Over (Spec (.of k))) :
    FramedRubberFamilies.StableFamily O P D R S m (g := g) a T ⥤
      RubberModuliStackModels.StableFamily O P D R S (g := g) a T where
  obj F := ⟨F.obj.rubber, F.property⟩
  map {F H} e := ⟨(show FramedRubberFamilies.Hom O P D R S m a F.obj H.obj from e.hom).iso⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable (H : Model O P D R S m (g := g) a) (B : RubberModuliModel O P D R S (g := g) a)

def mappedRubber {X : Stack (Spec (.of k))} (f : StackHom X B.stack)
    (T : Over (Spec (.of k))) (x : X.Fibre T) := ((B.family T).obj ((component f T).obj x)).obj

def mappedTargetReindex {X : Stack (Spec (.of k))} (f : StackHom X B.stack)
    {T U : Over (Spec (.of k))} (h : T ⟶ U) (x : X.Fibre U) :
    (mappedRubber O P D R S a B f T ((pull X h).obj x)).target.scheme ⟶
      (mappedRubber O P D R S a B f U x).target.scheme :=
  ((B.family T).map ((Cat.Hom.toNatIso (f.naturality h.op.toLoc)).hom.app x)).hom.target.iso.hom ≫
    (B.reindex h ((component f U).obj x)).target

def mappedSourceReindex {X : Stack (Spec (.of k))} (f : StackHom X B.stack)
    {T U : Over (Spec (.of k))} (h : T ⟶ U) (x : X.Fibre U) :
    (mappedRubber O P D R S a B f T ((pull X h).obj x)).curve.X ⟶
      (mappedRubber O P D R S a B f U x).curve.X :=
  ((B.family T).map ((Cat.Hom.toNatIso (f.naturality h.op.toLoc)).hom.app x)).hom.source.hom ≫
    (B.reindex h ((component f U).obj x)).source

structure Forget where
  map : StackHom H.stack B.stack
  family : ∀ T : Over (Spec (.of k)),
    H.family T ⋙ stableForget O P D R S m a T ≅ component map T ⋙ B.family T
  target_base : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U) (x : H.stack.Fibre U),
    (H.reindex h x).rubber.target ≫ ((family U).hom.app x).hom.target.iso.hom =
      ((family T).hom.app ((pull H.stack h).obj x)).hom.target.iso.hom ≫ mappedTargetReindex O P D R S a B map h x
  source_base : ∀ {T U : Over (Spec (.of k))} (h : T ⟶ U) (x : H.stack.Fibre U),
    (H.reindex h x).rubber.source ≫ ((family U).hom.app x).hom.source.hom =
      ((family T).hom.app ((pull H.stack h).obj x)).hom.source.hom ≫ mappedSourceReindex O P D R S a B map h x

end MathlibExt.AlgebraicGeometry.FramedRubberModuliModels
