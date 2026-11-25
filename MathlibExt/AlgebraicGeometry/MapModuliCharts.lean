/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry

/-!
# Native fixed-source and varying-source map-moduli charts

A model's actual fibre groupoid is equated to the actual map families.
Base-change maps are cartesian and respect every marking and target map;
identity/composition are normalized by the native pseudofunctor's cells.
A scheme chart is the actual smooth atlas and its point. The represented
chart fibre is already the isomorphism/point-comparison presheaf in that
atlas, not an unrelated Hom set.

Generic normalization is source-complete in AxiomMath/Stacks,
c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/Stacks/UniversalFamilyNormalisation.lean and
Stacks/HomStack/Basic.lean (Apache 2.0). Their actual native counterpart
pointComparisonPresheaf/RelativeStack atlas is reused here. No moduli
representability theorem is assumed by the family definitions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MapModuliCharts
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

/-- The actual stable-family groupoid on a specified parameter scheme. -/
abbrev StableFamilies {V S : Scheme.{0}} (q : V ⟶ S) (n g : ℕ) (T : Over S) :=
  (show ObjectProperty (Family q n g T.left T.hom) from
    IsGeometricallyStable).FullSubcategory

/-- The moduli fibre is characterized by all actual stable map families. -/
structure VaryingData {V S : Scheme.{0}} (q : V ⟶ S) (n g : ℕ) where
  stack : RelativeStack S
  fibre : ∀ T : Over S, stack.Fibre T ≌ StableFamilies q n g T

namespace VaryingData
variable {V S : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} (M : VaryingData q n g)

abbrev family (T : Over S) (x : M.stack.Fibre T) : Family q n g T.left T.hom :=
  ((M.fibre T).functor.obj x).obj

/-- Actual source curves, and actual family-isomorphism scheme maps. -/
def sourceFunctor (T : Over S) : M.stack.Fibre T ⥤ Scheme.{0} where
  obj x := (M.family T x).curve.X
  map f := ((M.fibre T).functor.map f).hom.iso.hom
  map_id x := by rw [(M.fibre T).functor.map_id]; rfl
  map_comp f g := by rw [(M.fibre T).functor.map_comp f g]; rfl

abbrev pull {T U : Over S} (f : T ⟶ U) :=
  (M.stack.toPseudofunctor.map f.op.toLoc).toFunctor

end VaryingData

/-- A normalized varying-marked-curve moduli model. These fields are actual
geometric comparisons, not a representability/existence conclusion. -/
structure VaryingModel {V S : Scheme.{0}} (q : V ⟶ S) (n g : ℕ)
    extends VaryingData q n g where
  sourceMap : ∀ {T U : Over S} (f : T ⟶ U) (x : stack.Fibre U),
    (toVaryingData.family T ((toVaryingData.pull f).obj x)).curve.X ⟶
      (toVaryingData.family U x).curve.X
  baseChange : ∀ {T U : Over S} (f : T ⟶ U) (x : stack.Fibre U),
    IsPullback (sourceMap f x)
      (toVaryingData.family T ((toVaryingData.pull f).obj x)).curve.π
      (toVaryingData.family U x).curve.π f.left
  markings : ∀ {T U : Over S} (f : T ⟶ U) (x : stack.Fibre U) (i : Fin n),
    (toVaryingData.family T ((toVaryingData.pull f).obj x)).curve.marking i ≫
      sourceMap f x = f.left ≫ (toVaryingData.family U x).curve.marking i
  targetMap : ∀ {T U : Over S} (f : T ⟶ U) (x : stack.Fibre U),
    sourceMap f x ≫ (toVaryingData.family U x).map =
      (toVaryingData.family T ((toVaryingData.pull f).obj x)).map
  naturality : ∀ {T U : Over S} (f : T ⟶ U) {x y : stack.Fibre U} (a : x ⟶ y),
    (toVaryingData.sourceFunctor T).map ((toVaryingData.pull f).map a) ≫ sourceMap f y =
      sourceMap f x ≫ (toVaryingData.sourceFunctor U).map a
  identity : ∀ (T : Over S) (x : stack.Fibre T),
    sourceMap (𝟙 T) x = (toVaryingData.sourceFunctor T).map
      ((Cat.Hom.toNatIso (stack.toPseudofunctor.mapId (.mk (op T)))).hom.app x)
  composition : ∀ {T U W : Over S} (f : T ⟶ U) (h : U ⟶ W) (x : stack.Fibre W),
    sourceMap (f ≫ h) x = (toVaryingData.sourceFunctor T).map
      ((Cat.Hom.toNatIso (stack.toPseudofunctor.mapComp h.op.toLoc f.op.toLoc)).hom.app x) ≫
      sourceMap f ((toVaryingData.pull h).obj x) ≫ sourceMap h x

namespace VaryingModel
variable {V S : Scheme.{0}} {q : V ⟶ S} {n g : ℕ} (M : VaryingModel q n g)

/-- A represented smooth scheme chart, with the existing actual atlas fibres. -/
structure Chart where
  atlas : M.stack.SmoothAtlas

variable {M}

/-- The chart's actual universal family is the atlas point under the fibre equivalence. -/
abbrev Chart.family (a : M.Chart) :=
  M.toVaryingData.family a.atlas.U a.atlas.point

/-- Every evaluation uses that actual universal family. -/
abbrev Chart.evaluation (a : M.Chart) (i : Fin n) :=
  GeneralStableMapFamilies.evaluation a.family i

end VaryingModel

/-- An actual fixed-source map on C times the parameter T. -/
structure FixedMap {C V S : Scheme.{0}} (c : C ⟶ S) (q : V ⟶ S) (T : Over S) where
  map : pullback c T.hom ⟶ V
  over : map ≫ q = pullback.snd c T.hom ≫ T.hom

/-- The native fixed-source base-change map on the actual pullback schemes. -/
def fixedBaseChange {C S : Scheme.{0}} (c : C ⟶ S) {T U : Over S} (f : T ⟶ U) :
    pullback c T.hom ⟶ pullback c U.hom :=
  pullback.map c T.hom c U.hom (𝟙 C) f.left (𝟙 S)
    (by simp) (by simp)

/-- Fixed-source mapping has a discrete fibre groupoid: source automorphisms
are not silently introduced. -/
structure FixedModel {C V S : Scheme.{0}} (c : C ⟶ S) (q : V ⟶ S) where
  stack : RelativeStack S
  fibre : ∀ T : Over S, stack.Fibre T ≌ Discrete (FixedMap c q T)
  reindex_normalization : ∀ {T U : Over S} (f : T ⟶ U) (x : stack.Fibre U),
    (((fibre T).functor.obj
      ((stack.toPseudofunctor.map f.op.toLoc).toFunctor.obj x)).as).map =
    fixedBaseChange c f ≫ (((fibre U).functor.obj x).as).map

namespace FixedModel
variable {C V S : Scheme.{0}} {c : C ⟶ S} {q : V ⟶ S} (M : FixedModel c q)

abbrev family (T : Over S) (x : M.stack.Fibre T) :=
  ((M.fibre T).functor.obj x).as

structure Chart where
  atlas : M.stack.SmoothAtlas

variable {M}

abbrev Chart.family (a : M.Chart) := M.family a.atlas.U a.atlas.point

end FixedModel

end MathlibExt.AlgebraicGeometry.MapModuliCharts
