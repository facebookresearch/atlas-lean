/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StableMapCompositionFamilies
public import MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials

/-!
# Source normalized composition and stabilization of map stacks

The source fibers contain exactly stable families with stabilizable
target projection. The actual strong stack map retains all base-change
cells. Its family values and every curve map are fixed by the actual
stabilization contractions, including on nonreduced parameters.

An atlas comparison contains actual scheme arrows and the native
point-comparison isomorphism. Its parameter differential uses the
full polynomial-normalized cotangent arrow on that actual chart map.
Reference: Graber–Harris–Starr math/0109220v1, §2, Definition 2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StableMapCompositionStacks

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.StableMapCompositionFamilies
open MathlibExt.AlgebraicGeometry.SchemeFirstOrderDifferentials
open MathlibExt.AlgebraicGeometry.MarkedMapDeformationCones
open MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory

variable {V Y S : Scheme.{0}} (q : V ⟶ S) (r : Y ⟶ S)
    (h : V ⟶ Y) (over : h ≫ r = q) (n m g : ℕ)

/-- The actual admissible stable-family groupoid. -/
abbrev ProjectedFamilies (T : Over S) :=
  (show ObjectProperty (Family q n g T.left T.hom) from
    fun F => IsGeometricallyStable F ∧ IsStabilizable F h m).FullSubcategory

/-- A source model is normalized to these actual families on every parameter scheme. -/
structure CompositionDomain where
  stack : RelativeStack S
  fibre : ∀ T : Over S, stack.Fibre T ≌ ProjectedFamilies q h n m g T

namespace CompositionDomain

variable {q h n m g} (D : CompositionDomain q h n m g)

abbrev family (T : Over S) (x : D.stack.Fibre T) := ((D.fibre T).functor.obj x).obj
abbrev pull {T U : Over S} (f : T ⟶ U) := (D.stack.toPseudofunctor.map f.op.toLoc).toFunctor

def sourceFunctor (T : Over S) : D.stack.Fibre T ⥤ Scheme.{0} where
  obj x := (D.family T x).curve.X
  map f := ((D.fibre T).functor.map f).hom.iso.hom
  map_id x := by rw [(D.fibre T).functor.map_id]; rfl
  map_comp f g := by rw [(D.fibre T).functor.map_comp f g]; rfl

end CompositionDomain

variable {q r h over n m g}

/-- The source Cartesian maps retain the native pseudofunctor identity and composition cells. -/
structure DomainBaseChange (D : CompositionDomain q h n m g) where
  map : ∀ {T U : Over S} (f : T ⟶ U) (x : D.stack.Fibre U),
    (D.family T ((D.pull f).obj x)).curve.X ⟶ (D.family U x).curve.X
  square : ∀ {T U : Over S} (f : T ⟶ U) (x : D.stack.Fibre U),
    IsPullback (map f x) (D.family T ((D.pull f).obj x)).curve.π (D.family U x).curve.π f.left
  markings : ∀ {T U : Over S} (f : T ⟶ U) (x : D.stack.Fibre U) (i : Fin n),
    (D.family T ((D.pull f).obj x)).curve.marking i ≫ map f x =
      f.left ≫ (D.family U x).curve.marking i
  target : ∀ {T U : Over S} (f : T ⟶ U) (x : D.stack.Fibre U),
    map f x ≫ (D.family U x).map = (D.family T ((D.pull f).obj x)).map
  natural : ∀ {T U : Over S} (f : T ⟶ U) {x y : D.stack.Fibre U} (a : x ⟶ y),
    (D.sourceFunctor T).map ((D.pull f).map a) ≫ map f y =
      map f x ≫ (D.sourceFunctor U).map a
  identity : ∀ (T : Over S) (x : D.stack.Fibre T), map (𝟙 T) x =
    (D.sourceFunctor T).map ((Cat.Hom.toNatIso
      (D.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app x)
  composition : ∀ {T U W : Over S} (f : T ⟶ U) (j : U ⟶ W) (x : D.stack.Fibre W),
    map (f ≫ j) x = (D.sourceFunctor T).map ((Cat.Hom.toNatIso
      (D.stack.toPseudofunctor.mapComp j.op.toLoc f.op.toLoc)).hom.app x) ≫
        map f ((D.pull j).obj x) ≫ map j x

/-- The actual stack composition, fixed on all families and contraction/base-change maps. -/
structure CompositionModel (D : CompositionDomain q h n m g) (B : DomainBaseChange D)
    (M : VaryingModel r m g) (a : Fin m → Fin n) (injective : Function.Injective a)
    (over : h ≫ r = q) where
  map : Pseudofunctor.StrongTrans D.stack.toPseudofunctor M.stack.toPseudofunctor
  stabilization : ∀ (T : Over S) (x : D.stack.Fibre T),
    Stabilization (D.family T x) h over a injective
  family : ∀ (T : Over S) (x : D.stack.Fibre T), (stabilization T x).family =
    M.toVaryingData.family T ((map.app (.mk (op T))).toFunctor.obj x)
  natural : ∀ (T : Over S) (x y : D.stack.Fibre T) (f : x ⟶ y),
    (D.sourceFunctor T).map f ≫ (stabilization T y).contraction.map =
      (stabilization T x).contraction.map ≫
        eqToHom (congrArg (fun F => F.curve.X) (family T x)) ≫
          (M.toVaryingData.sourceFunctor T).map ((map.app (.mk (op T))).toFunctor.map f) ≫
            eqToHom (congrArg (fun F => F.curve.X) (family T y).symm)
  baseChange : ∀ {T U : Over S} (f : T ⟶ U) (x : D.stack.Fibre U),
    HEq ((stabilization T ((D.pull f).obj x)).contraction.map ≫
      eqToHom (congrArg (fun F => F.curve.X) (family T ((D.pull f).obj x))) ≫
        (M.toVaryingData.sourceFunctor T).map
          ((Cat.Hom.toNatIso (map.naturality f.op.toLoc)).hom.app x) ≫
            M.sourceMap f ((map.app (.mk (op U))).toFunctor.obj x) ≫
              eqToHom (congrArg (fun F => F.curve.X) (family U x).symm))
      (B.map f x ≫ (stabilization U x).contraction.map)

/-- An actual scheme chart of a stack map, retaining its point-comparison isomorphism. -/
structure StackMapChart {X Z : RelativeStack S}
    (f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor)
    (a : X.SmoothAtlas) (b : Z.SmoothAtlas) where
  parameter : Over S
  source : parameter ⟶ a.U
  target : parameter ⟶ b.U
  comparison : ((f.app (.mk (op parameter))).toFunctor.obj
      ((X.toPseudofunctor.map source.op.toLoc).toFunctor.obj a.point)) ≅
    ((Z.toPseudofunctor.map target.op.toLoc).toFunctor.obj b.point)

/-- The chart differential is exactly the normalized cotangent arrow
of its actual target scheme map. -/
structure ChartDifferential {k : Type} [CommRing k] {X Z : RelativeStack (Spec (.of k))}
    {f : Pseudofunctor.StrongTrans X.toPseudofunctor Z.toPseudofunctor}
    {a : X.SmoothAtlas} {b : Z.SmoothAtlas} (C : StackMapChart f a b) where
  source : CotangentNormalization C.parameter.hom
  target : CotangentNormalization b.U.hom
  differential : RelativeDifferential C.target.left (Over.w C.target) source target
  sourceForms : CotangentFormsProjection C.parameter source
  targetForms : CotangentFormsProjection b.U target

end MathlibExt.AlgebraicGeometry.StableMapCompositionStacks
