/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The tuple-projection construction adapts `Arrow.cechNerve` from
`Mathlib/AlgebraicTopology/CechNerve.lean`:
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE file.
Authors: Adam Topaz.
-/
module

public import MathlibExt.AlgebraicGeometry.LiCechChartModules

/-!
# The actual geometric Cech nerve and Li chart values

Tuple schemes are actual wide fibre products of the etale affine cover.
The parameter/source/target projections and all scalar maps are fixed by
their native projections. Each cochain degree is the product of actual
ordinary, boundary and node modules over all ordered tuples. Faces and
degeneracies use the corresponding literal projection restriction.
Source: Jun Li arXiv:math/0110113v1, equations1.18--1.20 and1.23--1.25.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiGeometricCechModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open LiAffineMapCharts LiCechChartModules
open scoped Simplicial

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  {C X Z : Scheme.{0}} {p : C ⟶ Spec (.of A)} {q : X ⟶ Spec (.of k)} {f : C ⟶ X}
  (g : X ⟶ Z) {b m : ℕ} (J : Fin b → X.IdealSheafData) (t : Fin m → Γ(X, ⊤))

structure Cover where
  count : ℕ
  charts : Fin count → Chart p q f
  covering : ∀ x : C, ∃ (i : Fin count) (y : Spec (.of (charts i).source)), (charts i).sourceMap y = x

def tuplePullback {ι : Type} {Y : Scheme.{0}} (U : ι → Scheme.{0})
    (h : ∀ i, U i ⟶ Y) (n : SimplexCategory) (a : Fin (n.len + 1) → ι) : Scheme.{0} :=
  widePullback Y (fun i : Fin (n.len + 1) => U (a i)) (fun i => h (a i))

def tupleProjection {ι : Type} {Y : Scheme.{0}} (U : ι → Scheme.{0})
    (h : ∀ i, U i ⟶ Y) {n z : SimplexCategory} (s : n ⟶ z)
    (a : Fin (z.len + 1) → ι) : tuplePullback U h z a ⟶ tuplePullback U h n (a ∘ s.toOrderHom) :=
  WidePullback.lift (WidePullback.base _)
    (fun i => WidePullback.π _ (s.toOrderHom i)) (by simp)

variable (L : Cover (p := p) (q := q) (f := f))

def sourceTuple (n : SimplexCategory) (a : Fin (n.len + 1) → Fin L.count) : Scheme.{0} :=
  tuplePullback (fun i => Spec (.of (L.charts i).source)) (fun i => (L.charts i).sourceMap) n a

def targetTuple (n : SimplexCategory) (a : Fin (n.len + 1) → Fin L.count) : Scheme.{0} :=
  tuplePullback (fun i => Spec (.of (L.charts i).target)) (fun i => (L.charts i).targetMap) n a

def baseTuple (n : SimplexCategory) (a : Fin (n.len + 1) → Fin L.count) : Scheme.{0} :=
  tuplePullback (fun i => Spec (.of (L.charts i).base)) (fun i => Spec.algebraMap A (L.charts i).base) n a

structure Geometry where
  chart : ∀ (n : SimplexCategory) (_a : Fin (n.len + 1) → Fin L.count), Chart p q f
  source : ∀ n a, Spec (.of (chart n a).source) ≅ sourceTuple L n a
  target : ∀ n a, Spec (.of (chart n a).target) ≅ targetTuple L n a
  base : ∀ n a, Spec (.of (chart n a).base) ≅ baseTuple L n a
  source_projection : ∀ n a, (source n a).hom ≫ WidePullback.base _ = (chart n a).sourceMap
  target_projection : ∀ n a, (target n a).hom ≫ WidePullback.base _ = (chart n a).targetMap
  base_projection : ∀ n a, (base n a).hom ≫ WidePullback.base _ = Spec.algebraMap A (chart n a).base
  source_base : ∀ n a (i : Fin (n.len + 1)),
    Spec.algebraMap (chart n a).base (chart n a).source ≫ (base n a).hom ≫ WidePullback.π _ i =
      (source n a).hom ≫ WidePullback.π _ i ≫ Spec.algebraMap (L.charts (a i)).base (L.charts (a i)).source
  source_target : ∀ n a (i : Fin (n.len + 1)),
    Spec.algebraMap (chart n a).target (chart n a).source ≫ (target n a).hom ≫ WidePullback.π _ i =
      (source n a).hom ≫ WidePullback.π _ i ≫ Spec.algebraMap (L.charts (a i)).target (L.charts (a i)).source
  mode : ∀ n a, Mode g J t (chart n a)
  /-- On every chart and every Čech intersection, a boundary chart meets only its selected
  boundary divisor and a node chart meets none. -/
  modeAvoids : ∀ n a, (mode n a).AvoidsUnselected
  restriction : ∀ {n z : SimplexCategory} (s : n ⟶ z) (a : Fin (z.len + 1) → Fin L.count),
    RingRestriction (chart n (a ∘ s.toOrderHom)) (chart z a)
  source_arrow : ∀ {n z : SimplexCategory} (s : n ⟶ z) (a : Fin (z.len + 1) → Fin L.count),
    Spec.map (CommRingCat.ofHom (restriction s a).source.toRingHom) ≫ (source n (a ∘ s.toOrderHom)).hom =
      (source z a).hom ≫ tupleProjection
        (fun i => Spec (.of (L.charts i).source)) (fun i => (L.charts i).sourceMap) s a
  target_arrow : ∀ {n z : SimplexCategory} (s : n ⟶ z) (a : Fin (z.len + 1) → Fin L.count),
    Spec.map (CommRingCat.ofHom (restriction s a).target.toRingHom) ≫ (target n (a ∘ s.toOrderHom)).hom =
      (target z a).hom ≫ tupleProjection
        (fun i => Spec (.of (L.charts i).target)) (fun i => (L.charts i).targetMap) s a
  base_arrow : ∀ {n z : SimplexCategory} (s : n ⟶ z) (a : Fin (z.len + 1) → Fin L.count),
    Spec.map (CommRingCat.ofHom (restriction s a).base.toRingHom) ≫ (base n (a ∘ s.toOrderHom)).hom =
      (base z a).hom ≫ tupleProjection
        (fun i => Spec (.of (L.charts i).base)) (fun i => Spec.algebraMap A (L.charts i).base) s a

variable (G : Geometry g J t L) (I : Type) [AddCommGroup I] [Module A I]

def cochainTerm (n : SimplexCategory) : ModuleCat.{0} A :=
  ModuleCat.of A (∀ a : Fin (n.len + 1) → Fin L.count, value g J t I (G.mode n a))

structure Model where
  cochains : CosimplicialObject (ModuleCat.{0} A)
  comparison : ∀ n : SimplexCategory, cochains.obj n ≅ cochainTerm g J t L G I n
  restriction : ∀ {n z : SimplexCategory} (s : n ⟶ z) (a : Fin (z.len + 1) → Fin L.count),
    ModuleRestriction g J t I (G.restriction s a) (G.mode n (a ∘ s.toOrderHom)) (G.mode z a)
  normalized : ∀ {n z : SimplexCategory} (s : n ⟶ z) (a : Fin (z.len + 1) → Fin L.count)
    (x : cochains.obj n),
    (comparison z).hom (cochains.map s x) a =
      (restriction s a).map ((comparison n).hom x (a ∘ s.toOrderHom))

end MathlibExt.AlgebraicGeometry.LiGeometricCechModels
