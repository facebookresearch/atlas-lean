/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiAffineMapCharts
public import MathlibExt.AlgebraicGeometry.LiCechObstructionComplexes

/-!
# Li's chartwise Cech modules

Each local value is the source's literal ordinary, boundary or two-branch
node module. Ordinary charts retain no free logarithm of a vanished
smoothing parameter. Boundary and node values retain their actual normal
logarithms, with the base-image condition at nodes.

The Cech terms are products over all ordered chart tuples. Every tuple
chart is compared to the actual wide fibre product of the selected cover
charts, and all face/degeneracy restrictions use its literal projections.
Source: Jun Li arXiv:math/0110113v1, equations1.10--1.11 and1.18--1.20;
the relative boundary modification is on printed p21.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiCechChartModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open LiAffineMapCharts LogarithmicMapDerivations
open scoped TensorProduct Simplicial

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
  {C X : Scheme.{0}} {p : C ⟶ Spec (.of A)} {q : X ⟶ Spec (.of k)} {f : C ⟶ X}
  {Z : Scheme.{0}} (g : X ⟶ Z)
  {b m : ℕ} (J : Fin b → X.IdealSheafData) (t : Fin m → Γ(X, ⊤))

def parameterValue (a : Chart p q f) (i : Fin m) : a.target :=
  (Scheme.ΓSpecIso (.of a.target)).hom.hom (a.targetMap.appTop.hom (t i))

/-- The affine parameter presentation is tied to the fixed actual target
projection. Extra coordinate functions cannot change which points are nodes. -/
structure ProjectionBinding {E : Type} [CommRing E] (h : X ⟶ Spec (.of E)) where
  iso : Spec (.of E) ≅ Z
  projection : h ≫ iso.hom = g

structure PureAffineContact (a : Chart p q f) (o : Node a m) where
  smoothing : a.base
  coordinate : Fin 2 → a.source
  sourceChart : RelativeContactGeometry.NodeRing a.base smoothing →+* a.source
  sourceScalar : ∀ x, sourceChart (RelativeContactGeometry.nodeCoefficient a.base smoothing x) =
    algebraMap a.base a.source x
  sourceGenerator : ∀ i, sourceChart (RelativeContactGeometry.nodeVariable a.base smoothing i) = coordinate i
  sourceEtale : Etale (Spec.map (CommRingCat.ofHom sourceChart))
  sourceEquation : coordinate 0 * coordinate 1 = algebraMap a.base a.source smoothing
  point : PrimeSpectrum a.source
  distinguished : ∀ i, coordinate i ∈ point.asIdeal
  order : ℕ
  positive : 0 < order
  permutation : Fin 2 ≃ Fin 2
  baseMap : RelativeContactGeometry.NearIdeal (Ideal.span {smoothing}) →+*
    RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate))
  baseNormalized : ∀ x : a.base,
    baseMap (algebraMap a.base (RelativeContactGeometry.NearIdeal (Ideal.span {smoothing})) x) =
      algebraMap a.source (RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate)))
        (algebraMap a.base a.source x)
  unit : Fin 2 → (RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate)))ˣ
  coefficient : RelativeContactGeometry.NearIdeal (Ideal.span {smoothing})
  product : (unit 0 : RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate))) *
      (unit 1 : RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate))) = baseMap coefficient
  normalEquation : ∀ i,
    algebraMap a.source (RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate)))
      (algebraMap a.target a.source (o.coordinate i)) =
    (algebraMap a.source (RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate)))
      (coordinate (permutation i))) ^ order * (unit i : RelativeContactGeometry.NearIdeal (Ideal.span (Set.range coordinate)))

inductive Mode (a : Chart p q f) where
  | ordinary (o : Ordinary a m)
      (projection : ProjectionBinding g o.targetProjection)
      (away : ∀ i : Fin b,
        ((J i).comap a.targetMap).comap (Spec.algebraMap a.target a.source) = ⊤)
      (parameters : o.targetParameter = parameterValue t a) : Mode a
  | boundary (i : Fin b) (o : Boundary a (J i) m)
      (projection : ProjectionBinding g o.ordinary.targetProjection)
      (point : PrimeSpectrum a.source)
      (boundaryPoint : algebraMap a.target a.source o.coordinate ∈ point.asIdeal)
      (parameters : o.ordinary.targetParameter = parameterValue t a) : Mode a
  | node (o : Node a m)
      (projection : ProjectionBinding g o.targetProjection)
      (pure : PureAffineContact a o)
      (parameters : o.targetParameter = parameterValue t a) : Mode a

/-- A boundary chart meets no boundary divisor other than its selected one, and a node chart
meets none: every such boundary ideal pulls back to the unit ideal on the chart. (Ordinary charts
avoid all boundaries by construction.) Without this, a boundary chart could contain another
prescribed end, where no logarithmic condition is imposed, and allow directions moving it. -/
def Mode.AvoidsUnselected {a : Chart p q f} : Mode g J t a → Prop
  | .ordinary _ _ _ _ => True
  | .boundary i _ _ _ _ _ => ∀ j : Fin b, j ≠ i →
      ((J j).comap a.targetMap).comap (Spec.algebraMap a.target a.source) = ⊤
  | .node _ _ _ _ => ∀ j : Fin b,
      ((J j).comap a.targetMap).comap (Spec.algebraMap a.target a.source) = ⊤

variable (I : Type) [AddCommGroup I] [Module A I]

def value {a : Chart p q f} : Mode g J t a → ModuleCat.{0} A
  | .ordinary o _ _ _ => ordinaryModule a I o
  | .boundary _ o _ _ _ _ => boundaryModule a I o
  | .node o _ _ _ => nodeModule a I o

def derivative {a : Chart p q f} (o : Mode g J t a) :
    value g J t I o →ₗ[A] (a.target →ₗ[k] sourceCoefficient a I) := by
  cases o with
  | ordinary o pr away h => exact (ordinary (k := k) o.targetParameter (baseCoefficientMap a I)).subtype
  | boundary i o pr pt hp h =>
      exact (LinearMap.fst A (a.target →ₗ[k] sourceCoefficient a I) (sourceCoefficient a I)).comp
        (boundary (k := k) o.coordinate o.ordinary.targetParameter (baseCoefficientMap a I)).subtype
  | node o pr pure h =>
      exact (LinearMap.fst A (a.target →ₗ[k] sourceCoefficient a I) (Fin 2 → sourceCoefficient a I)).comp
        (node (k := k) o.coordinate o.targetParameter (baseCoefficientMap a I)).subtype

def boundaryLog {a : Chart p q f} {i : Fin b} (o : Boundary a (J i) m)
    (pr : ProjectionBinding g o.ordinary.targetProjection) (pt : PrimeSpectrum a.source)
    (hp : algebraMap a.target a.source o.coordinate ∈ pt.asIdeal)
    (h : o.ordinary.targetParameter = parameterValue t a) :
    value g J t I (.boundary i o pr pt hp h) →ₗ[A] sourceCoefficient a I :=
  (LinearMap.snd A (a.target →ₗ[k] sourceCoefficient a I) (sourceCoefficient a I)).comp
    (boundary (k := k) o.coordinate o.ordinary.targetParameter (baseCoefficientMap a I)).subtype

def nodeLog {a : Chart p q f} (o : Node a m)
    (pr : ProjectionBinding g o.targetProjection) (pure : PureAffineContact a o)
    (h : o.targetParameter = parameterValue t a) :
    value g J t I (.node o pr pure h) →ₗ[A] (Fin 2 → sourceCoefficient a I) :=
  (LinearMap.snd A (a.target →ₗ[k] sourceCoefficient a I) (Fin 2 → sourceCoefficient a I)).comp
    (node (k := k) o.coordinate o.targetParameter (baseCoefficientMap a I)).subtype

structure RingRestriction (a c : Chart p q f) where
  source : a.source →ₐ[A] c.source
  target : a.target →ₐ[k] c.target
  base : a.base →ₐ[A] c.base
  sourceMap : Spec.map (CommRingCat.ofHom source.toRingHom) ≫ a.sourceMap = c.sourceMap
  targetMap : Spec.map (CommRingCat.ofHom target.toRingHom) ≫ a.targetMap = c.targetMap
  sourceBase : ∀ x : a.base,
    source (algebraMap a.base a.source x) = algebraMap c.base c.source (base x)
  sourceTarget : ∀ x : a.target,
    source (algebraMap a.target a.source x) = algebraMap c.target c.source (target x)

def RingRestriction.coefficient {a c : Chart p q f} (r : RingRestriction a c) :
    sourceCoefficient a I →ₗ[A] sourceCoefficient c I :=
  TensorProduct.map r.source.toLinearMap LinearMap.id

structure BoundaryCoordinateChange {a c : Chart p q f} (r : RingRestriction a c)
    {i j : Fin b} (o : Boundary a (J i) m) (z : Boundary c (J j) m) where
  divisor : i = j
  unit : c.targetˣ
  coordinate : z.coordinate = (unit : c.target) * r.target o.coordinate

structure NodeCoordinateChange {a c : Chart p q f} (r : RingRestriction a c)
    (o : Node a m) (z : Node c m) where
  permutation : Fin 2 ≃ Fin 2
  unit : Fin 2 → c.targetˣ
  coordinate : ∀ i, z.coordinate i =
    (unit i : c.target) * r.target (o.coordinate (permutation i))

/-- All regular derivatives and all retained normal logarithms are fixed.
Restrictions to ordinary intersections use their ordinary value only. -/
structure ModuleRestriction {a c : Chart p q f} (r : RingRestriction a c)
    (o : Mode g J t a) (z : Mode g J t c) where
  map : value g J t I o ⟶ value g J t I z
  regular : ∀ (x : value g J t I o) (s : a.target),
    derivative g J t I z (map x) (r.target s) = r.coefficient I (derivative g J t I o x s)
  boundary : ∀ {i j : Fin b} (o' : Boundary a (J i) m) (z' : Boundary c (J j) m)
    (pr : ProjectionBinding g o'.ordinary.targetProjection)
    (pr' : ProjectionBinding g z'.ordinary.targetProjection)
    (pt : PrimeSpectrum a.source) (pt' : PrimeSpectrum c.source)
    (hp : algebraMap a.target a.source o'.coordinate ∈ pt.asIdeal)
    (hp' : algebraMap c.target c.source z'.coordinate ∈ pt'.asIdeal)
    (h : o'.ordinary.targetParameter = parameterValue t a)
    (h' : z'.ordinary.targetParameter = parameterValue t c)
    (e : o = .boundary i o' pr pt hp h) (e' : z = .boundary j z' pr' pt' hp' h'),
    ∃ u : BoundaryCoordinateChange J r o' z', ∀ x : value g J t I o,
      boundaryLog g J t I z' pr' pt' hp' h' ((eqToHom (congrArg (value g J t I) e')) (map x)) =
        ((u.unit⁻¹ : c.targetˣ) : c.target) •
          derivative g J t I z (map x) (u.unit : c.target) +
        r.coefficient I (boundaryLog g J t I o' pr pt hp h ((eqToHom (congrArg (value g J t I) e)) x))
  node : ∀ (o' : Node a m) (z' : Node c m)
    (pr : ProjectionBinding g o'.targetProjection) (pr' : ProjectionBinding g z'.targetProjection)
    (pure : PureAffineContact a o') (pure' : PureAffineContact c z')
    (h : o'.targetParameter = parameterValue t a) (h' : z'.targetParameter = parameterValue t c)
    (e : o = .node o' pr pure h) (e' : z = .node z' pr' pure' h'),
    ∃ u : NodeCoordinateChange r o' z', ∀ (x : value g J t I o) (i : Fin 2),
      nodeLog g J t I z' pr' pure' h' ((eqToHom (congrArg (value g J t I) e')) (map x)) i =
        (((u.unit i)⁻¹ : c.targetˣ) : c.target) • derivative g J t I z (map x) (u.unit i : c.target) +
        r.coefficient I (nodeLog g J t I o' pr pure h ((eqToHom (congrArg (value g J t I) e)) x) (u.permutation i))

end MathlibExt.AlgebraicGeometry.LiCechChartModules
