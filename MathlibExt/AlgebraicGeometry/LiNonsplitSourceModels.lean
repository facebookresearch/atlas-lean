/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGenericGaugeSourceModels
public import MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses

/-!
# Li obstruction cocycles for actual nonsplit square-zero base extensions

The base extension is the existing surjective algebra map with its
literal square-zero kernel. All local extensions are actual etale lifts
of the source and base covers. Every full base Cech tuple, including the
parent label and mixed or empty source intersections, remains present.
Differences are the actual differences of the lifted target maps and
actual logarithmic units; no splitting of the base ring is requested.

Source: Jun Li math/0110113v1, Proposition1.18 and Proposition2.4,
printed pp18--19 and24--25, with (1.18)--(1.25). Polynomial extension
classes use the native AxiomMath/Stacks integration at
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache2.0).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiNonsplitSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Opposite
open GeneralStackGeometry StackCycleGeometry CoherentCurveLinearSeries RubberMapFamilies
open MarkedCurveStabilization
open LiGenericSourceModels LiGenericSourceIndex LiGeometricCechModels LiCechChartModules
open LiAffineMapCharts
open AffineSquareZeroCotangentClasses
open scoped Simplicial TensorProduct

variable {k : Type} [Field k] {X : Stack (Spec (.of k))} (C : SourceChart X)
  (E : AffineSquareZeroCotangentClasses.Extension k C.ring)

def reduction : Spec (.of C.ring) ⟶ Spec (.of E.ring) :=
  Spec.map (CommRingCat.ofHom E.projection.toRingHom)

/-- The marked curve lifts use this actual base extension and every original marking. -/
structure Curves where
  curve : ∀ v : Fin C.family.components,
    MarkedFamily (Spec (.of E.ring)) (C.family.markings v) (C.family.genus v)
  reduction : ∀ v, (C.family.curve v).X ⟶ (curve v).X
  cartesian : ∀ v, IsPullback (reduction v) (C.family.curve v).π
    (curve v).π (LiNonsplitSourceModels.reduction C E)
  markings : ∀ v i, (C.family.curve v).marking i ≫ reduction v =
    LiNonsplitSourceModels.reduction C E ≫ (curve v).marking i

abbrev Labels := LiSharedTargetCechModels.Label C.source.cover

instance baseTupleAlgebra (z : SimplexCategory) (a : Fin (z.len + 1) → Labels C) :
    Algebra k (LiSharedTargetCechModels.baseRing C.source.cover z a) :=
  ((algebraMap C.ring (LiSharedTargetCechModels.baseRing C.source.cover z a)).comp
    (algebraMap k C.ring)).toAlgebra

/-- Native base-cover lifts, with the actual parent retained even for an empty curve. -/
structure BaseCover where
  scheme : Labels C → Scheme.{0}
  projection : ∀ a, scheme a ⟶ Spec (.of E.ring)
  etale : ∀ a, Etale (projection a)
  reduction : ∀ a, LiSharedTargetCechModels.baseChart C.source.cover a ⟶ scheme a
  cartesian : ∀ a, IsPullback (reduction a)
    (LiSharedTargetCechModels.baseArrow C.source.cover a) (projection a)
    (LiNonsplitSourceModels.reduction C E)
  parent : scheme none ≅ Spec (.of E.ring)
  parent_projection : parent.hom = projection none

def BaseCover.tuple (B : BaseCover C E) (z : SimplexCategory)
    (a : Fin (z.len + 1) → Labels C) : Scheme.{0} :=
  LiGeometricCechModels.tuplePullback B.scheme B.projection z a

def BaseCover.tupleProjection (B : BaseCover C E) {n z : SimplexCategory}
    (s : n ⟶ z) (a : Fin (z.len + 1) → Labels C) :
    B.tuple C E z a ⟶ B.tuple C E n (a ∘ s.toOrderHom) :=
  LiGeometricCechModels.tupleProjection B.scheme B.projection s a

/-- Every tuple extension is identified with the actual native fibre product of base lifts. -/
structure BaseTuples (B : BaseCover C E) where
  reduction : ∀ z a, LiSharedTargetCechModels.baseTuple C.source.cover z a ⟶ B.tuple C E z a
  cartesian : ∀ z a, IsPullback (reduction z a)
    (WidePullback.base (fun i => LiSharedTargetCechModels.baseArrow C.source.cover (a i)))
    (WidePullback.base (fun i => B.projection (a i))) (LiNonsplitSourceModels.reduction C E)
  projections : ∀ z a i,
    reduction z a ≫ WidePullback.π (fun j => B.projection (a j)) i =
      WidePullback.π (fun j => LiSharedTargetCechModels.baseArrow C.source.cover (a j)) i ≫
        B.reduction (a i)
  naturality : ∀ {n z} (s : n ⟶ z) a,
    reduction z a ≫ B.tupleProjection C E s a =
      LiSharedTargetCechModels.baseProjection C.source.cover s a ≫
        reduction n (a ∘ s.toOrderHom)
  extension : ∀ z a, AffineSquareZeroCotangentClasses.Extension k
    (LiSharedTargetCechModels.baseRing C.source.cover z a)
  ring : ∀ z a, (extension z a).ring ≃+* Γ(B.tuple C E z a, ⊤)
  projection : ∀ z a x, (extension z a).projection x = (reduction z a).appTop.hom (ring z a x)
  coefficient : ∀ z a, (extension z a).coefficient ≅
    ModuleCat.of (LiSharedTargetCechModels.baseRing C.source.cover z a)
      (LiSharedTargetCechModels.baseCoefficient C.source.cover E.coefficient z a)
  kernel : ∀ z a, RingHom.ker E.projection.toRingHom →
    RingHom.ker (extension z a).projection.toRingHom
  kernel_value : ∀ z a x, ring z a (kernel z a x).val =
    (WidePullback.base (fun i => B.projection (a i))).appTop.hom
      ((Scheme.ΓSpecIso (.of E.ring)).inv.hom x.val)
  kernel_pure : ∀ z a x, (coefficient z a).hom ((extension z a).kernel (kernel z a x)) =
    1 ⊗ₜ[C.ring] E.kernel x

variable (H : Curves C E) (B : BaseCover C E)

/-- One actual local lift; its base parameter may be chosen independently of other lifts. -/
structure Lift (v : Fin C.family.components) (i : Fin (C.source.cover v).count) where
  extension : AffineSquareZeroCotangentClasses.Extension k ((C.source.cover v).charts i).source
  coefficient : extension.coefficient ≅
    ModuleCat.of ((C.source.cover v).charts i).source
      (sourceCoefficient ((C.source.cover v).charts i) E.coefficient)
  source : Spec (.of extension.ring) ⟶ (H.curve v).X
  etale : Etale source
  cartesian : IsPullback
    (Spec.map (CommRingCat.ofHom extension.projection.toRingHom))
    ((C.source.cover v).charts i).sourceMap source (H.reduction v)
  base : Spec (.of extension.ring) ⟶ B.scheme (some ⟨v, i⟩)
  base_projection : base ≫ B.projection (some ⟨v, i⟩) = source ≫ (H.curve v).π
  target : ((C.source.cover v).charts i).target →ₐ[k] extension.ring
  target_reduction : ∀ x, extension.projection (target x) =
    algebraMap ((C.source.cover v).charts i).target ((C.source.cover v).charts i).source x
  parameter : B.scheme (some ⟨v, i⟩) ⟶ C.family.parameterBase
  over : Spec.map (CommRingCat.ofHom target.toRingHom) ≫
    ((C.source.cover v).charts i).targetMap ≫ C.family.projection = base ≫ parameter
  parameter_reduction : B.reduction (some ⟨v, i⟩) ≫ parameter =
    LiSharedTargetCechModels.baseArrow C.source.cover (some ⟨v, i⟩) ≫ C.family.parameter
  relative : Spec (.of extension.ring) ⟶ pullback C.family.projection parameter
  relative_target : relative ≫ pullback.fst C.family.projection parameter =
    Spec.map (CommRingCat.ofHom target.toRingHom) ≫ ((C.source.cover v).charts i).targetMap
  relative_base : relative ≫ pullback.snd C.family.projection parameter = base
  predeformable : RelativeExpandedMapFamilies.IsPredeformable base
    (pullback.snd C.family.projection parameter) relative relative_base
  contact : ∀ j (W : (Spec (.of extension.ring)).affineOpens),
    (((C.family.boundary j).comap
      (Spec.map (CommRingCat.ofHom target.toRingHom) ≫ ((C.source.cover v).charts i).targetMap)).ideal W) =
      ∏ s : {s : Fin (C.family.markings v) // C.family.root v s = some j},
        ((((H.curve v).marking s.val).ker.comap source).ideal W) ^ C.family.order v s.val

def sourceTuple (L : ∀ v i, Lift C E H B v i) (v : Fin C.family.components)
    (z : SimplexCategory) (a : Fin (z.len + 1) → Fin (C.source.cover v).count) : Scheme.{0} :=
  LiGeometricCechModels.tuplePullback (fun i => Spec (.of (L v i).extension.ring))
    (fun i => (L v i).source) z a

def sourceToBase (L : ∀ v i, Lift C E H B v i) (v : Fin C.family.components)
    (z : SimplexCategory) (a : Fin (z.len + 1) → Fin (C.source.cover v).count) :
    sourceTuple C E H B L v z a ⟶
      B.tuple C E z (LiSharedTargetCechModels.sourceLabels C.source.cover v a) :=
  WidePullback.lift
    (WidePullback.base (fun i : Fin (z.len + 1) => (L v (a i)).source) ≫ (H.curve v).π)
    (fun i => WidePullback.π (fun j : Fin (z.len + 1) => (L v (a j)).source) i ≫ (L v (a i)).base)
    (by
      intro i
      dsimp only [sourceTuple, LiGeometricCechModels.tuplePullback, LiSharedTargetCechModels.sourceLabels]
      rw [Category.assoc, (L v (a i)).base_projection]
      simp)

/-- The full actual overlap ring and its coefficient kernel are fixed by the native source tuple. -/
structure SourceTuple (T : BaseTuples C E B) (L : ∀ v i, Lift C E H B v i)
    (v : Fin C.family.components) (z : SimplexCategory)
    (a : Fin (z.len + 1) → Fin (C.source.cover v).count) where
  extension : AffineSquareZeroCotangentClasses.Extension k ((C.source.geometry v).chart z a).source
  coefficient : extension.coefficient ≅
    ModuleCat.of ((C.source.geometry v).chart z a).source
      (sourceCoefficient ((C.source.geometry v).chart z a) E.coefficient)
  source : Spec (.of extension.ring) ≅ sourceTuple C E H B L v z a
  reduction : Spec.map (CommRingCat.ofHom extension.projection.toRingHom) ≫
    source.hom ≫ WidePullback.base _ =
      ((C.source.geometry v).source z a).hom ≫ WidePullback.base _ ≫ H.reduction v
  base : (T.extension z (LiSharedTargetCechModels.sourceLabels C.source.cover v a)).ring →+*
    extension.ring
  base_native : ∀ x, (Scheme.ΓSpecIso (.of extension.ring)).inv.hom (base x) =
    source.hom.appTop.hom ((sourceToBase C E H B L v z a).appTop.hom
      (T.ring z (LiSharedTargetCechModels.sourceLabels C.source.cover v a) x))
  kernel : RingHom.ker E.projection.toRingHom → RingHom.ker extension.projection.toRingHom
  kernel_value : ∀ x, (Scheme.ΓSpecIso (.of extension.ring)).inv.hom (kernel x).val =
    (source.hom ≫ WidePullback.base _ ≫ (H.curve v).π).appTop.hom
      ((Scheme.ΓSpecIso (.of E.ring)).inv.hom x.val)
  kernel_pure : ∀ x, coefficient.hom (extension.kernel (kernel x)) = 1 ⊗ₜ[C.ring] E.kernel x

variable {H B} {T : BaseTuples C E B} {L : ∀ v i, Lift C E H B v i}

/-- Two actual target lifts on their actual common overlap. -/
structure Pair {v : Fin C.family.components} {a : Fin 2 → Fin (C.source.cover v).count}
    (U : SourceTuple C E H B T L v ⦋1⦌ a) where
  first : ((C.source.geometry v).chart ⦋1⦌ a).target →ₐ[k] U.extension.ring
  second : ((C.source.geometry v).chart ⦋1⦌ a).target →ₐ[k] U.extension.ring
  first_reduction : ∀ x, U.extension.projection (first x) =
    algebraMap ((C.source.geometry v).chart ⦋1⦌ a).target
      ((C.source.geometry v).chart ⦋1⦌ a).source x
  second_reduction : ∀ x, U.extension.projection (second x) =
    algebraMap ((C.source.geometry v).chart ⦋1⦌ a).target
      ((C.source.geometry v).chart ⦋1⦌ a).source x
  first_target : Spec.map (CommRingCat.ofHom first.toRingHom) ≫
    ((C.source.geometry v).chart ⦋1⦌ a).targetMap =
      U.source.hom ≫ WidePullback.π _ 0 ≫ Spec.map (CommRingCat.ofHom (L v (a 0)).target.toRingHom) ≫
        ((C.source.cover v).charts (a 0)).targetMap
  second_target : Spec.map (CommRingCat.ofHom second.toRingHom) ≫
    ((C.source.geometry v).chart ⦋1⦌ a).targetMap =
      U.source.hom ≫ WidePullback.π _ 1 ≫ Spec.map (CommRingCat.ofHom (L v (a 1)).target.toRingHom) ≫
        ((C.source.cover v).charts (a 1)).targetMap

def differenceValue {v : Fin C.family.components} {a : Fin 2 → Fin (C.source.cover v).count}
    {U : SourceTuple C E H B T L v ⦋1⦌ a} (P : Pair C E U)
    (x : ((C.source.geometry v).chart ⦋1⦌ a).target) :
    sourceCoefficient ((C.source.geometry v).chart ⦋1⦌ a) E.coefficient :=
  U.coefficient.hom (U.extension.kernel ⟨P.second x - P.first x, by
    change U.extension.projection (_ - _) = 0
    rw [map_sub, P.second_reduction, P.first_reduction, sub_self]⟩)

def unitValue {v : Fin C.family.components} {a : Fin 2 → Fin (C.source.cover v).count}
    (U : SourceTuple C E H B T L v ⦋1⦌ a) (u : U.extension.ringˣ)
    (h : U.extension.projection u = 1) :
    sourceCoefficient ((C.source.geometry v).chart ⦋1⦌ a) E.coefficient :=
  U.coefficient.hom (U.extension.kernel ⟨(u : U.extension.ring) - 1, by
    change U.extension.projection (_ - _) = 0
    rw [map_sub, h, map_one, sub_self]⟩)

structure BoundaryRatio {v : Fin C.family.components} {a : Fin 2 → Fin (C.source.cover v).count}
    (U : SourceTuple C E H B T L v ⦋1⦌ a) (P : Pair C E U)
    (z : ((C.source.geometry v).chart ⦋1⦌ a).target) where
  unit : U.extension.ringˣ
  reduction : U.extension.projection unit = 1
  coordinate : P.second z = P.first z * (unit : U.extension.ring)

structure NodeRatios {v : Fin C.family.components} {a : Fin 2 → Fin (C.source.cover v).count}
    (U : SourceTuple C E H B T L v ⦋1⦌ a) (P : Pair C E U)
    (z : Fin 2 → ((C.source.geometry v).chart ⦋1⦌ a).target) where
  unit : Fin 2 → U.extension.ringˣ
  reduction : ∀ i, U.extension.projection (unit i) = 1
  coordinate : ∀ i, P.second (z i) = P.first (z i) * (unit i : U.extension.ring)
  baseUnit : (T.extension ⦋1⦌ (LiSharedTargetCechModels.sourceLabels C.source.cover v a)).ringˣ
  baseReduction : (T.extension ⦋1⦌
    (LiSharedTargetCechModels.sourceLabels C.source.cover v a)).projection baseUnit = 1
  product : (unit 0 : U.extension.ring) * (unit 1 : U.extension.ring) = U.base baseUnit

def Ratios {v : Fin C.family.components} {a : Fin 2 → Fin (C.source.cover v).count}
    (U : SourceTuple C E H B T L v ⦋1⦌ a) (P : Pair C E U) :
    Mode C.family.projection C.family.boundary C.family.parameterFunction
      ((C.source.geometry v).chart ⦋1⦌ a) → Type
  | .ordinary _ _ _ _ => PUnit
  | .boundary _ o _ _ _ _ => BoundaryRatio C E U P o.coordinate
  | .node o _ _ _ => NodeRatios C E U P o.coordinate

/-- The full logarithmic difference uses actual lifted functions and actual units. -/
def Normalized {v : Fin C.family.components} {a : Fin 2 → Fin (C.source.cover v).count}
    (U : SourceTuple C E H B T L v ⦋1⦌ a) (P : Pair C E U)
    (o : Mode C.family.projection C.family.boundary C.family.parameterFunction
      ((C.source.geometry v).chart ⦋1⦌ a)) (r : Ratios C E U P o)
    (x : value C.family.projection C.family.boundary C.family.parameterFunction E.coefficient o) : Prop :=
  (∀ s, derivative C.family.projection C.family.boundary C.family.parameterFunction
      E.coefficient o x s = differenceValue C E P s) ∧
    match o, r, x with
    | .ordinary _ _ _ _, _, _ => True
    | .boundary _ z pr pt hp h, u, y =>
      boundaryLog C.family.projection C.family.boundary C.family.parameterFunction E.coefficient
        z pr pt hp h y = unitValue C E U u.unit u.reduction
    | .node z pr pure h, u, y =>
      ∀ i : Fin 2, nodeLog C.family.projection C.family.boundary C.family.parameterFunction E.coefficient
        z pr pure h y i = unitValue C E U (u.unit i) (u.reduction i)

def parameterLiftValue (B : BaseCover C E) (T : BaseTuples C E B)
    (p : ∀ a : Labels C, B.scheme a ⟶ C.family.parameterBase)
    (a : Fin 2 → Labels C) (i : Fin 2) (j : Fin C.family.parameterCount) :
    (T.extension ⦋1⦌ a).ring :=
  (T.ring ⦋1⦌ a).symm
    ((WidePullback.π (fun i : Fin 2 => B.projection (a i)) i ≫ p (a i)).appTop.hom
      (C.family.parameterBaseFunction j))

/-- The raw obstruction cochain is computed from the SAME full shared log cochain. -/
def rawFromDifference (x : (C.source.shared.model E.coefficient).cochains.obj ⦋1⦌) :
    (C.source.complex E.coefficient).X 2 :=
  (C.source.termIso E.coefficient 2).inv ((C.source.log E.coefficient).inv.app ⦋1⦌ x)

/-- A constructed actual nonsplit lift system, on every full Cech source and base tuple. -/
structure System where
  curves : Curves C E
  base : BaseCover C E
  tuples : BaseTuples C E base
  lifts : ∀ v i, Lift C E curves base v i
  source : ∀ v z a, SourceTuple C E curves base tuples lifts v z a
  sourceMap : ∀ v {n z : SimplexCategory} (s : n ⟶ z) a,
    (source v n (a ∘ s.toOrderHom)).extension.ring →ₐ[k] (source v z a).extension.ring
  source_native : ∀ v {n z} (s : n ⟶ z) a,
    Spec.map (CommRingCat.ofHom (sourceMap v s a).toRingHom) ≫
      (source v n (a ∘ s.toOrderHom)).source.hom =
        (source v z a).source.hom ≫
          LiGeometricCechModels.tupleProjection (fun i => Spec (.of (lifts v i).extension.ring))
            (fun i => (lifts v i).source) s a
  source_projection : ∀ v {n z} (s : n ⟶ z) a x,
    (source v z a).extension.projection (sourceMap v s a x) =
      ((C.source.geometry v).restriction s a).source
        ((source v n (a ∘ s.toOrderHom)).extension.projection x)
  pairs : ∀ v a, Pair C E (source v ⦋1⦌ a)
  ratios : ∀ v a, Ratios C E (source v ⦋1⦌ a) (pairs v a) ((C.source.geometry v).mode ⦋1⦌ a)
  parameters : ∀ a : Labels C, base.scheme a ⟶ C.family.parameterBase
  parameter_source : ∀ v i, parameters (some ⟨v, i⟩) = (lifts v i).parameter
  parameter_reduction : ∀ a, base.reduction a ≫ parameters a =
    LiSharedTargetCechModels.baseArrow C.source.cover a ≫ C.family.parameter
  parameter_structural : ∀ a, parameters a ≫ C.family.parameterStructural =
    base.projection a ≫ Spec.algebraMap k E.ring
  parameterKernel : ∀ a j, RingHom.ker (tuples.extension ⦋1⦌ a).projection.toRingHom
  parameter_value : ∀ a j, (parameterKernel a j).val =
    parameterLiftValue C E base tuples parameters a 1 j -
      parameterLiftValue C E base tuples parameters a 0 j
  difference : (C.source.shared.model E.coefficient).cochains.obj ⦋1⦌
  source_normalized : ∀ v a,
    Normalized C E (source v ⦋1⦌ a) (pairs v a) ((C.source.geometry v).mode ⦋1⦌ a) (ratios v a)
      ((((C.source.coefficients v).localModel E.coefficient).comparison ⦋1⦌).hom
        ((((C.source.shared.model E.coefficient).comparison ⦋1⦌).hom difference).val.1 v) a)
  base_normalized : ∀ a j,
    ((((C.source.shared.model E.coefficient).comparison ⦋1⦌).hom difference).val.2 a j) =
      (tuples.coefficient ⦋1⦌ a).hom ((tuples.extension ⦋1⦌ a).kernel (parameterKernel a j))
  closed : (C.source.complex E.coefficient).d 2 3 (rawFromDifference C E difference) = 0

/-- Li's obstruction convention (1.22) is the NEGATIVE lifted-map difference.
The universal difference defining deltaOne remains positive. -/
def System.rawCocycle (T : System C E) : (C.source.complex E.coefficient).X 2 :=
  -rawFromDifference C E T.difference

/-- The quotient obstruction is the actual native mapping-cone inclusion of that cochain. -/
def System.quotientCocycle (T : System C E) (G : LiGenericGaugeSourceModels.Source C) :
    (LiGenericGaugeSourceModels.quotientCoefficientComplex C G E.coefficient).X 2 :=
  (CochainComplex.mappingCone.inr (G.coefficientMap E.coefficient)).f 2 (T.rawCocycle C E)

end MathlibExt.AlgebraicGeometry.LiNonsplitSourceModels
