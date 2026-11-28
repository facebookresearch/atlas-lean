/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGenericGaugeSourceModels
public import MathlibExt.AlgebraicGeometry.LiFamilyDeformationMaps

/-!
# Actual generic Li source refinements

Refinements retain the actual scalar, Cartesian curve, target and marking
maps. Matrix/dual maps preserve the whole marked-curve extension functor
and its two universal families. Every Cech tuple has actual source/target
ring maps. Coefficients use their literal tensor map; ordinary derivatives
and all normal logarithms retain the unit/permutation corrections.

The degree-one correction is the tensor evaluation of the difference
between the actual new universal lift and the transported old lift.
The resulting raw cochain map and scaling map give the native cone map.
These constructions and their overlap compatibility are Wanted outputs.
Source: Jun Li math/0110113v1 (1.15)--(1.25), Theorems 2.2--2.3.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGenericSourceRefinementModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Opposite
open GeneralStackGeometry StackCycleGeometry StackAffineModules StackBundleCones
open LiGenericSourceModels LiGenericSourceIndex LiFiniteComplexPresentations
open LiUniversalSourceExtensions LiLocalLiftDifferences LiCechChartModules
open scoped TensorProduct Simplicial

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm
  LiMarkedCurveExtensions.oppositeTower

variable {k : Type} [Field k] {X : Stack (Spec (.of k))}
  (C E : SourceChart X) (f : E.native ⟶ C.native)

def scalar : C.ring →+* E.ring :=
  ((Scheme.ΓSpecIso (.of E.ring)).hom.hom).comp
    (f.hom.base.left.appTop.hom.comp (Scheme.ΓSpecIso (.of C.ring)).inv.hom)

def restrictionComplex :=
  (ModuleCat.restrictScalars (scalar C E f)).mapHomologicalComplex (ComplexShape.up ℤ)

structure FamilyMap where
  scalar_k : ∀ x : k, scalar C E f (algebraMap k C.ring x) = algebraMap k E.ring x
  base : Spec.map (CommRingCat.ofHom (scalar C E f)) = f.hom.base.left
  vertex : Fin E.family.components ≃ Fin C.family.components
  marking : ∀ v, Fin (E.family.markings v) ≃ Fin (C.family.markings (vertex v))
  source : ∀ v, (E.family.curve v).X ⟶ (C.family.curve (vertex v)).X
  source_cartesian : ∀ v, IsPullback (source v) (E.family.curve v).π
    (C.family.curve (vertex v)).π f.hom.base.left
  markings : ∀ v i, (E.family.curve v).marking i ≫ source v =
    f.hom.base.left ≫ (C.family.curve (vertex v)).marking (marking v i)
  target : pullback E.family.projection E.family.parameter ⟶
    pullback C.family.projection C.family.parameter
  target_cartesian : IsPullback target (pullback.snd E.family.projection E.family.parameter)
    (pullback.snd C.family.projection C.family.parameter) f.hom.base.left
  maps : ∀ v, E.family.relative v ≫ target = source v ≫ C.family.relative (vertex v)

variable {C E f}

structure MatrixMap where
  left : left C.source.classification.matrix →ₛₗ[scalar C E f] left E.source.classification.matrix
  right : right C.source.classification.matrix →ₛₗ[scalar C E f] right E.source.classification.matrix
  differential : ∀ x, right (C.source.classification.matrix.differential x) =
    E.source.classification.matrix.differential (left x)

variable (F : FamilyMap C E f)
  (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring) (u : I →ₛₗ[scalar C E f] N)

structure CurveTransport where
  split : LiFamilyDeformationMaps.SplitMap (scalar C E f) I N u
  functor : CurveExtension C.family I ⥤ CurveExtension E.family N
  map : ∀ Q v, ((functor.obj Q).component v).curve.X ⟶ (Q.component (F.vertex v)).curve.X
  cartesian : ∀ Q v, IsPullback (map Q v) ((functor.obj Q).component v).curve.π
    (Q.component (F.vertex v)).curve.π (Spec.map (CommRingCat.ofHom split.map))
  reduction : ∀ Q v, ((functor.obj Q).component v).reduction ≫ map Q v =
    F.source v ≫ (Q.component (F.vertex v)).reduction
  markings : ∀ Q v i, ((functor.obj Q).component v).curve.marking i ≫ map Q v =
    Spec.map (CommRingCat.ofHom split.map) ≫ (Q.component (F.vertex v)).curve.marking (F.marking v i)
  arrows : ∀ {Q H : CurveExtension C.family I} (e : Q ⟶ H) v,
    ((functor.map e) v).iso.hom ≫ map H v = map Q v ≫ (e (F.vertex v)).iso.hom

/-- Global map extensions use one actual target transport over the same split base map. -/
structure MapTransport (T : CurveTransport F I N u) where
  functor : MapExtension C.family I ⥤ MapExtension E.family N
  curve : ∀ H, (functor.obj H).curve = T.functor.obj H.curve
  target : ∀ H, pullback E.family.projection (functor.obj H).parameter.map ⟶
    pullback C.family.projection H.parameter.map
  cartesian : ∀ H, IsPullback (target H)
    (pullback.snd E.family.projection (functor.obj H).parameter.map)
    (pullback.snd C.family.projection H.parameter.map)
    (Spec.map (CommRingCat.ofHom T.split.map))
  reduction : ∀ H, reduceTarget E.family (functor.obj H).parameter ≫ target H =
    F.target ≫ reduceTarget C.family H.parameter
  maps : ∀ H v, HEq ((functor.obj H).relative v ≫ target H)
    (T.map H.curve v ≫ H.relative (F.vertex v))

variable (M : MatrixMap (C := C) (E := E) (f := f))

structure CoefficientMatrixMap where
  left : leftCoefficient C.source.classification.matrix I →ₛₗ[scalar C E f]
    leftCoefficient E.source.classification.matrix N
  right : rightCoefficient C.source.classification.matrix I →ₛₗ[scalar C E f]
    rightCoefficient E.source.classification.matrix N
  left_tensor : ∀ x y, left (x ⊗ₜ[C.ring] y) = M.left x ⊗ₜ[E.ring] u y
  right_tensor : ∀ x y, right (x ⊗ₜ[C.ring] y) = M.right x ⊗ₜ[E.ring] u y
  differential : ∀ x, right (tensorDifferential C.source.classification.matrix I x) =
    tensorDifferential E.source.classification.matrix N (left x)

def coefficientQuotient (L : CoefficientMatrixMap I N u M) :
    AdditiveQuotient (tensorDifferential C.source.classification.matrix I).hom ⥤
      AdditiveQuotient (tensorDifferential E.source.classification.matrix N).hom :=
  (show SemilinearQuotientMap (tensorDifferential C.source.classification.matrix I).hom
    (tensorDifferential E.source.classification.matrix N).hom (scalar C E f) from
      ⟨L.left, L.right, L.differential⟩).functor

structure SourceComparison (T : CurveTransport F I N u) (L : CoefficientMatrixMap I N u M) where
  comparison : T.functor ⋙ E.source.classification.functor N ≅
    C.source.classification.functor I ⋙ coefficientQuotient I N u M L

variable {I N u M}

structure DualComparison (M : MatrixMap (C := C) (E := E) (f := f)) where
  right : rightDual C.source.classification.matrix →ₛₗ[scalar C E f]
    rightDual E.source.classification.matrix
  left : leftDual C.source.classification.matrix →ₛₗ[scalar C E f]
    leftDual E.source.classification.matrix
  right_pairing : ∀ a x,
    (show LiFiniteComplexPresentations.right E.source.classification.matrix →ₗ[E.ring] E.ring from right a) (M.right x) =
      scalar C E f ((show LiFiniteComplexPresentations.right C.source.classification.matrix →ₗ[C.ring] C.ring from a) x)
  left_pairing : ∀ a x,
    (show LiFiniteComplexPresentations.left E.source.classification.matrix →ₗ[E.ring] E.ring from left a) (M.left x) =
      scalar C E f ((show LiFiniteComplexPresentations.left C.source.classification.matrix →ₗ[C.ring] C.ring from a) x)
  differential : ∀ a, left (dualMap C.source.classification.matrix a) =
    dualMap E.source.classification.matrix (right a)
  rightTransport : CurveTransport F (rightDual C.source.classification.matrix)
    (rightDual E.source.classification.matrix) right
  leftTransport : CurveTransport F (leftDual C.source.classification.matrix)
    (leftDual E.source.classification.matrix) left
  universal : rightTransport.functor.obj C.source.universal.extension ≅ E.source.universal.extension
  trivial : leftTransport.functor.obj (trivialExtension C.family C.source.classification C.source.universal.trivial) ≅
    trivialExtension E.family E.source.classification E.source.universal.trivial
  trivialization : ∀ v,
    (E.source.universal.trivialization.inv v).iso.hom ≫
      ((E.source.classification.baseChange (dualMap E.source.classification.matrix)
        E.source.universal.extension).component v).map ≫ (universal.inv v).iso.hom ≫
      rightTransport.map C.source.universal.extension v =
    (trivial.inv v).iso.hom ≫
      leftTransport.map (trivialExtension C.family C.source.classification C.source.universal.trivial) v ≫
      (C.source.universal.trivialization.inv (F.vertex v)).iso.hom ≫
      ((C.source.classification.baseChange (dualMap C.source.classification.matrix)
        C.source.universal.extension).component (F.vertex v)).map

structure CechGeometry where
  index : ∀ v, Fin (E.source.cover v).count → Fin (C.source.cover (F.vertex v)).count
  source : ∀ v z a, ((C.source.geometry (F.vertex v)).chart z (index v ∘ a)).source →+*
    ((E.source.geometry v).chart z a).source
  target : ∀ v z a, ((C.source.geometry (F.vertex v)).chart z (index v ∘ a)).target →+*
    ((E.source.geometry v).chart z a).target
  scalar : ∀ v z a r, source v z a
    (algebraMap C.ring ((C.source.geometry (F.vertex v)).chart z (index v ∘ a)).source r) =
    algebraMap E.ring ((E.source.geometry v).chart z a).source (LiGenericSourceRefinementModels.scalar C E f r)
  source_map : ∀ v z a, Spec.map (CommRingCat.ofHom (source v z a)) ≫
    ((C.source.geometry (F.vertex v)).chart z (index v ∘ a)).sourceMap =
      ((E.source.geometry v).chart z a).sourceMap ≫ F.source v
  target_source : ∀ v z a r, source v z a
    (algebraMap ((C.source.geometry (F.vertex v)).chart z (index v ∘ a)).target
      ((C.source.geometry (F.vertex v)).chart z (index v ∘ a)).source r) =
    algebraMap ((E.source.geometry v).chart z a).target
      ((E.source.geometry v).chart z a).source (target v z a r)
  base : ∀ z (a : Fin (z.len + 1) → LiSharedTargetCechModels.Label E.source.cover),
    LiSharedTargetCechModels.baseTuple E.source.cover z a ⟶
      LiSharedTargetCechModels.baseTuple C.source.cover z
        (fun i => (a i).map (fun x => ⟨F.vertex x.1, index x.1 x.2⟩))
  baseRing : ∀ z (a : Fin (z.len + 1) → LiSharedTargetCechModels.Label E.source.cover),
    LiSharedTargetCechModels.baseRing C.source.cover z
      (fun i => (a i).map (fun x => ⟨F.vertex x.1, index x.1 x.2⟩)) →+*
        LiSharedTargetCechModels.baseRing E.source.cover z a
  base_native : ∀ z a x, baseRing z a x = (base z a).appTop.hom x
  base_scalar : ∀ z a x, baseRing z a
    (algebraMap C.ring (LiSharedTargetCechModels.baseRing C.source.cover z
      (fun i => (a i).map (fun x => ⟨F.vertex x.1, index x.1 x.2⟩))) x) =
    algebraMap E.ring (LiSharedTargetCechModels.baseRing E.source.cover z a)
      (LiGenericSourceRefinementModels.scalar C E f x)

variable (G : CechGeometry F) (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
  (u : I →ₛₗ[scalar C E f] N)

/-- The logarithmic coordinates of the coarse chart `a` are carried to those of the refining chart
`b`, up to units (and a permutation of the two branches at a node). The refining chart has the same
mode as `a`, or is an ordinary chart missing the transported special locus of `a` (the boundary
coordinate becomes a unit, or the two node coordinates generate the unit ideal); such a chart
retains only its ordinary derivatives (as for restrictions to ordinary intersections in
`LiCechChartModules.ModuleRestriction`). An ordinary chart is never refined by a boundary or node
chart, and boundary and node charts are never interchanged. -/
def LogNormalized {v : Fin C.family.components} {w : Fin E.family.components}
    (a : LiAffineMapCharts.Chart (C.family.curve v).π C.family.structural (C.family.map v))
    (b : LiAffineMapCharts.Chart (E.family.curve w).π E.family.structural (E.family.map w))
    (r : a.target →+* b.target)
    (coefficient : LiAffineMapCharts.sourceCoefficient a I →ₛₗ[scalar C E f]
      LiAffineMapCharts.sourceCoefficient b N)
    (o : Mode C.family.projection C.family.boundary C.family.parameterFunction a)
    (z : Mode E.family.projection E.family.boundary E.family.parameterFunction b)
    (h : LiCechChartModules.value C.family.projection C.family.boundary C.family.parameterFunction I o →ₛₗ[scalar C E f]
      LiCechChartModules.value E.family.projection E.family.boundary E.family.parameterFunction N z) : Prop :=
  match o, z, h with
  | .boundary _ old pr pt hp ht, .boundary _ new qr qt hq hs, h =>
    ∃ unit : b.targetˣ, new.coordinate = (unit : b.target) * r old.coordinate ∧
      ∀ x, LiCechChartModules.boundaryLog E.family.projection E.family.boundary E.family.parameterFunction N
        new qr qt hq hs (h x) =
      ((unit⁻¹ : b.targetˣ) : b.target) •
        LiCechChartModules.derivative E.family.projection E.family.boundary E.family.parameterFunction N
          (.boundary _ new qr qt hq hs) (h x) (unit : b.target) +
        coefficient (LiCechChartModules.boundaryLog C.family.projection C.family.boundary C.family.parameterFunction I
          old pr pt hp ht x)
  | .node old pr pure ht, .node new qr full hs, h =>
    ∃ (permutation : Fin 2 ≃ Fin 2) (unit : Fin 2 → b.targetˣ),
      (∀ i, new.coordinate i = (unit i : b.target) * r (old.coordinate (permutation i))) ∧
      ∀ x i, LiCechChartModules.nodeLog E.family.projection E.family.boundary E.family.parameterFunction N
        new qr full hs (h x) i =
      (((unit i)⁻¹ : b.targetˣ) : b.target) •
        LiCechChartModules.derivative E.family.projection E.family.boundary E.family.parameterFunction N
          (.node new qr full hs) (h x) (unit i : b.target) +
        coefficient (LiCechChartModules.nodeLog C.family.projection C.family.boundary C.family.parameterFunction I
          old pr pure ht x (permutation i))
  | .ordinary .., .ordinary .., _ => True
  | .boundary _ old _ _ _ _, .ordinary .., _ =>
    IsUnit (algebraMap b.target b.source (r old.coordinate))
  | .node old _ _ _, .ordinary .., _ =>
    Ideal.span (Set.range fun i => algebraMap b.target b.source (r (old.coordinate i))) = ⊤
  | _, _, _ => False

set_option maxHeartbeats 1000000 in
-- Kernel checking retains the complete coefficient action on every full base Čech tuple.
/-- All tuple values retain their ordinary derivative and actual tensor coefficients. -/
structure CechMap where
  map : (C.source.data I).logCochains ⟶
    (E.source.data N).logCochains ⋙ ModuleCat.restrictScalars (scalar C E f)
  coefficient : ∀ v z a,
    LiAffineMapCharts.sourceCoefficient ((C.source.geometry (F.vertex v)).chart z (G.index v ∘ a)) I →ₛₗ[scalar C E f]
      LiAffineMapCharts.sourceCoefficient ((E.source.geometry v).chart z a) N
  pure : ∀ v z a x y, coefficient v z a (x ⊗ₜ[C.ring] y) = G.source v z a x ⊗ₜ[E.ring] u y
  value : ∀ v z a,
    LiCechChartModules.value C.family.projection C.family.boundary C.family.parameterFunction I
      ((C.source.geometry (F.vertex v)).mode z (G.index v ∘ a)) →ₛₗ[scalar C E f]
    LiCechChartModules.value E.family.projection E.family.boundary E.family.parameterFunction N
      ((E.source.geometry v).mode z a)
  regular : ∀ v z a x r,
    LiCechChartModules.derivative E.family.projection E.family.boundary E.family.parameterFunction N
      ((E.source.geometry v).mode z a) (value v z a x) (G.target v z a r) =
    coefficient v z a
      (LiCechChartModules.derivative C.family.projection C.family.boundary C.family.parameterFunction I
        ((C.source.geometry (F.vertex v)).mode z (G.index v ∘ a)) x r)
  logarithms : ∀ v z a, LogNormalized I N
    ((C.source.geometry (F.vertex v)).chart z (G.index v ∘ a))
    ((E.source.geometry v).chart z a) (G.target v z a) (coefficient v z a)
    ((C.source.geometry (F.vertex v)).mode z (G.index v ∘ a))
    ((E.source.geometry v).mode z a) (value v z a)
  normalized : ∀ v z a (x : (C.source.data I).logCochains.obj z),
    (((E.source.coefficients v).localModel N).comparison z).hom
      (E.source.sourceLogValue N z (map.app z x) v) a =
    value v z a ((((C.source.coefficients (F.vertex v)).localModel I).comparison z).hom
      (C.source.sourceLogValue I z x (F.vertex v)) (G.index v ∘ a))
  baseCoefficient : ∀ z (a : Fin (z.len + 1) → LiSharedTargetCechModels.Label E.source.cover),
    (LiSharedTargetCechModels.baseRing C.source.cover z
      (fun i => (a i).map (fun x => ⟨F.vertex x.1, G.index x.1 x.2⟩)) ⊗[C.ring] I) →ₛₗ[G.baseRing z a]
        (LiSharedTargetCechModels.baseRing E.source.cover z a ⊗[E.ring] N)
  base_pure : ∀ z a x y, baseCoefficient z a (x ⊗ₜ[C.ring] y) =
    G.baseRing z a x ⊗ₜ[E.ring] u y
  parameter : ∀ z (a : Fin (z.len + 1) → LiSharedTargetCechModels.Label E.source.cover),
    (Fin C.family.parameterCount →
      LiSharedTargetCechModels.baseRing C.source.cover z
        (fun i => (a i).map (fun x => ⟨F.vertex x.1, G.index x.1 x.2⟩)) ⊗[C.ring] I) →ₛₗ[scalar C E f]
    (Fin E.family.parameterCount → LiSharedTargetCechModels.baseRing E.source.cover z a ⊗[E.ring] N)
  parameter_normalized : ∀ z (a : Fin (z.len + 1) → LiSharedTargetCechModels.Label E.source.cover)
    (x : (C.source.data I).logCochains.obj z), HEq
    ((((E.source.shared.model N).comparison z).hom ((E.source.log N).hom.app z (map.app z x))).val.2 a)
      (parameter z a
        ((((C.source.shared.model I).comparison z).hom ((C.source.log I).hom.app z x)).val.2
          (fun k => (a k).map (fun x => ⟨F.vertex x.1, G.index x.1 x.2⟩))))

variable {I N u G}

structure UniversalDifference (G : CechGeometry F) (M : MatrixMap (C := C) (E := E) (f := f))
    (V : DualComparison F M) where
  extension : ∀ v i, LocalExtension ((E.source.geometry v).chart ⦋0⦌ (fun _ => i))
    (rightDual E.source.classification.matrix)
  pair : ∀ v i, Pair E.family.parameterFunction ((E.source.geometry v).chart ⦋0⦌ (fun _ => i))
    (rightDual E.source.classification.matrix) (extension v i)
  globalBase : ∀ v i, TrivSqZeroExt E.ring (rightDual E.source.classification.matrix) →+*
    (extension v i).extension.ring
  global_scalar : ∀ v i r, globalBase v i (TrivSqZeroExt.inl r) =
    algebraMap E.ring (extension v i).extension.ring r
  global_coefficient : ∀ v i a, globalBase v i (TrivSqZeroExt.inr a) =
    (extension v i).baseMap (TrivSqZeroExt.inr (1 ⊗ₜ[E.ring] a))
  universal : ∀ v i, Spec (.of (extension v i).extension.ring) ⟶
    (E.source.universal.extension.component v).curve.X
  universal_over : ∀ v i, universal v i ≫ (E.source.universal.extension.component v).curve.π =
    Spec.map (CommRingCat.ofHom (globalBase v i))
  universal_cartesian : ∀ v i, IsPullback
    (Spec.map (CommRingCat.ofHom (extension v i).extension.projection.toRingHom))
    ((E.source.geometry v).chart ⦋0⦌ (fun _ => i)).sourceMap
    (universal v i) (E.source.universal.extension.component v).reduction
  new : ∀ v i, (E.source.lifts v i).extension.extension.ring →+* (extension v i).extension.ring
  old : ∀ v i, (C.source.lifts (F.vertex v) (G.index v i)).extension.extension.ring →+*
    (extension v i).extension.ring
  new_source : ∀ v i, Spec.map (CommRingCat.ofHom (new v i)) ≫ (E.source.lifts v i).source = universal v i
  old_source : ∀ v i, Spec.map (CommRingCat.ofHom (old v i)) ≫
    (C.source.lifts (F.vertex v) (G.index v i)).source =
    universal v i ≫ (V.universal.inv v).iso.hom ≫ V.rightTransport.map C.source.universal.extension v
  new_scalar : ∀ v i a, new v i ((E.source.lifts v i).globalBase a) = globalBase v i a
  old_scalar : ∀ v i a, old v i ((C.source.lifts (F.vertex v) (G.index v i)).globalBase a) =
    globalBase v i (V.rightTransport.split.map a)
  first : ∀ v i, Spec.map (CommRingCat.ofHom (pair v i).first) ≫
    ((E.source.geometry v).chart ⦋0⦌ (fun _ => i)).targetMap =
      Spec.map (CommRingCat.ofHom (new v i)) ≫ (E.source.lifts v i).target
  second : ∀ v i, Spec.map (CommRingCat.ofHom (pair v i).second) ≫
    Spec.map (CommRingCat.ofHom (G.target v ⦋0⦌ (fun _ => i))) ≫
    ((C.source.geometry (F.vertex v)).chart ⦋0⦌ (fun _ => G.index v i)).targetMap =
      Spec.map (CommRingCat.ofHom (old v i)) ≫ (C.source.lifts (F.vertex v) (G.index v i)).target
  ratios : ∀ v i, LiLocalLiftDifferences.Ratios E.family.projection E.family.boundary E.family.parameterFunction
    ((E.source.geometry v).chart ⦋0⦌ (fun _ => i)) (rightDual E.source.classification.matrix)
    (extension v i) (pair v i) ((E.source.geometry v).mode ⦋0⦌ (fun _ => i))
  cochain : (E.source.data (rightDual E.source.classification.matrix)).logCochains.obj ⦋0⦌
  normalized : ∀ v i, LiLocalLiftDifferences.Normalized
    E.family.projection E.family.boundary E.family.parameterFunction
    ((E.source.geometry v).chart ⦋0⦌ (fun _ => i)) (rightDual E.source.classification.matrix)
    (extension v i) (pair v i) ((E.source.geometry v).mode ⦋0⦌ (fun _ => i)) (ratios v i)
    ((((E.source.coefficients v).localModel (rightDual E.source.classification.matrix)).comparison ⦋0⦌).hom
      (E.source.sourceLogValue (rightDual E.source.classification.matrix) ⦋0⦌ cochain v) (fun _ => i))

def correctionValue {G : CechGeometry F} {M : MatrixMap (C := C) (E := E) (f := f)}
    {V : DualComparison F M} (H : UniversalDifference F G M V) (N : ModuleCat.{0} E.ring)
    (x : rightCoefficient E.source.classification.matrix N) : (E.source.data N).logCochains.obj ⦋0⦌ :=
  (E.coefficients.logMap (ModuleCat.ofHom (LiTensorEvaluation.evaluation E.ring
    (right E.source.classification.matrix) N x))).app ⦋0⦌ H.cochain

variable (GC : LiGenericGaugeSourceModels.Source C) (GE : LiGenericGaugeSourceModels.Source E)

structure SourceRefinement where
  family : FamilyMap C E f
  matrix : MatrixMap (C := C) (E := E) (f := f)
  dual : DualComparison family matrix
  geometry : CechGeometry family
  differences : UniversalDifference family geometry matrix dual
  curve : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N), CurveTransport family I N u
  maps : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N), MapTransport family I N u (curve I N u)
  coefficients : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N), CoefficientMatrixMap I N u matrix
  source : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N),
    SourceComparison family I N u matrix (curve I N u) (coefficients I N u)
  cech : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N), CechMap family geometry I N u
  raw : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N), C.source.complex I ⟶
    (restrictionComplex C E f).obj (E.source.complex N)
  zero : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N) x, (E.source.termIso N 0).hom ((raw I N u).f 0 x) =
    (E.source.source N).zero.inv
      ((coefficients I N u).left ((C.source.source I).zero.hom ((C.source.termIso I 0).hom x)))
  one : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N) x, (E.source.termIso N 1).hom ((raw I N u).f 1 x) =
    ((E.source.source N).one.inv
      ((coefficients I N u).right ((C.source.source I).one.hom (((C.source.termIso I 1).hom x).1))),
      (show (E.source.data N).logCochains.obj ⦋0⦌ from
        (cech I N u).map.app ⦋0⦌ (((C.source.termIso I 1).hom x).2)) -
        correctionValue family differences N
          ((coefficients I N u).right ((C.source.source I).one.hom (((C.source.termIso I 1).hom x).1))))
  higher : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N) (j : ℕ) x,
    (E.source.termIso N (j + 2)).hom ((raw I N u).f (j + 2 : ℕ) x) =
      (cech I N u).map.app ⦋j + 1⦌ ((C.source.termIso I (j + 2)).hom x)
  cocycle : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N),
    SemilinearQuotientMap (cocycleDifferential C.family C.source I).hom
      (cocycleDifferential E.family E.source N).hom (scalar C E f)
  cocycle_zero : ∀ I N u x,
    (cocycle I N u).degreeZero x = (E.source.termIso N 0).hom
      ((raw I N u).f 0 ((C.source.termIso I 0).inv x))
  cocycle_one : ∀ I N u x,
    ((cocycle I N u).degreeOne x).val = (E.source.termIso N 1).hom
      ((raw I N u).f 1 ((C.source.termIso I 1).inv x.val))
  deformations : ∀ (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring)
    (u : I →ₛₗ[scalar C E f] N),
    (maps I N u).functor ⋙ E.deformations.functor N ≅
      C.deformations.functor I ⋙ (cocycle I N u).functor
  torusMap : _root_.CategoryTheory.MonoidalCategoryStruct.tensorObj E.spec
    (ExpansionParameterModels.torusScheme k GC.gauge.rank) ⟶
      ExpansionParameterModels.torusScheme k GE.gauge.rank
  lieCoefficient : Fin GC.gauge.rank → Fin GE.gauge.rank → E.ring
  torus_normalized : ∀ j : Fin GC.gauge.rank,
    GE.gauge.torus.units (TorusInfinitesimalPoints.doubled (k := k) E.ring)
      (CartesianMonoidalCategory.lift (TorusInfinitesimalPoints.projection (k := k) E.ring)
        (TorusInfinitesimalPoints.point GC.gauge.torus E.ring j) ≫ torusMap) =
      fun i => Units.map (Scheme.ΓSpecIso (.of (TrivSqZeroExt E.ring E.ring))).inv.hom.toMonoidHom
        (TorusInfinitesimalPoints.unit E.ring (lieCoefficient j i))
  lie : LiGenericGaugeSourceModels.lieComplex C GC.gauge ⟶
    (restrictionComplex C E f).obj (LiGenericGaugeSourceModels.lieComplex E GE.gauge)
  lie_normalized : ∀ j : Fin GC.gauge.rank,
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
      (ModuleCat.of E.ring (Fin GE.gauge.rank → E.ring))).hom
        (lie.f 1 ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1
          (ModuleCat.of C.ring (Fin GC.gauge.rank → C.ring))).inv (Pi.single j 1))) = lieCoefficient j
  action : GC.map ≫ raw (ModuleCat.of C.ring C.ring) (ModuleCat.of E.ring E.ring)
    (scalar C E f).toSemilinearMap = lie ≫ (restrictionComplex C E f).map GE.map

def quotientMap (T : SourceRefinement (C := C) (E := E) (f := f) GC GE) :
    LiGenericGaugeSourceModels.quotientComplex C GC ⟶
      (restrictionComplex C E f).obj (LiGenericGaugeSourceModels.quotientComplex E GE) :=
  CochainComplex.mappingCone.map GC.map ((restrictionComplex C E f).map GE.map) T.lie
    (T.raw (ModuleCat.of C.ring C.ring) (ModuleCat.of E.ring E.ring) (scalar C E f).toSemilinearMap)
    T.action ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso GE.map
        (ModuleCat.restrictScalars (scalar C E f))).inv

end MathlibExt.AlgebraicGeometry.LiGenericSourceRefinementModels
