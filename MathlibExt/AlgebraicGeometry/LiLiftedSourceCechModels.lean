/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiUniversalSourceExtensions
public import MathlibExt.AlgebraicGeometry.LiLocalLiftDifferences
public import MathlibExt.AlgebraicGeometry.LiCechCoefficientModels
public import MathlibExt.AlgebraicGeometry.LiTensorEvaluation
public import MathlibExt.AlgebraicGeometry.RubberLieQuotientComplexes

/-!
# Li's delta from actual universal-source lifted charts

Each chart is the actual etale Cartesian extension over the fixed
universal marked curve. Its target map is a genuine predeformable lift
preserving the full signed contact ideals. Overlap schemes are the actual
fibre products of those lifts; delta1 uses zeta_beta minus zeta_alpha.
The F0-dual chart is their actual pullback to the fixed trivialization;
delta0 uses pulled zeta_alpha minus the original map.

Every coefficient is the actual tensor evaluation of those dual-coefficient
differences. Both source and log cochain terms are fixed by their native
comparisons before constructing the total complex.
Source: Jun Li arXiv:math/0110113v1, equations1.15--1.25.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiLiftedSourceCechModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries MarkedCurveStabilization RelativeProjectiveLineModels
open ExpandedTargetChainGeometry StandardRelativeExpansionModels ExpansionParameterModels
open RubberMapFamilies LiAffineMapCharts LiCechChartModules LiFiniteComplexPresentations
open LiUniversalSourceExtensions LiLocalLiftDifferences
open scoped Simplicial TensorProduct BigOperators

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm LiMarkedCurveExtensions.oppositeTower

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R) (m : ℕ)
  {A : Type} [CommRing A] [Algebra k A] {n genus : ℕ}
  (a : Fin n → ℤ) (F : MarkedFamily (Spec (.of A)) n genus)
  (f : F.X ⟶ (S.chart m).scheme.left)
  (L : LiGeometricCechModels.Cover (p := F.π) (q := (S.chart m).scheme.hom) (f := f))
  (G : LiGeometricCechModels.Geometry (S.chart m).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S m)
    (RubberLieQuotientComplexes.parameters P R S m) L)
  (V : LiCechCoefficientModels.Model (S.chart m).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S m)
    (RubberLieQuotientComplexes.parameters P R S m) L G)
  (C : LiMarkedCurveExtensions.Classification F)
  (U : LiUniversalSourceExtensions.Data F C)

structure Lift (i : Fin L.count) where
  extensionData : LocalExtension (L.charts i) (rightDual C.matrix)
  globalBase : TrivSqZeroExt A (rightDual C.matrix) →+* extensionData.extension.ring
  global_scalar : ∀ r : A, globalBase (TrivSqZeroExt.inl r) = algebraMap A extensionData.extension.ring r
  global_coefficient : ∀ x : rightDual C.matrix,
    globalBase (TrivSqZeroExt.inr x) = extensionData.baseMap (TrivSqZeroExt.inr (1 ⊗ₜ[A] x))
  source : Spec (.of extensionData.extension.ring) ⟶ U.universal.curve.X
  etale : Etale source
  source_over : source ≫ U.universal.curve.π = Spec.map (CommRingCat.ofHom globalBase)
  source_cartesian : IsPullback (Spec.map (CommRingCat.ofHom extensionData.extension.projection.toRingHom))
    (L.charts i).sourceMap source U.universal.reduction
  target : Spec (.of extensionData.extension.ring) ⟶ (S.chart m).scheme.left
  target_reduction : Spec.map (CommRingCat.ofHom extensionData.extension.projection.toRingHom) ≫ target =
    (L.charts i).sourceMap ≫ f
  target_scalar : target ≫ (S.chart m).scheme.hom =
    Spec.algebraMap A extensionData.extension.ring ≫ Spec.algebraMap k A
  parameter : Spec (.of (TrivSqZeroExt (L.charts i).base
    (baseCoefficientObject (L.charts i) (rightDual C.matrix)))) ⟶ (ParameterSpace k m).left
  parameter_square : target ≫ (S.chart m).projection.left =
    Spec.map (CommRingCat.ofHom extensionData.baseMap) ≫ parameter
  relative : Spec (.of extensionData.extension.ring) ⟶ pullback (S.chart m).projection.left parameter
  relative_target : relative ≫ pullback.fst (S.chart m).projection.left parameter = target
  relative_base : relative ≫ pullback.snd (S.chart m).projection.left parameter =
    Spec.map (CommRingCat.ofHom extensionData.baseMap)
  predeformable : RelativeExpandedMapFamilies.IsPredeformable
    (Spec.map (CommRingCat.ofHom extensionData.baseMap)) (pullback.snd (S.chart m).projection.left parameter)
    relative relative_base
  zero_contact : ∀ W : (Spec (.of extensionData.extension.ring)).affineOpens,
    ((RubberLieQuotientComplexes.boundaries O P D R S m 0).comap target).ideal W =
      ∏ j : Positive a, ((U.universal.curve.marking j.val).ker.comap source).ideal W ^ (a j.val).natAbs
  infinity_contact : ∀ W : (Spec (.of extensionData.extension.ring)).affineOpens,
    ((RubberLieQuotientComplexes.boundaries O P D R S m 1).comap target).ideal W =
      ∏ j : Negative a, ((U.universal.curve.marking j.val).ker.comap source).ideal W ^ (a j.val).natAbs

variable (lift : ∀ i : Fin L.count, Lift O P D R S m a F f L C U i)

structure Overlap (t : Fin 2 → Fin L.count) where
  extensionData : LocalExtension (G.chart ⦋1⦌ t) (rightDual C.matrix)
  iso : Spec (.of extensionData.extension.ring) ≅ pullback (lift (t 0)).source (lift (t 1)).source
  left_reduction : Spec.map (CommRingCat.ofHom extensionData.extension.projection.toRingHom) ≫ iso.hom ≫
      pullback.fst (lift (t 0)).source (lift (t 1)).source =
    (G.source ⦋1⦌ t).hom ≫ WidePullback.π _ 0 ≫
      Spec.map (CommRingCat.ofHom (lift (t 0)).extensionData.extension.projection.toRingHom)
  right_reduction : Spec.map (CommRingCat.ofHom extensionData.extension.projection.toRingHom) ≫ iso.hom ≫
      pullback.snd (lift (t 0)).source (lift (t 1)).source =
    (G.source ⦋1⦌ t).hom ≫ WidePullback.π _ 1 ≫
      Spec.map (CommRingCat.ofHom (lift (t 1)).extensionData.extension.projection.toRingHom)
  /-- The overlap's square-zero base is the pullback of the fixed universal split base, with the
  induced coefficient map, so lift differences are measured in the universal extension's
  coefficients (not a rescaled identification). -/
  globalBase : TrivSqZeroExt A (rightDual C.matrix) →+* extensionData.extension.ring
  global_coefficient : ∀ x : rightDual C.matrix,
    globalBase (TrivSqZeroExt.inr x) = extensionData.baseMap (TrivSqZeroExt.inr (1 ⊗ₜ[A] x))
  source_over : iso.hom ≫ pullback.fst (lift (t 0)).source (lift (t 1)).source ≫ (lift (t 0)).source ≫
      U.universal.curve.π = Spec.map (CommRingCat.ofHom globalBase)
  pair : Pair (RubberLieQuotientComplexes.parameters P R S m) (G.chart ⦋1⦌ t) (rightDual C.matrix) extensionData
  first : Spec.map (CommRingCat.ofHom pair.first) ≫ (G.chart ⦋1⦌ t).targetMap =
    iso.hom ≫ pullback.snd (lift (t 0)).source (lift (t 1)).source ≫ (lift (t 1)).target
  second : Spec.map (CommRingCat.ofHom pair.second) ≫ (G.chart ⦋1⦌ t).targetMap =
    iso.hom ≫ pullback.fst (lift (t 0)).source (lift (t 1)).source ≫ (lift (t 0)).target
  ratios : LiLocalLiftDifferences.Ratios (S.chart m).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S m) (RubberLieQuotientComplexes.parameters P R S m)
    (G.chart ⦋1⦌ t) (rightDual C.matrix) extensionData pair (G.mode ⦋1⦌ t)

structure TrivialLift (i : Fin L.count) where
  extensionData : LocalExtension (G.chart ⦋0⦌ (fun _ => i)) (leftDual C.matrix)
  source : Spec (.of extensionData.extension.ring) ⟶ U.trivial.family.curve.X
  etale : Etale source
  /-- The trivialising lift lives over the fixed trivial split base, with the induced coefficient
  map. -/
  globalBase : TrivSqZeroExt A (leftDual C.matrix) →+* extensionData.extension.ring
  global_coefficient : ∀ x : leftDual C.matrix,
    globalBase (TrivSqZeroExt.inr x) = extensionData.baseMap (TrivSqZeroExt.inr (1 ⊗ₜ[A] x))
  source_over : source ≫ U.trivial.family.curve.π = Spec.map (CommRingCat.ofHom globalBase)
  source_cartesian : IsPullback (Spec.map (CommRingCat.ofHom extensionData.extension.projection.toRingHom))
    (G.chart ⦋0⦌ (fun _ => i)).sourceMap source U.trivial.family.reduction
  pull : Spec (.of extensionData.extension.ring) ⟶ Spec (.of (lift i).extensionData.extension.ring)
  pull_square : IsPullback pull source (lift i).source
    (U.trivialization.inv.iso.hom ≫ (C.baseChange (dualMap C.matrix) U.universal).map)
  pair : Pair (RubberLieQuotientComplexes.parameters P R S m)
    (G.chart ⦋0⦌ (fun _ => i)) (leftDual C.matrix) extensionData
  first : Spec.map (CommRingCat.ofHom pair.first) ≫ (G.chart ⦋0⦌ (fun _ => i)).targetMap =
    pull ≫ (lift i).target
  second : Spec.map (CommRingCat.ofHom pair.second) ≫ (G.chart ⦋0⦌ (fun _ => i)).targetMap =
    source ≫ U.trivial.iso.hom ≫ pullback.fst F.π (trivialBase (leftDual C.matrix)) ≫ f
  ratios : LiLocalLiftDifferences.Ratios (S.chart m).projection.left
    (RubberLieQuotientComplexes.boundaries O P D R S m) (RubberLieQuotientComplexes.parameters P R S m)
    (G.chart ⦋0⦌ (fun _ => i)) (leftDual C.matrix) extensionData pair (G.mode ⦋0⦌ (fun _ => i))

structure System where
  overlap : ∀ t : Fin 2 → Fin L.count, Overlap O P D R S m a F f L G C U lift t
  trivial : ∀ i : Fin L.count, TrivialLift O P D R S m a F f L G C U lift i
  differenceOne : (V.localModel (rightDual C.matrix)).cochains.obj ⦋1⦌
  differenceOne_normalized : ∀ t : Fin 2 → Fin L.count,
    LiLocalLiftDifferences.Normalized (S.chart m).projection.left
      (RubberLieQuotientComplexes.boundaries O P D R S m) (RubberLieQuotientComplexes.parameters P R S m)
      (G.chart ⦋1⦌ t) (rightDual C.matrix) (overlap t).extensionData (overlap t).pair (G.mode ⦋1⦌ t) (overlap t).ratios
      (((V.localModel (rightDual C.matrix)).comparison ⦋1⦌).hom differenceOne t)
  differenceZero : (V.localModel (leftDual C.matrix)).cochains.obj ⦋0⦌
  differenceZero_normalized : ∀ i : Fin L.count,
    LiLocalLiftDifferences.Normalized (S.chart m).projection.left
      (RubberLieQuotientComplexes.boundaries O P D R S m) (RubberLieQuotientComplexes.parameters P R S m)
      (G.chart ⦋0⦌ (fun _ => i)) (leftDual C.matrix) (trivial i).extensionData (trivial i).pair
      (G.mode ⦋0⦌ (fun _ => i)) (trivial i).ratios
      (((V.localModel (leftDual C.matrix)).comparison ⦋0⦌).hom differenceZero (fun _ => i))
  complex : ∀ _I : ModuleCat.{0} A, LiCechObstructionComplexes.Data A
  source : ∀ I : ModuleCat.{0} A, SourceBinding C.matrix I (complex I)
  log : ∀ I : ModuleCat.{0} A, (complex I).logCochains ≅ (V.localModel I).cochains
  deltaZero : ∀ (I : ModuleCat.{0} A) (x : (complex I).zero),
    ((log I).hom.app ⦋0⦌) ((complex I).deltaZero x) =
      (LiCechCoefficientModels.transport (g := (S.chart m).projection.left)
        (J := RubberLieQuotientComplexes.boundaries O P D R S m)
        (t := RubberLieQuotientComplexes.parameters P R S m) (L := L) (G := G)
        (u := ModuleCat.ofHom
        (LiTensorEvaluation.evaluation A (left C.matrix) I ((source I).zero.hom x))) V).app ⦋0⦌ differenceZero
  deltaOne : ∀ (I : ModuleCat.{0} A) (x : (complex I).one),
    ((log I).hom.app ⦋1⦌) ((complex I).deltaOne x) =
      (LiCechCoefficientModels.transport (g := (S.chart m).projection.left)
        (J := RubberLieQuotientComplexes.boundaries O P D R S m)
        (t := RubberLieQuotientComplexes.parameters P R S m) (L := L) (G := G)
        (u := ModuleCat.ofHom
        (LiTensorEvaluation.evaluation A (right C.matrix) I ((source I).one.hom x))) V).app ⦋1⦌ differenceOne

end MathlibExt.AlgebraicGeometry.LiLiftedSourceCechModels
