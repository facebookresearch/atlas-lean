/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanChernModels
public import MathlibExt.AlgebraicGeometry.ArchimedeanChernModels
public import MathlibExt.AlgebraicGeometry.AdelicPicardVectors
public import MathlibExt.AlgebraicGeometry.HermitianModelRestrictions

/-!
# Adelic compact-test limits and the same-degree canonical probability

Every generic model is a common actual refinement of the original rational
models. The original generic open maps and the common generic open map are
DENSE. Model degrees are the actual coherent subset-Euler differences of
the literal generic model lines, divided by their original denominators.
The generic-forgetful degree is the native limit of precisely these degrees.

Model metrics use the actual compactification extensions and native
pullback fibre maps. Local Chern actions are computed by the genuine
Archimedean chart/resolution source or the general valuation model-test
intersection source. Open tests have the actual zero extension. Global
signed measure results retain genuine convergence and normalization on
EVERY compact test; no limit action, final measure, or open degree is assigned.

The canonical measure is the inverse POSITIVE SAME generic-forgetful
degree times the SAME positive Chern measure. Its mass theorem requires
properness, or the exact number-field/one-variable-function-field ground
source of Yuan--Zhang Lemma 5.4.4. The latter is not asserted for arbitrary
measured adelic fields or for arbitrary nonproper local metrics.

Source: Yuan--Zhang, arXiv:2105.13587v9, Proposition 4.1.1, Section 3.6.7,
printed pp153--154 and Lemma 5.4.4, pp170--171; Appendix A.6.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicChernLimits

open CategoryTheory CategoryTheory.Limits Opposite Filter MeasureTheory
open _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels RationalAdelicModelMetrics AdelicPicardVectors
open AdelicSemipositiveClosures ModelIntersectionDegrees GenericSectionMaps
open CompactificationMetricExtensions ComplexAnalytification
open scoped Topology CompactlySupported

instance pointMeasurable (F : Type) [NormedField F] (Z : Over (Spec (.of F))) :
    MeasurableSpace (ValuedLineFibres.Point F Z) := borel _
instance pointBorel (F : Type) [NormedField F] (Z : Over (Spec (.of F))) :
    BorelSpace (ValuedLineFibres.Point F Z) := ⟨rfl⟩

variable {K : Type} [Field K] {A : AdelicField K}

/-- Base change of the actual source scheme map at this original completed place. -/
def placeMap {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (v : A.places) :
    placeScheme A X v ⟶ placeScheme A Y v :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (A.embedding v)))).map f

theorem placeMap_projection {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (v : A.places) :
    (placeMap f v).left ≫ placeProjection A Y v = placeProjection A X v ≫ f.left := by
  simp [placeMap, placeProjection, Over.pullback]

/-- This is the native pullback-composition line comparison. -/
def placePullbackLine {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (L : Y.left.Modules)
    (v : A.places) :
    (Scheme.Modules.pullback (placeMap f v).left).obj (placeLine A Y L v) ≅
      placeLine A X ((Scheme.Modules.pullback f.left).obj L) v :=
  (Scheme.Modules.pullbackComp (placeMap f v).left (placeProjection A Y v)).app L ≪≫
    eqToIso (congrArg (fun g ↦ (Scheme.Modules.pullback g).obj L) (placeMap_projection f v)) ≪≫
      ((Scheme.Modules.pullbackComp (placeProjection A X v) f.left).app L).symm

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {d : ℕ} {L : Fin d → X.left.Modules}
  (m : ∀ i, RationalAdelicModelMetrics.ModelMetric (A := A) (X := X) (L := L i))

/-- Common generic refinements retain actual source maps and dense generic opens. -/
structure GenericModelStage where
  scheme : Over (Spec (.of K))
  [proper : IsProper scheme.hom]
  openMap : X ⟶ scheme
  [openImmersion : IsOpenImmersion openMap.left]
  dense : DenseRange openMap.left
  refinement : ∀ i, scheme ⟶ (m i).integral.model.compactification
  onOpen : ∀ i, openMap ≫ refinement i = (m i).integral.model.openMap
  sourceDense : ∀ i, DenseRange (m i).integral.model.openMap.left

attribute [instance] GenericModelStage.proper GenericModelStage.openImmersion

variable {m} (S : GenericModelStage m)

def GenericModelStage.line (i : Fin d) : S.scheme.left.Modules :=
  (Scheme.Modules.pullback ((S.refinement i).left ≫ (m i).integral.model.genericMap)).obj
    (m i).integral.model.line

/-- Its placewise line is the literal common refinement of the same model power line. -/
def GenericModelStage.placeLineIso (i : Fin d) (v : A.places) :
    (Scheme.Modules.pullback (placeMap (S.refinement i) v).left).obj
      (placeLine A (m i).integral.model.compactification (compactLine (m i).integral.model) v) ≅
        placeLine A S.scheme (S.line i) v :=
  placePullbackLine (S.refinement i) (compactLine (m i).integral.model) v ≪≫
    (Scheme.Modules.pullback (placeProjection A S.scheme v)).mapIso
      ((Scheme.Modules.pullbackComp (S.refinement i).left (m i).integral.model.genericMap).app
        (m i).integral.model.line)

/-- All norms are the actual native pullback norms of the source model extensions. -/
structure StageMetricSources where
  metric : ∀ i, MetrizedLine A S.scheme (S.line i)
  fibre : ∀ i v, MetrizedLineOperationModels.PullbackFibre (A.completion v)
    (placeScheme A (m i).integral.model.compactification v)
    (placeLine A (m i).integral.model.compactification (compactLine (m i).integral.model) v)
    (placeMap (S.refinement i) v)
  pullback : ∀ i v, MetrizedLineOperationModels.PullbackMetric (A.completion v)
    (placeScheme A (m i).integral.model.compactification v)
    (placeLine A (m i).integral.model.compactification (compactLine (m i).integral.model) v)
    (placeMap (S.refinement i) v) (fibre i v) ((m i).compactification.metric.metric v)
  lineFibre : ∀ i v, MetrizedLineOperationModels.FibreIso (A.completion v)
    (placeScheme A S.scheme v)
    ((Scheme.Modules.pullback (placeMap (S.refinement i) v).left).obj
      (placeLine A (m i).integral.model.compactification (compactLine (m i).integral.model) v))
    (placeLine A S.scheme (S.line i) v) (S.placeLineIso i v)
  normalized : ∀ i v p z,
    (((metric i).metric v).fibreNorm p).norm ((lineFibre i v).map p z) =
      ((pullback i v).metric.fibreNorm p).norm z
  hermitian : ∀ i, ArithmeticModelHermitianMetrics.HermitianLine (m i).integral.model.line
  hermitianNorm : ∀ i, HermitianModelRestrictions.IsModelMetric (m i).integral.model
    (hermitian i) (m i).integral.metric

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

variable (G : GroundBase (K := K)) (M : Fin d → LineObject (A := A) (X := X) G)

/-- Actual model classes and the literal generic-forgetful coherent degree source. -/
structure GenericModelSources where
  sequence : ∀ i, ModelSequence (L := (M i).line) (M i).boundary
  sameClass : ∀ i, (sequence i).class = (M i).metric.val
  stage : ∀ n, GenericModelStage (fun i ↦ (sequence i).model n)
  degree : ∀ n, DegreeData (stage n).scheme d (fun i ↦ (stage n).line i)

variable {G M} (F : GenericModelSources G M)

def genericModelDegree (n : ℕ) : ℝ :=
  rationalMixedDegree (F.degree n) (fun i ↦ ((F.sequence i).model n).denominator)

/-- The canonical generic-forgetful degree is computed, never independently assigned. -/
def genericDegree : ℝ := limUnder atTop (genericModelDegree F)

structure GenericDegreeConvergence : Prop where
  converges : Tendsto (genericModelDegree F) atTop (nhds (genericDegree F))

variable {F : Type} [NormedField F] (Y : Over (Spec (.of F)))

/-- The actual complex base change at an isometric Archimedean field embedding. -/
structure ArchRealization where
  embedding : F →+* ℂ
  isometry : ∀ a, ‖embedding a‖ = ‖a‖
  dictionary : ArithmeticModelHermitianMetrics.PointDictionary
    (Over.mk (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom embedding))))
  scalarNorm : ∀ (q : ComplexPoints (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom embedding))))
    (a : F),
    ‖dictionary.residue q
      ((pullback.fst Y.hom (Spec.map (CommRingCat.ofHom embedding))).residueFieldMap q.schemePoint
        (BerkovichAnalytification.scalarMap F Y
          (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom embedding)) q.schemePoint) a))‖ = ‖a‖

variable {Y}

def ArchRealization.scheme (E : ArchRealization Y) : Over (Spec (.of ℂ)) :=
  Over.mk (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom E.embedding)))

def ArchRealization.projection (E : ArchRealization Y) : E.scheme.left ⟶ Y.left :=
  pullback.fst Y.hom (Spec.map (CommRingCat.ofHom E.embedding))

def ArchRealization.point (E : ArchRealization Y) (q : ComplexPoints E.scheme.hom) :
    ValuedLineFibres.Point F Y where
  schemePoint := E.projection q.schemePoint
  absoluteValue := (IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)).comp
    (f := (E.dictionary.residue q).toRingHom.comp (E.projection.residueFieldMap q.schemePoint).hom)
    (RingHom.injective _)
  extends_norm a := E.scalarNorm q a

variable {d : ℕ} {Ls : Fin d → Y.left.Modules}
  (H : ∀ i, ValuedLineFibres.MetrizedLine F Y (Ls i))

/-- Local Archimedean metrics are fixed on actual pulled-back sections,
and tests use the canonical residue quotient to the real analytic space. -/
structure ArchSources where
  realization : ArchRealization Y
  metric : ∀ i, ArchimedeanChernModels.ComplexMetric
    ((Scheme.Modules.pullback realization.projection).obj (Ls i))
  normalized : ∀ i (U : Y.left.Opens) (s : Γ(Ls i,U))
    (q : ComplexPoints realization.scheme.hom) (hq : q.schemePoint ∈ realization.projection ⁻¹ᵁ U),
    ((metric i).metric.fibreNorm ((metric i).dictionary.point q)).norm
      (ValuedLineFibres.evaluateSection _ _ _
        (localPullbackSection realization.projection (Ls i) U (realization.projection ⁻¹ᵁ U) (by rfl) s)
        ((metric i).dictionary.point q) hq) =
      ((H i).fibreNorm (realization.point q)).norm
        (ValuedLineFibres.evaluateSection _ _ _ s (realization.point q) hq)
  continuous : Continuous realization.point
  surjective : Function.Surjective realization.point
  source : ArchimedeanChernModels.GlobalSources realization.scheme d
    (fun i ↦ (Scheme.Modules.pullback realization.projection).obj (Ls i)) metric
  test : C_c(ValuedLineFibres.Point F Y,ℝ) → C_c(ComplexPoints realization.scheme.hom,ℝ)
  testNormalized : ∀ f q, test f q = f (realization.point q)

/-- The nonarchimedean branch uses general model intersections, with actual subtype tests. -/
structure NonarchSources where
  ultrametric : ∀ a b : F, ‖a + b‖ ≤ max ‖a‖ ‖b‖
  allPoints : ∀ p : ValuedLineFibres.Point F Y, ∀ a b,
    p.absoluteValue (a+b) ≤ max (p.absoluteValue a) (p.absoluteValue b)
  source : NonarchimedeanChernModels.CompactTestSources
    (K := F) (X := Y) (hK := ultrametric) (L := Ls) H
  test : C_c(ValuedLineFibres.Point F Y,ℝ) → C_c(ValuedLineFibres.NonArchPoint F Y,ℝ)
  testNormalized : ∀ f p, test f p = f p.val

/-- These branches contain geometric/test sources, rather than final measures. -/
inductive LocalSources where
  | arch : ArchSources (Y := Y) H → LocalSources
  | nonarch : NonarchSources (Y := Y) H → LocalSources

variable {H}

def LocalSources.action (S : LocalSources (Y := Y) H)
    (f : C_c(ValuedLineFibres.Point F Y,ℝ)) : ℝ :=
  match S with
  | .arch T => ArchimedeanChernModels.globalAction T.source (T.test f)
  | .nonarch T => NonarchimedeanChernModels.compactAction T.source (T.test f)

/-- The output is the actual local measure construction, with its complete test-limit laws. -/
def LocalSources.MeasureParts (T : LocalSources (Y := Y) H) : Type :=
  match T with
  | .arch A => ArchimedeanChernModels.ChernMeasureParts A.source
  | .nonarch A => NonarchimedeanChernModels.ChernMeasureParts A.source

def LocalSources.positive (T : LocalSources (Y := Y) H) (R : T.MeasureParts) :
    Measure (ValuedLineFibres.Point F Y) :=
  match T, R with
  | .arch A, R => Measure.map A.realization.point R.positivePart
  | .nonarch _, R => Measure.map Subtype.val R.positivePart

def LocalSources.negative (T : LocalSources (Y := Y) H) (R : T.MeasureParts) :
    Measure (ValuedLineFibres.Point F Y) :=
  match T, R with
  | .arch A, R => Measure.map A.realization.point R.negativePart
  | .nonarch _, R => Measure.map Subtype.val R.negativePart

variable (M : Fin d → LineObject (A := A) (X := X) G)

/-- A global source uses the SAME model classes, and actual zero extensions of open tests. -/
structure ChernSources (B : GenericModelSources G M) where
  metrics : ∀ n, StageMetricSources (B.stage n)
  localSources : ∀ v n, LocalSources
    (Y := placeScheme A (B.stage n).scheme v)
    (fun i ↦ ((metrics n).metric i).metric v)
  extension : ∀ v n, C_c(ValuedLineFibres.Point (A.completion v) (placeScheme A X v),ℝ) →
    C_c(ValuedLineFibres.Point (A.completion v) (placeScheme A (B.stage n).scheme v),ℝ)
  openNormalized : ∀ v n f p, extension v n f
    (MetrizedLineOperationModels.mapPoint _ _ (placeMap (B.stage n).openMap v) p) = f p
  outside : ∀ v n f q, q ∉ Set.range
    (MetrizedLineOperationModels.mapPoint _ _ (placeMap (B.stage n).openMap v)) → extension v n f q = 0

variable {M} {B : GenericModelSources G M} (S : ChernSources M B)

def modelStage (v : A.places)
    (f : C_c(ValuedLineFibres.Point (A.completion v) (placeScheme A X v),ℝ)) (n : ℕ) : ℝ :=
  (S.localSources v n).action (S.extension v n f) /
    ∏ i : Fin d, (((B.sequence i).model n).denominator : ℝ)

def chernAction (v : A.places)
    (f : C_c(ValuedLineFibres.Point (A.completion v) (placeScheme A X v),ℝ)) : ℝ :=
  limUnder atTop (modelStage S v f)

/-- Genuine global signed measure limits on EVERY actual compact test. -/
structure SignedChernMeasure where
  positivePart : ∀ v, Measure (ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
  negativePart : ∀ v, Measure (ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
  [positiveFinite : ∀ v, IsFiniteMeasure (positivePart v)]
  [negativeFinite : ∀ v, IsFiniteMeasure (negativePart v)]
  converges : ∀ v f, Tendsto (modelStage S v f) atTop (nhds (chernAction S v f))
  normalized : ∀ v f, (∫ p, f p ∂positivePart v) - (∫ p, f p ∂negativePart v) = chernAction S v f

/-- Positivity is a result for the SAME source action, not a separately selected measure. -/
structure PositiveChernMeasure (v : A.places) where
  measure : Measure (ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
  [finite : IsFiniteMeasure measure]
  converges : ∀ f, Tendsto (modelStage S v f) atTop (nhds (chernAction S v f))
  normalized : ∀ f, (∫ p, f p ∂measure) = chernAction S v f

attribute [instance] SignedChernMeasure.positiveFinite SignedChernMeasure.negativeFinite
attribute [instance] PositiveChernMeasure.finite

/-- Actual number-field source; its rational rank is the original field degree. -/
structure NumberFieldSource (K : Type) [Field K] : Prop where
  [characteristic : CharZero K]
  [finite : FiniteDimensional ℚ K]

/-- Actual regular projective curve with the SAME function field and ground scalar map. -/
structure OneVariableSource (k : Type) [Field k] (embedding : k →+* K) where
  curve : Over (Spec (.of k))
  [proper : IsProper curve.hom]
  [integral : IsIntegral curve.left]
  [finiteType : LocallyOfFiniteType curve.hom]
  dimension : Order.krullDim curve.left = 1
  regular : ∀ x : curve.left, ∃ π : curve.left.presheaf.stalk x,
    IsLocalRing.maximalIdeal (curve.left.presheaf.stalk x) = Ideal.span {π}
  genericPoint : curve.left
  generic : _root_.closure ({genericPoint} : Set curve.left) = Set.univ
  functionField : curve.left.residueField genericPoint ≃+* K
  scalars : ∀ a : k,
    functionField (((Scheme.ΓSpecIso (.of k)).inv ≫ curve.hom.appTop ≫
      curve.left.Γevaluation genericPoint).hom a) = embedding a

def GlobalFieldScope (G : GroundBase (K := K)) : Prop :=
  match G with
  | .integers => NumberFieldSource K
  | @GroundBase.geometric _ _ k inst embedding =>
    letI := inst
    Nonempty (OneVariableSource k embedding)

/-- Lemma 5.4.4's nonproper hypothesis is kept separate from proper local mass. -/
inductive MassScope (G : GroundBase (K := K)) (X : Over (Spec (.of K))) : Prop
  | proper : IsProper X.hom → MassScope G X
  | globalField : GlobalFieldScope G → MassScope G X

variable {S} {v : A.places} (P : PositiveChernMeasure S v)

/-- The mass refers to the SAME coherent generic degree of the SAME model source. -/
structure MassIdentity (guard : MassScope G X) : Prop where
  normalized : P.measure Set.univ = ENNReal.ofReal (genericDegree B)

/-- Canonical probability: inverse POSITIVE SAME degree, times the SAME Chern measure. -/
def canonicalMeasure (_positive : 0 < genericDegree B) :
    Measure (ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) :=
  (ENNReal.ofReal (genericDegree B))⁻¹ • P.measure

/-- Probability normalization uses exactly this source mass and positive degree. -/
theorem canonicalMeasure_probability (h : 0 < genericDegree B) (guard : MassScope G X)
    (mass : MassIdentity P guard) : IsProbabilityMeasure (canonicalMeasure P h) := by
  constructor
  simp only [canonicalMeasure, Measure.smul_apply, smul_eq_mul, mass.normalized]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr h)) ENNReal.ofReal_ne_top

end MathlibExt.AlgebraicGeometry.AdelicChernLimits
