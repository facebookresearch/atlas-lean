/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MetricDelignePairingModels

/-!
# Actual arithmetic/geometric model intersections and numerical limits

Geometric model numbers are the native coherent subset-Euler degrees.
Arithmetic model numbers recurse through the actual regular Cartier
numerator and denominator zero schemes. The base case sums original
local-ring lengths times log of the cardinality of each actual finite
residue field. The Archimedean correction is the log norm of the actual
rational section integrated against the SAME global lower Chern product.
All nonreduced factors and all complex components occur.

Common models preserve the original field, generic maps and source model
lines. Their generic opens and base generic maps are dense. Numerical
adelic intersections are native limits of these actual model numbers,
with the original positive denominator product. Genuine convergence is a
separate result. No numerical model value or open degree is assigned.

Source: Yuan--Zhang, arXiv:2105.13587v9, Proposition 4.1.1, Section 5.3.3
(pp153--154) and Appendix A.3.2; the actual arithmetic curve base case is
compatible with ArithmeticModelCurveDegrees.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NumericalAdelicIntersections

open CategoryTheory CategoryTheory.Limits Opposite Filter MeasureTheory
open _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels RationalAdelicModelMetrics AdelicSemipositiveClosures AdelicPicardVectors
open ArithmeticModelHermitianMetrics HermitianModelRestrictions ArchimedeanChernModels
open ComplexAnalytification DeligneSymbolModels GenericSectionMaps ModelIntersectionDegrees
open scoped Topology

attribute [local instance] HasDerivedCategory.standard

/-- The degree-zero arithmetic cycle uses the entire actual closed-point carrier. -/
structure ZeroSchemeSources (Y : Scheme.{0}) where
  [points : Fintype Y]
  closed : ∀ y : Y, IsClosed ({y} : Set Y)
  finiteResidue : ∀ y : Y, Finite (Y.residueField y)
  lengthFinite : ∀ y : Y, Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) ≠ ⊤
  pureDimension : ∀ C : Set Y, C ∈ irreducibleComponents Y → topologicalKrullDim C = 0

def zeroArithmeticDegree (Y : Scheme.{0}) (S : ZeroSchemeSources Y) : ℝ := by
  letI := S.points
  exact ∑ y : Y, ((Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y)).toNat : ℝ) *
    Real.log (Nat.card (Y.residueField y))

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

variable {Y : Scheme.{0}} {k : ℕ} (L : Fin (k+1) → Y.Modules) (H : ∀ i, HermitianLine (L i))
  (s : RationalSection (L (Fin.last k)))

/-- The correction has actual global charts/resolutions and actual rational section norms. -/
structure ArchIntegralSources where
  source : GlobalSources (complexScheme Y) k
    (fun i : Fin k ↦ complexLine (L i.castSucc))
    (fun i ↦ ⟨(H i.castSucc).dictionary, (H i.castSucc).metric⟩)
  measures : ChernMeasureParts source
  logNorm : ComplexPoints (complexScheme Y).hom → ℝ
  normalized : ∀ q (hq : q.Mem (complexProjection Y ⁻¹ᵁ s.domain)),
    logNorm q = Real.log (((H (Fin.last k)).metric.fibreNorm ((H (Fin.last k)).dictionary.point q)).norm
      (ValuedLineFibres.evaluateSection _ _ _ (complexSection s.domain s.value)
        ((H (Fin.last k)).dictionary.point q)
        ((ComplexPoints.schemePoint_mem_iff _ _).mpr hq)))
  nonzeroPositive : ∀ᵐ q ∂measures.positivePart, ∃ hq : q.Mem (complexProjection Y ⁻¹ᵁ s.domain),
    0 < ((H (Fin.last k)).metric.fibreNorm ((H (Fin.last k)).dictionary.point q)).norm
      (ValuedLineFibres.evaluateSection _ _ _ (complexSection s.domain s.value)
        ((H (Fin.last k)).dictionary.point q) ((ComplexPoints.schemePoint_mem_iff _ _).mpr hq))
  nonzeroNegative : ∀ᵐ q ∂measures.negativePart, ∃ hq : q.Mem (complexProjection Y ⁻¹ᵁ s.domain),
    0 < ((H (Fin.last k)).metric.fibreNorm ((H (Fin.last k)).dictionary.point q)).norm
      (ValuedLineFibres.evaluateSection _ _ _ (complexSection s.domain s.value)
        ((H (Fin.last k)).dictionary.point q) ((ComplexPoints.schemePoint_mem_iff _ _).mpr hq))
  positiveIntegrable : Integrable logNorm measures.positivePart
  negativeIntegrable : Integrable logNorm measures.negativePart

def archIntegral (S : ArchIntegralSources L H s) : ℝ :=
  (∫ q, S.logNorm q ∂S.measures.positivePart) - (∫ q, S.logNorm q ∂S.measures.negativePart)

/-- Actual Cartier recursion, retaining nonreduced zero schemes and full lower metrics. -/
inductive ArithmeticSources : (Y : Scheme.{0}) → (d : ℕ) →
    (L : Fin d → Y.Modules) → (∀ i, HermitianLine (L i)) → Type 1
  | zero (Y : Scheme.{0}) (L : Fin 0 → Y.Modules) (H : ∀ i, HermitianLine (L i)) (S : ZeroSchemeSources Y) :
      ArithmeticSources Y 0 L H
  | step (Y : Scheme.{0}) (k : ℕ) (L : Fin (k+1) → Y.Modules) (H : ∀ i, HermitianLine (L i))
      (s : RationalSection (L (Fin.last k))) (F : CartierFraction (L (Fin.last k)) s)
      (positive : ∀ i : Fin k, HermitianPullback F.positive.inclusion (H i.castSucc))
      (negative : ∀ i : Fin k, HermitianPullback F.negative.inclusion (H i.castSucc))
      (P : ArithmeticSources F.positive.scheme k
        (fun i ↦ (Scheme.Modules.pullback F.positive.inclusion).obj (L i.castSucc))
        (fun i ↦ (positive i).hermitian))
      (N : ArithmeticSources F.negative.scheme k
        (fun i ↦ (Scheme.Modules.pullback F.negative.inclusion).obj (L i.castSucc))
        (fun i ↦ (negative i).hermitian))
      (A : ArchIntegralSources L H s) : ArithmeticSources Y (k+1) L H

def arithmeticValue {Y : Scheme.{0}} {d : ℕ} {L : Fin d → Y.Modules}
    {H : ∀ i, HermitianLine (L i)} : ArithmeticSources Y d L H → ℝ
  | .zero Y _ _ S => zeroArithmeticDegree Y S
  | .step _ _ _ _ _ _ _ _ P N A => arithmeticValue P - arithmeticValue N - archIntegral _ _ _ A

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {t : ℕ} {Ls : Fin t → X.left.Modules}
  (m : ∀ i, RationalAdelicModelMetrics.ModelMetric (A := A) (X := X) (L := Ls i))

def QuasiProjectiveScope (X : Over (Spec (.of K))) : Prop :=
  ∃ Y : Over (Spec (.of K)), IsProjectiveOver Y.hom ∧
    ∃ j : X ⟶ Y, IsOpenImmersion j.left ∧ DenseRange j.left

def GroundModelOver (G : GroundBase (K := K))
    (B : AdelicArithmeticModelFrames.ArithmeticBase A) : Prop :=
  match G with
  | .integers => CharZero K ∧ IsProper (integerMap B.scheme) ∧ Flat (integerMap B.scheme) ∧
    LocallyOfFiniteType (integerMap B.scheme) ∧ IsProjectiveOver (integerMap B.scheme)
  | @GroundBase.geometric _ _ k inst embedding =>
    letI := inst
    ∃ g : B.scheme ⟶ Spec (.of k), IsProper g ∧ LocallyOfFiniteType g ∧ IsProjectiveOver g ∧
      B.generic ≫ g = Spec.map (CommRingCat.ofHom embedding)

/-- A genuine finitely generated ground-field model, with the exact original function field. -/
structure GroundModel (G : GroundBase (K := K))
    (B : AdelicArithmeticModelFrames.ArithmeticBase A) (b : ℕ+) where
  dense : DenseRange B.generic
  integral : IsIntegral B.scheme
  residue : B.scheme.residueField (B.generic (IsLocalRing.closedPoint K)) ≃+* K
  fieldMap : B.generic = Spec.map (CommRingCat.ofHom residue.toRingHom) ≫
    B.scheme.fromSpecResidueField (B.generic (IsLocalRing.closedPoint K))
  dimension : Order.krullDim B.scheme = (b : ℕ)
  overGround : GroundModelOver G B

/-- A common actual arithmetic model, with dense generic fibre and original scalar maps. -/
structure CommonModel where
  base : AdelicArithmeticModelFrames.ArithmeticBase A
  baseDense : DenseRange base.generic
  baseIntegral : IsIntegral base.scheme
  baseResidue : base.scheme.residueField (base.generic (IsLocalRing.closedPoint K)) ≃+* K
  baseFieldMap : base.generic =
    Spec.map (CommRingCat.ofHom baseResidue.toRingHom) ≫
      base.scheme.fromSpecResidueField (base.generic (IsLocalRing.closedPoint K))
  scheme : Scheme.{0}
  structureMap : scheme ⟶ base.scheme
  [proper : IsProper structureMap]
  [flat : Flat structureMap]
  compactification : Over (Spec (.of K))
  [genericProper : IsProper compactification.hom]
  openMap : X ⟶ compactification
  [genericOpen : IsOpenImmersion openMap.left]
  dense : DenseRange openMap.left
  genericMap : compactification.left ⟶ scheme
  genericSquare : IsPullback genericMap compactification.hom structureMap base.generic
  baseMap : ∀ i, base.scheme ⟶ (m i).integral.model.base.scheme
  baseGeneric : ∀ i, base.generic ≫ baseMap i = (m i).integral.model.base.generic
  sourceMap : ∀ i, scheme ⟶ (m i).integral.model.scheme
  overBase : ∀ i, sourceMap i ≫ (m i).integral.model.structureMap = structureMap ≫ baseMap i
  sourceGeneric : ∀ i, openMap.left ≫ genericMap ≫ sourceMap i =
    (m i).integral.model.openMap.left ≫ (m i).integral.model.genericMap
  sourceDense : ∀ i, DenseRange (m i).integral.model.openMap.left

variable {m} (C : CommonModel m)

def CommonModel.line (i : Fin t) : C.scheme.Modules :=
  (Scheme.Modules.pullback (C.sourceMap i)).obj (m i).integral.model.line

/-- Arithmetic metrics use the native full-model pullback and every original norm. -/
structure ArithmeticData where
  characteristic : CharZero K
  [groundProper : IsProper (integerMap C.scheme)]
  [groundFiniteType : LocallyOfFiniteType (integerMap C.scheme)]
  pureDimension : ∀ T : Set C.scheme, T ∈ irreducibleComponents C.scheme → topologicalKrullDim T = t
  hermitian : ∀ i, HermitianLine (m i).integral.model.line
  normalized : ∀ i, IsModelMetric (m i).integral.model (hermitian i) (m i).integral.metric
  pullback : ∀ i, HermitianPullback (C.sourceMap i) (hermitian i)
  intersection : ArithmeticSources C.scheme t (C.line) (fun i ↦ (pullback i).hermitian)

def arithmeticModelValue (D : ArithmeticData C) : ℝ :=
  arithmeticValue D.intersection / ∏ i : Fin t, ((m i).denominator : ℝ)

/-- Geometric model degrees retain the actual ground map and generic scalar embedding. -/
structure GeometricData (k : Type) [Field k] (embedding : k →+* K) where
  groundMap : C.scheme ⟶ Spec (.of k)
  generic : C.genericMap ≫ groundMap = C.compactification.hom ≫ Spec.map (CommRingCat.ofHom embedding)
  degree : DegreeData (Over.mk groundMap) t (C.line)

def geometricModelValue {k : Type} [Field k] {embedding : k →+* K}
    (D : GeometricData C k embedding) : ℝ :=
  rationalMixedDegree D.degree (fun i ↦ (m i).denominator)

def ModelData (G : GroundBase (K := K)) : Type 1 :=
  match G with
  | .integers => ArithmeticData C
  | @GroundBase.geometric _ _ k inst embedding =>
    letI := inst
    GeometricData C k embedding

def modelValue (G : GroundBase (K := K)) (D : ModelData C G) : ℝ :=
  match G, D with
  | .integers, D => arithmeticModelValue C D
  | @GroundBase.geometric _ _ k inst embedding, D =>
    letI := inst
    geometricModelValue C D

variable (G : GroundBase (K := K)) (M : Fin t → LineObject (A := A) (X := X) G)

/-- Every stage uses the SAME original adelic classes and actual global model intersection. -/
structure Sources where
  sequence : ∀ i, ModelSequence (L := (M i).line) (M i).boundary
  sameClass : ∀ i, (sequence i).class = (M i).metric.val
  common : ∀ n, CommonModel (fun i ↦ (sequence i).model n)
  intersection : ∀ n, ModelData (common n) G

variable {G M} (S : Sources G M)

def modelIntersection (n : ℕ) : ℝ := modelValue (S.common n) G (S.intersection n)
def intersection : ℝ := limUnder atTop (modelIntersection S)

structure Convergence : Prop where
  converges : Tendsto (modelIntersection S) atTop (nhds (intersection S))

end MathlibExt.AlgebraicGeometry.NumericalAdelicIntersections
