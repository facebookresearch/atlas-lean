/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicChernLimits
public import MathlibExt.AlgebraicGeometry.FiniteFlatDeligneNormModels
public import MathlibExt.AlgebraicGeometry.OpenDeligneSymbolSources
public import Lean.Elab.Tactic.Omega

/-!
# Actual metric Deligne symbols, divisor recursion and model completion

The target sheaf is the SAME GlobalBoundedDeterminantModels.DeligneLine.
Source models retain proper flat relative scheme maps, actual generic
Cartesian squares, dense generic opens, the original rational powers and
their common base maps. The target model line is the actual model Deligne
line of the literal restricted source tuple, with all affine/cochain
transitions, and its denominator is the product of the source denominators.

Rational symbols retain real local sections, regular numerator/denominator
Cartier zero schemes, tensor-twisted Koszul maps and every signed zero/pole
flag. The symbol atlas covers the actual target scheme by source frames.
Its local generators are fixed by actual canonical regular Koszul torsions
and the source-normalized cubical tensor quotient extension. Open base
change reuses the SAME original subset cochains and native source mates.
Thus norm constants are fixed by source symbols and the
finite determinant norm, rather than only by the Chern current.

For every completed target point, the fibre is the native scheme pullback
over its actual completed residue field. Fibre metrics preserve every
original section evaluation and scalar. The divisor-integral recursion uses
the SAME lower Chern product on a genuine dense common flat locus of the
Cartier flags, with actual convergence and log integrability. Source p120
distinguishes normal-base extension from a nonflat special-fibre metric.
The final adelic norm is the genuine native model Cauchy limit of these
pairing models. No final pairing, height or measure oracle is an input.

Source: Yuan--Zhang, arXiv:2105.13587v9, Theorem 4.1.3, Sections 4.2--4.3,
pp109--110, pp119--120; Proposition 4.1.1. Provider construction and proof
availability are recorded separately in direct Wanted requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MetricDelignePairingModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite Filter MeasureTheory
open _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels RationalAdelicModelMetrics AdelicSemipositiveClosures
open AdelicPicardVectors GlobalBoundedDeterminantModels RelativeDeterminantPairings
open GenericSectionMaps DeligneSymbolModels AdelicChernLimits
open DeligneCubicalModels OpenDeligneSymbolSources
open scoped Topology CompactlySupported
attribute [local instance] HasDerivedCategory.standard

variable {K : Type} [Field K] {A : AdelicField K} (G : GroundBase (K := K))
  {X Y Z : Over (Spec (.of K))}

/-- Pullback objects contain the existing actual pullback maps and completed norm rule. -/
structure PullbackObject (f : Z ⟶ X) (M : LineObject (A := A) (X := X) G) where
  boundary : BoundaryMetricCompletionModels.EffectiveBoundary A Z
  fibre : AdelicCompletionOperations.AllPlacePullback (A := A) (L := M.line) f
  result : AdelicCompletionOperations.PullbackResult (B := M.boundary) f boundary M.metric fibre
  isLine : CoherentCurveLinearSeries.IsLineBundle ((Scheme.Modules.pullback f.left).obj M.line)
  integrable : IsIntegrable G boundary result.metric

variable {G} in
def PullbackObject.asObject {f : Z ⟶ X} {M : LineObject (A := A) (X := X) G}
    (P : PullbackObject G f M) : LineObject (A := A) (X := Z) G :=
  ⟨(Scheme.Modules.pullback f.left).obj M.line, P.isLine, P.boundary, P.result.metric, P.integrable⟩

/-- The actual completed residue field of this exact analytic target point. -/
abbrev FibreField (v : A.places) (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v)) :=
  ValuedLineFibres.CompletedResidue (A.completion v) (placeScheme A Y v) p

def fibrePointMap (v : A.places) (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v)) :
    Spec (.of (FibreField v p)) ⟶ (placeScheme A Y v).left :=
  Spec.map (CommRingCat.ofHom (ValuedLineFibres.completionUnit _ _ p)) ≫
    (placeScheme A Y v).left.fromSpecResidueField p.schemePoint

def fibreScheme (f : Z ⟶ Y) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v)) :
    Over (Spec (.of (FibreField v p))) :=
  Over.mk (pullback.snd (AdelicChernLimits.placeMap f v).left (fibrePointMap v p))

def fibreProjection (f : Z ⟶ Y) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v)) :
    (fibreScheme f v p).left ⟶ (placeScheme A Z v).left :=
  pullback.fst (AdelicChernLimits.placeMap f v).left (fibrePointMap v p)

variable {r : ℕ} (f : Z ⟶ Y) (N : Fin r → LineObject (A := A) (X := Z) G)
  (v : A.places) (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v))

def fibreLine (i : Fin r) : (fibreScheme f v p).left.Modules :=
  (Scheme.Modules.pullback (fibreProjection f v p)).obj (placeLine A Z (N i).line v)

/-- Original points are computed from the actual residue-field comorphism. -/
structure FibreMetricSources where
  scalarNorm : ∀ (q : ValuedLineFibres.Point (FibreField v p) (fibreScheme f v p)) (a : A.completion v),
    q.absoluteValue ((fibreProjection f v p).residueFieldMap q.schemePoint
      (BerkovichAnalytification.scalarMap (A.completion v) (placeScheme A Z v)
        (fibreProjection f v p q.schemePoint) a)) = ‖a‖
  metric : ∀ i, ValuedLineFibres.MetrizedLine (FibreField v p) (fibreScheme f v p) (fibreLine G f N v p i)
  normalized : ∀ i (U : (placeScheme A Z v).left.Opens)
    (s : Γ(placeLine A Z (N i).line v,U))
    (q : ValuedLineFibres.Point (FibreField v p) (fibreScheme f v p))
    (hq : q.schemePoint ∈ fibreProjection f v p ⁻¹ᵁ U),
    ((metric i).fibreNorm q).norm
      (ValuedLineFibres.evaluateSection _ _ _
        (localPullbackSection (fibreProjection f v p) (placeLine A Z (N i).line v) U
          (fibreProjection f v p ⁻¹ᵁ U) (by rfl) s) q hq) =
      AdelicCompletionEvaluations.fibreNorm (N i).boundary (N i).metric.val v
        (show ValuedLineFibres.Point (A.completion v) (placeScheme A Z v) from
          ⟨fibreProjection f v p q.schemePoint,
            BerkovichAnalytification.pullAbsoluteValue q.absoluteValue
              ((fibreProjection f v p).residueFieldMap q.schemePoint).hom,
            scalarNorm q⟩)
        (ValuedLineFibres.evaluateSection _ _ _ s
          (show ValuedLineFibres.Point (A.completion v) (placeScheme A Z v) from
            ⟨fibreProjection f v p q.schemePoint,
              BerkovichAnalytification.pullAbsoluteValue q.absoluteValue
                ((fibreProjection f v p).residueFieldMap q.schemePoint).hom,
              scalarNorm q⟩) hq)

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

variable {G f N v p}

def rationalSectionNorm {m : ℕ} {N : Fin (m+1) → LineObject (A := A) (X := Z) G}
    {f : Z ⟶ Y} {v : A.places}
    {p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v)}
    (T : FibreMetricSources G f N v p) (s : RationalSection (N 0).line)
    (q : ValuedLineFibres.Point (FibreField v p) (fibreScheme f v p))
    (hq : q.schemePoint ∈ fibreProjection f v p ⁻¹ᵁ (placeProjection A Z v ⁻¹ᵁ s.domain)) : ℝ :=
  ((T.metric 0).fibreNorm q).norm
    (ValuedLineFibres.evaluateSection _ _ _
      (localPullbackSection (fibreProjection f v p) (placeLine A Z (N 0).line v)
        (placeProjection A Z v ⁻¹ᵁ s.domain)
        (fibreProjection f v p ⁻¹ᵁ (placeProjection A Z v ⁻¹ᵁ s.domain)) (by rfl)
        (RationalAdelicModelMetrics.placeSection s.domain s.value v)) q hq)

/-- Actual lower Chern products, including the empty product on the finite fibre. -/
structure LogIntegralSources {m : ℕ} (N : Fin (m+1) → LineObject (A := A) (X := Z) G)
    (f : Z ⟶ Y) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v))
    (s : RationalSection (N 0).line) where
  fibres : FibreMetricSources G f N v p
  chern : LocalSources (Y := fibreScheme f v p) (fun i : Fin m ↦ fibres.metric i.succ)
  measures : chern.MeasureParts
  logNorm : ValuedLineFibres.Point (FibreField v p) (fibreScheme f v p) → ℝ
  sectionNormalized : ∀ q
    (hq : q.schemePoint ∈ fibreProjection f v p ⁻¹ᵁ (placeProjection A Z v ⁻¹ᵁ s.domain)),
    logNorm q = Real.log (rationalSectionNorm fibres s q hq)
  supportedPositive : ∀ᵐ q ∂chern.positive measures,
    q.schemePoint ∈ fibreProjection f v p ⁻¹ᵁ (placeProjection A Z v ⁻¹ᵁ s.domain)
  supportedNegative : ∀ᵐ q ∂chern.negative measures,
    q.schemePoint ∈ fibreProjection f v p ⁻¹ᵁ (placeProjection A Z v ⁻¹ᵁ s.domain)
  nonzeroPositive : ∀ᵐ q ∂chern.positive measures, ∃ hq :
    q.schemePoint ∈ fibreProjection f v p ⁻¹ᵁ (placeProjection A Z v ⁻¹ᵁ s.domain),
    0 < rationalSectionNorm fibres s q hq
  nonzeroNegative : ∀ᵐ q ∂chern.negative measures, ∃ hq :
    q.schemePoint ∈ fibreProjection f v p ⁻¹ᵁ (placeProjection A Z v ⁻¹ᵁ s.domain),
    0 < rationalSectionNorm fibres s q hq
  integrablePositive : Integrable logNorm (chern.positive measures)
  integrableNegative : Integrable logNorm (chern.negative measures)

def logIntegral {m : ℕ} {N : Fin (m+1) → LineObject (A := A) (X := Z) G}
    {f : Z ⟶ Y} {v : A.places}
    {p : ValuedLineFibres.Point (A.completion v) (placeScheme A Y v)}
    {s : RationalSection (N 0).line} (S : LogIntegralSources N f v p s) : ℝ :=
  (∫ q, S.logNorm q ∂S.chern.positive S.measures) -
    (∫ q, S.logNorm q ∂S.chern.negative S.measures)

def remainingIndex (n : ℕ) (j : Fin (n+1)) (i : Fin (n-j.val+1)) : Fin (n+1) :=
  ⟨j.val+i.val, by omega⟩

def branchSign {j : ℕ} (b : Fin j → Bool) : ℝ :=
  (-1) ^ ((Finset.univ.filter (fun i ↦ b i = true)).card)

def chosenZero {T : Scheme.{0}} {L : T.Modules} {s : RationalSection L}
    (F : CartierFraction L s) (negative : Bool) : Scheme.{0} :=
  match negative with
  | false => F.positive.scheme
  | true => F.negative.scheme

def chosenInclusion {T : Scheme.{0}} {L : T.Modules} {s : RationalSection L}
    (F : CartierFraction L s) (negative : Bool) : chosenZero F negative ⟶ T :=
  match negative with
  | false => F.positive.inclusion
  | true => F.negative.inclusion

variable (G) (f : X ⟶ Y) (n : ℕ) (M : Fin (n+1) → LineObject (A := A) (X := X) G)
  (I : DeterminantSources)
  (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y.left), Presentations f.left (fun i ↦ (M i).line) R a)
  (D : DeligneLine I f.left n (fun i ↦ (M i).line) P)

def openBase (U : Y.left.Opens) : Over (Spec (.of K)) := Over.mk (U.ι ≫ Y.hom)
def openBaseMap (U : Y.left.Opens) : openBase U ⟶ Y := Over.homMk U.ι rfl

theorem openPoint_mem (U : Y.left.Opens) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A (openBase U) v)) :
    placeProjection A Y v
      (MetrizedLineOperationModels.mapPoint _ _ (AdelicChernLimits.placeMap (openBaseMap U) v) p).schemePoint ∈ U := by
  change ((AdelicChernLimits.placeMap (openBaseMap U) v).left ≫ placeProjection A Y v) p.schemePoint ∈ U
  rw [AdelicChernLimits.placeMap_projection]
  change (placeProjection A (openBase U) v p.schemePoint : U).val ∈ U
  exact (placeProjection A (openBase U) v p.schemePoint : U).property

/-- The exact line restriction map is the native composed pullback, with
the actual factorization through the original source open. -/
def rootRestrictionIso {Z₀ : Scheme.{0}} (U : Y.left.Opens) (N : X.left.Modules)
    (g : Z₀ ⟶ X.left) (r : Z₀ ⟶ (f.left ⁻¹ᵁ U).toScheme)
    (h : r ≫ (f.left ⁻¹ᵁ U).ι = g) :
    (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback (f.left ⁻¹ᵁ U).ι).obj N) ≅
      (Scheme.Modules.pullback g).obj N :=
  (Scheme.Modules.pullbackComp r (f.left ⁻¹ᵁ U).ι).app N ≪≫
    eqToIso (congrArg (fun q ↦ (Scheme.Modules.pullback q).obj N) h)

set_option maxHeartbeats 1200000 in
/-- A source atlas of actual rational symbols and all signed Cartier flags. -/
structure SymbolAtlas where
  index : Type
  domain : index → Y.left.Opens
  cover : ∀ y : Y.left, ∃ a, y ∈ domain a
  openSources : ∀ a : index,
    OpenDeligneSymbolSources.OpenSources f.left (fun i ↦ (M i).line) (domain a)
  rootRational : ∀ (a : index) (i : Fin (n+1)),
    RationalSection (openLines f.left (fun i ↦ (M i).line) (domain a) i)
  rootFractions : ∀ a : index,
    FractionRegularTuple (FiniteCoverLocalComparison.restrictedMap f.left (domain a)) n
      (openLines f.left (fun i ↦ (M i).line) (domain a)) (rootRational a)
  cubical : ∀ a : index,
    CubicalSources I (FiniteCoverLocalComparison.restrictedMap f.left (domain a)) n
  sourceBasis : ∀ (a : index) (R : CommRingCat.{0}) (r : Spec R ⟶ (domain a).toScheme),
    Module.Basis Unit R (localPairing (OpenDeligneSymbolSources.presentations (openSources a) P R r))
  canonicalExpression : ∀ a : index,
    RationalExpression I (FiniteCoverLocalComparison.restrictedMap f.left (domain a)) n (cubical a)
      (openLines f.left (fun i ↦ (M i).line) (domain a)) (rootRational a)
      (OpenDeligneSymbolSources.presentations (openSources a) P) (sourceBasis a)
  flag : ∀ (a : index) (j : Fin (n+1)), (Fin j.val → Bool) → Over (Spec (.of K))
  flagMap : ∀ a j b, flag a j b ⟶ X
  rootLift : ∀ a j b, (flag a j b).left ⟶ (f.left ⁻¹ᵁ domain a).toScheme
  rootLiftMap : ∀ a j b, rootLift a j b ≫ (f.left ⁻¹ᵁ domain a).ι = (flagMap a j b).left
  baseMap : ∀ a j b, flag a j b ⟶ openBase (domain a)
  factor : ∀ a j b, flagMap a j b ≫ f = baseMap a j b ≫ openBaseMap (domain a)
  first : ∀ a b, flag a 0 b ≅ pullback f (openBaseMap (domain a))
  firstMap : ∀ a b, (first a b).hom ≫ pullback.fst f (openBaseMap (domain a)) = flagMap a 0 b
  pullback : ∀ a j b i, PullbackObject G (flagMap a j b) (M i)
  rational : ∀ a j b, RationalSection ((pullback a j b j).asObject.line)
  rationalDomain : ∀ a j b,
    (rational a j b).domain ≤ rootLift a j b ⁻¹ᵁ (rootRational a j).domain
  rationalSource : ∀ a j b, (rational a j b).value =
    (rootRestrictionIso f (domain a) (M j).line (flagMap a j b).left (rootLift a j b)
      (rootLiftMap a j b)).hom.app (rational a j b).domain
        (localPullbackSection (rootLift a j b)
          (openLines f.left (fun i ↦ (M i).line) (domain a) j)
          (rootRational a j).domain (rational a j b).domain (rationalDomain a j b)
          (rootRational a j).value)
  fraction : ∀ a j b, CartierFraction ((pullback a j b j).asObject.line) (rational a j b)
  next : ∀ a (j : Fin n) (b : Fin j.val → Bool) (negative : Bool),
    chosenZero (fraction a j.castSucc b) negative ≅ (flag a j.succ (Fin.snoc b negative)).left
  nextMap : ∀ a (j : Fin n) (b : Fin j.val → Bool) (negative : Bool),
    (next a j b negative).hom ≫ (flagMap a j.succ (Fin.snoc b negative)).left =
      chosenInclusion (fraction a j.castSucc b) negative ≫ (flagMap a j.castSucc b).left
  finiteTor : ∀ a j b, FiniteTorDimension (baseMap a j b).left
  pureDimension : ∀ a j b, IsPureRelativeDimension (baseMap a j b).left (n-j.val)
  finiteLast : ∀ a b, IsFinite (baseMap a (Fin.last n) b).left
  sectionValue : ∀ a, Γ(D.line,domain a)
  frame : ∀ a (y : Y.left) (hy : y ∈ domain a),
    Module.Basis Unit (Y.left.presheaf.stalk y)
      (↑(TopCat.Presheaf.stalk D.line.val.presheaf y : AddCommGrpCat.{0}))
  frameSource : ∀ a y hy, frame a y hy () =
    TopCat.Presheaf.germ D.line.val.presheaf (domain a) y hy (sectionValue a)
  positiveKoszul : ∀ a j b (R : CommRingCat.{0}) (r : Spec R ⟶ Y.left),
    KoszulAffineSource ((flagMap a j b).left ≫ f.left)
      (fraction a j b).positiveLine (fraction a j b).numerator R r
  negativeKoszul : ∀ a j b (R : CommRingCat.{0}) (r : Spec R ⟶ Y.left),
    KoszulAffineSource ((flagMap a j b).left ≫ f.left)
      (fraction a j b).negativeLine (fraction a j b).denominator R r
  twistedKoszul : ∀ a j b (R : CommRingCat.{0}) (r : Spec R ⟶ Y.left)
    (t : Finset (Fin (n+1))),
    TwistedKoszulAffineSource ((flagMap a j b).left ≫ f.left)
      (subsetTensor (fun i ↦ (pullback a j b i).asObject.line) t)
      (fraction a j b).negativeLine (fraction a j b).denominator R r
  affineNormalized : ∀ a (R : CommRingCat.{0}) (r : Spec R ⟶ (domain a).toScheme),
    (D.affine R (r ≫ (domain a).ι)).hom.app ⊤
      (localPullbackSection (r ≫ (domain a).ι) D.line (domain a) ⊤
        (by simp) (sectionValue a)) =
      (tilde.isoTop (R := R) (localPairing (P R (r ≫ (domain a).ι)))).hom
        ((canonicalExpression a).value R r)

variable {G f n M I P D} (S : SymbolAtlas G f n M I P D)

def flagTuple (a : S.index) (j : Fin (n+1)) (b : Fin j.val → Bool) :
    Fin (n-j.val+1) → LineObject (A := A) (X := S.flag a j b) G :=
  fun i ↦ (S.pullback a j b (remainingIndex n j i)).asObject

/-- Divisor-integral recursion uses every signed zero/pole flag and the SAME lower Chern measures. -/
structure RecursionSources where
  fibralDomain : ∀ a : S.index, (S.domain a).toScheme.Opens
  fibralDense : ∀ a : S.index, Dense (fibralDomain a : Set (S.domain a).toScheme)
  fibralFlat : ∀ (a : S.index) (j : Fin (n+1)) (b : Fin j.val → Bool),
    Flat (FiniteCoverLocalComparison.restrictedMap (S.baseMap a j b).left (fibralDomain a))
  integral : ∀ (a : S.index) (j : Fin (n+1)) (b : Fin j.val → Bool)
    (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A (openBase (S.domain a)) v)),
    LogIntegralSources (flagTuple S a j b) (S.baseMap a j b) v p
      (show RationalSection ((flagTuple S a j b) 0).line from S.rational a j b)

def symbolLogNorm (R : RecursionSources S) (a : S.index) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A (openBase (S.domain a)) v)) : ℝ :=
  ∑ j : Fin (n+1), ∑ b : Fin j.val → Bool, branchSign b * logIntegral (R.integral a j b v p)

/-- A common relative model retains actual maps to every original source model. -/
structure RelativeModelStage
    (S : SymbolAtlas G f n M I P D)
    (models : ∀ i, RationalAdelicModelMetrics.ModelMetric (A := A) (X := X) (L := (M i).line))
    (target : RationalAdelicModelMetrics.ModelMetric (A := A) (X := Y) (L := D.line)) where
  scheme : Scheme.{0}
  map : scheme ⟶ target.integral.model.scheme
  [proper : IsProper map]
  [flat : Flat map]
  pureDimension : IsPureRelativeDimension map n
  sourceIntegral : IsIntegral scheme
  compactification : Over (Spec (.of K))
  [genericProper : IsProper compactification.hom]
  openMap : X ⟶ compactification
  [genericOpen : IsOpenImmersion openMap.left]
  commonDense : DenseRange openMap.left
  compactGeneric : compactification.left ⟶ scheme
  compactSquare : IsPullback compactGeneric compactification.hom
    (map ≫ target.integral.model.structureMap) target.integral.model.base.generic
  genericMap : X.left ⟶ scheme
  genericSource : openMap.left ≫ compactGeneric = genericMap
  genericCartesian : IsPullback genericMap f.left map
    (target.integral.model.openMap.left ≫ target.integral.model.genericMap)
  targetDense : DenseRange target.integral.model.openMap.left
  sourceDense : ∀ i, DenseRange (models i).integral.model.openMap.left
  sourceMap : ∀ i, scheme ⟶ (models i).integral.model.scheme
  sourceGeneric : ∀ i, genericMap ≫ sourceMap i =
    (models i).integral.model.openMap.left ≫ (models i).integral.model.genericMap
  baseMap : ∀ i, target.integral.model.base.scheme ⟶ (models i).integral.model.base.scheme
  baseGeneric : ∀ i, target.integral.model.base.generic ≫ baseMap i = (models i).integral.model.base.generic
  overBase : ∀ i, sourceMap i ≫ (models i).integral.model.structureMap =
    map ≫ target.integral.model.structureMap ≫ baseMap i
  determinant : DeterminantSources
  presentations : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ target.integral.model.scheme),
    Presentations map (fun i ↦ (Scheme.Modules.pullback (sourceMap i)).obj (models i).integral.model.line) R a
  deligne : DeligneLine determinant map n
    (fun i ↦ (Scheme.Modules.pullback (sourceMap i)).obj (models i).integral.model.line) presentations
  sameLine : deligne.line = target.integral.model.line
  denominator : (target.denominator : ℕ) = ∏ i : Fin (n+1), (models i).denominator

/-- A metric result lies on the SAME native Deligne sheaf and the SAME Cauchy quotient. -/
structure MetricResult (R : RecursionSources S) where
  boundary : BoundaryMetricCompletionModels.EffectiveBoundary A Y
  metric : AdelicMetric (L := D.line) boundary
  integrable : IsIntegrable G boundary metric
  sequence : ModelSequence (L := D.line) boundary
  sameClass : sequence.class = metric.val
  sourceSequence : ∀ i, ModelSequence (L := (M i).line) (M i).boundary
  sourceClass : ∀ i, (sourceSequence i).class = (M i).metric.val
  models : ∀ k, RelativeModelStage S (fun i ↦ (sourceSequence i).model k) (sequence.model k)
  divisorRecursion : ∀ (a : S.index) (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A (openBase (S.domain a)) v))
    (hfibral : placeProjection A (openBase (S.domain a)) v p.schemePoint ∈ R.fibralDomain a),
    Real.log (AdelicCompletionEvaluations.fibreNorm boundary metric.val v
      (MetrizedLineOperationModels.mapPoint _ _ (AdelicChernLimits.placeMap (openBaseMap (S.domain a)) v) p)
      (ValuedLineFibres.evaluateSection _ _ _
        (RationalAdelicModelMetrics.placeSection (S.domain a) (S.sectionValue a) v)
        (MetrizedLineOperationModels.mapPoint _ _ (AdelicChernLimits.placeMap (openBaseMap (S.domain a)) v) p)
        (openPoint_mem (S.domain a) v p))) = symbolLogNorm S R a v p
  modelConvergence : ∀ v p z,
    Tendsto (fun k ↦ PlacewiseMetrizedLineModels.norm (sequence.model k).metric v p z)
      atTop (nhds (AdelicCompletionEvaluations.fibreNorm boundary metric.val v p z))

variable {S} in
def MetricResult.asObject {R : RecursionSources S} (T : MetricResult S R) :
    LineObject (A := A) (X := Y) G := ⟨D.line, D.isLine, T.boundary, T.metric, T.integrable⟩

end MathlibExt.AlgebraicGeometry.MetricDelignePairingModels
