/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements
public import MathlibExt.AlgebraicGeometry.UntiltingCartierChartModels
public import MathlibExt.AlgebraicGeometry.PeriodGroupPositionModels

/-!
# Actual completed Hecke coefficients and period lattice positions

The local G-point is extracted from the actual completed punctured
comparison. Its matrix entries are the original finite-pole entries
under the same completion map. Formal positions and represented
lattices retain arbitrary coefficient fields and all representations.

At a marked mixed-characteristic untilt, the period bridge uses the
actual source chart model/global-ring dictionary, every finite quotient,
and the original theta-adic completion comparison. It fixes the source
E scalars and Cartier generator before localizing. Consequently period
positions and represented modules concern that same local comparison.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1--VI.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MeromorphicPeriodPositionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicTorsorCompletion MeromorphicCompletionRefinements
open MeromorphicCoefficientCompletion FramedMeromorphicGroupModels
open AlgebraicGroupPointRepresentations
open MathlibExt.LinearAlgebra.LocalizedLattices

section GeneralCoefficients

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
  (Q : PoleChart p E d U)
  (A : Algebraization p E G H Q.space)
  (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))
  (F : SourceFrames p E G H P d U Q A)
  (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
  (C : MeromorphicTorsorCompletion.CompletionComparison p E G H P d U Q A B F h)

/-- The positive group uses the actual original E-algebra on the completed chart. -/
def positiveTest : CommAlgCat.{0} E := by
  letI := (positiveScalars p E d U Q).toAlgebra
  exact CommAlgCat.of E (FormalRing p E d U Q)

/-- Original completed positive-to-generic coefficients, including every E scalar. -/
def positiveTestMap : positiveTest p E d U Q ⟶ completedTest p E d U Q := by
  letI := (positiveScalars p E d U Q).toAlgebra
  letI := (genericScalars p E d U Q).toAlgebra
  exact CommAlgCat.ofHom
    { __ := algebraMap (FormalRing p E d U Q) (GenericRing p E d U Q)
      commutes' := fun _ ↦ rfl }

/-- The unit is the original formal Cartier generator in its actual localization. -/
def localParameterUnit : (GenericRing p E d U Q)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := GenericRing p E d U Q) (formalParameter p E d U Q)).unit

/-- Relative position is the actual positive double orbit of the original cocharacter. -/
def HasLocalPosition (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (μ : Cocharacter E G) : Prop :=
  ∃ a b : (groups E G).obj (positiveTest p E d U Q),
    framedElement p E G H P d U Q A B F h C M left right =
      ((groups E G).map (positiveTestMap p E d U Q)).hom a *
        (μ.app (completedTest p E d U Q)).hom (localParameterUnit p E d U Q) *
          ((groups E G).map (positiveTestMap p E d U Q)).hom b

/-- The actual formal represented lattice module, for every original representation. -/
def representedFormalModule (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (n : ℕ) (ρ : Representation E G n) :
    Submodule (FormalRing p E d U Q)
      (Ambient (FormalRing p E d U Q) (formalParameter p E d U Q) n) :=
  (standard (FormalRing p E d U Q) (formalParameter p E d U Q) n).map
    ((Matrix.mulVecLin
      (framedMatrix p E G H P d U Q A B F h C M left right n ρ)).restrictScalars
        (FormalRing p E d U Q))

/-- A lattice realization retains that same actual matrix-image submodule. -/
structure RepresentedFormalLattice (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (n : ℕ) (ρ : Representation E G n) where
  lattice : Lattice (FormalRing p E d U Q) (formalParameter p E d U Q) n
  normalized : lattice.module =
    representedFormalModule p E G H P d U Q A B F h C M left right n ρ

end GeneralCoefficients

section MarkedUntilting

open LocalWittCoefficientFields RelativeFarguesFontaineRings MarkedUntiltingPeriodModels
open LocalCoefficientScalarFrames AnalyticTateAdicModels AffinoidPeriodRings

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
  (R : AffineRealization p) (I : IntegerPresentation p K)
  (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
  (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
  (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
  {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
  (Q : PoleChart p E.field d U)

/-- The coefficient dictionary is computed from the actual chart equality and source globalRing. -/
def chartDictionary (e : Q.space.left.obj = V.chart.curve.model.valued) :
    SectionRing p E.field Q.space ≃+* V.chart.curve.pair.ring := by
  change Q.space.left.obj.space.presheaf.obj (op ⊤) ≃+* V.chart.curve.pair.ring
  rw [e]
  exact V.chart.curve.model.globalRing.symm

/-- The source completion comparison fixes every coefficient and every finite quotient. -/
structure CompletionDictionary where
  space_same : Q.space.left.obj = V.chart.curve.model.valued
  map_same : HEq Q.map.left.hom V.chart.curve.map
  divisor_same : HEq Q.divisorMap.left.hom V.chart.untilt
  ideal : (chartIdeal p E.field d U Q).map
    (chartDictionary p K R I A T D V d U Q space_same).toRingHom =
      RingHom.ker (UntiltingCartierChartModels.theta p K R I A T D V.chart)
  powers : ∀ n : ℕ, chartIdeal p E.field d U Q ^ n ≤
    (RingHom.ker (UntiltingCartierChartModels.theta p K R I A T D V.chart) ^ n).comap
      (chartDictionary p K R I A T D V d U Q space_same).toRingHom
  equivalence : FormalRing p E.field d U Q ≃+*
    UntiltingCartierChartModels.FormalRing p K R I A T D V.chart
  coefficients : ∀ a : SectionRing p E.field Q.space,
    equivalence (completionMap p E.field d U Q a) =
      algebraMap V.chart.curve.pair.ring
        (UntiltingCartierChartModels.FormalRing p K R I A T D V.chart)
          (chartDictionary p K R I A T D V d U Q space_same a)
  finite : ∀ (n : ℕ) (a : FormalRing p E.field d U Q),
    AdicCompletion.evalₐ
      (RingHom.ker (UntiltingCartierChartModels.theta p K R I A T D V.chart)) n
        (equivalence a) =
      Ideal.quotientMap
        (RingHom.ker (UntiltingCartierChartModels.theta p K R I A T D V.chart) ^ n)
        (chartDictionary p K R I A T D V d U Q space_same).toRingHom (powers n)
          (AdicCompletion.evalₐ (chartIdeal p E.field d U Q) n a)

variable (J : CompletionDictionary p K R I A T D V d U Q)

/-- The positive period map is the actual two source completion dictionaries composed. -/
def positivePeriod : FormalRing p E.field d U Q ≃+*
    DeRhamPlus p V.chart.refinement.untilt.affine.pair :=
  J.equivalence.trans V.comparison.equivalence

/-- The source raw annular coefficients enter through that same original global-ring dictionary. -/
def originalRawCoefficient (a : RelativeFarguesFontaineRings.Ring p K V.chart.refinement.base) :
    SectionRing p E.field Q.space :=
  (chartDictionary p K R I A T D V d U Q J.space_same).symm
    (UntiltingCartierChartModels.rawCoefficient p K R I A T D V.chart a)

/-- Every original annular coefficient is mapped by the source period embedding. -/
theorem positivePeriod_rawCoefficient
    (a : RelativeFarguesFontaineRings.Ring p K V.chart.refinement.base) :
    positivePeriod p K R I A T D V d U Q J
      (completionMap p E.field d U Q
        (originalRawCoefficient p K R I A T D V d U Q J a)) =
      periodEmbedding p K V.chart.refinement.untilt V.scalar a := by
  change V.comparison.equivalence (J.equivalence _) = _
  rw [J.coefficients]
  simp only [originalRawCoefficient, RingEquiv.apply_symm_apply]
  exact V.comparison.coefficients a

set_option maxHeartbeats 1200000 in
-- These fields compare two actual completed-ring models and their finite projections.
/-- E scalars, the actual Cartier generator and every theta-adic level are fixed. -/
structure PeriodBridge extends CompletionDictionary p K R I A T D V d U Q where
  scalars : ∀ a : E.field,
    positivePeriod p K R I A T D V d U Q toCompletionDictionary
      (positiveScalars p E.field d U Q a) = V.scalar.map a
  parameterUnit : (DeRhamPlus p V.chart.refinement.untilt.affine.pair)ˣ
  parameter :
    positivePeriod p K R I A T D V d U Q toCompletionDictionary
      (formalParameter p E.field d U Q) = parameterUnit.val * V.parameter.value
  filtration : ∀ n : ℕ,
    Ideal.comap
      (positivePeriod p K R I A T D V d U Q toCompletionDictionary).toRingHom
      (AffinoidPeriodRings.filtration p V.chart.refinement.untilt.affine.pair n) =
        RingHom.ker (AdicCompletion.evalₐ (chartIdeal p E.field d U Q) n).toRingHom

variable (B : PeriodBridge p K R I A T D V d U Q)

/-- The displayed source parameter unit becomes a unit in the actual period localization. -/
theorem genericPeriodParameterUnit : IsUnit
    (((algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
      (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).comp
        (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).toRingHom)
          (formalParameter p E.field d U Q)) := by
  change IsUnit (algebraMap _ _
    (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary
      (formalParameter p E.field d U Q)))
  rw [B.parameter, map_mul]
  exact (B.parameterUnit.isUnit.map (algebraMap _ _)).mul
    (IsLocalization.Away.algebraMap_isUnit V.parameter.value)

/-- The completed generic-to-period map localizes the original parameter-normalized positive map. -/
def genericPeriodMap : GenericRing p E.field d U Q →+*
    FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value :=
  Localization.awayLift
    ((algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
      (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).comp
        (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).toRingHom)
    (formalParameter p E.field d U Q)
      (genericPeriodParameterUnit p K R I A T D V d U Q B)

/-- Every completed integral coefficient follows the original localization square. -/
theorem genericPeriodMap_coefficients (a : FormalRing p E.field d U Q) :
    genericPeriodMap p K R I A T D V d U Q B
      (algebraMap _ (GenericRing p E.field d U Q) a) =
        algebraMap _ (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
          V.parameter.value)
            (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary a) :=
  IsLocalization.Away.lift_eq (formalParameter p E.field d U Q)
    (genericPeriodParameterUnit p K R I A T D V d U Q B) a

/-- The algebra-test map preserves the actual original E scalar lift into periods. -/
def periodTestMap : completedTest p E.field d U Q ⟶
    PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter := by
  letI := (genericScalars p E.field d U Q).toAlgebra
  letI := ((algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
    (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).comp
      V.scalar.map).toAlgebra
  exact CommAlgCat.ofHom
    { __ := genericPeriodMap p K R I A T D V d U Q B
      commutes' := fun a ↦ by
        change genericPeriodMap p K R I A T D V d U Q B
          (algebraMap _ (GenericRing p E.field d U Q) (positiveScalars p E.field d U Q a)) = _
        rw [genericPeriodMap_coefficients, B.scalars]
        rfl }

variable (G : Over (Spec (.of E.field))) [GrpObj G]
  (H : ∀ W : ESpace p E.field, GroupDescent p E.field G W)
  (P : PullbackPreservation p E.field G H)
  (Aq : Algebraization p E.field G H Q.space)
  (Bq : FpqcPreservesTorsors E.field G (completionBaseMap p E.field d U Q))
  (F : SourceFrames p E.field G H P d U Q Aq)
  (h : IsUnit (sectionMap p E.field Q.puncture.map Q.parameter))
  (C : MeromorphicTorsorCompletion.CompletionComparison p E.field G H P d U Q Aq Bq F h)

/-- This is the actual global Hecke comparison mapped by the original period coefficient map. -/
def periodElement (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right) :
    PeriodGroupPositionModels.GenericGroup p K V.chart.refinement.untilt V.scalar V.parameter G :=
  ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
    (framedElement p E.field G H P d U Q Aq Bq F h C M left right)

/-- Every representation entry follows the same original finite-pole completion and period map. -/
theorem periodMatrix_entries (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (g : GroupFactorization p E.field G H P d U Q h
      (originalModification p E.field G H P d U M) left right)
    (n : ℕ) (ρ : Representation E.field G n) (i j : Fin n) :
    ((PeriodGroupPositionModels.representationMatrix p K V.chart.refinement.untilt
      V.scalar V.parameter G ρ
        (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) :
          Matrix (Fin n) (Fin n)
            (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value))
              i j) =
      genericPeriodMap p K R I A T D V d U Q B
        (completedMap p E.field d U Q
          (meromorphicMatrix p E.field G H P d U Q h
            (originalModification p E.field G H P d U M) left right g n ρ i j)) := by
  have hn := ConcreteCategory.congr_hom
    (ρ.naturality (periodTestMap p K R I A T D V d U Q B))
      (framedElement p E.field G H P d U Q Aq Bq F h C M left right)
  have he := congrArg (fun a : GL (Fin n)
    (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value) ↦
      (a : Matrix (Fin n) (Fin n)
        (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
          V.parameter.value)) i j) hn
  exact he.trans (congrArg (genericPeriodMap p K R I A T D V d U Q B)
    (framedMatrix_entries p E.field G H P d U Q Aq Bq F h C M left right g n ρ i j))

/-- Exact period position concerns that same computed comparison. -/
def HasPeriodPosition (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (μ : Cocharacter E.field G) : Prop :=
  PeriodGroupPositionModels.HasRelativePosition p K V.chart.refinement.untilt
    V.scalar V.parameter G
      (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) μ

/-- Closed bounds retain all actual representation lattices and source weight frames. -/
def IsPeriodBounded (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (μ : Cocharacter E.field G) : Prop :=
  PeriodGroupPositionModels.IsRepresentationBounded p K V.chart.refinement.untilt
    V.scalar V.parameter G
      (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) μ

/-- The period lattice module is the literal represented image of the actual local comparison. -/
def representedPeriodModule (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (n : ℕ) (ρ : Representation E.field G n) :
    Submodule (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
      (Ambient (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value n) :=
  PeriodGroupPositionModels.representedModule p K V.chart.refinement.untilt
    V.scalar V.parameter G ρ
      (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right)

/-- A local source chart retains its actual pair and full marked-untilt period bridge. -/
structure MatchedPeriodPoleChart (U : Puncture p E.field D.map) where
  chart : PoleChart p E.field D.map U
  pair_same : chart.pair = V.chart.curve.pair
  bridge : PeriodBridge p K R I A T D V D.map U chart


variable (V' : UntiltingCartierChartModels.PeriodChart p K R I A T D)
  (Q' : PoleChart p E.field d U)
  (B' : PeriodBridge p K R I A T D V' d U Q')
  (r : PoleRefinement p E.field d U Q Q')
  (Rc : CoefficientRefinement p E.field d U Q Q' r)

/-- Period refinement uses the original completed coefficient map and source dictionaries. -/
def positivePeriodRefinement :
    DeRhamPlus p V.chart.refinement.untilt.affine.pair →+*
      DeRhamPlus p V'.chart.refinement.untilt.affine.pair :=
  (positivePeriod p K R I A T D V' d U Q' B'.toCompletionDictionary).toRingHom.comp
    ((positiveMap p E.field d U Q Q' r Rc.powers Rc.finite).comp
      (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toRingHom)

/-- Every original chart coefficient follows its actual source refinement. -/
theorem positivePeriodRefinement_coefficients (a : SectionRing p E.field Q.space) :
    positivePeriodRefinement p K R I A T D V d U Q B V' Q' B' r Rc
      (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary
        (completionMap p E.field d U Q a)) =
      positivePeriod p K R I A T D V' d U Q' B'.toCompletionDictionary
        (completionMap p E.field d U Q' (sectionMap p E.field r.map a)) := by
  change positivePeriod p K R I A T D V' d U Q' B'.toCompletionDictionary
    (positiveMap p E.field d U Q Q' r Rc.powers Rc.finite
      ((positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm
        ((positivePeriod p K R I A T D V d U Q B.toCompletionDictionary)
          (completionMap p E.field d U Q a)))) = _
  rw [RingEquiv.symm_apply_apply,
    positiveMap_coefficients p E.field d U Q Q' r Rc.powers Rc.finite]

/-- Generic period refinement uses the inverse of the same characterized native source map. -/
def genericPeriodRefinement
    (hb : Function.Bijective (genericPeriodMap p K R I A T D V d U Q B)) :
    FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value →+*
      FractionRing (DeRhamPlus p V'.chart.refinement.untilt.affine.pair) V'.parameter.value :=
  (genericPeriodMap p K R I A T D V' d U Q' B').comp
    ((genericMap p E.field d U Q Q' r Rc).comp
      (RingEquiv.ofBijective (genericPeriodMap p K R I A T D V d U Q B) hb).symm.toRingHom)

/-- Every completed generic coefficient uses that same original source/period square. -/
theorem genericPeriodRefinement_coefficients
    (hb : Function.Bijective (genericPeriodMap p K R I A T D V d U Q B))
    (a : GenericRing p E.field d U Q) :
    genericPeriodRefinement p K R I A T D V d U Q B V' Q' B' r Rc hb
      (genericPeriodMap p K R I A T D V d U Q B a) =
        genericPeriodMap p K R I A T D V' d U Q' B'
          (genericMap p E.field d U Q Q' r Rc a) := by
  let e := RingEquiv.ofBijective (genericPeriodMap p K R I A T D V d U Q B) hb
  change genericPeriodMap p K R I A T D V' d U Q' B'
    (genericMap p E.field d U Q Q' r Rc (e.symm (e a))) = _
  rw [RingEquiv.symm_apply_apply]

end MarkedUntilting

end MathlibExt.AlgebraicGeometry.MeromorphicPeriodPositionMaps
