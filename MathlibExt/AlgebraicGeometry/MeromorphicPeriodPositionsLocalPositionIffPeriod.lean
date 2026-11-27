/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.MeromorphicPeriodPositionMaps
public import MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels
public import MathlibExt.AlgebraicGeometry.AnalyticProObjectSites

/-!
# Local source positions and period double orbits

The positive test isomorphism transports completed coefficients to period rings.
The generic period map and its inverse relate local and period parameters.
Local Hecke positions agree with period double orbits.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1--VI.2.
No classification or Hecke-stack equivalence is a hypothesis.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings MarkedUntiltingPeriodModels
open LocalCoefficientScalarFrames AnalyticTateAdicModels AffinoidPeriodRings
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicTorsorCompletion MeromorphicPeriodPositionMaps
open MeromorphicCoefficientCompletion
open AlgebraicGroupPointRepresentations AnalyticProObjectSites
open MathlibExt.LinearAlgebra.LocalizedLattices

private theorem symm_param (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    formalParameter p E.field d U Q =
      (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm
        B.parameterUnit.val *
        (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm
          V.parameter.value := by
  have hB := B.parameter
  have h1 := congrArg
    (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm hB
  simpa only [RingEquiv.symm_apply_apply, map_mul] using h1

private theorem inv_unit (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) : IsUnit
    (((algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).comp
      (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toRingHom)
        V.parameter.value) := by
  have hsymm := symm_param p K R I A T D V d U Q B
  have hunit : IsUnit (algebraMap (FormalRing p E.field d U Q)
    (GenericRing p E.field d U Q) (formalParameter p E.field d U Q)) :=
    IsLocalization.Away.algebraMap_isUnit (formalParameter p E.field d U Q)
  have h2 := congrArg (algebraMap (FormalRing p E.field d U Q)
    (GenericRing p E.field d U Q)) hsymm
  simp only [map_mul] at h2
  rw [h2] at hunit
  change IsUnit (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)
    ((positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm V.parameter.value))
  exact isUnit_of_mul_isUnit_right hunit

private def genericPeriodInv (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value →+*
      GenericRing p E.field d U Q :=
  Localization.awayLift
    ((algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).comp
      (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toRingHom)
    V.parameter.value (inv_unit p K R I A T D V d U Q B)

private theorem genericPeriodInv_coefficients (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (a : DeRhamPlus p V.chart.refinement.untilt.affine.pair) :
    genericPeriodInv p K R I A T D V d U Q B
      (algebraMap _ (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
        V.parameter.value) a) =
      algebraMap _ (GenericRing p E.field d U Q)
        ((positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm a) :=
  IsLocalization.Away.lift_eq V.parameter.value (inv_unit p K R I A T D V d U Q B) a

private theorem inv_fwd (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    (genericPeriodInv p K R I A T D V d U Q B).comp
      (genericPeriodMap p K R I A T D V d U Q B) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (formalParameter p E.field d U Q))
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [genericPeriodMap_coefficients, genericPeriodInv_coefficients]
  simp only [RingEquiv.symm_apply_apply]

private def periodTestInv (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter ⟶
      completedTest p E.field d U Q := by
  letI := ((algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
    (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).comp
      V.scalar.map).toAlgebra
  letI := (genericScalars p E.field d U Q).toAlgebra
  exact CommAlgCat.ofHom
    { __ := genericPeriodInv p K R I A T D V d U Q B
      commutes' := fun a => by
        change genericPeriodInv p K R I A T D V d U Q B
          (algebraMap _ _ (V.scalar.map a)) = algebraMap _ _ (positiveScalars p E.field d U Q a)
        rw [genericPeriodInv_coefficients]
        have h := B.scalars a
        have h2 := congrArg
          (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm h
        simp only [RingEquiv.symm_apply_apply] at h2
        exact congrArg (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)) h2.symm }

private def testAlgEquiv (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    letI := (positiveScalars p E.field d U Q).toAlgebra
    letI := V.scalar.map.toAlgebra
    (FormalRing p E.field d U Q ≃ₐ[E.field] DeRhamPlus p V.chart.refinement.untilt.affine.pair) := by
  letI := (positiveScalars p E.field d U Q).toAlgebra
  letI := V.scalar.map.toAlgebra
  exact
    { (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary) with
      commutes' := fun a => B.scalars a }

private def testIso (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    positiveTest p E.field d U Q ≅
      PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar := by
  letI := (positiveScalars p E.field d U Q).toAlgebra
  letI := V.scalar.map.toAlgebra
  exact CommAlgCat.isoMk (testAlgEquiv p K R I A T D V d U Q B)

private theorem revSquare (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter ≫
        periodTestInv p K R I A T D V d U Q B =
      (testIso p K R I A T D V d U Q B).inv ≫ positiveTestMap p E.field d U Q := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  rw [CommAlgCat.hom_comp, CommAlgCat.hom_comp, AlgHom.comp_apply, AlgHom.comp_apply]
  change genericPeriodInv p K R I A T D V d U Q B
      (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
        (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value) a) =
    algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)
      ((positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm a)
  exact genericPeriodInv_coefficients p K R I A T D V d U Q B a

private theorem leftInv (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    periodTestMap p K R I A T D V d U Q B ≫ periodTestInv p K R I A T D V d U Q B =
      𝟙 (completedTest p E.field d U Q) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  rw [CommAlgCat.hom_comp, AlgHom.comp_apply]
  change genericPeriodInv p K R I A T D V d U Q B
      (genericPeriodMap p K R I A T D V d U Q B (a : GenericRing p E.field d U Q)) =
    (a : GenericRing p E.field d U Q)
  exact DFunLike.congr_fun (inv_fwd p K R I A T D V d U Q B) (a : GenericRing p E.field d U Q)

private theorem leftInvGroup (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (x : (groups E.field G).obj (completedTest p E.field d U Q)) :
    ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
        (((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom x) = x := by
  have hcomp := _root_.CategoryTheory.Functor.map_comp (groups E.field G)
    (periodTestMap p K R I A T D V d U Q B) (periodTestInv p K R I A T D V d U Q B)
  have hleft := leftInv p K R I A T D V d U Q B
  have h1 : ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
        (((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom x) =
      ((groups E.field G).map
        (periodTestMap p K R I A T D V d U Q B ≫ periodTestInv p K R I A T D V d U Q B)).hom x := by
    rw [hcomp]
    rfl
  rw [h1, hleft]
  have hmapid := _root_.CategoryTheory.Functor.map_id (groups E.field G) (completedTest p E.field d U Q)
  rw [hmapid]
  rfl

private theorem posTransportRev (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (a : (groups E.field G).obj
      (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)) :
    ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
        (((groups E.field G).map
          (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom a) =
      ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
        (((groups E.field G).map (testIso p K R I A T D V d U Q B).inv).hom a) := by
  have hcomp1 := _root_.CategoryTheory.Functor.map_comp (groups E.field G)
    (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)
    (periodTestInv p K R I A T D V d U Q B)
  have hcomp2 := _root_.CategoryTheory.Functor.map_comp (groups E.field G)
    (testIso p K R I A T D V d U Q B).inv (positiveTestMap p E.field d U Q)
  have hsq := revSquare p K R I A T D V d U Q B
  have hlhs : ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
        (((groups E.field G).map
          (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom a) =
      ((groups E.field G).map
        (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter ≫
          periodTestInv p K R I A T D V d U Q B)).hom a := by
    rw [hcomp1]
    rfl
  have hrhs : ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
        (((groups E.field G).map (testIso p K R I A T D V d U Q B).inv).hom a) =
      ((groups E.field G).map
        ((testIso p K R I A T D V d U Q B).inv ≫ positiveTestMap p E.field d U Q)).hom a := by
    rw [hcomp2]
    rfl
  rw [hlhs, hrhs, hsq]

private theorem revUnit (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    localParameterUnit p E.field d U Q =
      (Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
        ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
          B.parameterUnit)) *
        (Units.map (genericPeriodInv p K R I A T D V d U Q B).toMonoidHom
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) := by
  apply Units.ext
  rw [Units.val_mul, Units.coe_map, Units.coe_map, Units.coe_map]
  have hlt : ((localParameterUnit p E.field d U Q).val =
    algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)
      (formalParameter p E.field d U Q)) := IsUnit.unit_spec _
  have hpt : ((MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar
    V.parameter).val =
    algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
      (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)
      V.parameter.value) := IsUnit.unit_spec _
  rw [hlt, hpt]
  change algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)
      (formalParameter p E.field d U Q) =
    algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)
      ((positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm B.parameterUnit.val) *
      genericPeriodInv p K R I A T D V d U Q B
        (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
          (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)
          V.parameter.value)
  rw [genericPeriodInv_coefficients]
  have hsymm := symm_param p K R I A T D V d U Q B
  have h2 := congrArg (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)) hsymm
  simp only [map_mul] at h2
  exact h2

private theorem midTransportRev (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (μ : Cocharacter E.field G) :
    ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
        ((μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) =
      ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
          ((((μ.app (positiveTest p E.field d U Q)).hom
            ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
              B.parameterUnit)))⁻¹) *
        (μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q) := by
  have hnat1 : ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
        ((μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) =
      (μ.app (completedTest p E.field d U Q)).hom
        ((Units.map (genericPeriodInv p K R I A T D V d U Q B).toMonoidHom)
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) := by
    have h := (ConcreteCategory.congr_hom
      (μ.naturality (periodTestInv p K R I A T D V d U Q B))
      (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)).symm
    exact h
  have hrev := revUnit p K R I A T D V d U Q B
  have hgp : (Units.map (genericPeriodInv p K R I A T D V d U Q B).toMonoidHom
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) =
      ((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
        ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
          B.parameterUnit)))⁻¹ *
        localParameterUnit p E.field d U Q := by
    have hw : (Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
        ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
          B.parameterUnit))⁻¹ *
        ((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
          ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
            B.parameterUnit)) *
          (Units.map (genericPeriodInv p K R I A T D V d U Q B).toMonoidHom
            (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter))) =
        (Units.map (genericPeriodInv p K R I A T D V d U Q B).toMonoidHom
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) := by
      rw [←mul_assoc, inv_mul_cancel, one_mul]
    have h := congrArg (fun u : (GenericRing p E.field d U Q)ˣ =>
      ((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
        ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
          B.parameterUnit)))⁻¹ * u) hrev
    rw [hw] at h
    exact h.symm
  have h1 := congrArg (μ.app (completedTest p E.field d U Q)).hom hgp
  have h2 : (μ.app (completedTest p E.field d U Q)).hom
        (((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
          ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
            B.parameterUnit)))⁻¹ *
          localParameterUnit p E.field d U Q) =
      (μ.app (completedTest p E.field d U Q)).hom
        (((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
          ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
            B.parameterUnit)))⁻¹) *
        (μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q) :=
    map_mul _ _ _
  have hnat2 : ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
        ((μ.app (positiveTest p E.field d U Q)).hom
          ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
            B.parameterUnit)) =
      (μ.app (completedTest p E.field d U Q)).hom
        ((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
          ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
            B.parameterUnit))) := by
    have h := (ConcreteCategory.congr_hom
      (μ.naturality (positiveTestMap p E.field d U Q))
      ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
        B.parameterUnit)).symm
    exact h
  calc ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
          ((μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
            (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter))
      = (μ.app (completedTest p E.field d U Q)).hom
          ((Units.map (genericPeriodInv p K R I A T D V d U Q B).toMonoidHom)
            (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) := hnat1
    _ = (μ.app (completedTest p E.field d U Q)).hom
          (((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
            ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
              B.parameterUnit)))⁻¹ *
            localParameterUnit p E.field d U Q) := h1
    _ = (μ.app (completedTest p E.field d U Q)).hom
            (((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
              ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                B.parameterUnit)))⁻¹) *
          (μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q) := h2
    _ = (((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
            (((μ.app (positiveTest p E.field d U Q)).hom
              ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                B.parameterUnit)))⁻¹) *
          (μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q) := by
          have h_a : (μ.app (completedTest p E.field d U Q)).hom
              (((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
                ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                  B.parameterUnit)))⁻¹) =
              (((μ.app (completedTest p E.field d U Q)).hom
                ((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
                  ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                    B.parameterUnit))))⁻¹) :=
            map_inv _ _
          have h_b : (((μ.app (completedTest p E.field d U Q)).hom
                ((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
                  ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                    B.parameterUnit))))⁻¹) =
              ((((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
                (((μ.app (positiveTest p E.field d U Q)).hom
                  ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                    B.parameterUnit))))⁻¹) :=
            congrArg Inv.inv hnat2.symm
          have h3 : (μ.app (completedTest p E.field d U Q)).hom
              (((Units.map (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)).toMonoidHom
                ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                  B.parameterUnit)))⁻¹) =
              ((((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
                (((μ.app (positiveTest p E.field d U Q)).hom
                  ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                    B.parameterUnit))))⁻¹) :=
            h_a.trans h_b
          exact congrArg (· * (μ.app (completedTest p E.field d U Q)).hom
            (localParameterUnit p E.field d U Q)) h3
    _ = ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom
            ((((μ.app (positiveTest p E.field d U Q)).hom
              ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
                B.parameterUnit)))⁻¹) *
          (μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q) := by
          rw [map_inv]

private theorem revImp (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (H : ∀ W : ESpace p E.field, GroupDescent p E.field G W)
    (P : PullbackPreservation p E.field G H)
    (Aq : Algebraization p E.field G H Q.space)
    (Bq : FpqcPreservesTorsors E.field G (completionBaseMap p E.field d U Q))
    (F : SourceFrames p E.field G H P d U Q Aq)
    (h : IsUnit (sectionMap p E.field Q.puncture.map Q.parameter))
    (C : MeromorphicTorsorCompletion.CompletionComparison p E.field G H P d U Q Aq Bq F h)
    (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (μ : Cocharacter E.field G)
    (hper : HasPeriodPosition p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ) :
    HasLocalPosition p E.field G H P d U Q Aq Bq F h C M left right μ := by
  obtain ⟨a', b', hab⟩ := hper
  have hg0 : framedElement p E.field G H P d U Q Aq Bq F h C M left right =
      ((groups E.field G).map (periodTestInv p K R I A T D V d U Q B)).hom
        (periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right) := by
    have hleft := leftInvGroup p K R I A T D V d U Q B G
      (framedElement p E.field G H P d U Q Aq Bq F h C M left right)
    have hQ : periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right =
        ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
          (framedElement p E.field G H P d U Q Aq Bq F h C M left right) := rfl
    rw [←hQ] at hleft
    exact hleft.symm
  rw [hab] at hg0
  simp only [map_mul, PeriodGroupPositionModels.positiveMap] at hg0
  have hposA := posTransportRev p K R I A T D V d U Q B G a'
  have hposB := posTransportRev p K R I A T D V d U Q B G b'
  have hmid := midTransportRev p K R I A T D V d U Q B G μ
  rw [hposA, hposB, hmid] at hg0
  let A0 : (groups E.field G).obj (positiveTest p E.field d U Q) :=
    ((groups E.field G).map (testIso p K R I A T D V d U Q B).inv).hom a'
  let U0 : (groups E.field G).obj (positiveTest p E.field d U Q) :=
    (μ.app (positiveTest p E.field d U Q)).hom
      ((Units.map (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary).symm.toMonoidHom)
        B.parameterUnit)
  let B0 : (groups E.field G).obj (positiveTest p E.field d U Q) :=
    ((groups E.field G).map (testIso p K R I A T D V d U Q B).inv).hom b'
  refine ⟨A0 * U0⁻¹, B0, ?_⟩
  have hmap : ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom (A0 * U0⁻¹) =
      ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom A0 *
        ((groups E.field G).map (positiveTestMap p E.field d U Q)).hom (U0⁻¹) :=
    map_mul _ _ _
  have hassoc := mul_assoc
    (((groups E.field G).map (positiveTestMap p E.field d U Q)).hom A0)
    (((groups E.field G).map (positiveTestMap p E.field d U Q)).hom (U0⁻¹))
    ((μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q))
  rw [←hassoc, ←hmap] at hg0
  exact hg0

private theorem fwdSquare (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    positiveTestMap p E.field d U Q ≫ periodTestMap p K R I A T D V d U Q B =
      (testIso p K R I A T D V d U Q B).hom ≫
        PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  rw [CommAlgCat.hom_comp, CommAlgCat.hom_comp, AlgHom.comp_apply, AlgHom.comp_apply]
  change genericPeriodMap p K R I A T D V d U Q B
      (algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q) a) =
    algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
      (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)
      (positivePeriod p K R I A T D V d U Q B.toCompletionDictionary a)
  exact genericPeriodMap_coefficients p K R I A T D V d U Q B a


private theorem posTransport (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (a : (groups E.field G).obj (positiveTest p E.field d U Q)) :
    ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
        (((groups E.field G).map (positiveTestMap p E.field d U Q)).hom a) =
      ((groups E.field G).map
        (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        (((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom a) := by
  have hcomp1 := _root_.CategoryTheory.Functor.map_comp (groups E.field G)
    (positiveTestMap p E.field d U Q) (periodTestMap p K R I A T D V d U Q B)
  have hcomp2 := _root_.CategoryTheory.Functor.map_comp (groups E.field G)
    (testIso p K R I A T D V d U Q B).hom
    (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)
  have hsq := fwdSquare p K R I A T D V d U Q B
  have hlhs : ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
        (((groups E.field G).map (positiveTestMap p E.field d U Q)).hom a) =
      ((groups E.field G).map
        (positiveTestMap p E.field d U Q ≫ periodTestMap p K R I A T D V d U Q B)).hom a := by
    rw [hcomp1]
    rfl
  have hrhs : ((groups E.field G).map
        (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        (((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom a) =
      ((groups E.field G).map
        ((testIso p K R I A T D V d U Q B).hom ≫
          PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom a := by
    rw [hcomp2]
    rfl
  rw [hlhs, hrhs, hsq]

private theorem fwdUnit (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q) :
    (Units.map (genericPeriodMap p K R I A T D V d U Q B).toMonoidHom)
        (localParameterUnit p E.field d U Q) =
      (Units.map (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
        (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).toMonoidHom
        B.parameterUnit) *
        MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter := by
  apply Units.ext
  rw [Units.val_mul, Units.coe_map, Units.coe_map]
  have hlt : ((localParameterUnit p E.field d U Q).val =
    algebraMap (FormalRing p E.field d U Q) (GenericRing p E.field d U Q)
      (formalParameter p E.field d U Q)) := IsUnit.unit_spec _
  have hpt : ((MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar
    V.parameter).val =
    algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
      (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)
      V.parameter.value) := IsUnit.unit_spec _
  rw [hlt, hpt]
  have hmap := genericPeriodMap_coefficients p K R I A T D V d U Q B
    (formalParameter p E.field d U Q)
  rw [B.parameter, map_mul] at hmap
  exact hmap

private theorem midTransportFwd (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (μ : Cocharacter E.field G) :
    ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
        ((μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q)) =
      ((groups E.field G).map
        (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        ((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
          B.parameterUnit) *
        (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter) := by
  have hnat1 : ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
        ((μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q)) =
      (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        ((Units.map (genericPeriodMap p K R I A T D V d U Q B).toMonoidHom)
          (localParameterUnit p E.field d U Q)) := by
    have h := (ConcreteCategory.congr_hom
      (μ.naturality (periodTestMap p K R I A T D V d U Q B))
      (localParameterUnit p E.field d U Q)).symm
    exact h
  have hfw := fwdUnit p K R I A T D V d U Q B
  have h1 := congrArg
    (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
    hfw
  have h2 : (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        (((Units.map (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
          (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).toMonoidHom
          B.parameterUnit)) *
          MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter) =
      (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        ((Units.map (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
          (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).toMonoidHom
          B.parameterUnit)) *
        (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter) :=
    map_mul _ _ _
  have hnat2 : ((groups E.field G).map
        (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        ((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
          B.parameterUnit) =
      (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        ((Units.map (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
          (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).toMonoidHom
          B.parameterUnit)) := by
    have h := (ConcreteCategory.congr_hom
      (μ.naturality (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter))
      B.parameterUnit).symm
    exact h
  calc ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
          ((μ.app (completedTest p E.field d U Q)).hom (localParameterUnit p E.field d U Q))
      = (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          ((Units.map (genericPeriodMap p K R I A T D V d U Q B).toMonoidHom)
            (localParameterUnit p E.field d U Q)) := hnat1
    _ = (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (((Units.map (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
            (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).toMonoidHom
            B.parameterUnit)) *
            MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter) := h1
    _ = (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          ((Units.map (algebraMap (DeRhamPlus p V.chart.refinement.untilt.affine.pair)
            (FractionRing (DeRhamPlus p V.chart.refinement.untilt.affine.pair) V.parameter.value)).toMonoidHom
            B.parameterUnit)) *
          (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
            (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter) := h2
    _ = ((groups E.field G).map
          (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          ((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
            B.parameterUnit) *
          (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
            (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter) := by
          rw [hnat2]

private theorem fwdImp (p : ℕ) [Fact p.Prime] {E : MixedField p} (K : CoefficientData p E)
    (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (H : ∀ W : ESpace p E.field, GroupDescent p E.field G W)
    (P : PullbackPreservation p E.field G H)
    (Aq : Algebraization p E.field G H Q.space)
    (Bq : FpqcPreservesTorsors E.field G (completionBaseMap p E.field d U Q))
    (F : SourceFrames p E.field G H P d U Q Aq)
    (h : IsUnit (sectionMap p E.field Q.puncture.map Q.parameter))
    (C : MeromorphicTorsorCompletion.CompletionComparison p E.field G H P d U Q Aq Bq F h)
    (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    (μ : Cocharacter E.field G)
    (hloc : HasLocalPosition p E.field G H P d U Q Aq Bq F h C M left right μ) :
    HasPeriodPosition p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ := by
  obtain ⟨a, b, hab⟩ := hloc
  have hQ : periodElement p K R I A T D V d U Q B G H P Aq Bq F h C M left right =
      ((groups E.field G).map (periodTestMap p K R I A T D V d U Q B)).hom
        (framedElement p E.field G H P d U Q Aq Bq F h C M left right) := rfl
  rw [hab] at hQ
  simp only [map_mul] at hQ
  have hposA := posTransport p K R I A T D V d U Q B G a
  have hposB := posTransport p K R I A T D V d U Q B G b
  have hmid := midTransportFwd p K R I A T D V d U Q B G μ
  rw [hposA, hposB, hmid] at hQ
  refine ⟨(((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom a) *
      ((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
        B.parameterUnit),
    ((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom b, ?_⟩
  have hmap : (((groups E.field G).map
      (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
      ((((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom a) *
        (((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
          B.parameterUnit)))) =
      (((groups E.field G).map
        (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        (((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom a)) *
        (((groups E.field G).map
          (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
            B.parameterUnit))) :=
    map_mul _ _ _
  have hassoc : ((((groups E.field G).map
      (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
        (((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom a)) *
        (((groups E.field G).map
          (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
            B.parameterUnit))) *
          (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
            (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)) =
      ((((groups E.field G).map
        (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
          (((groups E.field G).map (testIso p K R I A T D V d U Q B).hom).hom a)) *
          ((((groups E.field G).map
            (PeriodGroupPositionModels.localizationTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
              (((μ.app (PeriodGroupPositionModels.positiveTest p K V.chart.refinement.untilt V.scalar)).hom
                B.parameterUnit)) *
            (μ.app (PeriodGroupPositionModels.genericTest p K V.chart.refinement.untilt V.scalar V.parameter)).hom
              (MarkedUntiltingPeriodModels.parameterUnit p K V.chart.refinement.untilt V.scalar V.parameter)))) := by
    rw [mul_assoc]
  rw [←hassoc, ←hmap] at hQ
  exact hQ

/-- Exact source position agrees with the actual period double orbit, retaining its unit. -/
public theorem localPosition_iff_period (p : ℕ) [Fact p.Prime] {E : MixedField p}
    (K : CoefficientData p E) (R : AffineRealization p) (I : IntegerPresentation p K)
    (A : RelativeFFCurveFamilies.Family p K I) {S : Base p K}
    (T : Untilting p K S) (D : UntiltingCartierModels.Divisor p K R I A T)
    (V : UntiltingCartierChartModels.PeriodChart p K R I A T D)
    {X Z : ESpace p E.field} (d : Z ⟶ X) (U : Puncture p E.field d)
    (Q : PoleChart p E.field d U)
    (B : PeriodBridge p K R I A T D V d U Q)
    (G : Over (Spec (.of E.field))) [GrpObj G]
    (H : ∀ W : ESpace p E.field, GroupDescent p E.field G W)
    (P : PullbackPreservation p E.field G H)
    (Aq : Algebraization p E.field G H Q.space)
    (Bq : FpqcPreservesTorsors E.field G (completionBaseMap p E.field d U Q))
    (F : SourceFrames p E.field G H P d U Q Aq)
    (h : IsUnit (sectionMap p E.field Q.puncture.map Q.parameter))
    (C : MeromorphicTorsorCompletion.CompletionComparison p E.field G H P d U Q Aq Bq F h)
    (M : Hecke p E.field G H P d U)
    (left : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).left)
    (right : IntegralFrame p E.field G H d U Q (originalModification p E.field G H P d U M).right)
    [ReductiveGroupSchemeModels.IsReductive (Spec (.of E.field)) G]
    (μ : Cocharacter E.field G) :
    HasLocalPosition p E.field G H P d U Q Aq Bq F h C M left right μ ↔
      HasPeriodPosition p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ := by
  constructor
  · intro hloc
    exact fwdImp p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ hloc
  · intro hper
    exact revImp p K R I A T D V d U Q B G H P Aq Bq F h C M left right μ hper

end WantedExt.AlgebraicGeometry.MeromorphicPeriodPositions
