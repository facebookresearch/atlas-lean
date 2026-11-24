/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.FunctionalAnalysis.ContinuousMapRealDualJordan
public import MathlibExt.MeasureTheory.Integral.RieszMarkovKakutani.CompactReal
public import MathlibExt.MeasureTheory.Measure.RegularSignedMeasure
public import MathlibExt.MeasureTheory.VectorMeasure.RegularVariation

/-!
# Signed real Riesz--Markov representation on compact spaces

For a compact Hausdorff Borel space, integration identifies the real bounded dual of `C(X, ℝ)`
with the real signed measures whose total variation is regular.  The inverse is constructed from
the positive and negative functionals in the Jordan decomposition of a bounded functional.  The
two representing positive measures are proved mutually singular, so their sum is the canonical
total variation and its mass is exactly the operator norm.
-/

public section

open CompactlySupportedContinuousMap Filter MeasureTheory Set TopologicalSpace
open scoped CompactlySupported ENNReal MeasureTheory NNReal

namespace MathlibExt.MeasureTheory

open MathlibExt.Analysis.FunctionalAnalysis

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private theorem cm_sub_nonneg {f g : C(X, ℝ)} (hfg : f ≤ g) : 0 ≤ g - f := by
  rw [ContinuousMap.le_def]
  intro x
  exact sub_nonneg.mpr (ContinuousMap.le_def.mp hfg x)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private theorem cm_one_nonneg : (0 : C(X, ℝ)) ≤ 1 := by
  rw [ContinuousMap.le_def]
  exact fun _ ↦ zero_le_one

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private theorem positive_apply_norm_bound (P : C(X, ℝ) →P[ℝ] ℝ) (f : C(X, ℝ)) :
    ‖P f‖ ≤ P 1 * ‖f‖ := by
  have hupperFun : f ≤ ‖f‖ • (1 : C(X, ℝ)) := by
    rw [ContinuousMap.le_def]
    exact fun x ↦ by simpa using ContinuousMap.apply_le_norm f x
  have hlowerFun : -(‖f‖ • (1 : C(X, ℝ))) ≤ f := by
    rw [ContinuousMap.le_def]
    exact fun x ↦ by simpa using ContinuousMap.neg_norm_le_apply f x
  have hupper : P f ≤ P (‖f‖ • (1 : C(X, ℝ))) := P.monotone' hupperFun
  have hlower : P (-(‖f‖ • (1 : C(X, ℝ)))) ≤ P f := P.monotone' hlowerFun
  simp only [map_smul, smul_eq_mul] at hupper
  simp only [map_neg, map_smul, smul_eq_mul] at hlower
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · simpa [mul_comm] using hlower
  · simpa [mul_comm] using hupper

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
private theorem positive_opNorm_le_apply_one (P : C(X, ℝ) →P[ℝ] ℝ) :
    ‖P.toContinuousLinearMap‖ ≤ P 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (P.map_nonneg cm_one_nonneg)
  exact positive_apply_norm_bound P

private noncomputable def positiveSub (P Q : C(X, ℝ) →P[ℝ] ℝ)
    (hQP : ∀ f : C(X, ℝ), 0 ≤ f → Q f ≤ P f) : C(X, ℝ) →P[ℝ] ℝ :=
  { toPositiveLinearMap :=
      { toLinearMap := P.toContinuousLinearMap.toLinearMap - Q.toContinuousLinearMap.toLinearMap
        monotone' := by
          intro f g hfg
          have h := hQP (g - f) (cm_sub_nonneg hfg)
          rw [map_sub, map_sub] at h
          change P f - Q f ≤ P g - Q g
          linarith }
    cont := (P.toContinuousLinearMap - Q.toContinuousLinearMap).cont }

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
@[simp]
private theorem positiveSub_apply (P Q : C(X, ℝ) →P[ℝ] ℝ)
    (hQP : ∀ f : C(X, ℝ), 0 ≤ f → Q f ≤ P f) (f : C(X, ℝ)) :
    positiveSub P Q hQP f = P f - Q f :=
  rfl

/-- The positive representing measure of the Jordan positive functional. -/
noncomputable def signedRieszPositivePart (F : StrongDual ℝ C(X, ℝ)) : Measure X :=
  continuousRieszMeasure (realDualJordan F).pos

/-- The positive representing measure of the Jordan negative functional. -/
noncomputable def signedRieszNegativePart (F : StrongDual ℝ C(X, ℝ)) : Measure X :=
  continuousRieszMeasure (realDualJordan F).neg

/-- The positive representing measure in the signed Riesz construction is regular. -/
theorem signedRieszPositivePart_regular (F : StrongDual ℝ C(X, ℝ)) :
    (signedRieszPositivePart F).Regular :=
  continuousRieszMeasure_regular (realDualJordan F).pos

/-- The negative representing measure in the signed Riesz construction is regular. -/
theorem signedRieszNegativePart_regular (F : StrongDual ℝ C(X, ℝ)) :
    (signedRieszNegativePart F).Regular :=
  continuousRieszMeasure_regular (realDualJordan F).neg

/-- The positive representing measure in the signed Riesz construction is finite. -/
theorem signedRieszPositivePart_finite (F : StrongDual ℝ C(X, ℝ)) :
    IsFiniteMeasure (signedRieszPositivePart F) :=
  continuousRieszMeasure_finite (realDualJordan F).pos

/-- The negative representing measure in the signed Riesz construction is finite. -/
theorem signedRieszNegativePart_finite (F : StrongDual ℝ C(X, ℝ)) :
    IsFiniteMeasure (signedRieszNegativePart F) :=
  continuousRieszMeasure_finite (realDualJordan F).neg

private theorem continuousRieszMeasure_mutuallySingular
    (P N : C(X, ℝ) →P[ℝ] ℝ)
    (hnorm : ‖P.toContinuousLinearMap - N.toContinuousLinearMap‖ = P 1 + N 1) :
    continuousRieszMeasure P ⟂ₘ continuousRieszMeasure N := by
  let muP : Measure X := continuousRieszMeasure P
  let muN : Measure X := continuousRieszMeasure N
  let _ : IsFiniteMeasure muP := continuousRieszMeasure_finite P
  let _ : IsFiniteMeasure muN := continuousRieszMeasure_finite N
  let _ : muP.Regular := continuousRieszMeasure_regular P
  let _ : muN.Regular := continuousRieszMeasure_regular N
  let lambda : Measure X := muP ⊓ muN
  let _ : IsFiniteMeasure lambda := isFiniteMeasure_of_le muP inf_le_left
  let _ : lambda.Regular := Measure.Regular.of_le inf_le_left
  let Q : C(X, ℝ) →P[ℝ] ℝ := continuousIntegralPositive lambda
  have hQP (f : C(X, ℝ)) (hf : 0 ≤ f) : Q f ≤ P f := by
    calc
      Q f ≤ continuousIntegralPositive muP f :=
        continuousIntegralPositive_mono_measure inf_le_left hf
      _ = P f := by
        rw [continuousIntegralPositive_apply]
        exact integral_continuousRieszMeasure P f
  have hQN (f : C(X, ℝ)) (hf : 0 ≤ f) : Q f ≤ N f := by
    calc
      Q f ≤ continuousIntegralPositive muN f :=
        continuousIntegralPositive_mono_measure inf_le_right hf
      _ = N f := by
        rw [continuousIntegralPositive_apply]
        exact integral_continuousRieszMeasure N f
  let A : C(X, ℝ) →P[ℝ] ℝ := positiveSub P Q hQP
  let B : C(X, ℝ) →P[ℝ] ℝ := positiveSub N Q hQN
  have hsub : A.toContinuousLinearMap - B.toContinuousLinearMap =
      P.toContinuousLinearMap - N.toContinuousLinearMap := by
    ext f
    change (P f - Q f) - (N f - Q f) = P f - N f
    ring
  have hupper :
      ‖P.toContinuousLinearMap - N.toContinuousLinearMap‖ ≤ A 1 + B 1 := by
    rw [← hsub]
    calc
      ‖A.toContinuousLinearMap - B.toContinuousLinearMap‖ ≤
          ‖A.toContinuousLinearMap‖ + ‖B.toContinuousLinearMap‖ := by
        rw [sub_eq_add_neg]
        exact (norm_add_le A.toContinuousLinearMap (-B.toContinuousLinearMap)).trans_eq (by
          congr 1
          exact norm_neg B.toContinuousLinearMap)
      _ ≤ A 1 + B 1 := add_le_add
        (positive_opNorm_le_apply_one A) (positive_opNorm_le_apply_one B)
  rw [hnorm] at hupper
  change P 1 + N 1 ≤ (P 1 - Q 1) + (N 1 - Q 1) at hupper
  have hQnonneg : 0 ≤ Q 1 := Q.map_nonneg cm_one_nonneg
  have hQzero : Q 1 = 0 := by linarith
  have hlambdaReal : lambda.real univ = 0 := by
    rw [← continuousIntegralPositive_apply_one lambda]
    exact hQzero
  have hlambdaUniv : lambda univ = 0 :=
    (measureReal_eq_zero_iff (by finiteness)).mp hlambdaReal
  have hlambda : lambda = 0 := Measure.measure_univ_eq_zero.mp hlambdaUniv
  rw [Measure.mutuallySingular_iff_disjoint, disjoint_iff]
  change lambda = 0
  exact hlambda

/-- The positive and negative representing measures are mutually singular. -/
theorem signedRieszParts_mutuallySingular (F : StrongDual ℝ C(X, ℝ)) :
    signedRieszPositivePart F ⟂ₘ signedRieszNegativePart F := by
  apply continuousRieszMeasure_mutuallySingular
  rw [(realDualJordan F).sub_eq, (realDualJordan F).norm_eq]

/-- The Jordan decomposition formed by the two positive Riesz measures. -/
noncomputable def signedRieszJordan (F : StrongDual ℝ C(X, ℝ)) : JordanDecomposition X where
  posPart := signedRieszPositivePart F
  negPart := signedRieszNegativePart F
  posPart_finite := signedRieszPositivePart_finite F
  negPart_finite := signedRieszNegativePart_finite F
  mutuallySingular := signedRieszParts_mutuallySingular F

/-- The regular signed measure representing a bounded functional on `C(X, ℝ)`. -/
noncomputable def signedRieszMeasure (F : StrongDual ℝ C(X, ℝ)) : RegularSignedMeasure X := by
  let _ : (signedRieszPositivePart F).Regular := signedRieszPositivePart_regular F
  let _ : (signedRieszNegativePart F).Regular := signedRieszNegativePart_regular F
  let _ : IsFiniteMeasure (signedRieszPositivePart F) := signedRieszPositivePart_finite F
  let _ : IsFiniteMeasure (signedRieszNegativePart F) := signedRieszNegativePart_finite F
  refine ⟨(signedRieszJordan F).toSignedMeasure, ?_⟩
  change (signedRieszJordan F).toSignedMeasure.totalVariation.Regular
  rw [SignedMeasure.totalVariation_eq_variation]
  change VectorMeasure.HasRegularVariation (signedRieszJordan F).toSignedMeasure
  rw [JordanDecomposition.toSignedMeasure]
  change VectorMeasure.HasRegularVariation
    ((signedRieszPositivePart F).toSignedMeasure -
      (signedRieszNegativePart F).toSignedMeasure)
  exact SignedMeasure.hasRegularVariation_toSignedMeasure_sub _ _

/-- The underlying signed Riesz measure is the difference of its constructed positive and negative parts. -/
@[simp]
theorem coe_signedRieszMeasure (F : StrongDual ℝ C(X, ℝ)) :
    ((signedRieszMeasure F : RegularSignedMeasure X) : SignedMeasure X) =
      (signedRieszJordan F).toSignedMeasure :=
  by
    unfold signedRieszMeasure
    rfl

/-- The canonical Jordan decomposition of `signedRieszMeasure F` is the pair constructed from the
positive and negative functionals of `F`. -/
theorem signedRieszMeasure_toJordanDecomposition (F : StrongDual ℝ C(X, ℝ)) :
    ((signedRieszMeasure F : RegularSignedMeasure X) : SignedMeasure X).toJordanDecomposition =
      signedRieszJordan F := by
  apply SignedMeasure.toJordanDecomposition_eq
  exact coe_signedRieszMeasure F

omit [T2Space X] in
private theorem continuousMap_integrable_toSignedMeasure (mu : Measure X) [IsFiniteMeasure mu]
    (f : C(X, ℝ)) : mu.toSignedMeasure.Integrable (fun x ↦ f x) := by
  change Integrable (fun x ↦ f x) mu.toSignedMeasure.variation
  rw [Measure.variation_toSignedMeasure]
  exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Integrating against the constructed signed measure recovers the original functional. -/
@[simp]
theorem signedIntegralDual_signedRieszMeasure (F : StrongDual ℝ C(X, ℝ)) :
    RegularSignedMeasure.signedIntegralDual (signedRieszMeasure F) = F := by
  let _ : IsFiniteMeasure (signedRieszPositivePart F) := signedRieszPositivePart_finite F
  let _ : IsFiniteMeasure (signedRieszNegativePart F) := signedRieszNegativePart_finite F
  apply ContinuousLinearMap.ext
  intro f
  rw [RegularSignedMeasure.signedIntegralDual_apply]
  rw [coe_signedRieszMeasure]
  change (∫ᵛ x, f x ∂<•((signedRieszPositivePart F).toSignedMeasure -
    (signedRieszNegativePart F).toSignedMeasure)) = F f
  rw [VectorMeasure.integral_sub_vectorMeasure
      (continuousMap_integrable_toSignedMeasure (signedRieszPositivePart F) f)
      (continuousMap_integrable_toSignedMeasure (signedRieszNegativePart F) f),
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure,
    signedRieszPositivePart, signedRieszNegativePart,
    integral_continuousRieszMeasure, integral_continuousRieszMeasure]
  have happ := congrArg (fun L : StrongDual ℝ C(X, ℝ) ↦ L f) (realDualJordan F).sub_eq
  change ((realDualJordan F).pos.toContinuousLinearMap -
    (realDualJordan F).neg.toContinuousLinearMap) f = F f
  exact happ

private theorem signedIntegralDual_apply_jordan (s : RegularSignedMeasure X) (f : C(X, ℝ)) :
    RegularSignedMeasure.signedIntegralDual s f =
      ∫ x, f x ∂((s : SignedMeasure X).toJordanDecomposition.posPart) -
        ∫ x, f x ∂((s : SignedMeasure X).toJordanDecomposition.negPart) := by
  let sp := (s : SignedMeasure X).toJordanDecomposition.posPart
  let sn := (s : SignedMeasure X).toJordanDecomposition.negPart
  have hsp : IsFiniteMeasure sp := inferInstance
  have hsn : IsFiniteMeasure sn := inferInstance
  let _ : IsFiniteMeasure sp := hsp
  let _ : IsFiniteMeasure sn := hsn
  change RegularSignedMeasure.signedIntegralDual s f =
    (∫ x, f x ∂sp) - ∫ x, f x ∂sn
  have hs : (s : SignedMeasure X) = sp.toSignedMeasure - sn.toSignedMeasure := by
    calc
      (s : SignedMeasure X) =
          (s : SignedMeasure X).toJordanDecomposition.toSignedMeasure :=
        (SignedMeasure.toSignedMeasure_toJordanDecomposition _).symm
      _ = sp.toSignedMeasure - sn.toSignedMeasure := rfl
  rw [RegularSignedMeasure.signedIntegralDual_apply, hs]
  change (∫ᵛ x, f x ∂<•(sp.toSignedMeasure - sn.toSignedMeasure)) = _
  rw [VectorMeasure.integral_sub_vectorMeasure
      (continuousMap_integrable_toSignedMeasure sp f)
      (continuousMap_integrable_toSignedMeasure sn f),
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure]

private theorem regular_crossSum_eq
    {muP muN nuP nuN : Measure X}
    [IsFiniteMeasure muP] [IsFiniteMeasure muN]
    [IsFiniteMeasure nuP] [IsFiniteMeasure nuN]
    [muP.Regular] [muN.Regular] [nuP.Regular] [nuN.Regular]
    (h : ∀ f : C(X, ℝ),
      (∫ x, f x ∂muP) - ∫ x, f x ∂muN =
        (∫ x, f x ∂nuP) - ∫ x, f x ∂nuN) :
    muP + nuN = nuP + muN := by
  let _ : (muP + nuN).Regular := Measure.Regular.add_of_finite _ _
  let _ : (nuP + muN).Regular := Measure.Regular.add_of_finite _ _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_add_measure (f.integrable (μ := muP)) (f.integrable (μ := nuN)),
    integral_add_measure (f.integrable (μ := nuP)) (f.integrable (μ := muN))]
  exact sub_eq_sub_iff_add_eq_add.mp (h f.toContinuousMap)

/-- Integration separates regular signed measures. -/
theorem signedIntegralDual_injective :
    Function.Injective
      (RegularSignedMeasure.signedIntegralDual (X := X)) := by
  intro s t hst
  let sp := (s : SignedMeasure X).toJordanDecomposition.posPart
  let sn := (s : SignedMeasure X).toJordanDecomposition.negPart
  let tp := (t : SignedMeasure X).toJordanDecomposition.posPart
  let tn := (t : SignedMeasure X).toJordanDecomposition.negPart
  have hsvar : VectorMeasure.HasRegularVariation (s : SignedMeasure X) := by
    rw [VectorMeasure.HasRegularVariation, ← SignedMeasure.totalVariation_eq_variation]
    exact RegularSignedMeasure.totalVariation_regular s
  have htvar : VectorMeasure.HasRegularVariation (t : SignedMeasure X) := by
    rw [VectorMeasure.HasRegularVariation, ← SignedMeasure.totalVariation_eq_variation]
    exact RegularSignedMeasure.totalVariation_regular t
  have hsreg := (SignedMeasure.hasRegularVariation_iff_jordanParts_regular
    (s : SignedMeasure X)).mp hsvar
  have htreg := (SignedMeasure.hasRegularVariation_iff_jordanParts_regular
    (t : SignedMeasure X)).mp htvar
  let _ : sp.Regular := hsreg.1
  let _ : sn.Regular := hsreg.2
  let _ : tp.Regular := htreg.1
  let _ : tn.Regular := htreg.2
  let _ : IsFiniteMeasure sp := inferInstance
  let _ : IsFiniteMeasure sn := inferInstance
  let _ : IsFiniteMeasure tp := inferInstance
  let _ : IsFiniteMeasure tn := inferInstance
  have hint (f : C(X, ℝ)) :
      (∫ x, f x ∂sp) - ∫ x, f x ∂sn =
        (∫ x, f x ∂tp) - ∫ x, f x ∂tn := by
    have happ := congrArg (fun L : StrongDual ℝ C(X, ℝ) ↦ L f) hst
    simpa only [signedIntegralDual_apply_jordan] using happ
  have hcross : sp + tn = tp + sn := regular_crossSum_eq hint
  have hdiff : sp.toSignedMeasure - sn.toSignedMeasure =
      tp.toSignedMeasure - tn.toSignedMeasure := by
    ext i hi
    rw [Measure.toSignedMeasure_sub_apply hi, Measure.toSignedMeasure_sub_apply hi]
    have hc := congrArg (fun mu : Measure X ↦ mu.real i) hcross
    rw [measureReal_add_apply, measureReal_add_apply] at hc
    linarith
  apply Subtype.ext
  calc
    (s : SignedMeasure X) = (s : SignedMeasure X).toJordanDecomposition.toSignedMeasure :=
      (SignedMeasure.toSignedMeasure_toJordanDecomposition _).symm
    _ = sp.toSignedMeasure - sn.toSignedMeasure := rfl
    _ = tp.toSignedMeasure - tn.toSignedMeasure := hdiff
    _ = (t : SignedMeasure X).toJordanDecomposition.toSignedMeasure := rfl
    _ = (t : SignedMeasure X) := SignedMeasure.toSignedMeasure_toJordanDecomposition _

/-- The constructed signed Riesz measure is the unique regular signed measure representing the
given functional. -/
theorem signedRieszMeasure_unique (F : StrongDual ℝ C(X, ℝ))
    (s : RegularSignedMeasure X)
    (h : RegularSignedMeasure.signedIntegralDual s = F) :
    signedRieszMeasure F = s := by
  apply signedIntegralDual_injective
  rw [signedIntegralDual_signedRieszMeasure, h]

/-- Applying the inverse construction to signed integration recovers the signed measure. -/
@[simp]
theorem signedRieszMeasure_signedIntegralDual (s : RegularSignedMeasure X) :
    signedRieszMeasure (RegularSignedMeasure.signedIntegralDual s) = s :=
  signedRieszMeasure_unique _ s rfl

/-- Integration is a real-linear equivalence from regular signed measures to the bounded real dual
of `C(X, ℝ)`. -/
noncomputable def signedIntegralEquiv :
    RegularSignedMeasure X ≃ₗ[ℝ] StrongDual ℝ C(X, ℝ) where
  toLinearMap :=
    { toFun := RegularSignedMeasure.signedIntegralDual
      map_add' := RegularSignedMeasure.signedIntegralDual_add
      map_smul' := RegularSignedMeasure.signedIntegralDual_smul }
  invFun := signedRieszMeasure
  left_inv := signedRieszMeasure_signedIntegralDual
  right_inv := signedIntegralDual_signedRieszMeasure

/-- The signed Riesz equivalence sends a regular signed measure to its integral functional. -/
@[simp]
theorem signedIntegralEquiv_apply (s : RegularSignedMeasure X) :
    signedIntegralEquiv s = RegularSignedMeasure.signedIntegralDual s :=
  by
    unfold signedIntegralEquiv
    rfl

/-- The inverse signed Riesz equivalence is the constructed representing signed measure. -/
@[simp]
theorem signedIntegralEquiv_symm_apply (F : StrongDual ℝ C(X, ℝ)) :
    (signedIntegralEquiv (X := X)).symm F = signedRieszMeasure F :=
  by
    unfold signedIntegralEquiv
    rfl

/-- The canonical total variation of the constructed signed measure has mass equal to the operator
norm of the original functional. -/
@[simp]
theorem totalVariation_signedRieszMeasure (F : StrongDual ℝ C(X, ℝ)) :
    ((signedRieszMeasure F : RegularSignedMeasure X) : SignedMeasure X).totalVariation.real univ =
      ‖F‖ := by
  let _ : IsFiniteMeasure (signedRieszPositivePart F) := signedRieszPositivePart_finite F
  let _ : IsFiniteMeasure (signedRieszNegativePart F) := signedRieszNegativePart_finite F
  rw [SignedMeasure.totalVariation, signedRieszMeasure_toJordanDecomposition]
  change (signedRieszPositivePart F + signedRieszNegativePart F).real univ = ‖F‖
  rw [measureReal_add_apply, signedRieszPositivePart, signedRieszNegativePart,
    continuousRieszMeasure_real_univ, continuousRieszMeasure_real_univ]
  exact (realDualJordan F).norm_eq.symm

/-- The operator norm of signed integration is exactly the mass of the total variation. -/
theorem norm_signedIntegralDual_eq_totalVariation (s : RegularSignedMeasure X) :
    ‖RegularSignedMeasure.signedIntegralDual s‖ =
      (s : SignedMeasure X).totalVariation.real univ := by
  have h := totalVariation_signedRieszMeasure
    (F := RegularSignedMeasure.signedIntegralDual s)
  rw [signedRieszMeasure_signedIntegralDual] at h
  exact h.symm

/-- The inverse signed Riesz construction is real-linear, including for negative scalars. -/
@[simp]
theorem signedRieszMeasure_smul (c : ℝ) (F : StrongDual ℝ C(X, ℝ)) :
    signedRieszMeasure (c • F) = c • signedRieszMeasure F := by
  simpa only [signedIntegralEquiv_symm_apply] using
    (signedIntegralEquiv (X := X)).symm.map_smul c F

end

end MathlibExt.MeasureTheory
