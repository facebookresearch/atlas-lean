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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureIndicatorIntegration
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureOperatorCommutation
public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureOperatorLaws
public import MathlibExt.MeasureTheory.Function.ContinuousIndicatorApproximation
public import Mathlib.Algebra.Star.StarProjection

/-!
# Projection and intersection laws of normal CFC set operators

For a normal operator `T` on a complete complex Hilbert space, let `P_s` be its coefficient
operator on the spectrum `K`. For measurable `s,t`, the regular measures satisfy `μ_(P_t
g,h)(s)=μ_(g,h)(s∩t)`.

Consequently `P_s P_t=P_(s∩t)`. Each set operator is an orthogonal projection, with the zero
projection on nonmeasurable sets. Continuous functions also satisfy `μ_(f(T)g,h)(t)=∫ 1_t f
dμ_(g,h)`; these are identities for the coefficient operators and measures defined by CFC.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace Topology
open MathlibExt.MeasureTheory
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uX uH

private theorem existsContinuousComplexIndicator {X : Type uX}
    [TopologicalSpace X] [NormalSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [mu.WeaklyRegular] [IsFiniteMeasure mu]
    (s : Set X) (hs : MeasurableSet s) :
    ∃ F : ℕ → C(X, ℂ), (∀ n x, ‖F n x‖ ≤ 1) ∧
      ∀ᵐ x ∂mu, Tendsto (fun n => F n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℂ)) x)) := by
  obtain ⟨f, hf, _, hlim⟩ := exists_continuous_indicator_l2_ae mu s hs
  let F : ℕ → C(X, ℂ) := fun n =>
    ⟨fun x => (f n x : ℂ), Complex.continuous_ofReal.comp (f n).continuous⟩
  refine ⟨F, ?_, ?_⟩
  · intro n x
    change ‖(f n x : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_of_nonneg (hf n x).1]
    exact (hf n x).2
  · filter_upwards [hlim] with x hx
    change Tendsto (fun n => (f n x : ℂ)) atTop (𝓝 (s.indicator (fun _ => (1 : ℂ)) x))
    have hcast : Tendsto (fun n => Complex.ofReal (f n x)) atTop
        (𝓝 (Complex.ofReal (s.indicator (fun _ => (1 : ℝ)) x))) :=
      (Complex.continuous_ofReal.tendsto (s.indicator (fun _ => (1 : ℝ)) x)).comp hx
    by_cases hxs : x ∈ s
    · simpa only [Set.indicator_of_mem hxs, Complex.ofReal_one] using hcast
    · simpa only [Set.indicator_of_notMem hxs, Complex.ofReal_zero] using hcast

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Continuous integral after a spectral set operator.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let
`P_s` be the bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for
nonmeasurable `s`. for measurable `t ⊆ K`, `q ∈ C(K,ℂ)` and `g,h ∈ H`, `∫ q dμ_(P_t
g,h)=μ_(q(T)g,h)(t)`. -/
theorem normalCFCCoefficientMeasure_operator_continuousIntegral
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H)
    (t : Set (spectrum ℂ T)) (ht : MeasurableSet t) (q : C(spectrum ℂ T, ℂ)) :
    complexIntegralDual
      (normalCFCCoefficientMeasure T hT (normalCFCCoefficientOperator T hT t g) h) q =
      (normalCFCCoefficientMeasure T hT (cfcHom hT q g) h : ComplexMeasure (spectrum ℂ T)) t := by
  have heq : normalCFCCoefficientOperator T hT t (cfcHom hT q g) =
      cfcHom hT q (normalCFCCoefficientOperator T hT t g) :=
    congrArg (fun A : H →L[ℂ] H => A g) (normalCFCCoefficientOperator_commute_cfc T hT t q).eq
  calc
    complexIntegralDual
        (normalCFCCoefficientMeasure T hT (normalCFCCoefficientOperator T hT t g) h) q =
        ⟪h, cfcHom hT q (normalCFCCoefficientOperator T hT t g)⟫_ℂ :=
      normalCFCCoefficientMeasure_represents T hT (normalCFCCoefficientOperator T hT t g) h q
    _ = ⟪h, normalCFCCoefficientOperator T hT t (cfcHom hT q g)⟫_ℂ :=
      congrArg (fun x : H => ⟪h, x⟫_ℂ) heq.symm
    _ = (normalCFCCoefficientMeasure T hT (cfcHom hT q g) h : ComplexMeasure (spectrum ℂ T)) t :=
      normalCFCCoefficientOperator_coefficient T hT t ht (cfcHom hT q g) h

/-- **Indicator integral of a continuous CFC coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let
`P_s` be the bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for
nonmeasurable `s`. for measurable `t ⊆ K`, `q ∈ C(K,ℂ)` and `g,h ∈ H`, `μ_(q(T)g,h)(t)=∫
1_t*q dμ_(g,h)`. -/
theorem normalCFCCoefficientMeasure_cfc_setIntegral
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H)
    (q : C(spectrum ℂ T, ℂ)) (t : Set (spectrum ℂ T)) (ht : MeasurableSet t) :
    (normalCFCCoefficientMeasure T hT (cfcHom hT q g) h : ComplexMeasure (spectrum ℂ T)) t =
      complexIntegral (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.indicator t ht * BoundedMeasurableFunction.ofContinuousMap q) := by
  let mu := normalCFCCoefficientMeasure T hT g h
  let nu := normalCFCCoefficientMeasure T hT (cfcHom hT q g) h
  let : IsFiniteMeasure (mu : ComplexMeasure (spectrum ℂ T)).variation :=
    ComplexMeasure.isFiniteMeasure_variation _
  let : IsFiniteMeasure (nu : ComplexMeasure (spectrum ℂ T)).variation :=
    ComplexMeasure.isFiniteMeasure_variation _
  let : (mu : ComplexMeasure (spectrum ℂ T)).variation.Regular := mu.property
  let : (nu : ComplexMeasure (spectrum ℂ T)).variation.Regular := nu.property
  let lam := (nu : ComplexMeasure (spectrum ℂ T)).variation +
    (mu : ComplexMeasure (spectrum ℂ T)).variation
  let : lam.Regular := Measure.Regular.add_of_finite _ _
  let : IsFiniteMeasure lam := inferInstance
  obtain ⟨F, hF, hlim⟩ := existsContinuousComplexIndicator lam t ht
  have hnu_le : (nu : ComplexMeasure (spectrum ℂ T)).variation ≤ lam :=
    Measure.le_add_right le_rfl
  have hmu_le : (mu : ComplexMeasure (spectrum ℂ T)).variation ≤ lam :=
    Measure.le_add_left le_rfl
  have hnu := continuousIndicator_complexIntegral_mul_tendsto
    (nu : ComplexMeasure (spectrum ℂ T)) t ht F hF (hlim.filter_mono (ae_mono hnu_le)) 1
  have hmu := continuousIndicator_complexIntegral_mul_tendsto
    (mu : ComplexMeasure (spectrum ℂ T)) t ht F hF (hlim.filter_mono (ae_mono hmu_le))
    (BoundedMeasurableFunction.ofContinuousMap q)
  simp only [mul_one, complexIntegral_indicator] at hnu
  have heq (n : ℕ) :
      complexIntegral (nu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n)) =
      complexIntegral (mu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n) *
          BoundedMeasurableFunction.ofContinuousMap q) := by
    have hprod := normalCFCCoefficientMeasure_cfc_mul_left T hT g h q (F n)
    change complexIntegralDual nu (F n) = complexIntegralDual mu (F n * q) at hprod
    rw [complexIntegralDual_apply, complexIntegralDual_apply] at hprod
    have hm : BoundedMeasurableFunction.ofContinuousMap (F n * q) =
        BoundedMeasurableFunction.ofContinuousMap (F n) *
          BoundedMeasurableFunction.ofContinuousMap q :=
      map_mul (BoundedMeasurableFunction.continuousMapStarAlgHom (X := spectrum ℂ T)) (F n) q
    rw [hm] at hprod
    exact hprod
  have hsame :
      (fun n => complexIntegral (nu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n))) =
      (fun n => complexIntegral (mu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n) *
          BoundedMeasurableFunction.ofContinuousMap q)) := funext heq
  rw [hsame] at hnu
  exact tendsto_nhds_unique hnu hmu

/-- **Restriction of a coefficient measure by a spectral operator.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. Let `μ_(g,h)` be the regular complex
measure on `K` characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable
`s ⊆ K`, let `P_s` be the bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and
set `P_s=0` for nonmeasurable `s`. for measurable `s,t ⊆ K` and `g,h ∈ H`, `μ_(P_t
g,h)(s)=μ_(g,h)(s∩t)`. -/
theorem normalCFCCoefficientMeasure_operator_inter
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s)
    (t : Set (spectrum ℂ T)) (ht : MeasurableSet t) :
    (normalCFCCoefficientMeasure T hT (normalCFCCoefficientOperator T hT t g) h :
      ComplexMeasure (spectrum ℂ T)) s =
      (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) (s ∩ t) := by
  let mu := normalCFCCoefficientMeasure T hT g h
  let nu := normalCFCCoefficientMeasure T hT (normalCFCCoefficientOperator T hT t g) h
  let : IsFiniteMeasure (mu : ComplexMeasure (spectrum ℂ T)).variation :=
    ComplexMeasure.isFiniteMeasure_variation _
  let : IsFiniteMeasure (nu : ComplexMeasure (spectrum ℂ T)).variation :=
    ComplexMeasure.isFiniteMeasure_variation _
  let : (mu : ComplexMeasure (spectrum ℂ T)).variation.Regular := mu.property
  let : (nu : ComplexMeasure (spectrum ℂ T)).variation.Regular := nu.property
  let lam := (nu : ComplexMeasure (spectrum ℂ T)).variation +
    (mu : ComplexMeasure (spectrum ℂ T)).variation
  let : lam.Regular := Measure.Regular.add_of_finite _ _
  let : IsFiniteMeasure lam := inferInstance
  obtain ⟨F, hF, hlim⟩ := existsContinuousComplexIndicator lam s hs
  have hnu_le : (nu : ComplexMeasure (spectrum ℂ T)).variation ≤ lam :=
    Measure.le_add_right le_rfl
  have hmu_le : (mu : ComplexMeasure (spectrum ℂ T)).variation ≤ lam :=
    Measure.le_add_left le_rfl
  have hnu := continuousIndicator_complexIntegral_mul_tendsto
    (nu : ComplexMeasure (spectrum ℂ T)) s hs F hF (hlim.filter_mono (ae_mono hnu_le)) 1
  have hmu := continuousIndicator_complexIntegral_mul_tendsto
    (mu : ComplexMeasure (spectrum ℂ T)) s hs F hF (hlim.filter_mono (ae_mono hmu_le))
    (BoundedMeasurableFunction.indicator t ht)
  simp only [mul_one, complexIntegral_indicator] at hnu
  rw [← BoundedMeasurableFunction.indicator_inter s t hs ht, complexIntegral_indicator] at hmu
  have heq (n : ℕ) :
      complexIntegral (nu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n)) =
      complexIntegral (mu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n) *
          BoundedMeasurableFunction.indicator t ht) := by
    have htest := normalCFCCoefficientMeasure_operator_continuousIntegral T hT g h t ht (F n)
    rw [normalCFCCoefficientMeasure_cfc_setIntegral T hT g h (F n) t ht,
      complexIntegralDual_apply] at htest
    exact htest.trans (congrArg (complexIntegral (mu : ComplexMeasure (spectrum ℂ T)))
      (mul_comm (BoundedMeasurableFunction.indicator t ht)
        (BoundedMeasurableFunction.ofContinuousMap (F n))))
  have hsame :
      (fun n => complexIntegral (nu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n))) =
      (fun n => complexIntegral (mu : ComplexMeasure (spectrum ℂ T))
        (BoundedMeasurableFunction.ofContinuousMap (F n) *
          BoundedMeasurableFunction.indicator t ht)) := funext heq
  rw [hsame] at hnu
  exact tendsto_nhds_unique hnu hmu

/-- **Intersection product of normal CFC set operators.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let
`P_s` be the bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for
nonmeasurable `s`. for measurable `s,t ⊆ K`, `normalCFCCoefficientOperator T hT s *
normalCFCCoefficientOperator T hT t=P_(s∩t)`. -/
theorem normalCFCCoefficientOperator_mul_inter
    (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (s : Set (spectrum ℂ T)) (hs : MeasurableSet s)
    (t : Set (spectrum ℂ T)) (ht : MeasurableSet t) :
    normalCFCCoefficientOperator T hT s * normalCFCCoefficientOperator T hT t =
      normalCFCCoefficientOperator T hT (s ∩ t) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  change ⟪h, normalCFCCoefficientOperator T hT s (normalCFCCoefficientOperator T hT t g)⟫_ℂ =
    ⟪h, normalCFCCoefficientOperator T hT (s ∩ t) g⟫_ℂ
  calc
    ⟪h, normalCFCCoefficientOperator T hT s (normalCFCCoefficientOperator T hT t g)⟫_ℂ =
        (normalCFCCoefficientMeasure T hT (normalCFCCoefficientOperator T hT t g) h :
          ComplexMeasure (spectrum ℂ T)) s :=
      normalCFCCoefficientOperator_coefficient T hT s hs (normalCFCCoefficientOperator T hT t g) h
    _ = (normalCFCCoefficientMeasure T hT g h : ComplexMeasure (spectrum ℂ T)) (s ∩ t) :=
      normalCFCCoefficientMeasure_operator_inter T hT g h s hs t ht
    _ = ⟪h, normalCFCCoefficientOperator T hT (s ∩ t) g⟫_ℂ :=
      (normalCFCCoefficientOperator_coefficient T hT (s ∩ t) (hs.inter ht) g h).symm

/-- **Idempotence of every normal CFC set operator.** Let `H` be a complete complex Hilbert
space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. Let `μ_(g,h)` be the regular complex measure on `K` characterized by
`∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable `s ⊆ K`, let `P_s` be the
bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and set `P_s=0` for
nonmeasurable `s`. for every set `s ⊆ K`, `P_s²=P_s`, including nonmeasurable sets
assigned zero. -/
theorem normalCFCCoefficientOperator_idempotent
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (s : Set (spectrum ℂ T)) :
    IsIdempotentElem (normalCFCCoefficientOperator T hT s) := by
  classical
  change normalCFCCoefficientOperator T hT s * normalCFCCoefficientOperator T hT s =
    normalCFCCoefficientOperator T hT s
  by_cases hs : MeasurableSet s
  · simpa only [Set.inter_self] using normalCFCCoefficientOperator_mul_inter T hT s hs s hs
  · rw [normalCFCCoefficientOperator_not_measurable T hT s hs, zero_mul]

/-- **Orthogonal projection property of normal CFC set operators.** Let `H` be a complete
complex Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put
`K=σ_ℂ(T)` with its Borel measurable structure. Let `μ_(g,h)` be the regular complex
measure on `K` characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. For measurable
`s ⊆ K`, let `P_s` be the bounded coefficient operator with `⟨h,P_s g⟩=μ_(g,h)(s)`, and
set `P_s=0` for nonmeasurable `s`. for every set `s ⊆ K`, `P_s²=P_s` and `P_s*=P_s`, so
`normalCFCCoefficientOperator T hT s` is an orthogonal projection. -/
theorem normalCFCCoefficientOperator_isStarProjection
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (s : Set (spectrum ℂ T)) :
    IsStarProjection (normalCFCCoefficientOperator T hT s) :=
  ⟨normalCFCCoefficientOperator_idempotent T hT s,
    normalCFCCoefficientOperator_isSelfAdjoint T hT s⟩

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
