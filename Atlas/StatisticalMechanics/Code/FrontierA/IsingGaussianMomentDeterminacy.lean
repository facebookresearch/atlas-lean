/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianTrivialityReduction
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Probability.Moments.ComplexMGF











open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open ProbabilityTheory



theorem probabilityMeasure_eq_of_complexMoments_of_localExp
    (mu nu : Measure Real) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : (0 : Real) ∈ interior (integrableExpSet id mu))
    (hnu : (0 : Real) ∈ interior (integrableExpSet id nu))
    (hmoments : ∀ n : Nat,
      (∫ x, (x : Complex) ^ n ∂mu) = ∫ x, (x : Complex) ^ n ∂nu) :
    mu = nu := by
  let U : Set Complex :=
    {z | z.re ∈ interior (integrableExpSet id mu) ∧
      z.re ∈ interior (integrableExpSet id nu)}
  have hUopen : IsOpen U := by
    exact (isOpen_interior.inter isOpen_interior).preimage Complex.continuous_re
  have hzero : (0 : Complex) ∈ U := by
    exact ⟨hmu, hnu⟩
  have hmuAnalytic : AnalyticOnNhd Complex (complexMGF id mu) U := by
    apply analyticOnNhd_complexMGF.mono
    intro z hz
    exact hz.1
  have hnuAnalytic : AnalyticOnNhd Complex (complexMGF id nu) U := by
    apply analyticOnNhd_complexMGF.mono
    intro z hz
    exact hz.2
  have hmuConvex : Convex Real (interior (integrableExpSet id mu)) :=
    convex_integrableExpSet.interior
  have hnuConvex : Convex Real (interior (integrableExpSet id nu)) :=
    convex_integrableExpSet.interior
  have hUconvex : Convex Real U := by
    simpa only [U, Set.mem_setOf_eq, Set.preimage_inter] using
      (hmuConvex.inter hnuConvex).linear_preimage Complex.reLm
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUopen 0 hzero
  have hmuDiff : DifferentiableOn Complex (complexMGF id mu)
      (Metric.ball 0 r) := by
    apply differentiableOn_complexMGF.mono
    intro z hz
    exact (hball hz).1
  have hnuDiff : DifferentiableOn Complex (complexMGF id nu)
      (Metric.ball 0 r) := by
    apply differentiableOn_complexMGF.mono
    intro z hz
    exact (hball hz).2
  have hderiv (n : Nat) :
      iteratedDeriv n (complexMGF id mu) 0 =
        iteratedDeriv n (complexMGF id nu) 0 := by
    rw [iteratedDeriv_complexMGF hmu n,
      iteratedDeriv_complexMGF hnu n]
    simpa using hmoments n
  have hlocal : ∀ z ∈ Metric.ball (0 : Complex) r,
      complexMGF id mu z = complexMGF id nu z := by
    intro z hz
    have hmuSeries := Complex.taylorSeries_eq_on_ball'
      (c := (0 : Complex)) (r := r) hz hmuDiff
    have hnuSeries := Complex.taylorSeries_eq_on_ball'
      (c := (0 : Complex)) (r := r) hz hnuDiff
    rw [← hmuSeries, ← hnuSeries]
    apply tsum_congr
    intro n
    rw [hderiv n]
  have heventually :
      complexMGF id mu =ᶠ[nhds (0 : Complex)] complexMGF id nu := by
    filter_upwards [Metric.ball_mem_nhds (0 : Complex) hr] with z hz
    exact hlocal z hz
  have heqOn : Set.EqOn (complexMGF id mu) (complexMGF id nu) U :=
    hmuAnalytic.eqOn_of_preconnected_of_eventuallyEq hnuAnalytic
      hUconvex.isPreconnected hzero heventually
  apply Measure.ext_of_charFun
  funext t
  have hmem : ((t : Complex) * Complex.I) ∈ U := by
    change ((t : Complex) * Complex.I).re ∈
        interior (integrableExpSet id mu) ∧
      ((t : Complex) * Complex.I).re ∈
        interior (integrableExpSet id nu)
    simpa using And.intro hmu hnu
  have hcomplex := heqOn hmem
  simpa only [complexMGF_id_mul_I] using hcomplex


theorem probabilityMeasure_eq_of_realMoments_of_localExp
    (mu nu : Measure Real) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : (0 : Real) ∈ interior (integrableExpSet id mu))
    (hnu : (0 : Real) ∈ interior (integrableExpSet id nu))
    (hmoments : ∀ n : Nat,
      (∫ x, x ^ n ∂mu) = ∫ x, x ^ n ∂nu) :
    mu = nu := by
  apply probabilityMeasure_eq_of_complexMoments_of_localExp mu nu hmu hnu
  intro n
  simp_rw [← Complex.ofReal_pow]
  exact_mod_cast hmoments n



theorem ScalarWickMoments.moments_eq
    {variance : Real} {moments moments' : Nat → Real}
    (h : ScalarWickMoments variance moments)
    (h' : ScalarWickMoments variance moments') :
    moments = moments' := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · rw [h.moment_zero, h'.moment_zero]
      · rcases n with _ | n
        · rw [h.moment_one, h'.moment_one]
        · calc
            moments (n + 1 + 1) = moments (n + 2) := rfl
            _ = (n + 1 : Real) * variance * moments n := h.recursion n
            _ = (n + 1 : Real) * variance * moments' n := by
              rw [ih n (by omega)]
            _ = moments' (n + 2) := (h'.recursion n).symm
            _ = moments' (n + 1 + 1) := rfl



theorem probabilityMeasure_eq_of_wickMoments_of_localExp
    (mu nu : Measure Real) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (variance : Real)
    (hmu : (0 : Real) ∈ interior (integrableExpSet id mu))
    (hnu : (0 : Real) ∈ interior (integrableExpSet id nu))
    (hmuWick : ScalarWickMoments variance
      (fun n => ∫ x, x ^ n ∂mu))
    (hnuWick : ScalarWickMoments variance
      (fun n => ∫ x, x ^ n ∂nu)) :
    mu = nu := by
  apply probabilityMeasure_eq_of_realMoments_of_localExp mu nu hmu hnu
  exact congrFun (hmuWick.moments_eq hnuWick)



theorem probabilityMeasure_eq_of_all_projection_map_eq
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (mu nu : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hprojection : ∀ t : E,
      mu.map (InnerProductSpace.toDualMap Real E t) =
        nu.map (InnerProductSpace.toDualMap Real E t)) :
    mu = nu := by
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun mu t = charFunDual mu
        (InnerProductSpace.toDualMap Real E t) :=
      charFun_eq_charFunDual_toDualMap t
    _ = charFun (mu.map (InnerProductSpace.toDualMap Real E t)) 1 :=
      charFunDual_eq_charFun_map_one (InnerProductSpace.toDualMap Real E t)
    _ = charFun (nu.map (InnerProductSpace.toDualMap Real E t)) 1 :=
      congrArg (fun rho => charFun rho 1) (hprojection t)
    _ = charFunDual nu (InnerProductSpace.toDualMap Real E t) :=
      (charFunDual_eq_charFun_map_one
        (InnerProductSpace.toDualMap Real E t)).symm
    _ = charFun nu t := (charFun_eq_charFunDual_toDualMap t).symm



theorem probabilityMeasure_eq_of_projectionMoments_of_localExp
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (mu nu : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id (mu.map (InnerProductSpace.toDualMap Real E t))))
    (hnu : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id (nu.map (InnerProductSpace.toDualMap Real E t))))
    (hmoments : ∀ (t : E) (n : Nat),
      (∫ x, (x : Complex) ^ n
        ∂(mu.map (InnerProductSpace.toDualMap Real E t))) =
      ∫ x, (x : Complex) ^ n
        ∂(nu.map (InnerProductSpace.toDualMap Real E t))) :
    mu = nu := by
  apply probabilityMeasure_eq_of_all_projection_map_eq mu nu
  intro t
  let L := InnerProductSpace.toDualMap Real E t
  letI : IsProbabilityMeasure (mu.map L) :=
    Measure.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
  letI : IsProbabilityMeasure (nu.map L) :=
    Measure.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
  exact probabilityMeasure_eq_of_complexMoments_of_localExp
    (mu.map L) (nu.map L) (hmu t) (hnu t) (hmoments t)


theorem probabilityMeasure_eq_of_projectionRealMoments_of_localExp
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (mu nu : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id (mu.map (InnerProductSpace.toDualMap Real E t))))
    (hnu : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id (nu.map (InnerProductSpace.toDualMap Real E t))))
    (hmoments : ∀ (t : E) (n : Nat),
      (∫ x, x ^ n ∂(mu.map (InnerProductSpace.toDualMap Real E t))) =
      ∫ x, x ^ n ∂(nu.map (InnerProductSpace.toDualMap Real E t))) :
    mu = nu := by
  apply probabilityMeasure_eq_of_all_projection_map_eq mu nu
  intro t
  let L := InnerProductSpace.toDualMap Real E t
  letI : IsProbabilityMeasure (mu.map L) :=
    Measure.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
  letI : IsProbabilityMeasure (nu.map L) :=
    Measure.isProbabilityMeasure_map L.continuous.measurable.aemeasurable
  exact probabilityMeasure_eq_of_realMoments_of_localExp
    (mu.map L) (nu.map L) (hmu t) (hnu t) (hmoments t)



theorem probabilityMeasure_eq_of_projectionWickMoments_of_localExp
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (mu nu : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (variance : E → Real)
    (hmu : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id (mu.map (InnerProductSpace.toDualMap Real E t))))
    (hnu : ∀ t : E, (0 : Real) ∈ interior
      (integrableExpSet id (nu.map (InnerProductSpace.toDualMap Real E t))))
    (hmuWick : ∀ t : E, ScalarWickMoments (variance t)
      (fun n => ∫ x, x ^ n
        ∂(mu.map (InnerProductSpace.toDualMap Real E t))))
    (hnuWick : ∀ t : E, ScalarWickMoments (variance t)
      (fun n => ∫ x, x ^ n
        ∂(nu.map (InnerProductSpace.toDualMap Real E t)))) :
    mu = nu := by
  apply probabilityMeasure_eq_of_projectionRealMoments_of_localExp
    mu nu hmu hnu
  intro t n
  exact congrFun ((hmuWick t).moments_eq (hnuWick t)) n

end StatMech.FrontierA
