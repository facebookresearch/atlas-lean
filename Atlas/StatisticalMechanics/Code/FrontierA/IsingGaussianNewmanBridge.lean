/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianMomentConvergence

















open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open ProbabilityTheory





theorem scalarFourthCumulant_tendsto_zero_of_renormalizedCoupling
    (fourthMoment variance normalization : Nat -> Real)
    (normalizationLimit : Real)
    (hnonzero : forall scale, normalization scale ≠ 0)
    (hcoupling : Tendsto
      (fun scale => renormalizedFourPointCoupling
        (fourthMoment scale) (variance scale) (normalization scale))
      atTop (nhds 0))
    (hnormalization : Tendsto normalization atTop
      (nhds normalizationLimit)) :
    Tendsto
      (fun scale => scalarFourthCumulant
        (fourthMoment scale) (variance scale))
      atTop (nhds 0) := by
  have hproduct := hcoupling.neg.mul hnormalization
  have hidentity :
      (fun scale =>
        -renormalizedFourPointCoupling
            (fourthMoment scale) (variance scale) (normalization scale) *
          normalization scale) =
        fun scale => scalarFourthCumulant
          (fourthMoment scale) (variance scale) := by
    funext scale
    unfold renormalizedFourPointCoupling
    field_simp [hnonzero scale]
  rw [hidentity] at hproduct
  simpa using hproduct




structure NewmanFourthCumulantControl
    (cumulants : Nat -> Nat -> Real) : Prop where
  order_zero : forall scale, cumulants scale 0 = 0
  odd_order : forall scale order, Odd order -> cumulants scale order = 0
  even_order : forall scale halfOrder, 2 <= halfOrder ->
    |cumulants scale (2 * halfOrder)| <=
      (Nat.factorial (2 * halfOrder) : Real) *
        |cumulants scale 4| *
        (1 + |cumulants scale 2|) ^ (halfOrder - 2)



theorem cumulantLimits_of_newmanFourthControl
    (cumulants : Nat -> Nat -> Real) (variance : Real)
    (hcontrol : NewmanFourthCumulantControl cumulants)
    (hvariance : Tendsto (fun scale => cumulants scale 2)
      atTop (nhds variance))
    (hfourth : Tendsto (fun scale => cumulants scale 4)
      atTop (nhds 0)) :
    forall order,
      Tendsto (fun scale => cumulants scale order) atTop
        (nhds (scalarGaussianCumulant variance order)) := by
  intro order
  by_cases horderTwo : order = 2
  · simpa [scalarGaussianCumulant, horderTwo] using hvariance
  rw [scalarGaussianCumulant, if_neg horderTwo]
  rcases Nat.even_or_odd order with heven | hodd
  · rcases heven with ⟨halfOrder, hhalfOrder⟩
    have horder : order = 2 * halfOrder := by omega
    subst order
    by_cases hhalf : 2 <= halfOrder
    · apply (tendsto_zero_iff_abs_tendsto_zero _).2
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
      · exact Filter.Eventually.of_forall fun scale =>
          by simpa [two_mul] using
            hcontrol.even_order scale halfOrder hhalf
      · have habsFourth : Tendsto
            (fun scale => |cumulants scale 4|) atTop (nhds 0) := by
          simpa using hfourth.abs
        have habsVariance : Tendsto
            (fun scale => |cumulants scale 2|) atTop
              (nhds |variance|) := hvariance.abs
        have hpower : Tendsto
            (fun scale => (1 + |cumulants scale 2|) ^ (halfOrder - 2))
            atTop (nhds ((1 + |variance|) ^ (halfOrder - 2))) :=
          (tendsto_const_nhds.add habsVariance).pow (halfOrder - 2)
        simpa using
          ((tendsto_const_nhds.mul habsFourth).mul hpower)
    · have hzero : halfOrder = 0 := by
        omega
      subst halfOrder
      simpa only [mul_zero, hcontrol.order_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real))
          atTop (nhds 0))
  · simpa only [hcontrol.odd_order _ _ hodd] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real))
        atTop (nhds 0))



theorem scalarWickMoments_of_newmanFourthControl
    (moments cumulants : Nat -> Nat -> Real)
    (limitMoments : Nat -> Real) (variance : Real)
    (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
    (hmoments : forall order, Tendsto (fun scale => moments scale order)
      atTop (nhds (limitMoments order)))
    (hcontrol : NewmanFourthCumulantControl cumulants)
    (hvariance : Tendsto (fun scale => cumulants scale 2)
      atTop (nhds variance))
    (hfourth : Tendsto (fun scale => cumulants scale 4)
      atTop (nhds 0)) :
    ScalarWickMoments variance limitMoments := by
  apply scalarWickMoments_of_cumulant_limits moments cumulants
    limitMoments variance hrecurrence hmoments
  exact cumulantLimits_of_newmanFourthControl cumulants variance
    hcontrol hvariance hfourth




theorem weakLimit_eq_of_projection_newmanFourth_uniform_exp
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    (muN : Nat -> ProbabilityMeasure E)
    (mu nu : ProbabilityMeasure E)
    (hlim : Tendsto muN atTop (nhds mu))
    (variance : E -> Real) (cumulants : Nat -> E -> Nat -> Real)
    (hrecurrence : forall t : E,
      HasScalarMomentCumulantRecurrence
        (fun scale order =>
          ∫ x, x ^ order
            ∂((muN scale : Measure E).map
              (InnerProductSpace.toDualMap Real E t)))
        (fun scale order => cumulants scale t order))
    (hcontrol : forall t : E,
      NewmanFourthCumulantControl (fun scale order =>
        cumulants scale t order))
    (hvariance : forall t : E,
      Tendsto (fun scale => cumulants scale t 2) atTop
        (nhds (variance t)))
    (hfourth : forall t : E,
      Tendsto (fun scale => cumulants scale t 4) atTop (nhds 0))
    (a C : E -> Real) (ha : forall t, 0 < a t)
    (hint : forall (t : E) (scale : Nat), Integrable
      (fun x : Real => Real.exp (a t * |x|))
      ((muN scale : Measure E).map
        (InnerProductSpace.toDualMap Real E t)))
    (hbound : forall (t : E) (scale : Nat),
      (∫ x, Real.exp (a t * |x|)
        ∂((muN scale : Measure E).map
          (InnerProductSpace.toDualMap Real E t))) <= C t)
    (hnuExp : forall t : E, (0 : Real) ∈ interior
      (integrableExpSet id
        ((nu : Measure E).map (InnerProductSpace.toDualMap Real E t))))
    (hnuWick : forall t : E, ScalarWickMoments (variance t)
      (fun order => ∫ x, x ^ order
        ∂((nu : Measure E).map (InnerProductSpace.toDualMap Real E t)))) :
    (mu : Measure E) = (nu : Measure E) := by
  refine weakLimit_eq_of_projection_cumulant_limits_uniform_exp
    muN mu nu hlim variance cumulants hrecurrence ?_ a C ha hint hbound
      hnuExp hnuWick
  intro t order
  exact cumulantLimits_of_newmanFourthControl
    (fun scale order => cumulants scale t order) (variance t)
    (hcontrol t) (hvariance t) (hfourth t) order

end StatMech.FrontierA
