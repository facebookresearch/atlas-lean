/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.GrahamImprovementReduction
import Code.FrontierA.RandomWalkHighDimensionalReduction

open Filter Finset Topology
open scoped BigOperators

namespace StatMech.FrontierA


def scalarFourthCumulant (fourthMoment variance : ℝ) : ℝ :=
  fourthMoment - 3 * variance ^ 2



noncomputable def renormalizedFourPointCoupling
    (fourthMoment variance normalization : ℝ) : ℝ :=
  -scalarFourthCumulant fourthMoment variance / normalization



theorem renormalizedFourPointCoupling_tendsto_zero
    (fourthMoment variance normalization : ℕ → ℝ)
    (normalizationLimit : ℝ)
    (hfourthCumulant : Tendsto
      (fun n => scalarFourthCumulant (fourthMoment n) (variance n))
      atTop (nhds 0))
    (hnormalization : Tendsto normalization atTop (nhds normalizationLimit))
    (hnormalizationLimit : normalizationLimit ≠ 0) :
    Tendsto
      (fun n => renormalizedFourPointCoupling
        (fourthMoment n) (variance n) (normalization n))
      atTop (nhds 0) := by
  have hneg : Tendsto
      (fun n => -scalarFourthCumulant (fourthMoment n) (variance n))
      atTop (nhds (-0)) := hfourthCumulant.neg
  have hdiv := hneg.div hnormalization hnormalizationLimit
  simpa [renormalizedFourPointCoupling] using hdiv


def scalarGaussianCumulant (variance : ℝ) (order : ℕ) : ℝ :=
  if order = 2 then variance else 0


def HasScalarMomentCumulantRecurrence
    (moments cumulants : ℕ → ℕ → ℝ) : Prop :=
  (∀ scale, moments scale 0 = 1) ∧
  ∀ scale order,
    moments scale (order + 1) =
      ∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * cumulants scale (k + 1) *
          moments scale (order - k)



structure ScalarWickMoments (variance : ℝ) (moments : ℕ → ℝ) : Prop where
  moment_zero : moments 0 = 1
  moment_one : moments 1 = 0
  recursion : ∀ n,
    moments (n + 2) = (n + 1 : ℝ) * variance * moments n


theorem scalarMomentCumulantRecurrence_limit
    (moments cumulants : ℕ → ℕ → ℝ)
    (limitMoments : ℕ → ℝ) (variance : ℝ)
    (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
    (hmoments : ∀ order, Tendsto (fun scale => moments scale order)
      atTop (nhds (limitMoments order)))
    (hcumulants : ∀ order, Tendsto (fun scale => cumulants scale order)
      atTop (nhds (scalarGaussianCumulant variance order))) :
    ∀ order,
      limitMoments (order + 1) =
        ∑ k ∈ Finset.range (order + 1),
          (order.choose k : ℝ) * scalarGaussianCumulant variance (k + 1) *
            limitMoments (order - k) := by
  intro order
  have hsum : Tendsto
      (fun scale => ∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * cumulants scale (k + 1) *
          moments scale (order - k)) atTop
      (nhds (∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * scalarGaussianCumulant variance (k + 1) *
          limitMoments (order - k))) := by
    apply tendsto_finsetSum
    intro k hk
    exact (tendsto_const_nhds.mul (hcumulants (k + 1))).mul
      (hmoments (order - k))
  have hleft := hmoments (order + 1)
  have heq : (fun scale => moments scale (order + 1)) =
      fun scale => ∑ k ∈ Finset.range (order + 1),
        (order.choose k : ℝ) * cumulants scale (k + 1) *
          moments scale (order - k) := by
    funext scale
    exact hrecurrence.2 scale order
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hsum



theorem scalarWickMoments_of_cumulant_limits
    (moments cumulants : ℕ → ℕ → ℝ)
    (limitMoments : ℕ → ℝ) (variance : ℝ)
    (hrecurrence : HasScalarMomentCumulantRecurrence moments cumulants)
    (hmoments : ∀ order, Tendsto (fun scale => moments scale order)
      atTop (nhds (limitMoments order)))
    (hcumulants : ∀ order, Tendsto (fun scale => cumulants scale order)
      atTop (nhds (scalarGaussianCumulant variance order))) :
    ScalarWickMoments variance limitMoments := by
  have hlimit := scalarMomentCumulantRecurrence_limit moments cumulants
    limitMoments variance hrecurrence hmoments hcumulants
  constructor
  · have hone : Tendsto (fun _scale : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hm0 : Tendsto (fun scale => moments scale 0) atTop (nhds 1) := by
      simpa only [hrecurrence.1] using hone
    exact tendsto_nhds_unique (hmoments 0) hm0
  · have h := hlimit 0
    simpa [scalarGaussianCumulant] using h
  · intro n
    have h := hlimit (n + 1)
    rw [Finset.sum_eq_single 1] at h
    · simpa [scalarGaussianCumulant] using h
    · intro b hb hbne
      have hb2 : b + 1 ≠ 2 := by omega
      simp [scalarGaussianCumulant, hb2]
    · simp


theorem ScalarWickMoments.odd_eq_zero
    {variance : ℝ} {moments : ℕ → ℝ}
    (hwick : ScalarWickMoments variance moments) :
    ∀ n, moments (2 * n + 1) = 0 := by
  intro n
  induction n with
  | zero => simpa using hwick.moment_one
  | succ n ih =>
      have h := hwick.recursion (2 * n + 1)
      rw [ih, mul_zero] at h
      have hindex : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [hindex]
      exact h


theorem ScalarWickMoments.fourth_eq_three_mul_sq
    {variance : ℝ} {moments : ℕ → ℝ}
    (hwick : ScalarWickMoments variance moments) :
    moments 4 = 3 * variance ^ 2 := by
  have htwo := hwick.recursion 0
  have hfour := hwick.recursion 2
  rw [hwick.moment_zero] at htwo
  norm_num at htwo hfour
  rw [htwo] at hfour
  nlinarith

end StatMech.FrontierA
