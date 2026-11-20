/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalTorusLocalObservables
import Code.FrontierA.IsingGaussianTorusCumulants











open Filter Finset MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


def criticalTorusCompactScaledField
    (A : Finset (Site d)) (a : Site d → Real) (c : Nat → Real)
    (n : Nat) (sigma : ConfigSpace (IsingDyadicTorus d n)) : Real :=
  c n * isingTorusSmearedSpin (compactTorusWeight A a n) sigma


def criticalTorusCompactScaledFieldLaw
    (A : Finset (Site d)) (a : Site d → Real) (c : Nat → Real)
    (n : Nat) : ProbabilityMeasure Real :=
  isingTorusFieldLaw d n (IsingFK.betaC (magnetization d))
    (criticalTorusCompactScaledField A a c n)

theorem isingTorusSmearedSpin_compactTorusWeight
    (A : Finset (Site d)) (a : Site d → Real) (n : Nat)
    (sigma : ConfigSpace (IsingDyadicTorus d n)) :
    isingTorusSmearedSpin (compactTorusWeight A a n) sigma =
      compactWeightedSpin A a (criticalTorusLocalRestriction A n sigma) := by
  rw [← finiteIsingWeightedSpinReal_compactTorusWeight]
  unfold isingTorusSmearedSpin finiteIsingWeightedSpinReal isingTorusSpinField
  apply Finset.sum_congr rfl
  intro x hx
  ring



theorem integral_criticalTorusCompactScaledFieldLaw
    (A : Finset (Site d)) (a : Site d → Real) (c : Nat → Real)
    (n : Nat) (g : BoundedContinuousFunction Real Real) :
    (∫ x, g x ∂(criticalTorusCompactScaledFieldLaw A a c n : Measure Real)) =
      criticalTorusLocalObservableExpectation A
        (fun sigma ↦ g (c n * compactWeightedSpin A a sigma)) n := by
  unfold criticalTorusCompactScaledFieldLaw isingTorusFieldLaw
  change (∫ x, g x ∂Measure.map
    (criticalTorusCompactScaledField A a c n)
      (isingTorusZeroFieldLaw
        (d := d) (k := n) (IsingFK.betaC (magnetization d)) : Measure _)) = _
  rw [MeasureTheory.integral_map
    (Measurable.of_discrete :
      Measurable (criticalTorusCompactScaledField A a c n)).aemeasurable
    g.continuous.aestronglyMeasurable]
  rw [integral_isingTorusZeroFieldLaw]
  unfold criticalTorusLocalObservableExpectation expJ ZJ
  have hweight (sigma : ConfigSpace (IsingDyadicTorus d n)) :
      zeroFieldInteractionWeight (isingTorusGraph d n)
          (IsingFK.betaC (magnetization d)) sigma =
        wJ (isingTorusGraph d n).edgeFinset
          (fun _ ↦ IsingFK.betaC (magnetization d)) (fun _ ↦ 0) sigma := by
    unfold zeroFieldInteractionWeight wJ
    simp only [zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  simp_rw [isingTorusZeroFieldMass_eq_finiteIsingWeight, hweight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  unfold criticalTorusCompactScaledField
  rw [isingTorusSmearedSpin_compactTorusWeight]
  ring



theorem criticalTorusCompactScaledFieldLaw_tendsto_zeroGaussian
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real)
    (c : Nat → Real) (hc : Tendsto c atTop (nhds 0)) :
    Tendsto (criticalTorusCompactScaledFieldLaw A a c) atTop
      (nhds (MeasureTheory.diracProba (0 : Real))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  rw [show (∫ x, g x ∂(MeasureTheory.diracProba (0 : Real) :
      ProbabilityMeasure Real)) = g 0 by
        change (∫ x, g x ∂Measure.dirac (0 : Real)) = _
        rw [integral_dirac]]
  have hlocal := criticalTorusLocalObservableExpectation_tendsto_varying hd A
      (fun n sigma ↦ g (c n * compactWeightedSpin A a sigma))
      (fun _ ↦ g 0)
      (fun sigma ↦ by
        have harg := hc.mul_const (compactWeightedSpin A a sigma)
        have hg := g.continuous.continuousAt.tendsto.comp harg
        simpa [Function.comp_apply] using hg)
  have hconst : criticalFreeLocalObservableExpectation A (fun _ ↦ g 0) = g 0 := by
    unfold criticalFreeLocalObservableExpectation
    rw [integral_const]
    simp
  simpa only [integral_criticalTorusCompactScaledFieldLaw, hconst] using hlocal



theorem weakLimit_eq_zeroGaussian_of_criticalTorusCompactSupport
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real)
    (c : Nat → Real) (hc : Tendsto c atTop (nhds 0))
    (mu : ProbabilityMeasure Real)
    (hlim : Tendsto (criticalTorusCompactScaledFieldLaw A a c) atTop
      (nhds mu)) :
    (mu : Measure Real) =
      (MeasureTheory.diracProba (0 : Real) : ProbabilityMeasure Real) := by
  have hzero := criticalTorusCompactScaledFieldLaw_tendsto_zeroGaussian
    hd A a c hc
  exact congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique hlim hzero)




theorem criticalFiniteBoxWeightedFourthScale_tendsto_zero
    (hd : 2 ≤ d) :
    Tendsto (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
      d n hd) atTop (nhds 0) := by
  let c : Nat → Real := fun n ↦
    PhysicalIsing.criticalFiniteBoxWeightedFourthScale d n hd
  have hpow : Tendsto (fun n ↦ c n ^ 4) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : Nat ↦ (1 : Real) / (n + 1))
    · exact Filter.Eventually.of_forall fun n ↦ pow_nonneg
        (PhysicalIsing.criticalFiniteBoxWeightedFourthScale_pos d n hd).le 4
    · apply Filter.Eventually.of_forall
      intro n
      rw [PhysicalIsing.criticalFiniteBoxWeightedFourthScale_pow_four]
      have hcard : 1 ≤ (Fintype.card (sctBox d n) : Real) := by
        exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
          0 < Fintype.card (sctBox d n))
      have hchi : 1 ≤ criticalFreeBoxSusceptibility d (2 * n) :=
        one_le_criticalFreeBoxSusceptibility hd (2 * n)
      have hrbase : (n + 1 : Real) ≤ ((2 * n + 1 : Nat) : Real) := by
        norm_cast
        omega
      have hrone : (1 : Real) ≤ ((2 * n + 1 : Nat) : Real) := by
        norm_cast
        omega
      have hrpow : ((2 * n + 1 : Nat) : Real) ≤
          ((2 * n + 1 : Nat) : Real) ^ d := by
        simpa only [pow_one] using pow_le_pow_right₀ hrone (by omega : 1 ≤ d)
      have hden : (n + 1 : Real) ≤
          2 * (Fintype.card (sctBox d n) : Real) *
            criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
              ((2 * n + 1 : Nat) : Real) ^ d := by
        calc
          (n + 1 : Real) ≤ ((2 * n + 1 : Nat) : Real) ^ d :=
            hrbase.trans hrpow
          _ ≤ 2 * (Fintype.card (sctBox d n) : Real) *
              criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
                ((2 * n + 1 : Nat) : Real) ^ d := by
            have hfactor : 1 ≤ 2 * (Fintype.card (sctBox d n) : Real) *
                criticalFreeBoxSusceptibility d (2 * n) ^ 2 := by
              nlinarith [sq_nonneg
                (criticalFreeBoxSusceptibility d (2 * n))]
            nlinarith [pow_nonneg (show (0 : Real) ≤
              ((2 * n + 1 : Nat) : Real) by positivity) d]
      exact one_div_le_one_div_of_le (by positivity) hden
    · simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : Nat ↦ (1 : Real) / (n + 1)) atTop (nhds 0))
  have hsqrt1 : Tendsto (fun n ↦ Real.sqrt (c n ^ 4)) atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hpow
  have hsq : Tendsto (fun n ↦ c n ^ 2) atTop (nhds 0) := by
    apply hsqrt1.congr'
    apply Filter.Eventually.of_forall
    intro n
    change Real.sqrt (c n ^ 4) = c n ^ 2
    rw [show c n ^ 4 = (c n ^ 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg (c n))]
  have hsqrt2 : Tendsto (fun n ↦ Real.sqrt (c n ^ 2)) atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply hsqrt2.congr'
  apply Filter.Eventually.of_forall
  intro n
  change Real.sqrt (c n ^ 2) = c n
  rw [Real.sqrt_sq_eq_abs,
    abs_of_pos (PhysicalIsing.criticalFiniteBoxWeightedFourthScale_pos d n hd)]



theorem criticalTorusCanonicalCompactScaledFieldLaw_tendsto_zeroGaussian
    (hd : 4 < d) (A : Finset (Site d)) (a : Site d → Real) :
    Tendsto
      (criticalTorusCompactScaledFieldLaw A a
        (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
          d n (by omega)))
      atTop (nhds (MeasureTheory.diracProba (0 : Real))) :=
  criticalTorusCompactScaledFieldLaw_tendsto_zeroGaussian
    (by omega) A a _ (criticalFiniteBoxWeightedFourthScale_tendsto_zero (by omega))



theorem weakLimit_eq_zeroGaussian_of_canonicalCriticalCompactSupport
    (hd : 4 < d) (A : Finset (Site d)) (a : Site d → Real)
    (mu : ProbabilityMeasure Real)
    (hlim : Tendsto
      (criticalTorusCompactScaledFieldLaw A a
        (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
          d n (by omega))) atTop (nhds mu)) :
    (mu : Measure Real) =
      (MeasureTheory.diracProba (0 : Real) : ProbabilityMeasure Real) := by
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hlim
    (criticalTorusCanonicalCompactScaledFieldLaw_tendsto_zeroGaussian hd A a))



theorem zeroGaussian_scalarWickMoments :
    ScalarWickMoments 0
      (fun order ↦ ∫ x : Real, x ^ order
        ∂(MeasureTheory.diracProba (0 : Real) : ProbabilityMeasure Real)) := by
  constructor
  · change (∫ x : Real, x ^ 0 ∂Measure.dirac 0) = 1
    rw [integral_dirac]
    norm_num
  · change (∫ x : Real, x ^ 1 ∂Measure.dirac 0) = 0
    rw [integral_dirac]
    norm_num
  · intro n
    change (∫ x : Real, x ^ (n + 2) ∂Measure.dirac 0) =
      (n + 1 : Real) * 0 * ∫ x : Real, x ^ n ∂Measure.dirac 0
    rw [integral_dirac]
    simp

end

end StatMech.FrontierA
