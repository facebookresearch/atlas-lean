/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalFreeBoxDiagonalBridge










open Filter Finset MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


def criticalTorusGrowingCanonicalField
    (hd : 2 ≤ d) (A : Nat → Finset (Site d)) (a : Nat → Site d → Real)
    (boxScale torusScale : Nat → Nat) (n : Nat)
    (sigma : ConfigSpace (IsingDyadicTorus d (torusScale n))) : Real :=
  PhysicalIsing.criticalFiniteBoxWeightedFourthScale
      d (boxScale n) hd *
    isingTorusSmearedSpin
      (compactTorusWeight (A n) (a n) (torusScale n)) sigma


def criticalTorusGrowingCanonicalFieldLaw
    (hd : 2 ≤ d) (A : Nat → Finset (Site d)) (a : Nat → Site d → Real)
    (boxScale torusScale : Nat → Nat) (n : Nat) : ProbabilityMeasure Real :=
  isingTorusFieldLaw d (torusScale n)
    (IsingFK.betaC (magnetization d))
    (criticalTorusGrowingCanonicalField hd A a boxScale torusScale n)

theorem compactTorusWeight_scale
    (A : Finset (Site d)) (a : Site d → Real) (c : Real) (n : Nat) :
    compactTorusWeight A (fun x ↦ c * a x) n =
      fun z ↦ c * compactTorusWeight A a n z := by
  funext z
  unfold compactTorusWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> ring

theorem finiteIsingWeightedRawMoment_scale_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (a : V → Real) (c : Real) (order : Nat) :
    finiteIsingWeightedRawMoment G beta (fun x ↦ c * a x) order =
      c ^ order * finiteIsingWeightedRawMoment G beta a order := by
  unfold finiteIsingWeightedRawMoment
  have hspin (sigma : ConfigSpace V) :
      finiteIsingWeightedSpinReal (fun x ↦ c * a x) sigma =
        c * finiteIsingWeightedSpinReal a sigma := by
    unfold finiteIsingWeightedSpinReal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hnum :
      (∑ sigma : ConfigSpace V,
        zeroFieldInteractionWeight G beta sigma *
          finiteIsingWeightedSpinReal (fun x ↦ c * a x) sigma ^ order) =
        c ^ order * ∑ sigma : ConfigSpace V,
          zeroFieldInteractionWeight G beta sigma *
            finiteIsingWeightedSpinReal a sigma ^ order := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    rw [hspin, mul_pow]
    ring
  rw [hnum]
  ring



theorem integral_pow_criticalTorusGrowingCanonicalFieldLaw
    (hd : 2 ≤ d) (A : Nat → Finset (Site d)) (a : Nat → Site d → Real)
    (boxScale torusScale : Nat → Nat) (n order : Nat) :
    (∫ x, x ^ order
        ∂(criticalTorusGrowingCanonicalFieldLaw
          hd A a boxScale torusScale n : Measure Real)) =
      finiteIsingWeightedRawMoment
        (isingTorusGraph d (torusScale n))
        (IsingFK.betaC (magnetization d))
        (compactTorusWeight (A n)
          (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
              d (boxScale n) hd * a n x)
          (torusScale n)) order := by
  let c := PhysicalIsing.criticalFiniteBoxWeightedFourthScale
    d (boxScale n) hd
  unfold criticalTorusGrowingCanonicalFieldLaw isingTorusFieldLaw
  change (∫ x, x ^ order
      ∂Measure.map (criticalTorusGrowingCanonicalField hd A a boxScale torusScale n)
        (isingTorusZeroFieldLaw
          (d := d) (k := torusScale n)
          (IsingFK.betaC (magnetization d)) : Measure _)) = _
  rw [MeasureTheory.integral_map
    (Measurable.of_discrete : Measurable
      (criticalTorusGrowingCanonicalField hd A a boxScale torusScale n)).aemeasurable
    (by fun_prop)]
  change (∫ sigma,
      (c * isingTorusSmearedSpin
        (compactTorusWeight (A n) (a n) (torusScale n)) sigma) ^ order
      ∂(isingTorusZeroFieldLaw
        (d := d) (k := torusScale n)
        (IsingFK.betaC (magnetization d)) : ProbabilityMeasure _)) = _
  simp_rw [mul_pow]
  rw [integral_const_mul,
    integral_pow_isingTorusSmearedSpin_eq_finiteIsingWeightedRawMoment]
  rw [compactTorusWeight_scale]
  rw [finiteIsingWeightedRawMoment_scale_weight]



theorem criticalTorusGrowingCanonical_hasScalarMomentCumulantRecurrence
    (hd : 2 ≤ d) (A : Nat → Finset (Site d)) (a : Nat → Site d → Real)
    (boxScale torusScale : Nat → Nat) :
    HasScalarMomentCumulantRecurrence
      (fun n order ↦ ∫ x, x ^ order
        ∂(criticalTorusGrowingCanonicalFieldLaw
          hd A a boxScale torusScale n : Measure Real))
      (fun n order ↦ criticalTorusCompactWeightedCumulant (A n)
        (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
            d (boxScale n) hd * a n x)
        (torusScale n) order) := by
  unfold criticalTorusCompactWeightedCumulant
  let moments : Nat → Nat → Real := fun n order ↦ ∫ x, x ^ order
    ∂(criticalTorusGrowingCanonicalFieldLaw
      hd A a boxScale torusScale n : Measure Real)
  have hmoments : moments = fun n order ↦
      finiteIsingWeightedRawMoment
        (isingTorusGraph d (torusScale n))
        (IsingFK.betaC (magnetization d))
        (compactTorusWeight (A n)
          (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
              d (boxScale n) hd * a n x)
          (torusScale n)) order := by
    funext n order
    exact integral_pow_criticalTorusGrowingCanonicalFieldLaw
      hd A a boxScale torusScale n order
  change HasScalarMomentCumulantRecurrence moments _
  rw [hmoments]
  apply hasScalarMomentCumulantRecurrence_cumulantsOfMoments
  intro n
  exact PhysicalIsing.finiteIsingWeightedRawMoment_zero _ _ _




theorem exists_criticalTorusGrowingCanonical_weakLimit_wick
    (hd : 4 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real)
    (ha0 : ∀ n x, 0 ≤ a n x) (ha1 : ∀ n x, a n x ≤ 1) :
    ∃ boxScale torusScale : Nat → Nat,
      Tendsto boxScale atTop atTop ∧
      Tendsto torusScale atTop atTop ∧
      (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧
      ∀ (mu : ProbabilityMeasure Real) (s C : Real), 0 < s →
        Tendsto (criticalTorusGrowingCanonicalFieldLaw
          (by omega) A a boxScale torusScale) atTop (nhds mu) →
        (∀ n, Integrable (fun x : Real ↦ Real.exp (s * |x|))
          (criticalTorusGrowingCanonicalFieldLaw
            (by omega) A a boxScale torusScale n : Measure Real)) →
        (∀ n, (∫ x, Real.exp (s * |x|)
          ∂(criticalTorusGrowingCanonicalFieldLaw
            (by omega) A a boxScale torusScale n : Measure Real)) ≤ C) →
        ScalarWickMoments
          (∫ x, x ^ 2 ∂(mu : Measure Real))
          (fun order ↦ ∫ x, x ^ order ∂(mu : Measure Real)) := by
  obtain ⟨boxScale, torusScale, hboxScale, htorusScale, hcontains,
      hcumulants⟩ :=
    exists_criticalTorusGrowingCanonicalScaledCumulantLimits
      hd A a ha0 ha1
  refine ⟨boxScale, torusScale, hboxScale, htorusScale, hcontains, ?_⟩
  intro mu s C hs hlim hint hbound
  let moments : Nat → Nat → Real := fun n order ↦
    ∫ x, x ^ order
      ∂(criticalTorusGrowingCanonicalFieldLaw
        (by omega) A a boxScale torusScale n : Measure Real)
  let cumulants : Nat → Nat → Real := fun n order ↦
    criticalTorusCompactWeightedCumulant (A n)
      (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
          d (boxScale n) (by omega) * a n x)
      (torusScale n) order
  let limitMoments : Nat → Real := fun order ↦
    ∫ x, x ^ order ∂(mu : Measure Real)
  let variance : Real := limitMoments 2
  have hmoments (order : Nat) : Tendsto (fun n ↦ moments n order)
      atTop (nhds (limitMoments order)) := by
    exact integral_pow_tendsto_of_weakLimit_uniform_exp
      (criticalTorusGrowingCanonicalFieldLaw (by omega) A a boxScale torusScale)
      mu hlim s C hs hint hbound order
  have hcumulantTwo (n : Nat) : cumulants n 2 = moments n 2 := by
    dsimp [cumulants, moments]
    rw [integral_pow_criticalTorusGrowingCanonicalFieldLaw (by omega)]
    unfold criticalTorusCompactWeightedCumulant
    rw [scalarCumulantsOfMoments_two,
      PhysicalIsing.finiteIsingWeightedRawMoment_odd
        (isingTorusGraph d (torusScale n))
        (IsingFK.betaC (magnetization d))
        (compactTorusWeight (A n)
          (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
              d (boxScale n) (by omega) * a n x)
          (torusScale n)) 1 (by exact ⟨0, rfl⟩)]
    ring
  have hvariance : Tendsto (fun n ↦ cumulants n 2)
      atTop (nhds variance) := by
    apply (hmoments 2).congr'
    exact Filter.Eventually.of_forall fun n ↦ (hcumulantTwo n).symm
  have hclimits (order : Nat) : Tendsto (fun n ↦ cumulants n order)
      atTop (nhds (scalarGaussianCumulant variance order)) := by
    exact hcumulants variance hvariance order
  apply scalarWickMoments_of_cumulant_limits
    moments cumulants limitMoments variance
  · exact criticalTorusGrowingCanonical_hasScalarMomentCumulantRecurrence
      (by omega) A a boxScale torusScale
  · exact hmoments
  · exact hclimits




theorem exists_criticalTorusGrowingCanonical_weakLimit_eq_wickReference
    (hd : 4 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real)
    (ha0 : ∀ n x, 0 ≤ a n x) (ha1 : ∀ n x, a n x ≤ 1) :
    ∃ boxScale torusScale : Nat → Nat,
      Tendsto boxScale atTop atTop ∧
      Tendsto torusScale atTop atTop ∧
      (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧
      ∀ (mu nu : ProbabilityMeasure Real) (s C : Real), 0 < s →
        Tendsto (criticalTorusGrowingCanonicalFieldLaw
          (by omega) A a boxScale torusScale) atTop (nhds mu) →
        (∀ n, Integrable (fun x : Real ↦ Real.exp (s * |x|))
          (criticalTorusGrowingCanonicalFieldLaw
            (by omega) A a boxScale torusScale n : Measure Real)) →
        (∀ n, (∫ x, Real.exp (s * |x|)
          ∂(criticalTorusGrowingCanonicalFieldLaw
            (by omega) A a boxScale torusScale n : Measure Real)) ≤ C) →
        (0 : Real) ∈ interior (integrableExpSet id (nu : Measure Real)) →
        ScalarWickMoments
          (∫ x, x ^ 2 ∂(mu : Measure Real))
          (fun order ↦ ∫ x, x ^ order ∂(nu : Measure Real)) →
        (mu : Measure Real) = (nu : Measure Real) := by
  obtain ⟨boxScale, torusScale, hboxScale, htorusScale, hcontains, hwick⟩ :=
    exists_criticalTorusGrowingCanonical_weakLimit_wick
      hd A a ha0 ha1
  refine ⟨boxScale, torusScale, hboxScale, htorusScale, hcontains, ?_⟩
  intro mu nu s C hs hlim hint hbound hnuExp hnuWick
  have hmuWick := hwick mu s C hs hlim hint hbound
  have hmuExp := zero_mem_interior_integrableExpSet_of_weakLimit_uniform
    (criticalTorusGrowingCanonicalFieldLaw
      (by omega) A a boxScale torusScale)
    mu hlim s C hs hint hbound
  exact probabilityMeasure_eq_of_wickMoments_of_localExp
    (mu : Measure Real) (nu : Measure Real)
    (∫ x, x ^ 2 ∂(mu : Measure Real))
    hmuExp hnuExp hmuWick hnuWick

end

end StatMech.FrontierA
