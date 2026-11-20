/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalFreeBoxLocalObservables
import Code.FrontierA.IsingCriticalTorusGrowingSupport
import Code.FrontierA.IsingGaussianCompactSupportScaling
import Code.FrontierA.IsingGaussianNonnegativeNewman












open Filter Finset MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}

private def freeBoxGrowingRowOrderFamily (n : Nat) : Finset (Nat × Nat) :=
  {n} ×ˢ Finset.range (n + 1)

noncomputable def finiteSupportBoxRadius (A : Finset (Site d)) : Nat :=
  Classical.choose (finite_subset_box (↑A : Set (Site d)) A.finite_toSet)

theorem finiteSupport_subset_box (A : Finset (Site d)) :
    (↑A : Set (Site d)) ⊆ box d (finiteSupportBoxRadius A) :=
  Classical.choose_spec
    (finite_subset_box (↑A : Set (Site d)) A.finite_toSet)



theorem exists_criticalFreeBoxGrowingCompactCumulant_diagonal
    (hd : 2 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real) :
    ∃ boxScale : Nat → Nat,
      Tendsto boxScale atTop atTop ∧
      (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧
      ∀ n order, order ≤ n →
        |criticalFreeBoxCompactWeightedCumulant
              (A n) (a n) (boxScale n) order -
            criticalFreeCompactWeightedCumulant (A n) (a n) order| <
          1 / (n + 1 : Real) := by
  let shiftedBoxCumulant : Nat × Nat → Nat → Real := fun p k ↦
    criticalFreeBoxCompactWeightedCumulant
      (A p.1) (a p.1) (k + finiteSupportBoxRadius (A p.1)) p.2
  let infiniteCumulant : Nat × Nat → Real := fun p ↦
    criticalFreeCompactWeightedCumulant (A p.1) (a p.1) p.2
  have hpoint (p : Nat × Nat) :
      Tendsto (shiftedBoxCumulant p) atTop (nhds (infiniteCumulant p)) := by
    exact (tendsto_add_atTop_iff_nat (finiteSupportBoxRadius (A p.1))).2
      (criticalFreeBoxCompactWeightedCumulant_tendsto
        hd (A p.1) (a p.1) p.2)
  obtain ⟨scale, hscale, hclose⟩ :=
    exists_diagonal_close_on_finiteFamilies shiftedBoxCumulant
      infiniteCumulant hpoint freeBoxGrowingRowOrderFamily
  let boxScale : Nat → Nat := fun n ↦
    scale n + finiteSupportBoxRadius (A n)
  have hboxScale : Tendsto boxScale atTop atTop :=
    tendsto_atTop_mono
      (fun n ↦ Nat.le_add_right (scale n) (finiteSupportBoxRadius (A n)))
      hscale
  refine ⟨boxScale, hboxScale, ?_, ?_⟩
  · intro n
    exact (finiteSupport_subset_box (A n)).trans
      (box_mono d (Nat.le_add_left (finiteSupportBoxRadius (A n)) (scale n)))
  · intro n order horder
    have hmem : (n, order) ∈ freeBoxGrowingRowOrderFamily n := by
      simp only [freeBoxGrowingRowOrderFamily, Finset.mem_product,
        Finset.mem_singleton, Finset.mem_range, true_and]
      omega
    simpa only [shiftedBoxCumulant, infiniteCumulant, boxScale] using
      hclose n (n, order) hmem



theorem criticalFreeCompactWeightedCumulant_scale
    (A : Finset (Site d)) (a : Site d → Real) (c : Real) (order : Nat) :
    criticalFreeCompactWeightedCumulant A (fun x ↦ c * a x) order =
      c ^ order * criticalFreeCompactWeightedCumulant A a order := by
  unfold criticalFreeCompactWeightedCumulant
  have hmoment :
      (fun m ↦ criticalFreeLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A (fun x ↦ c * a x) sigma ^ m)) =
      (fun m ↦ c ^ m * criticalFreeLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ m)) := by
    funext m
    unfold criticalFreeLocalObservableExpectation compactWeightedSpin
    have hspin (sigma : ConfigSpace {x // x ∈ A}) :
        (∑ x, c * a x.1 * spin sigma x) =
          c * ∑ x, a x.1 * spin sigma x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    simp_rw [hspin, mul_pow, integral_const_mul]
  rw [hmoment, scalarCumulantsOfMoments_scale]




theorem criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero_along
    (d : Nat) (hd : 4 < d) (boxScale : Nat → Nat)
    (hboxScale : Tendsto boxScale atTop atTop)
    (a : (n : Nat) → sctBox d (boxScale n) → Real)
    (ha0 : ∀ n x, 0 ≤ a n x) (ha1 : ∀ n x, a n x ≤ 1) :
    Tendsto
      (fun n ↦ PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
        d (boxScale n) (by omega) (a n) 4)
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n ↦ -criticalFiniteBoxGlobalNormalizedFourthCumulant
        d (boxScale n)) atTop (nhds 0) := by
    simpa only [neg_zero] using
      (criticalFiniteBoxGlobalNormalizedFourthCumulant_tendsto_zero
        d hd).neg.comp hboxScale
  have hnormalized : Tendsto
      (fun n ↦ -criticalFiniteBoxWeightedNormalizedFourthCumulant
        d (boxScale n) (a n)) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦
        (criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
          d (boxScale n) (by omega) (a n) (ha0 n) (ha1 n)).1
    · exact Filter.Eventually.of_forall fun n ↦
        (criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
          d (boxScale n) (by omega) (a n) (ha0 n) (ha1 n)).2
    · exact hupper
  have hscaled : (fun n ↦
      PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
        d (boxScale n) (by omega) (a n) 4) =
      (fun n ↦ criticalFiniteBoxWeightedNormalizedFourthCumulant
        d (boxScale n) (a n)) := by
    funext n
    exact (PhysicalIsing.criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
      d (boxScale n) (a n)
      (PhysicalIsing.criticalFiniteBoxWeightedFourthScale
        d (boxScale n) (by omega))
      (PhysicalIsing.criticalFiniteBoxWeightedFourthScale_pow_four
        d (boxScale n) (by omega))).symm
  rw [hscaled]
  simpa using hnormalized.neg




theorem exists_criticalFreeGrowingCanonicalScaledFourthCumulant_tendsto_zero
    (hd : 4 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real)
    (ha0 : ∀ n x, 0 ≤ a n x) (ha1 : ∀ n x, a n x ≤ 1) :
    ∃ boxScale : Nat → Nat,
      Tendsto boxScale atTop atTop ∧
      (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧
      Tendsto
        (fun n ↦ criticalFreeCompactWeightedCumulant (A n)
          (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
              d (boxScale n) (by omega) * a n x) 4)
        atTop (nhds 0) := by
  obtain ⟨boxScale, hboxScale, hcontains, hclose⟩ :=
    exists_criticalFreeBoxGrowingCompactCumulant_diagonal
      (by omega) A a
  let c : Nat → Real := fun n ↦
    PhysicalIsing.criticalFiniteBoxWeightedFourthScale
      d (boxScale n) (by omega)
  let boxWeight : (n : Nat) → sctBox d (boxScale n) → Real := fun n ↦
    compactFreeBoxWeight (A n) (a n) (boxScale n)
  have hboxWeight0 (n : Nat) (x : sctBox d (boxScale n)) :
      0 ≤ boxWeight n x := by
    dsimp [boxWeight, compactFreeBoxWeight]
    split <;> simp_all [ha0]
  have hboxWeight1 (n : Nat) (x : sctBox d (boxScale n)) :
      boxWeight n x ≤ 1 := by
    dsimp [boxWeight, compactFreeBoxWeight]
    split <;> simp_all [ha1]
  have hphysical :=
    criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero_along
      d hd boxScale hboxScale boxWeight hboxWeight0 hboxWeight1
  have hc : Tendsto c atTop (nhds 0) := by
    exact (criticalFiniteBoxWeightedFourthScale_tendsto_zero
      (d := d) (by omega)).comp hboxScale
  have hrawDiff : Tendsto
      (fun n ↦ criticalFreeBoxCompactWeightedCumulant
          (A n) (a n) (boxScale n) 4 -
        criticalFreeCompactWeightedCumulant (A n) (a n) 4)
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ abs_nonneg _
    · filter_upwards [eventually_ge_atTop 4] with n hn
      exact (hclose n 4 hn).le
    · simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : Nat ↦ (1 : Real) / (n + 1)) atTop (nhds 0))
  have hscaledDiff : Tendsto
      (fun n ↦ c n ^ 4 *
        (criticalFreeCompactWeightedCumulant (A n) (a n) 4 -
          criticalFreeBoxCompactWeightedCumulant
            (A n) (a n) (boxScale n) 4))
      atTop (nhds 0) := by
    have hneg := hrawDiff.neg
    simpa [mul_zero] using (hc.pow 4).mul hneg
  have hexact (n : Nat) :
      criticalFreeCompactWeightedCumulant (A n)
          (fun x ↦ c n * a n x) 4 -
        PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
          d (boxScale n) (by omega) (boxWeight n) 4 =
      c n ^ 4 *
        (criticalFreeCompactWeightedCumulant (A n) (a n) 4 -
          criticalFreeBoxCompactWeightedCumulant
            (A n) (a n) (boxScale n) 4) := by
    rw [criticalFreeCompactWeightedCumulant_scale]
    unfold PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant
    rw [PhysicalIsing.finiteIsingWeighted_scaledCumulants]
    rw [← criticalFreeBoxCompactWeightedCumulant_eq_finiteCumulant
      (A n) (a n) (boxScale n) 4 (hcontains n)]
    dsimp only [c]
    ring
  have htarget : Tendsto
      (fun n ↦ criticalFreeCompactWeightedCumulant (A n)
        (fun x ↦ c n * a n x) 4) atTop (nhds 0) := by
    have hadd := hscaledDiff.add hphysical
    convert hadd using 1
    · funext n
      rw [← hexact n]
      ring
    · simp
  exact ⟨boxScale, hboxScale, hcontains, htarget⟩




theorem exists_criticalTorusGrowingCanonicalScaledFourthCumulant_tendsto_zero
    (hd : 4 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real)
    (ha0 : ∀ n x, 0 ≤ a n x) (ha1 : ∀ n x, a n x ≤ 1) :
    ∃ boxScale torusScale : Nat → Nat,
      Tendsto boxScale atTop atTop ∧
      Tendsto torusScale atTop atTop ∧
      (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧
      Tendsto
        (fun n ↦ criticalTorusCompactWeightedCumulant (A n)
          (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
              d (boxScale n) (by omega) * a n x)
          (torusScale n) 4)
        atTop (nhds 0) := by
  obtain ⟨boxScale, hboxScale, hcontains, hinfinite⟩ :=
    exists_criticalFreeGrowingCanonicalScaledFourthCumulant_tendsto_zero
      hd A a ha0 ha1
  let scaledWeight : Nat → Site d → Real := fun n x ↦
    PhysicalIsing.criticalFiniteBoxWeightedFourthScale
      d (boxScale n) (by omega) * a n x
  obtain ⟨torusScale, htorusScale, htorusDiff⟩ :=
    exists_criticalTorusGrowingCompactCumulant_tendsto
      (by omega) A scaledWeight
  have htarget := (htorusDiff 4).add hinfinite
  refine ⟨boxScale, torusScale, hboxScale, htorusScale, hcontains, ?_⟩
  convert htarget using 1
  · funext n
    dsimp [scaledWeight]
    ring
  · simp




theorem exists_criticalTorusGrowingCanonicalScaledCumulantLimits
    (hd : 4 < d) (A : Nat → Finset (Site d))
    (a : Nat → Site d → Real)
    (ha0 : ∀ n x, 0 ≤ a n x) (ha1 : ∀ n x, a n x ≤ 1) :
    ∃ boxScale torusScale : Nat → Nat,
      Tendsto boxScale atTop atTop ∧
      Tendsto torusScale atTop atTop ∧
      (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧
      ∀ variance : Real,
        Tendsto
          (fun n ↦ criticalTorusCompactWeightedCumulant (A n)
            (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
                d (boxScale n) (by omega) * a n x)
            (torusScale n) 2)
          atTop (nhds variance) →
        ∀ order,
          Tendsto
            (fun n ↦ criticalTorusCompactWeightedCumulant (A n)
              (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale
                  d (boxScale n) (by omega) * a n x)
              (torusScale n) order)
            atTop (nhds (scalarGaussianCumulant variance order)) := by
  obtain ⟨boxScale, torusScale, hboxScale, htorusScale, hcontains, hfourth⟩ :=
    exists_criticalTorusGrowingCanonicalScaledFourthCumulant_tendsto_zero
      hd A a ha0 ha1
  let scaledWeight : Nat → Site d → Real := fun n x ↦
    PhysicalIsing.criticalFiniteBoxWeightedFourthScale
      d (boxScale n) (by omega) * a n x
  have hscaled0 (n : Nat) (x : Site d) : 0 ≤ scaledWeight n x := by
    exact mul_nonneg
      (PhysicalIsing.criticalFiniteBoxWeightedFourthScale_pos
        d (boxScale n) (by omega)).le (ha0 n x)
  have hcontrol :=
    criticalTorusGrowingCompactWeighted_newmanFourthCumulantControl
      (by omega : 2 ≤ d) A scaledWeight torusScale hscaled0
  refine ⟨boxScale, torusScale, hboxScale, htorusScale, hcontains, ?_⟩
  intro variance hvariance order
  apply cumulantLimits_of_newmanFourthControl
    (fun n order ↦ criticalTorusCompactWeightedCumulant
      (A n) (scaledWeight n) (torusScale n) order)
    variance hcontrol hvariance
  simpa only [scaledWeight] using hfourth

end

end StatMech.FrontierA
