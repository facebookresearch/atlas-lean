/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianWeightedMomentBridge









open Filter Finset Topology
open scoped BigOperators

namespace StatMech.FrontierA

noncomputable section



def scalarCumulantsOfMoments (moments : Nat -> Real) : Nat -> Real
  | 0 => 0
  | n + 1 => moments (n + 1) -
      ∑ k : Fin n, (n.choose k : Real) *
        scalarCumulantsOfMoments moments (k + 1) * moments (n - k)
termination_by order => order
decreasing_by omega

@[simp] theorem scalarCumulantsOfMoments_zero (moments : Nat -> Real) :
    scalarCumulantsOfMoments moments 0 = 0 := by
  rw [scalarCumulantsOfMoments]

theorem scalarCumulantsOfMoments_succ (moments : Nat -> Real) (n : Nat) :
    scalarCumulantsOfMoments moments (n + 1) = moments (n + 1) -
      ∑ k : Fin n, (n.choose k : Real) *
        scalarCumulantsOfMoments moments (k + 1) * moments (n - k) := by
  rw [scalarCumulantsOfMoments]



theorem hasScalarMomentCumulantRecurrence_cumulantsOfMoments
    (moments : Nat -> Nat -> Real)
    (hmomentZero : forall scale, moments scale 0 = 1) :
    HasScalarMomentCumulantRecurrence moments
      (fun scale => scalarCumulantsOfMoments (moments scale)) := by
  constructor
  · exact hmomentZero
  · intro scale order
    rw [Finset.sum_range_succ]
    have hprior :
        (∑ k ∈ Finset.range order,
          (order.choose k : Real) *
            scalarCumulantsOfMoments (moments scale) (k + 1) *
              moments scale (order - k)) =
          ∑ k : Fin order,
            (order.choose k : Real) *
              scalarCumulantsOfMoments (moments scale) (k + 1) *
                moments scale (order - k) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun k : Nat =>
        (order.choose k : Real) *
          scalarCumulantsOfMoments (moments scale) (k + 1) *
            moments scale (order - k)) order).symm
    rw [hprior]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
      hmomentZero, mul_one]
    rw [scalarCumulantsOfMoments_succ]
    ring



theorem scalarCumulantsOfMoments_eq_of_recurrence
    (moments cumulants : Nat -> Real)
    (hmomentZero : moments 0 = 1)
    (hcumulantZero : cumulants 0 = 0)
    (hrecurrence : forall order,
      moments (order + 1) =
        ∑ k ∈ Finset.range (order + 1),
          (order.choose k : Real) * cumulants (k + 1) *
            moments (order - k)) :
    forall order,
      scalarCumulantsOfMoments moments order = cumulants order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simpa using hcumulantZero.symm
      | succ n =>
          rw [scalarCumulantsOfMoments_succ]
          have hrec := hrecurrence n
          rw [Finset.sum_range_succ] at hrec
          simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
            hmomentZero, mul_one] at hrec
          have hprior :
              (∑ k : Fin n, (n.choose k : Real) *
                scalarCumulantsOfMoments moments (k + 1) *
                  moments (n - k)) =
                ∑ k ∈ Finset.range n, (n.choose k : Real) *
                  cumulants (k + 1) * moments (n - k) := by
            rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
              (n.choose k : Real) *
                scalarCumulantsOfMoments moments (k + 1) *
                  moments (n - k)) n]
            apply Finset.sum_congr rfl
            intro k hk
            rw [ih (k + 1) (by simpa using Finset.mem_range.mp hk)]
          rw [hprior]
          linarith

@[simp] theorem scalarCumulantsOfMoments_one (moments : Nat -> Real) :
    scalarCumulantsOfMoments moments 1 = moments 1 := by
  rw [show 1 = 0 + 1 by omega, scalarCumulantsOfMoments_succ]
  simp

theorem scalarCumulantsOfMoments_two (moments : Nat -> Real) :
    scalarCumulantsOfMoments moments 2 =
      moments 2 - moments 1 ^ 2 := by
  rw [show 2 = 1 + 1 by omega, scalarCumulantsOfMoments_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
    ((1 : Nat).choose k : Real) * scalarCumulantsOfMoments moments (k + 1) *
      moments (1 - k)) 1]
  norm_num [Finset.sum_range_succ, scalarCumulantsOfMoments_one]
  ring

theorem scalarCumulantsOfMoments_three_of_centered
    (moments : Nat -> Real) (hone : moments 1 = 0)
    (hthree : moments 3 = 0) :
    scalarCumulantsOfMoments moments 3 = 0 := by
  rw [show 3 = 2 + 1 by omega, scalarCumulantsOfMoments_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
    ((2 : Nat).choose k : Real) * scalarCumulantsOfMoments moments (k + 1) *
      moments (2 - k)) 2]
  norm_num [Finset.sum_range_succ, scalarCumulantsOfMoments_one,
    scalarCumulantsOfMoments_two, hone, hthree]



theorem scalarCumulantsOfMoments_four_of_symmetric
    (moments : Nat -> Real) (hone : moments 1 = 0)
    (hthree : moments 3 = 0) :
    scalarCumulantsOfMoments moments 4 =
      scalarFourthCumulant (moments 4) (moments 2) := by
  rw [show 4 = 3 + 1 by omega, scalarCumulantsOfMoments_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
    ((3 : Nat).choose k : Real) * scalarCumulantsOfMoments moments (k + 1) *
      moments (3 - k)) 3]
  norm_num [Finset.sum_range_succ, scalarCumulantsOfMoments_one,
    scalarCumulantsOfMoments_two,
    scalarCumulantsOfMoments_three_of_centered moments hone hthree,
    hone, hthree, scalarFourthCumulant]
  ring



theorem scalarCumulantsOfMoments_odd
    (moments : Nat -> Real)
    (hmoments : forall order, Odd order -> moments order = 0) :
    forall order, Odd order -> scalarCumulantsOfMoments moments order = 0 := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      intro horder
      cases order with
      | zero => exact (Nat.not_odd_zero horder).elim
      | succ n =>
          rw [scalarCumulantsOfMoments_succ, hmoments (n + 1) horder,
            zero_sub]
          apply neg_eq_zero.mpr
          apply Finset.sum_eq_zero
          intro k _
          rcases Nat.even_or_odd k.val with hkEven | hkOdd
          · have hkSuccOdd : Odd (k.val + 1) := hkEven.add_one
            rw [ih (k.val + 1) (by omega) hkSuccOdd]
            ring
          · have hnEven : Even n := by
              obtain ⟨q, hq⟩ := horder
              exact ⟨q, by omega⟩
            have hdiffOdd : Odd (n - k.val) :=
              Nat.Even.sub_odd (Nat.le_of_lt k.isLt) hnEven hkOdd
            rw [hmoments (n - k.val) hdiffOdd, mul_zero]



theorem scalarCumulantsOfMoments_scale
    (moments : Nat -> Real) (c : Real) :
    forall order,
      scalarCumulantsOfMoments (fun m => c ^ m * moments m) order =
        c ^ order * scalarCumulantsOfMoments moments order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp
      | succ n =>
          rw [scalarCumulantsOfMoments_succ,
            scalarCumulantsOfMoments_succ]
          have hsum :
              (∑ k : Fin n, (n.choose k : Real) *
                scalarCumulantsOfMoments
                  (fun m => c ^ m * moments m) (k + 1) *
                    (c ^ (n - k) * moments (n - k))) =
                c ^ (n + 1) *
                  ∑ k : Fin n, (n.choose k : Real) *
                    scalarCumulantsOfMoments moments (k + 1) *
                      moments (n - k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [ih (k.val + 1) (by omega)]
            have hexponent : k.val + 1 + (n - k.val) = n + 1 := by omega
            calc
              (n.choose k : Real) *
                    (c ^ (k.val + 1) *
                      scalarCumulantsOfMoments moments (k.val + 1)) *
                    (c ^ (n - k.val) * moments (n - k.val)) =
                  (c ^ (k.val + 1) * c ^ (n - k.val)) *
                    ((n.choose k : Real) *
                      scalarCumulantsOfMoments moments (k.val + 1) *
                        moments (n - k.val)) := by ring
              _ = c ^ (k.val + 1 + (n - k.val)) *
                    ((n.choose k : Real) *
                      scalarCumulantsOfMoments moments (k.val + 1) *
                        moments (n - k.val)) := by
                  exact congrArg
                    (fun x : Real => x *
                      ((n.choose k : Real) *
                        scalarCumulantsOfMoments moments (k.val + 1) *
                          moments (n - k.val)))
                    (pow_add c (k.val + 1) (n - k.val)).symm
              _ = _ := by rw [hexponent]
          rw [hsum]
          ring


theorem iteratedDeriv_zero_of_even_of_odd
    (F : Complex -> Complex) (heven : forall z, F (-z) = F z)
    (order : Nat) (horder : Odd order) :
    iteratedDeriv order F 0 = 0 := by
  have hfunction : (fun z => F (-z)) = F := by
    funext z
    exact heven z
  have hderiv := congrArg (fun f : Complex -> Complex =>
    iteratedDeriv order f 0) hfunction
  change iteratedDeriv order (fun z => F (-z)) 0 =
    iteratedDeriv order F 0 at hderiv
  rw [iteratedDeriv_comp_neg, neg_zero, horder.neg_one_pow,
    neg_one_smul] at hderiv
  exact CharZero.neg_eq_self_iff.mp hderiv

namespace PhysicalIsing

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedCumulant
    (beta : Real) (a : V -> Real) (order : Nat) : Real :=
  scalarCumulantsOfMoments (finiteIsingWeightedRawMoment G beta a) order

theorem finiteIsingWeightedRawMoment_zero
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedRawMoment G beta a 0 = 1 := by
  unfold finiteIsingWeightedRawMoment
  simp only [pow_zero, mul_one]
  apply div_self
  exact ne_of_gt (Finset.sum_pos
    (fun s _ => by unfold zeroFieldInteractionWeight; positivity)
    Finset.univ_nonempty)


theorem finiteIsingWeightedRawMoment_odd
    (beta : Real) (a : V -> Real) (order : Nat) (horder : Odd order) :
    finiteIsingWeightedRawMoment G beta a order = 0 := by
  have hderiv := iteratedDeriv_zero_of_even_of_odd
    (finiteIsingWeightedMomentGeneratingFunction G beta a)
    (finiteIsingWeightedMomentGeneratingFunction_neg G beta a)
    order horder
  rw [iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment]
    at hderiv
  exact_mod_cast hderiv



theorem finiteIsingWeighted_hasScalarMomentCumulantRecurrence
    (beta : Nat -> Real) (a : (scale : Nat) -> V -> Real) :
    HasScalarMomentCumulantRecurrence
      (fun scale => finiteIsingWeightedRawMoment G (beta scale) (a scale))
      (fun scale => finiteIsingWeightedCumulant G (beta scale) (a scale)) := by
  exact hasScalarMomentCumulantRecurrence_cumulantsOfMoments _
    (fun scale => finiteIsingWeightedRawMoment_zero G (beta scale) (a scale))

theorem finiteIsingWeightedCumulant_zero
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedCumulant G beta a 0 = 0 := by
  unfold finiteIsingWeightedCumulant
  rw [scalarCumulantsOfMoments_zero]

theorem finiteIsingWeightedCumulant_odd
    (beta : Real) (a : V -> Real) (order : Nat) (horder : Odd order) :
    finiteIsingWeightedCumulant G beta a order = 0 := by
  unfold finiteIsingWeightedCumulant
  exact scalarCumulantsOfMoments_odd _
    (finiteIsingWeightedRawMoment_odd G beta a) order horder



theorem finiteIsingWeighted_scaledCumulants
    (beta : Real) (a : V -> Real) (c : Real) (order : Nat) :
    scalarCumulantsOfMoments
        (fun m => c ^ m * finiteIsingWeightedRawMoment G beta a m) order =
      c ^ order * finiteIsingWeightedCumulant G beta a order := by
  exact scalarCumulantsOfMoments_scale
    (finiteIsingWeightedRawMoment G beta a) c order


theorem finiteIsingWeightedCumulant_two_eq_parity
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedCumulant G beta a 2 =
      finiteWeightedParitySecondMoment G beta (fun _ => 1) a := by
  unfold finiteIsingWeightedCumulant
  rw [scalarCumulantsOfMoments_two,
    finiteIsingWeightedRawMoment_odd G beta a 1 (by exact ⟨0, rfl⟩),
    finiteIsingWeightedRawMoment_two_eq_parity]
  ring



theorem finiteIsingWeightedCumulant_four_eq_parity
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedCumulant G beta a 4 =
      finiteWeightedParityFourthCumulant G beta (fun _ => 1) a := by
  unfold finiteIsingWeightedCumulant
  rw [scalarCumulantsOfMoments_four_of_symmetric
      (finiteIsingWeightedRawMoment G beta a)
      (finiteIsingWeightedRawMoment_odd G beta a 1 (by exact ⟨0, rfl⟩))
      (finiteIsingWeightedRawMoment_odd G beta a 3 (by exact ⟨1, rfl⟩)),
    scalarFourthCumulant_finiteIsingWeightedRawMoment_eq]




theorem criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
    (d n : Nat) (a : sctBox d n -> Real) (c : Real)
    (hc : c ^ 4 = 1 /
      (2 * (Fintype.card (sctBox d n) : Real) *
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
        ((2 * n + 1 : Nat) : Real) ^ d)) :
    criticalFiniteBoxWeightedNormalizedFourthCumulant d n a =
      scalarCumulantsOfMoments
        (fun order => c ^ order *
          finiteIsingWeightedRawMoment
            (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a order) 4 := by
  rw [finiteIsingWeighted_scaledCumulants,
    finiteIsingWeightedCumulant_four_eq_parity]
  unfold criticalFiniteBoxWeightedNormalizedFourthCumulant
    criticalFiniteBoxWeightedParityFourthCumulant
  rw [hc]
  ring



theorem exists_criticalFiniteBoxWeightedFourthScale
    (d n : Nat) (hd : 2 <= d) :
    ∃ c : Real, 0 < c ∧ c ^ 4 = 1 /
      (2 * (Fintype.card (sctBox d n) : Real) *
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
        ((2 * n + 1 : Nat) : Real) ^ d) := by
  let denominator : Real :=
    2 * (Fintype.card (sctBox d n) : Real) *
      criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d
  have hcard : 0 < (Fintype.card (sctBox d n) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨criticalFiniteBoxOrigin d n⟩
  have hchi : 0 < criticalFreeBoxSusceptibility d (2 * n) := by
    linarith [one_le_criticalFreeBoxSusceptibility hd (2 * n)]
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  let x : Real := 1 / denominator
  let c : Real := Real.sqrt (Real.sqrt x)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hc : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 hsqrtx
  refine ⟨c, hc, ?_⟩
  have hcSquare : c ^ 2 = Real.sqrt x := by
    dsimp [c]
    exact Real.sq_sqrt hsqrtx.le
  have hxSquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  change c ^ 4 = x
  calc
    c ^ 4 = (c ^ 2) ^ 2 := by ring
    _ = (Real.sqrt x) ^ 2 := by rw [hcSquare]
    _ = x := hxSquare


noncomputable def criticalFiniteBoxWeightedFourthScale
    (d n : Nat) (hd : 2 <= d) : Real :=
  Classical.choose (exists_criticalFiniteBoxWeightedFourthScale d n hd)

theorem criticalFiniteBoxWeightedFourthScale_pos
    (d n : Nat) (hd : 2 <= d) :
    0 < criticalFiniteBoxWeightedFourthScale d n hd :=
  (Classical.choose_spec
    (exists_criticalFiniteBoxWeightedFourthScale d n hd)).1

theorem criticalFiniteBoxWeightedFourthScale_pow_four
    (d n : Nat) (hd : 2 <= d) :
    criticalFiniteBoxWeightedFourthScale d n hd ^ 4 = 1 /
      (2 * (Fintype.card (sctBox d n) : Real) *
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
        ((2 * n + 1 : Nat) : Real) ^ d) :=
  (Classical.choose_spec
    (exists_criticalFiniteBoxWeightedFourthScale d n hd)).2



noncomputable def criticalFiniteBoxWeightedScaledCumulant
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real)
    (order : Nat) : Real :=
  scalarCumulantsOfMoments
    (fun m => criticalFiniteBoxWeightedFourthScale d n hd ^ m *
      finiteIsingWeightedRawMoment
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a m) order



theorem exists_criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real) :
    ∃ c : Real, 0 < c ∧
      criticalFiniteBoxWeightedNormalizedFourthCumulant d n a =
        scalarCumulantsOfMoments
          (fun order => c ^ order *
            finiteIsingWeightedRawMoment
              (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) a order) 4 := by
  obtain ⟨c, hc, hpow⟩ := exists_criticalFiniteBoxWeightedFourthScale d n hd
  exact ⟨c, hc,
    criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
      d n a c hpow⟩




theorem criticalFiniteBoxWeightedScaledFourthCumulant_tendsto_zero
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1) :
    Tendsto
      (fun n => scalarCumulantsOfMoments
        (fun order =>
          criticalFiniteBoxWeightedFourthScale d n (by omega) ^ order *
            finiteIsingWeightedRawMoment
              (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
                (a n) order) 4)
      atTop (nhds 0) := by
  have h := criticalFiniteBoxWeightedNormalizedFourthCumulant_tendsto_zero
    d hd a ha0 ha1
  convert h using 1
  funext n
  exact (criticalFiniteBoxWeightedNormalizedFourthCumulant_eq_scaled
    d n (a n) (criticalFiniteBoxWeightedFourthScale d n (by omega))
    (criticalFiniteBoxWeightedFourthScale_pow_four d n (by omega))).symm

theorem criticalFiniteBoxWeightedScaledCumulant_four_tendsto_zero
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1) :
    Tendsto
      (fun n => criticalFiniteBoxWeightedScaledCumulant
        d n (by omega) (a n) 4) atTop (nhds 0) := by
  simpa [criticalFiniteBoxWeightedScaledCumulant] using
    criticalFiniteBoxWeightedScaledFourthCumulant_tendsto_zero
      d hd a ha0 ha1

end PhysicalIsing

end

end StatMech.FrontierA
