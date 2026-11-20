/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianWeightedHadamardPrereq
import Code.FrontierA.IsingGaussianWeightedFourth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv










open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedSpin (a : V -> Real) (s : ConfigSpace V) : Complex :=
  ∑ v : V, (a v : Complex) * spin s v


def finiteIsingWeightedSpinReal (a : V -> Real) (s : ConfigSpace V) : Real :=
  ∑ v : V, a v * spin s v

@[simp] theorem ofReal_finiteIsingWeightedSpinReal
    (a : V -> Real) (s : ConfigSpace V) :
    (finiteIsingWeightedSpinReal a s : Complex) =
      finiteIsingWeightedSpin a s := by
  simp [finiteIsingWeightedSpinReal, finiteIsingWeightedSpin]


def finiteIsingWeightedRawMoment
    (beta : Real) (a : V -> Real) (order : Nat) : Real :=
  (∑ s : ConfigSpace V,
      zeroFieldInteractionWeight G beta s *
        finiteIsingWeightedSpinReal a s ^ order) /
    ∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s



def finiteIsingWeightedMomentGeneratingFunction
    (beta : Real) (a : V -> Real) (z : Complex) : Complex :=
  finiteIsingWeightedFieldPartition G beta a z /
    finiteIsingWeightedFieldPartition G beta a 0


@[simp] theorem finiteIsingWeightedMomentGeneratingFunction_zero
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedMomentGeneratingFunction G beta a 0 = 1 := by
  unfold finiteIsingWeightedMomentGeneratingFunction
  exact div_self (Complex.ne_zero_of_re_pos
    (finiteIsingWeightedFieldPartition_zero_re_pos G beta a))


theorem finiteIsingWeightedMomentGeneratingFunction_neg
    (beta : Real) (a : V -> Real) (z : Complex) :
    finiteIsingWeightedMomentGeneratingFunction G beta a (-z) =
      finiteIsingWeightedMomentGeneratingFunction G beta a z := by
  unfold finiteIsingWeightedMomentGeneratingFunction
  rw [finiteIsingWeightedFieldPartition_neg]


theorem finiteIsingWeightedMomentGeneratingFunction_analyticOnNhd
    (beta : Real) (a : V -> Real) :
    AnalyticOnNhd Complex
      (finiteIsingWeightedMomentGeneratingFunction G beta a) Set.univ := by
  unfold finiteIsingWeightedMomentGeneratingFunction
  intro z hz
  exact ((finiteIsingWeightedFieldPartition_analyticOnNhd G beta a) z hz).div_const



theorem finiteIsingWeightedMomentGeneratingFunction_ne_zero_of_re_ne_zero
    (beta : Real) (hbeta : 0 <= beta) (a : V -> Real)
    (ha : forall v, 0 < a v) (z : Complex) (hz : z.re ≠ 0) :
    finiteIsingWeightedMomentGeneratingFunction G beta a z ≠ 0 := by
  unfold finiteIsingWeightedMomentGeneratingFunction
  exact div_ne_zero
    (finiteIsingWeightedFieldPartition_ne_zero_of_re_ne_zero
      G hbeta a ha (z := z) hz)
    (Complex.ne_zero_of_re_pos
      (finiteIsingWeightedFieldPartition_zero_re_pos G beta a))



theorem iteratedDeriv_finiteIsingWeightedFieldPartition
    (beta : Real) (a : V -> Real) (order : Nat) (z : Complex) :
    iteratedDeriv order (finiteIsingWeightedFieldPartition G beta a) z =
      ∑ s : ConfigSpace V,
        (zeroFieldInteractionWeight G beta s : Complex) *
          finiteIsingWeightedSpin a s ^ order *
            Complex.exp (finiteIsingWeightedSpin a s * z) := by
  have hfunction : finiteIsingWeightedFieldPartition G beta a =
      fun w => ∑ s : ConfigSpace V,
        (zeroFieldInteractionWeight G beta s : Complex) *
          Complex.exp (finiteIsingWeightedSpin a s * w) := by
    funext w
    unfold finiteIsingWeightedFieldPartition finiteIsingWeightedSpin
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_comm w]
  rw [hfunction, iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro s _
    simp only [iteratedDeriv_const_mul_field,
      iteratedDeriv_cexp_const_mul]
    ring
  · intro s _
    fun_prop



theorem iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero
    (beta : Real) (a : V -> Real) (order : Nat) :
    iteratedDeriv order
        (finiteIsingWeightedMomentGeneratingFunction G beta a) 0 =
      (∑ s : ConfigSpace V,
        (zeroFieldInteractionWeight G beta s : Complex) *
          finiteIsingWeightedSpin a s ^ order) /
        finiteIsingWeightedFieldPartition G beta a 0 := by
  unfold finiteIsingWeightedMomentGeneratingFunction
  rw [iteratedDeriv_div_const,
    iteratedDeriv_finiteIsingWeightedFieldPartition]
  simp



theorem iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero_eq_rawMoment
    (beta : Real) (a : V -> Real) (order : Nat) :
    iteratedDeriv order
        (finiteIsingWeightedMomentGeneratingFunction G beta a) 0 =
      (finiteIsingWeightedRawMoment G beta a order : Complex) := by
  rw [iteratedDeriv_finiteIsingWeightedMomentGeneratingFunction_zero]
  unfold finiteIsingWeightedRawMoment
  rw [finiteIsingWeightedFieldPartition_zero]
  push_cast
  simp only [ofReal_finiteIsingWeightedSpinReal]

private theorem zeroFieldInteractionWeight_eq_boltzmannJ_one
    (beta : Real) (s : ConfigSpace V) :
    zeroFieldInteractionWeight G beta s =
      boltzmannJ G beta (fun _ => 1) s := by
  unfold zeroFieldInteractionWeight boltzmannJ
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem finiteIsingWeightedSpinReal_sq
    (a : V -> Real) (s : ConfigSpace V) :
    finiteIsingWeightedSpinReal a s ^ 2 =
      ∑ i : V, ∑ j : V,
        a i * a j * (spin s i * spin s j) := by
  unfold finiteIsingWeightedSpinReal
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem finiteIsingWeightedSpinReal_pow_four
    (a : V -> Real) (s : ConfigSpace V) :
    finiteIsingWeightedSpinReal a s ^ 4 =
      ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
        a i * a j * a k * a l *
          ((spin s i * spin s j) * (spin s k * spin s l)) := by
  have hsq := finiteIsingWeightedSpinReal_sq a s
  calc
    finiteIsingWeightedSpinReal a s ^ 4 =
        finiteIsingWeightedSpinReal a s ^ 2 *
          finiteIsingWeightedSpinReal a s ^ 2 := by ring
    _ = (∑ i : V, ∑ j : V, a i * a j * (spin s i * spin s j)) *
        (∑ k : V, ∑ l : V, a k * a l * (spin s k * spin s l)) := by
      rw [hsq]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

private theorem expectationJ_one_grahamPairSupport_eq_weighted_ratio
    (beta : Real) (i j : V) :
    expectationJ G beta (fun _ => 1) (grahamPairSupport i j) =
      (∑ s : ConfigSpace V,
        zeroFieldInteractionWeight G beta s * (spin s i * spin s j)) /
        ∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s := by
  unfold expectationJ partitionJ
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    rw [spinProd_grahamPairSupport,
      zeroFieldInteractionWeight_eq_boltzmannJ_one]
    ring
  · apply Finset.sum_congr rfl
    intro s _
    rw [zeroFieldInteractionWeight_eq_boltzmannJ_one]

private theorem expectationJ_one_grahamFourSupport_eq_weighted_ratio
    (beta : Real) (i j k l : V) :
    expectationJ G beta (fun _ => 1) (grahamFourSupport i j k l) =
      (∑ s : ConfigSpace V,
        zeroFieldInteractionWeight G beta s *
          ((spin s i * spin s j) * (spin s k * spin s l))) /
        ∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s := by
  unfold expectationJ partitionJ
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    rw [spinProd_grahamFourSupport,
      zeroFieldInteractionWeight_eq_boltzmannJ_one]
    ring
  · apply Finset.sum_congr rfl
    intro s _
    rw [zeroFieldInteractionWeight_eq_boltzmannJ_one]



theorem finiteIsingWeightedRawMoment_two_eq_parity
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedRawMoment G beta a 2 =
      finiteWeightedParitySecondMoment G beta (fun _ => 1) a := by
  let weight : ConfigSpace V -> Real :=
    fun s => zeroFieldInteractionWeight G beta s
  have hnum :
      (∑ s : ConfigSpace V, weight s * finiteIsingWeightedSpinReal a s ^ 2) =
        ∑ i : V, ∑ j : V,
          a i * a j * (∑ s : ConfigSpace V,
            weight s * (spin s i * spin s j)) := by
    calc
      _ = ∑ s : ConfigSpace V, ∑ i : V, ∑ j : V,
          weight s * (a i * a j * (spin s i * spin s j)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [finiteIsingWeightedSpinReal_sq, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i : V, ∑ s : ConfigSpace V, ∑ j : V,
          weight s * (a i * a j * (spin s i * spin s j)) := by
        rw [Finset.sum_comm]
      _ = ∑ i : V, ∑ j : V, ∑ s : ConfigSpace V,
          weight s * (a i * a j * (spin s i * spin s j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
  unfold finiteIsingWeightedRawMoment finiteWeightedParitySecondMoment
  change (∑ s : ConfigSpace V,
      weight s * finiteIsingWeightedSpinReal a s ^ 2) /
      (∑ s : ConfigSpace V, weight s) = _
  rw [hnum]
  simp_rw [expectationJ_one_grahamPairSupport_eq_weighted_ratio G]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem finiteIsingWeightedRawMoment_four_eq_parity
    (beta : Real) (a : V -> Real) :
    finiteIsingWeightedRawMoment G beta a 4 =
      finiteWeightedParityFourthMoment G beta (fun _ => 1) a := by
  let weight : ConfigSpace V -> Real :=
    fun s => zeroFieldInteractionWeight G beta s
  have hnum :
      (∑ s : ConfigSpace V, weight s * finiteIsingWeightedSpinReal a s ^ 4) =
        ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          a i * a j * a k * a l *
            (∑ s : ConfigSpace V, weight s *
              ((spin s i * spin s j) * (spin s k * spin s l))) := by
    calc
      _ = ∑ s : ConfigSpace V, ∑ i : V, ∑ j : V,
          ∑ k : V, ∑ l : V,
          weight s * (a i * a j * a k * a l *
            ((spin s i * spin s j) * (spin s k * spin s l))) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [finiteIsingWeightedSpinReal_pow_four, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      _ = ∑ i : V, ∑ s : ConfigSpace V, ∑ j : V,
          ∑ k : V, ∑ l : V,
          weight s * (a i * a j * a k * a l *
            ((spin s i * spin s j) * (spin s k * spin s l))) := by
        rw [Finset.sum_comm]
      _ = ∑ i : V, ∑ j : V, ∑ s : ConfigSpace V,
          ∑ k : V, ∑ l : V,
          weight s * (a i * a j * a k * a l *
            ((spin s i * spin s j) * (spin s k * spin s l))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ s : ConfigSpace V,
          ∑ l : V,
          weight s * (a i * a j * a k * a l *
            ((spin s i * spin s j) * (spin s k * spin s l))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          ∑ s : ConfigSpace V,
          weight s * (a i * a j * a k * a l *
            ((spin s i * spin s j) * (spin s k * spin s l))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
  unfold finiteIsingWeightedRawMoment finiteWeightedParityFourthMoment
  change (∑ s : ConfigSpace V,
      weight s * finiteIsingWeightedSpinReal a s ^ 4) /
      (∑ s : ConfigSpace V, weight s) = _
  rw [hnum]
  simp_rw [expectationJ_one_grahamFourSupport_eq_weighted_ratio G]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l _
  ring



theorem scalarFourthCumulant_finiteIsingWeightedRawMoment_eq
    (beta : Real) (a : V -> Real) :
    scalarFourthCumulant
        (finiteIsingWeightedRawMoment G beta a 4)
        (finiteIsingWeightedRawMoment G beta a 2) =
      finiteWeightedParityFourthCumulant G beta (fun _ => 1) a := by
  rw [finiteIsingWeightedRawMoment_four_eq_parity,
    finiteIsingWeightedRawMoment_two_eq_parity]
  exact scalarFourthCumulant_finiteWeightedParity_eq G beta (fun _ => 1) a

end

end StatMech.FrontierA
