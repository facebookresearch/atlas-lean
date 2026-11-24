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

public import MathlibExt.Analysis.Fourier.CircleFejerPolynomial
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual Fejer Fourier coefficients

Finite difference counts compute the genuine Fourier coefficients of the
actual bounded Fejer polynomial. Their normalized multiplicities tend to
one at every fixed integer frequency. These facts are needed to descend the
actual Hardy integral pairing to its source quotient; no desired weak-star
approximation or duality output is an assumption.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- Actual finite double difference sum, retaining every integer frequency. -/
def circleDifferenceSum (N : ℕ) (k : ℤ) (c : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), if k = (i : ℤ) - j then c else 0

/-- Actual inner difference sum at a nonnegative source frequency. -/
theorem circleDifferenceSum_row (N k i : ℕ) (hi : i < N + 1) (c : ℂ) :
    (∑ j ∈ Finset.range (N + 1), if (k : ℤ) = (i : ℤ) - j then c else 0) =
      if k ≤ i then c else 0 := by
  by_cases hk : k ≤ i
  · rw [ite_eq_left hk]
    have hm : i - k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single (i - k)]
    · have he : (k : ℤ) = (i : ℤ) - ((i - k : ℕ) : ℤ) := by omega
      rw [ite_eq_left he]
    · intro j hj hne
      exact ite_eq_right (by omega)
    · intro hnot
      exact False.elim (hnot hm)
  · rw [ite_eq_right hk]
    exact Finset.sum_eq_zero (fun j hj => ite_eq_right (by omega))

/-- Literal finite count of every nonnegative difference, with zero count beyond the finite range. -/
theorem circleDifferenceSum_nat (N k : ℕ) (c : ℂ) :
    circleDifferenceSum N (k : ℤ) c = (N + 1 - k : ℕ) • c := by
  unfold circleDifferenceSum
  have hrow : (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      if (k : ℤ) = (i : ℤ) - j then c else 0) =
      ∑ i ∈ Finset.range (N + 1), if k ≤ i then c else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact circleDifferenceSum_row N k i (Finset.mem_range.mp hi) c
  rw [hrow]
  by_cases hk : k ≤ N
  · have hn : N + 1 = k + (N + 1 - k) := by omega
    rw [hn, Finset.sum_range_add]
    have hleft : (∑ i ∈ Finset.range k, if k ≤ i then c else 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => ite_eq_right (by have h := Finset.mem_range.mp hi; omega))
    have hright : (∑ i ∈ Finset.range (N + 1 - k), if k ≤ k + i then c else 0) =
        (N + 1 - k : ℕ) • c := by
      simp only [Nat.le_add_right, ite_true, Finset.sum_const, Finset.card_range]
    rw [hleft, hright, zero_add, Nat.add_sub_cancel_left]
  · have hn : N + 1 - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [hn, zero_nsmul]
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (by have hi' := Finset.mem_range.mp hi; omega)

/-- The actual difference count is symmetric under reversal of the frequency. -/
theorem circleDifferenceSum_neg (N : ℕ) (k : ℤ) (c : ℂ) :
    circleDifferenceSum N (-k) c = circleDifferenceSum N k c := by
  unfold circleDifferenceSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he : (-k = (j : ℤ) - i) ↔ (k = (i : ℤ) - j) := by omega
  exact if_congr he rfl rfl

/-- Literal normalized multiplicity, using natural subtraction to give zero outside the finite support. -/
def circleFejerWeight (N : ℕ) (k : ℤ) : ℂ :=
  (N + 1 : ℂ)⁻¹ * (N + 1 - k.natAbs : ℕ)

/-- Actual finite difference count for either sign of any integer frequency. -/
theorem circleDifferenceSum_eq (N : ℕ) (k : ℤ) (c : ℂ) :
    (N + 1 : ℂ)⁻¹ * circleDifferenceSum N k c = circleFejerWeight N k * c := by
  have he : circleDifferenceSum N k c = (N + 1 - k.natAbs : ℕ) • c := by
    by_cases hsign : 0 ≤ k
    · have hnat : ((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [← hnat]
      exact circleDifferenceSum_nat N k.natAbs c
    · have hneg : k = -((k.natAbs : ℕ) : ℤ) := by omega
      rw [hneg, circleDifferenceSum_neg]
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using circleDifferenceSum_nat N k.natAbs c
  rw [he]
  simp only [circleFejerWeight, nsmul_eq_mul, mul_assoc]

/-- Full actual Fourier coefficient of the finite normalized Fejer polynomial. -/
theorem circleFejerPolynomial_fourierCoeff_sum
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) k =
      (N + 1 : ℂ)⁻¹ * circleDifferenceSum N k (fourierCoeff (f : UnitAddCircle → ℂ) k) := by
  have hterm : ∀ i j : ℕ,
      Integrable (fun x : UnitAddCircle =>
        fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
          fourier ((i : ℤ) - (j : ℤ)) x) AddCircle.haarAddCircle := by
    intro i j
    have hm := ContinuousMap.memLp (p := (1 : ℝ≥0∞))
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) ℂ
      (fourier ((i : ℤ) - (j : ℤ)))
    exact (memLp_one_iff_integrable.mp hm).const_mul _
  have hfun : (fun x : UnitAddCircle => circleFejerPolynomial f N x) =
      (N + 1 : ℂ)⁻¹ •
        (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          (fun x : UnitAddCircle =>
            fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
              fourier ((i : ℤ) - (j : ℤ)) x)) := by
    funext x
    simp only [circleFejerPolynomial, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [hfun, fourierCoeff.const_smul]
  change (N + 1 : ℂ)⁻¹ * _ = _
  congr 1
  have hout := fourierCoeff.sum (Finset.range (N + 1))
    (fun (i : ℕ) => ∑ j ∈ Finset.range (N + 1),
      (fun x : UnitAddCircle =>
        fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
          fourier ((i : ℤ) - (j : ℤ)) x))
    (fun (i : ℕ) hi =>
      integrable_finsetSum' (Finset.range (N + 1)) (fun (j : ℕ) hj => hterm i j))
  rw [congrFun hout k]
  simp only [Finset.sum_apply]
  unfold circleDifferenceSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin := fourierCoeff.sum (Finset.range (N + 1))
    (fun (j : ℕ) => fun x : UnitAddCircle =>
      fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - (j : ℤ)) *
        fourier ((i : ℤ) - (j : ℤ)) x)
    (fun (j : ℕ) hj => hterm i j)
  rw [congrFun hin k]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fourierCoeff.const_mul]
  have he := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) ((i : ℤ) - (j : ℤ))) k
  rw [he, Pi.single_apply]
  by_cases hk : k = (i : ℤ) - (j : ℤ)
  · simp only [ite_eq_left hk, mul_one]
    exact congrArg (fourierCoeff (f : UnitAddCircle → ℂ)) hk.symm
  · simp only [ite_eq_right hk, mul_zero]

/-- Actual Fourier coefficient at every integer frequency, including zero outside the finite support. -/
theorem circleFejerPolynomial_fourierCoeff
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) k =
      circleFejerWeight N k * fourierCoeff (f : UnitAddCircle → ℂ) k := by
  rw [circleFejerPolynomial_fourierCoeff_sum]
  exact circleDifferenceSum_eq N k _

/-- The actual finite normalized Fourier weights tend to one at every fixed source frequency. -/
theorem circleFejerWeight_tendsto (k : ℤ) :
    Tendsto (fun N : ℕ => circleFejerWeight N k) atTop (𝓝 1) := by
  have hzero : Tendsto (fun N : ℕ => (k.natAbs : ℂ) / ((N : ℂ) + 1)) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (k.natAbs : ℂ)) atTop (𝓝 (k.natAbs : ℂ)) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      hconst.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
  have ht : Tendsto (fun N : ℕ => 1 - (k.natAbs : ℂ) / ((N : ℂ) + 1)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (1 : ℂ)) := tendsto_const_nhds
    simpa only [sub_zero] using hone.sub hzero
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k.natAbs] with N hN
  have he : ((N + 1 - k.natAbs : ℕ) : ℂ) = (N : ℂ) + 1 - (k.natAbs : ℂ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hn : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  unfold circleFejerWeight
  rw [he]
  field_simp [hn]

/-- Actual convergence of every Fourier coefficient of the bounded Fejer polynomial. -/
theorem circleFejerPolynomial_fourierCoeff_tendsto
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (k : ℤ) :
    Tendsto (fun N : ℕ => fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) k)
      atTop (𝓝 (fourierCoeff (f : UnitAddCircle → ℂ) k)) := by
  have ht := (circleFejerWeight_tendsto k).mul_const (fourierCoeff (f : UnitAddCircle → ℂ) k)
  apply (show Tendsto (fun N : ℕ => circleFejerWeight N k * fourierCoeff (f : UnitAddCircle → ℂ) k)
    atTop (𝓝 (fourierCoeff (f : UnitAddCircle → ℂ) k)) from by simpa only [one_mul] using ht).congr'
  exact Filter.Eventually.of_forall (fun N => (circleFejerPolynomial_fourierCoeff f N k).symm)

end MathlibExt.Analysis.Fourier
