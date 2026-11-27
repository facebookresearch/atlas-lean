/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Algebra.BigOperators.Fin

/-!
# Processed amount and idle energy of a production sequence

A finite partition of the production period specifies one constant achieved rate per
open subinterval. The cumulative amount is continuous across partition points, but need
not have a derivative there. Integrating the constant derivatives and telescoping gives
the total amount processed. Integrating the power lower bounds gives a separate idle
energy bound, with idle time counted by an indicator on the subinterval indices.

The local amount calculation uses the fundamental theorem of calculus (OpenStax,
*Calculus Volume 1*, §5.3, Part 2).
-/

open MeasureTheory Set
open scoped BigOperators

namespace Chemistry.ProcessBalances

/-- For a partition starting at zero, the change in cumulative processed amount is the sum of
rate times duration. Nonnegative good and scrap amounts that sum to this change are each at most
it. If integrable power is at least the nonnegative idle power on zero-rate subintervals and
nonnegative on positive-rate subintervals, its integral is at least idle power times the total
length of the zero-rate subintervals. The derivative and power bounds are only required on the open
subintervals; power at the finitely many partition points does not affect the integral. -/
public theorem processedAmount_and_idleEnergy {m : ℕ} (t : Fin (m + 1) → ℝ)
    (ht₀ : t 0 = 0) (ht : StrictMono t) (rate : Fin m → ℝ) (hrate : ∀ k, 0 ≤ rate k)
    (Q : ℝ → ℝ) (hQ : ContinuousOn Q (Icc 0 (t (Fin.last m))))
    (hderiv : ∀ k, ∀ x ∈ Ioo (t k.castSucc) (t k.succ), HasDerivAt Q (rate k) x) :
    Q (t (Fin.last m)) - Q 0 = ∑ k, rate k * (t k.succ - t k.castSucc) ∧
    (∀ G S : ℝ, 0 ≤ G → 0 ≤ S → G + S = Q (t (Fin.last m)) - Q 0 →
      G ≤ Q (t (Fin.last m)) - Q 0 ∧ S ≤ Q (t (Fin.last m)) - Q 0) ∧
    (∀ (P : ℝ → ℝ) (idlePower : ℝ), IntervalIntegrable P volume 0 (t (Fin.last m)) →
      0 ≤ idlePower →
      (∀ k, rate k = 0 → ∀ x ∈ Ioo (t k.castSucc) (t k.succ), idlePower ≤ P x) →
      (∀ k, 0 < rate k → ∀ x ∈ Ioo (t k.castSucc) (t k.succ), 0 ≤ P x) →
      idlePower * (∑ k, {j | rate j = 0}.indicator (fun j ↦ t j.succ - t j.castSucc) k) ≤
        ∫ x in 0..t (Fin.last m), P x) := by
  have hT : 0 ≤ t (Fin.last m) := ht₀ ▸ ht.monotone (Fin.zero_le _)
  have hstep (k : Fin m) : t k.castSucc ≤ t k.succ := (ht Fin.castSucc_lt_succ).le
  have hsub (k : Fin m) : Icc (t k.castSucc) (t k.succ) ⊆ Icc 0 (t (Fin.last m)) :=
    Icc_subset_Icc (ht₀ ▸ ht.monotone (Fin.zero_le _)) (ht.monotone (Fin.le_last _))
  -- Mathlib's telescoping and adjacent-integral formulas are indexed by natural numbers.
  let tNat (i : ℕ) : ℝ := t (Fin.ofNat (m + 1) i)
  have htNat₀ : tNat 0 = 0 := ht₀
  have htNatLast : tNat m = t (Fin.last m) := congrArg t (Fin.ofNat_val_eq_self (Fin.last m))
  have htNatLeft (k : Fin m) : tNat (k : ℕ) = t k.castSucc :=
    congrArg t (Fin.ofNat_val_eq_self k.castSucc)
  have htNatRight (k : Fin m) : tNat ((k : ℕ) + 1) = t k.succ :=
    congrArg t (Fin.ofNat_val_eq_self k.succ)
  refine ⟨?_, ?_, ?_⟩
  · calc
      Q (t (Fin.last m)) - Q 0 = ∑ k : Fin m, (Q (t k.succ) - Q (t k.castSucc)) := by
        simpa only [Finset.sum_range, htNat₀, htNatLast, htNatLeft, htNatRight] using
          (Finset.sum_range_sub (fun i ↦ Q (tNat i)) m).symm
      _ = ∑ k, rate k * (t k.succ - t k.castSucc) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          (hstep k) (hQ.mono (hsub k)) (hderiv k) intervalIntegrable_const
        simpa only [intervalIntegral.integral_const, smul_eq_mul,
          mul_comm (t k.succ - t k.castSucc)] using h.symm
  · intro G S hG hS hbalance
    rw [← hbalance]
    exact ⟨le_add_of_nonneg_right hS, le_add_of_nonneg_left hG⟩
  · intro P idlePower hP _ hIdle hActive
    have hInt (k : Fin m) : IntervalIntegrable P volume (t k.castSucc) (t k.succ) :=
      hP.mono_set (by simpa only [uIcc_of_le (hstep k), uIcc_of_le hT] using hsub k)
    have hsum : (∑ k : Fin m, ∫ x in t k.castSucc..t k.succ, P x) =
        ∫ x in 0..t (Fin.last m), P x := by
      have hIntNat (i : ℕ) (hi : i < m) : IntervalIntegrable P volume (tNat i) (tNat (i + 1)) := by
        rw [htNatLeft (⟨i, hi⟩ : Fin m), htNatRight (⟨i, hi⟩ : Fin m)]
        exact hInt ⟨i, hi⟩
      simpa only [Finset.sum_range, htNat₀, htNatLast, htNatLeft, htNatRight] using
        intervalIntegral.sum_integral_adjacent_intervals hIntNat
    rw [Finset.mul_sum, ← hsum]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    let idle : Set (Fin m) := {j | rate j = 0}
    have hcompare (c : ℝ) (hc : ∀ x ∈ Ioo (t k.castSucc) (t k.succ), c ≤ P x) :
        c * (t k.succ - t k.castSucc) ≤ ∫ x in t k.castSucc..t k.succ, P x := by
      simpa only [intervalIntegral.integral_const, smul_eq_mul,
        mul_comm (t k.succ - t k.castSucc)] using
        intervalIntegral.integral_mono_on_of_le_Ioo (hstep k) intervalIntegrable_const (hInt k) hc
    by_cases hk : rate k = 0
    · rw [indicator_of_mem (show k ∈ idle from hk)]
      exact hcompare idlePower (hIdle k hk)
    · rw [indicator_of_notMem (show k ∉ idle from hk), mul_zero]
      simpa only [zero_mul] using hcompare 0 (hActive k (lt_of_le_of_ne (hrate k) (Ne.symm hk)))

end Chemistry.ProcessBalances
