/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QCollatzParityFlip
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Congruence of q-Collatz parity vectors

## References

* Kenneth G. Monks, *On q-Analogs of the 3x + 1 Dynamical System*, Journal of Integer
  Sequences 28 (2025), Article 25.6.8, pp. 1–13, §2.1, Theorem 11. The proof uses the
  perturbation results in Lemma 7 and Corollaries 8 and 9 of the same paper.
* Jeffrey C. Lagarias, *The 3x + 1 Problem and Its Generalizations*, American Mathematical
  Monthly 92 (1985), pp. 3–23 (classical 2-adic background cited by Monks in §2.1).
-/

namespace MetaMathlibExt

open Finset PowerSeries

private theorem toZModPow_qCollatzParityVector (A B a : PowerSeries (ZMod 2)) (m : ℕ) :
    PadicInt.toZModPow m (qCollatzParityVector A B a) =
      ((∑ k ∈ range m, (constantCoeff ((qCollatz A B)^[k] a)).val * 2 ^ k : ℕ) : ZMod (2 ^ m)) := by
  let d (k : ℕ) : ℤ_[2] := (constantCoeff ((qCollatz A B)^[k] a)).val
  have hs (c : ℕ → ℤ_[2]) : Summable (fun k => c k * (2 : ℤ_[2]) ^ k) := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹)
      (by norm_num) (by norm_num)) fun k => ?_
    rw [norm_mul, norm_pow, show ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ from PadicInt.norm_p]
    exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one _)
  have hzero : ((2 : ZMod (2 ^ m)) ^ m) = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2 ^ m)
  have htail : (∑' k : ℕ, d (k + m) * (2 : ℤ_[2]) ^ (k + m)) =
      (2 : ℤ_[2]) ^ m * ∑' k : ℕ, d (k + m) * (2 : ℤ_[2]) ^ k := by
    rw [← (hs (fun k => d (k + m))).tsum_mul_left]
    exact tsum_congr fun k => by rw [pow_add]; ac_rfl
  unfold qCollatzParityVector
  change PadicInt.toZModPow m (∑' k : ℕ, d k * (2 : ℤ_[2]) ^ k) = _
  rw [← (hs d).sum_add_tsum_nat_add m, htail, map_add, map_mul, map_pow, map_ofNat, hzero,
    zero_mul, add_zero]
  simp only [d, map_sum, map_mul, map_pow, map_ofNat, map_natCast, Nat.cast_sum, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]

private theorem binaryPrefix_lt (d : ℕ → ZMod 2) (m : ℕ) :
    (∑ k ∈ range m, (d k).val * 2 ^ k) < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd := ZMod.val_lt (d m)
    rw [sum_range_succ, pow_succ]
    interval_cases (d m).val <;> simp only [zero_mul, one_mul] <;> omega

private theorem binaryPrefix_inj {d e : ℕ → ZMod 2} {m : ℕ}
    (h : (∑ k ∈ range m, (d k).val * 2 ^ k) = ∑ k ∈ range m, (e k).val * 2 ^ k) :
    ∀ k < m, d k = e k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd := ZMod.val_lt (d m)
    have he := ZMod.val_lt (e m)
    have hb := binaryPrefix_lt d m
    have hc := binaryPrefix_lt e m
    rw [sum_range_succ, sum_range_succ] at h
    have hdigit : (d m).val = (e m).val := by
      interval_cases (d m).val <;> interval_cases (e m).val <;>
        simp only [zero_mul, one_mul] at h <;> omega
    rw [hdigit, Nat.add_right_cancel_iff] at h
    intro k hk
    obtain hkm | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk)
    · exact ih h k hkm
    · exact ZMod.val_injective _ hdigit

/-- **Parity vectors detect congruence modulo $q^{n+1}$.** Let $A, B \in \mathbb{F}_2[[q]]$ be odd
(constant term $1$), let $\mathrm{PV}_{A,B}$ be the parity vector map of the $q$-analog $T_{A,B}$
of the $3x+1$ map, and let $n \ge 0$ be an integer. For all $a, b \in \mathbb{F}_2[[q]]$, we have
$\mathrm{PV}_{A,B}(a) \equiv \mathrm{PV}_{A,B}(b) \pmod{2^{n+1}}$ in $\mathbb{Z}_2$ if and only if
$q^{n+1}$ divides $a - b$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 11 (`jis-2025-25.6.8-thm-11`). -/
public theorem qCollatzParityVector_modEq_iff (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (n : ℕ) (a b : PowerSeries (ZMod 2)) :
    PadicInt.toZModPow (n + 1) (qCollatzParityVector A B a) =
        PadicInt.toZModPow (n + 1) (qCollatzParityVector A B b) ↔
      X ^ (n + 1) ∣ a - b := by
  by_cases hz : a - b = 0
  · simp [sub_eq_zero.mp hz]
  let j := (a - b).order.toNat
  let v := (a - b).divXPowOrder
  have hv : constantCoeff v ≠ 0 := fun h => hz (constantCoeff_divXPowOrder_eq_zero_iff.mp h)
  have hab : a = b + X ^ j * v := by
    rw [show X ^ j * v = a - b from X_pow_order_mul_divXPowOrder, add_sub_cancel]
  constructor
  · intro h
    rw [toZModPow_qCollatzParityVector, toZModPow_qCollatzParityVector] at h
    have hsum := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (binaryPrefix_lt _ _),
      ZMod.val_natCast_of_lt (binaryPrefix_lt _ _)] at hsum
    have hj : n + 1 ≤ j := by
      by_contra! hlt
      exact qCollatz_iterate_parity_flip A B hA hB j b v hv (hab ▸ binaryPrefix_inj hsum j hlt)
    exact (pow_dvd_pow X hj).trans X_pow_order_dvd
  · intro h
    have hj : n + 1 ≤ j := by
      by_contra! hlt
      exact coeff_order hz (X_pow_dvd_iff.mp h j hlt)
    rw [toZModPow_qCollatzParityVector, toZModPow_qCollatzParityVector]
    congr 1
    apply sum_congr rfl
    intro k hk
    have hkj : k < j := (mem_range.mp hk).trans_le hj
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    change j = l + 1 at hl
    obtain ⟨w, _, hw⟩ := qCollatz_iterate_add_X_pow_mul A B hA hB l b v hv k (by omega)
    rw [← hl, ← hab] at hw
    rw [hw, map_add, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul, add_zero]

end MetaMathlibExt
