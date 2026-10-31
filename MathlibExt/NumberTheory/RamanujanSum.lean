/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import MathlibExt.NumberTheory.ArithmeticFunction.VonMangoldtConvolution

/-!
# Ramanujan sums

This file defines the classical Ramanujan sum using the standard additive character of `ZMod n`.

## Main definitions

* `MetaMathlibExt.ramanujanSum`

## Main statements

* `MetaMathlibExt.ramanujanSum_zero`
* `MetaMathlibExt.ramanujanSum_modulus_one`
* `MetaMathlibExt.ramanujanSum_add_mul_modulus`
* `MetaMathlibExt.ramanujanSum_eq_sum_exp`: the classical form
  `c_n(t) = ∑_{0 ≤ h < n, (h, n) = 1} exp(2πi h t / n)`
* `MetaMathlibExt.ramanujanSum_eq_sum_divisors_gcd`: `c_n(t) = ∑_{d ∣ gcd(t, n)} d μ(n / d)`
* `MetaMathlibExt.ramanujanSum_one`: `c_n(1) = μ(n)`

## References

The definition follows the convention
`c_n(t) = ∑_{a ∈ (ZMod n)ˣ} e_n(a * t)`. Its Lean representation is adapted from the
Apache-2.0 licensed `ramanujanSum` declaration in
[UW Lean Pool](https://github.com/Vilin97/lean-pool), revision
`faa8c032722c955187fae103c96e8e93066f4592`, in `LeanPool.LatticeTriangle.Solution`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- The Ramanujan sum of modulus `n` at `t`, expressed through the standard additive
character on `ZMod n`.

The assumption `[NeZero n]` expresses the usual requirement that the natural-number
modulus be positive. -/
noncomputable def ramanujanSum (n : ℕ) [NeZero n] (t : ℤ) : ℂ :=
  ∑ a : (ZMod n)ˣ, ZMod.stdAddChar ((a : ZMod n) * (t : ZMod n))

/-- The Ramanujan sum at zero is Euler's totient function. -/
@[simp]
theorem ramanujanSum_zero (n : ℕ) [NeZero n] :
    ramanujanSum n 0 = Nat.totient n := by
  simp [ramanujanSum, ZMod.card_units_eq_totient]

/-- Every Ramanujan sum of modulus one equals one. -/
@[simp]
theorem ramanujanSum_modulus_one (t : ℤ) : ramanujanSum 1 t = 1 := by
  have ht : (t : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [ramanujanSum, ht]

/-- A Ramanujan sum is periodic in its integer argument with period the modulus. -/
@[simp]
theorem ramanujanSum_add_mul_modulus (n : ℕ) [NeZero n] (t k : ℤ) :
    ramanujanSum n (t + k * n) = ramanujanSum n t := by
  simp [ramanujanSum]

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- The Ramanujan sum as the classical exponential sum
`c_n(t) = ∑_{0 ≤ h < n, (h, n) = 1} exp(2πi h t / n)`. -/
theorem ramanujanSum_eq_sum_exp (n : ℕ) [NeZero n] (t : ℤ) :
    ramanujanSum n t = ∑ h ∈ range n with h.Coprime n,
      Complex.exp (2 * Real.pi * Complex.I * h * t / n) := by
  symm
  refine Finset.sum_bij' (fun h hh => ZMod.unitOfCoprime h (mem_filter.mp hh).2)
    (fun a _ => (a : ZMod n).val) ?_ ?_ ?_ ?_ ?_
  · intro h _; exact mem_univ _
  · intro a _
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro h hh
    simp [ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt (mem_range.mp (mem_filter.mp hh).1)]
  · intro a _
    ext
    simp [ZMod.coe_unitOfCoprime]
  · intro h _
    rw [ZMod.coe_unitOfCoprime,
      show ((h : ZMod n) * (t : ZMod n)) = (((h : ℤ) * t : ℤ) : ZMod n) by push_cast; rfl,
      ZMod.stdAddChar_coe]
    push_cast
    ring_nf

/-- The complete exponential sum: for `k ≠ 0`, `∑_{b < k} e(b t / k)` is `k` if `k ∣ t` and
`0` otherwise. -/
private theorem sum_range_exp_eq (k : ℕ) (hk : k ≠ 0) (t : ℤ) :
    ∑ b ∈ range k, Complex.exp (2 * Real.pi * Complex.I * b * t / k) =
      if (k : ℤ) ∣ t then (k : ℂ) else 0 := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * t / k) with hz
  have hterm (b : ℕ) : Complex.exp (2 * Real.pi * Complex.I * b * t / k) = z ^ b := by
    rw [hz, ← Complex.exp_nat_mul]; ring_nf
  simp only [hterm]
  split_ifs with hdvd
  · obtain ⟨q, rfl⟩ := hdvd
    have hz1 : z = 1 := by
      rw [hz, Complex.exp_eq_one_iff]
      exact ⟨q, by push_cast; field_simp⟩
    simp [hz1]
  · have hz1 : z ≠ 1 := by
      rw [hz]
      intro h
      obtain ⟨j, hj⟩ := Complex.exp_eq_one_iff.mp h
      apply hdvd
      refine ⟨j, ?_⟩
      have : (t : ℂ) = k * j := by
        have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        field_simp at hj
        linear_combination hj
      exact_mod_cast this
    have hzk : z ^ k = 1 := by
      rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨t, by field_simp⟩
    rw [geom_sum_eq hz1, hzk, sub_self, zero_div]

/-- **Divisor-sum evaluation of the Ramanujan sum**, indexed by the divisors `d` of `n` that
divide `t`: `c_n(t) = ∑_{d ∣ n, d ∣ t} μ(n / d) d`. -/
theorem ramanujanSum_eq_sum_divisors_moebius (n : ℕ) [NeZero n] (t : ℤ) :
    ramanujanSum n t =
      ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℤ) ∣ t), (μ (n / d) : ℂ) * d := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [ramanujanSum_eq_sum_exp]
  -- expand the coprimality indicator as a Möbius sum
  have hind (h : ℕ) : (if h.Coprime n then (1 : ℂ) else 0) =
      ∑ d ∈ n.divisors with d ∣ h, (μ d : ℂ) := by
    have hset : {d ∈ n.divisors | d ∣ h} = (Nat.gcd h n).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h2, h1⟩, by simp [Nat.gcd_eq_zero_iff, hn]⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hn⟩, h1⟩
    rw [hset, ArithmeticFunction.sum_divisors_moebius]
  calc ∑ h ∈ range n with h.Coprime n, Complex.exp (2 * Real.pi * Complex.I * h * t / n)
      = ∑ h ∈ range n, ∑ d ∈ n.divisors with d ∣ h,
          (μ d : ℂ) * Complex.exp (2 * Real.pi * Complex.I * h * t / n) := by
        rw [sum_filter]
        refine sum_congr rfl fun h _ => ?_
        rw [← sum_mul, ← hind]
        split_ifs <;> simp
    _ = ∑ d ∈ n.divisors, (μ d : ℂ) * ∑ h ∈ range n with d ∣ h,
          Complex.exp (2 * Real.pi * Complex.I * h * t / n) := by
        simp_rw [sum_filter, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun d _ => sum_congr rfl fun h _ => ?_
        split_ifs <;> simp
    _ = ∑ d ∈ n.divisors,
          (μ d : ℂ) * if ((n / d : ℕ) : ℤ) ∣ t then ((n / d : ℕ) : ℂ) else 0 := by
        refine sum_congr rfl fun d hd => ?_
        obtain ⟨hdn, -⟩ := Nat.mem_divisors.mp hd
        have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hdn
        have hk : n / d ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hdn).mpr ⟨hn, hd0⟩
        rw [← sum_range_exp_eq (n / d) hk t]
        congr 1
        refine sum_nbij' (fun h => h / d) (fun b => d * b) ?_ ?_ ?_ ?_ ?_
        · intro h hh
          obtain ⟨hlt, hdh⟩ := mem_filter.mp hh
          exact mem_range.mpr (Nat.div_lt_div_of_lt_of_dvd hdn (mem_range.mp hlt))
        · intro b hb
          refine mem_filter.mpr ⟨mem_range.mpr ?_, dvd_mul_right d b⟩
          have := mem_range.mp hb
          calc d * b < d * (n / d) := Nat.mul_lt_mul_of_pos_left this (Nat.pos_of_ne_zero hd0)
            _ = n := Nat.mul_div_cancel' hdn
        · intro h hh; exact Nat.mul_div_cancel' (mem_filter.mp hh).2
        · intro b _; exact Nat.mul_div_cancel_left b (Nat.pos_of_ne_zero hd0)
        · intro h hh
          obtain ⟨c, rfl⟩ := (mem_filter.mp hh).2
          rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hd0)]
          congr 1
          have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
          rw [Nat.cast_div hdn hdc]
          push_cast
          field_simp
    _ = ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℤ) ∣ t), (μ (n / d) : ℂ) * d := by
        rw [← Nat.sum_div_divisors n, sum_filter]
        refine sum_congr rfl fun d hd => ?_
        rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn]
        split_ifs <;> simp

/-- **Divisor-sum evaluation of the Ramanujan sum**:
`c_n(t) = ∑_{d ∣ gcd(t, n)} d μ(n / d)`. -/
theorem ramanujanSum_eq_sum_divisors_gcd (n : ℕ) [NeZero n] (t : ℤ) :
    ramanujanSum n t = ∑ d ∈ (Int.gcd t n).divisors, (d : ℂ) * μ (n / d) := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [ramanujanSum_eq_sum_divisors_moebius]
  have hset : n.divisors.filter (fun d : ℕ => (d : ℤ) ∣ t) = (Int.gcd t n).divisors := by
    ext d
    have hg : Int.gcd t n ≠ 0 := by simp [Int.gcd_eq_zero_iff, hn]
    simp only [mem_filter, Nat.mem_divisors, Int.gcd, Int.natAbs_natCast, Nat.dvd_gcd_iff,
      Int.natCast_dvd]
    tauto
  rw [hset]
  exact sum_congr rfl fun d _ => mul_comm _ _

/-- The Ramanujan sum at one is the Möbius function: the primitive `n`-th roots of unity sum to
`μ n`. -/
@[simp]
theorem ramanujanSum_one (n : ℕ) [NeZero n] : ramanujanSum n 1 = μ n := by
  rw [ramanujanSum_eq_sum_divisors_moebius]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    obtain ⟨-, hdt⟩ := mem_filter.mp hd
    have : d = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hdt
    exact absurd this hd1
  · intro h1
    exact absurd (mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne n), by simp⟩) h1

end MetaMathlibExt

