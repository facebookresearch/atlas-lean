/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace AbsoluteValue

variable {K : Type*} [Field K]

/-- **Absolute values in positive characteristic are nonarchimedean.** Let $K$ be a field of
characteristic $p > 0$. Then every real-valued absolute value $v$ on $K$ is nonarchimedean:
$v(x + y) \le \max(v(x), v(y))$ for all $x, y \in K$. -/
public theorem isNonarchimedean_of_charP {p : ℕ} [CharP K p] [NeZero p]
    (v : AbsoluteValue K ℝ) : IsNonarchimedean v := by
  let _ : NormedField K := v.toNormedField
  change IsNonarchimedean (norm : K → ℝ)
  rw [← IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm]
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one]
  intro n
  by_cases hdiv : p ∣ n
  · have hzero : (n : K) = 0 := (CharP.cast_eq_zero_iff K p n).mpr hdiv
    rw [hzero, norm_zero]
    exact zero_le_one
  · have hcast : (n : K) ≠ 0 := fun h => hdiv ((CharP.cast_eq_zero_iff K p n).mp h)
    let _ : Fact (Nat.Prime p) := CharP.char_is_prime_of_pos K p
    have hprime : Nat.Prime p := Fact.out
    let _ : ExpChar K p := ExpChar.prime hprime
    have hfrob : (n : K) ^ p = (n : K) := by
      change (frobenius K p) (n : K) = (n : K)
      exact map_natCast (frobenius K p) n
    have hpow : (n : K) ^ (p - 1) = 1 := by
      have hp1 : 1 ≤ p := hprime.one_le
      have hmul : (n : K) ^ (p - 1) * (n : K) = 1 * (n : K) := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp1, hfrob]
      exact mul_right_cancel₀ hcast hmul
    have hnorm : ‖(n : K)‖ ^ (p - 1) = 1 := by
      rw [← norm_pow, hpow, norm_one]
    have hsub : p - 1 ≠ 0 := by
      have h := hprime.one_lt
      omega
    have heq := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hsub).mp hnorm
    rw [heq]

/-- **Absolute values on finite fields are trivial.** Let $K$ be a finite field and $v$ a
real-valued absolute value on $K$. Then $v(x) = 1$ for every nonzero $x \in K$. -/
public theorem eq_one_of_ne_zero_of_finite [Finite K] (v : AbsoluteValue K ℝ)
    {x : K} (hx : x ≠ 0) : v x = 1 := by
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : 1 < Fintype.card K :=
    Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hpow : x ^ (Fintype.card K - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hx
  have hv : (v x) ^ (Fintype.card K - 1) = 1 := by
    have h := congrArg v hpow
    simpa using h
  have hnn : 0 ≤ v x := v.nonneg x
  have hsub : Fintype.card K - 1 ≠ 0 := by omega
  exact (pow_eq_one_iff_of_nonneg hnn hsub).mp hv

end AbsoluteValue

end
