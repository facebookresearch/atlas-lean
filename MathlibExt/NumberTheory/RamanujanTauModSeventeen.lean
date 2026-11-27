/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Interval
public import MathlibExt.NumberTheory.GeneralizedTau
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Ramanujan's tau function modulo 17

The coefficient of degree `n` in the 24th power of Euler's product gives `τ(n + 1)`.
Modulo 17, the 17th power replaces `X` by `X ^ 17`, and the remaining seventh power
supplies the shifted `τ₇` coefficients in the pentagonal sum.
-/

namespace MetaMathlibExt

open PowerSeries

namespace ramanujanTau_succ_modEq_pentagonal_tau_seven

/-- In the expanded pentagonal series, the signed terms occur at degrees `17 * pentagonal r`. -/
private theorem coeff_expand_pentagonal_mul (A : ℤ⟦X⟧) (n : ℕ) :
    coeff n (expand 17 (by decide) (pentagonalSeries ℤ) * A) =
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 17 * pentagonal r ≤ n then (r.negOnePow : ℤ) * coeff (n - 17 * pentagonal r) A
        else 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Finset.sum_filter]
  symm
  apply Finset.sum_of_injOn (fun r : ℤ => 17 * pentagonal r)
  · exact ((mul_right_injective₀ (by decide : (17 : ℕ) ≠ 0)).comp pentagonal_injective).injOn
  · intro r hr
    exact Finset.mem_range_succ_iff.mpr (Finset.mem_filter.mp hr).2
  · intro i hi hout
    by_cases hd : 17 ∣ i
    · obtain ⟨j, rfl⟩ := hd
      rw [PowerSeries.coeff_expand_mul]
      suffices j ∉ Set.range pentagonal by rw [coeff_pentagonalSeries_eq_zero ℤ this, zero_mul]
      rintro ⟨r, rfl⟩
      have hle := Finset.mem_range_succ_iff.mp hi
      have hcast : (17 : ℤ) * pentagonal r ≤ n := by exact_mod_cast hle
      have hformula := two_mul_natCast_pentagonal r
      have hr : r ∈ Finset.Icc (-(n : ℤ)) n := by
        rw [Finset.mem_Icc]
        constructor <;> nlinarith
      exact hout ⟨r, Finset.mem_filter.mpr ⟨hr, hle⟩, rfl⟩
    · rw [coeff_expand_of_not_dvd 17 (by decide) _ hd, zero_mul]
  · intro r _
    simp only [PowerSeries.coeff_expand_mul, coeff_pentagonalSeries_pentagonal, Int.cast_id]

end ramanujanTau_succ_modEq_pentagonal_tau_seven

open ramanujanTau_succ_modEq_pentagonal_tau_seven in
set_option linter.unusedVariables false in
/-- **Ramanujan's $\tau$ modulo $17$ via $\tau_7$.** Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,
$$\tau(n + 1) \equiv \sum_{17P(r) \le n} (-1)^r \tau_7(n - 17P(r) + 1) \pmod{17},$$
the sum running over all integers $r$ with $17P(r) \le n$.

The source record prints $\tau_7(s)$ in place of $\tau_7(s + 1)$, where $n = 17P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^7 (1 - q^{17m}) = \sum_{r, s} (-1)^r \tau_7(s + 1) q^{17P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Theorem 11 (`integers-2024-A39-thm-11`). -/
public theorem ramanujanTau_succ_modEq_pentagonal_tau_seven (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 17 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 7 (n - 17 * pentagonal r + 1)
        else 0 [ZMOD 17] := by
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  let E := pentagonalSeries ℤ
  let f := map (Int.castRingHom (ZMod 17))
  have hpow : expand 17 (by decide) (f E) = f E ^ 17 := by
    simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card (f E)
  have hseries : f (E ^ 24) = f (expand 17 (by decide) E * E ^ 7) := by
    rw [show 24 = 17 + 7 by decide, pow_add, map_mul, map_mul, map_expand, hpow, map_pow]
  have hc := congrArg (coeff n) hseries
  simp only [f, coeff_map, Int.coe_castRingHom, ZMod.intCast_eq_intCast_iff] at hc
  rw [coeff_expand_pentagonal_mul] at hc
  have hcoeff (k m : ℕ) : coeff m (E ^ k) = generalizedTau k (m + 1) := by
    rw [generalizedTau_natCast, coeff_succ_X_mul]
  simpa only [hcoeff, Nat.cast_ofNat] using hc

end MetaMathlibExt
