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
import Mathlib.Tactic.NormNum.Prime

/-!
# Ramanujan's tau function modulo 19

Modulo a prime `ℓ`, the Frobenius map turns the `ℓ`-th power of Euler's product `∏ (1 - q^m)`
into `∏ (1 - q^(ℓ m))`. For `ℓ = 19` this gives
`∏ (1 - q^m) ^ 24 ≡ ∏ (1 - q^m) ^ 5 ∏ (1 - q^(19 m))`, and expanding the second factor by Euler's
pentagonal number theorem proves the main result, `ramanujanTau_succ_modEq_pentagonal_tau_five`:
for `n ≥ 1`, Ramanujan's `τ(n + 1)` is congruent modulo `19` to the sum of
`(-1)^r τ_5(n - 19 P(r) + 1)` over the integers `r` with `19 P(r) ≤ n`, where
`P(r) = r(3r - 1)/2` and `τ_5` is the generalized tau function.

The argument follows the proof of Theorem 3.21 in S. Sriram and A. David Christopher,
*Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition
Function Weighted Composition Sums*, arXiv:2509.26559 (INTEGERS 24 (2024), Article A39), which
reduces `(1 - q^m) ^ 24` modulo `19` through its binomial coefficients. The index of `τ_5` is
shifted by one, as the theorem's docstring explains.
-/

namespace MetaMathlibExt

open PowerSeries

namespace ramanujanTau_succ_modEq_pentagonal_tau_five

/-- An integer `r` with `P(r) ≤ n` lies in `[-n, n]`, since `|r| ≤ P(r)`. -/
private theorem mem_Icc_of_pentagonal_le {r : ℤ} {n : ℕ} (h : pentagonal r ≤ n) :
    r ∈ Finset.Icc (-(n : ℤ)) n := by
  have h₂ := two_mul_natCast_pentagonal r
  have h' : (pentagonal r : ℤ) ≤ n := by exact_mod_cast h
  rw [Finset.mem_Icc]
  constructor <;> nlinarith

/-- For `j ≤ n`, the coefficient of `X ^ j` in `∑_r (-1)^r X^(p P(r))`, the expansion of Euler's
pentagonal series by `p`, is a finite sum over `r ∈ [-n, n]`. -/
private theorem coeff_expand_pentagonalSeries (p : ℕ) (hp : p ≠ 0) {j n : ℕ} (hj : j ≤ n) :
    coeff j (expand p hp (pentagonalSeries ℤ)) =
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n, if p * pentagonal r = j then (r.negOnePow : ℤ) else 0 := by
  rw [coeff_expand]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    simp_rw [Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hp)]
    by_cases hm : m ∈ Set.range pentagonal
    · obtain ⟨r₀, rfl⟩ := hm
      have hle : pentagonal r₀ ≤ n :=
        (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hp)).trans hj
      rw [coeff_pentagonalSeries_pentagonal, Int.cast_id]
      simp_rw [pentagonal_inj]
      rw [Finset.sum_ite_eq', ite_eq_left (mem_Icc_of_pentagonal_le hle)]
    · rw [coeff_pentagonalSeries_eq_zero ℤ hm]
      exact (Finset.sum_eq_zero fun r _ => ite_eq_right fun h => hm ⟨r, h⟩).symm
  · exact (Finset.sum_eq_zero fun r _ => ite_eq_right fun h => hdvd ⟨_, h.symm⟩).symm

/-- Multiplying a power series `A` by `∏ (1 - X^(p m)) = ∑_r (-1)^r X^(p P(r))`: the coefficient of
`X ^ n` is `∑ (-1)^r [X^(n - p P(r))] A` over the integers `r` with `p P(r) ≤ n`. -/
private theorem coeff_mul_expand_pentagonalSeries (A : ℤ⟦X⟧) (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    coeff n (A * expand p hp (pentagonalSeries ℤ)) =
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if p * pentagonal r ≤ n then (r.negOnePow : ℤ) * coeff (n - p * pentagonal r) A
        else 0 := by
  rw [mul_comm, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i _ * coeff j A)]
  rw [Finset.sum_congr rfl fun k hk => by
    rw [coeff_expand_pentagonalSeries p hp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
      Finset.sum_mul]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- Modulo a prime `ℓ`, the coefficients of `(∏ (1 - X^m)) ^ (k + ℓ)` and of
`(∏ (1 - X^m)) ^ k ∏ (1 - X^(ℓ m))` agree: the Frobenius map sends the `ℓ`-th power of Euler's
product to its expansion by `ℓ`. -/
private theorem coeff_pow_add_modEq (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (k n : ℕ) :
    coeff n (pentagonalSeries ℤ ^ (k + ℓ)) ≡
      coeff n (pentagonalSeries ℤ ^ k * expand ℓ hℓ.out.ne_zero (pentagonalSeries ℤ)) [ZMOD ℓ] := by
  have key : map (Int.castRingHom (ZMod ℓ)) (pentagonalSeries ℤ ^ (k + ℓ)) =
      map (Int.castRingHom (ZMod ℓ))
        (pentagonalSeries ℤ ^ k * expand ℓ hℓ.out.ne_zero (pentagonalSeries ℤ)) := by
    rw [pow_add, map_mul, map_mul, map_expand, map_pow _ _ ℓ,
      ← map_frobenius_expand ℓ hℓ.out.ne_zero, ZMod.frobenius_zmod, map_id]
    rfl
  rw [← ZMod.intCast_eq_intCast_iff]
  change Int.castRingHom (ZMod ℓ) _ = Int.castRingHom (ZMod ℓ) _
  rw [← coeff_map, ← coeff_map, key]

/-- For a natural number `k`, `τ_k(m + 1)` is the coefficient of `X ^ m` in `(∏ (1 - X^j)) ^ k`. -/
private theorem generalizedTau_natCast_succ (k m : ℕ) :
    generalizedTau k (m + 1) = coeff m (pentagonalSeries ℤ ^ k) := by
  rw [generalizedTau_natCast, coeff_succ_X_mul]

end ramanujanTau_succ_modEq_pentagonal_tau_five

open ramanujanTau_succ_modEq_pentagonal_tau_five in
set_option linter.unusedVariables false in
/-- **Ramanujan's $\tau$ modulo $19$ via $\tau_5$.** Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,
$$\tau(n + 1) \equiv \sum_{19P(r) \le n} (-1)^r \tau_5(n - 19P(r) + 1) \pmod{19},$$
the sum running over all integers $r$ with $19P(r) \le n$.

The source record prints $\tau_5(s)$ in place of $\tau_5(s + 1)$, where $n = 19P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^5 (1 - q^{19m}) = \sum_{r, s} (-1)^r \tau_5(s + 1) q^{19P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Theorem 12 (`integers-2024-A39-thm-12`). -/
public theorem ramanujanTau_succ_modEq_pentagonal_tau_five (n : ℕ) (hn : 0 < n) :
    generalizedTau 24 (n + 1) ≡
      ∑ r ∈ Finset.Icc (-(n : ℤ)) n,
        if 19 * pentagonal r ≤ n then
          (r.negOnePow : ℤ) * generalizedTau 5 (n - 19 * pentagonal r + 1)
        else 0 [ZMOD 19] := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  rw [show (24 : ℤ) = ((5 + 19 : ℕ) : ℤ) by rfl, generalizedTau_natCast_succ]
  refine (coeff_pow_add_modEq 19 5 n).trans ?_
  rw [coeff_mul_expand_pentagonalSeries]
  simp_rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, generalizedTau_natCast_succ]
  rfl

end MetaMathlibExt
