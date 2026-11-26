/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.JosephusBaseThreeHalves
import MathlibExt.NumberTheory.JosephusFixedPointRecurrence
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-!
# Base-3/2 digits of the next Josephus fixed point, gap at least two

`josephusThreeFixedPoint_digits_of_gap_at_least_two` shows that between consecutive fixed
points of the Josephus function `J₃` with at least two intervening pure high extremal points,
the base-3/2 digit list of the next fixed point is the digit `2`, then one digit `1` fewer
than the gap, then the digit `0`, followed by the digit list of the previous fixed point.

The statement follows Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the
Josephus Function via Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1.

The proof writes `3a + 2 = t 2^m` with `m = ν₂(3a + 2)` and takes `2b + 1 = t 3^m` from
`josephusThree_fixedPoint_recurrence`. The quotients `2^u 3^v t - 1` with `u + v + 1 = m`
then emit one digit each: the digit `2` reaching `3^(m-1) t - 1`, then `m - 1` digits `1`,
then the digit `0` reaching `a`.
-/

namespace MetaMathlibExt

namespace josephusThreeFixedPoint_digits_of_gap_at_least_two

-- Emitting one base-3/2 digit: `2 * m = 3 * n + d` makes `d` the least significant digit of `m`.
private theorem digits_step {n m d : ℕ} (hm : 0 < m) (hd : d < 3)
    (h : 2 * m = 3 * n + d) : baseThreeHalvesDigits m = d :: baseThreeHalvesDigits n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hrem : 2 * (k + 1) % 3 = d := by omega
  have hquot : (2 * (k + 1) - d) / 3 = n := by omega
  rw [baseThreeHalvesDigits.eq_2, hrem, hquot]

-- With finitely many fixed points, the recurrence two indices past the end would read `2 = 6`.
private theorem infinite_fixedPoint : (Set.ofPred IsJosephusThreeFixedPoint).Infinite := by
  intro h
  have hrec := (josephusThree_fixedPoint_recurrence h.toFinset.card).2
  rw [Nat.nth_of_card_le h le_rfl, Nat.nth_of_card_le h (Nat.le_succ _)] at hrec
  have hv : padicValNat 2 (3 * 0 + 2) = 1 := by
    rw [Nat.padicValNat_def]
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Nat.Prime.multiplicity_self
  rw [hv] at hrec
  omega

-- A product of a power of two, a power of three and a positive number is positive.
private theorem chain_pos {u v t : ℕ} (ht : 1 ≤ t) : 1 ≤ 2 ^ u * 3 ^ v * t := by
  have ht0 : 0 < t := by omega
  have hpos : 0 < 2 ^ u * 3 ^ v * t :=
    mul_pos (mul_pos (pow_pos (by decide) u) (pow_pos (by decide) v)) ht0
  omega

-- The quotients `2 ^ u * 3 ^ v * t - 1` with `u + v + 1 = m` emit `v` digits `1` then `0`.
private theorem digits_of_chain {a m t : ℕ} (ht : 1 ≤ t)
    (hs : 3 * a + 2 = t * 2 ^ m) (ha : 1 ≤ a) :
    ∀ u v : ℕ, u + v + 1 = m →
      baseThreeHalvesDigits (2 ^ u * 3 ^ v * t - 1) =
        List.replicate v 1 ++ 0 :: baseThreeHalvesDigits a := by
  intro u v
  induction v generalizing u with
  | zero =>
    intro hm
    have hm' : u + 1 = m := by omega
    have h2X : 2 * (2 ^ u * 3 ^ 0 * t) = 3 * a + 2 := by
      calc (2 : ℕ) * (2 ^ u * 3 ^ 0 * t) = 2 ^ (u + 1) * t := by
            simp only [pow_zero, mul_one]
            ring
        _ = 2 ^ m * t := by rw [hm']
        _ = 3 * a + 2 := by rw [hs]; ring
    have hstep : 2 * (2 ^ u * 3 ^ 0 * t - 1) = 3 * a + 0 := by omega
    have hpos : 0 < 2 ^ u * 3 ^ 0 * t - 1 := by omega
    rw [digits_step hpos (by decide) hstep]
    simp only [List.replicate_zero, List.nil_append]
  | succ v ih =>
    intro hm
    have hY := ih (u + 1) (by omega)
    have h2XY : 2 * (2 ^ u * 3 ^ (v + 1) * t) = 3 * (2 ^ (u + 1) * 3 ^ v * t) := by
      ring
    have hX1 : 1 ≤ 2 ^ u * 3 ^ (v + 1) * t := chain_pos ht
    have hY1 : 1 ≤ 2 ^ (u + 1) * 3 ^ v * t := chain_pos ht
    have hstep : 2 * (2 ^ u * 3 ^ (v + 1) * t - 1) =
        3 * (2 ^ (u + 1) * 3 ^ v * t - 1) + 1 := by omega
    have hpos : 0 < 2 ^ u * 3 ^ (v + 1) * t - 1 := by omega
    rw [digits_step hpos (by decide) hstep, hY]
    simp only [List.replicate_succ, List.cons_append]

end josephusThreeFixedPoint_digits_of_gap_at_least_two

open josephusThreeFixedPoint_digits_of_gap_at_least_two in
/-- **Base-3/2 digits of the next Josephus fixed point, gap at least two.** Let $J_3$ be the
Josephus function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point
of $J_3$ in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of
integers $n$ with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points
between them). For every $\ell$, if $m_\ell \ge 2$, then the base-$3/2$ digit list of
$n_{\ell+1}$, least significant digit first, is the digit $2$, then $m_\ell - 1$ digits equal to
$1$, then the digit $0$, followed by the digit list of $n_\ell$.

Written most significant digit first, this appends to the digits of $n_\ell$ a $0$, then
$m_\ell - 1$ ones, then a $2$. This is part (iii) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_digits_of_gap_at_least_two (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    2 ≤ m → E = 2 :: List.replicate (m - 1) 1 ++ 0 :: D := by
  dsimp only
  let a := josephusThreeFixedPoint ℓ
  let b := josephusThreeFixedPoint (ℓ + 1)
  change 2 ≤ josephusThreeGap ℓ →
    baseThreeHalvesDigits b = 2 :: List.replicate (josephusThreeGap ℓ - 1) 1 ++
      0 :: baseThreeHalvesDigits a
  intro hgap
  obtain ⟨hcount, hrec⟩ := josephusThree_fixedPoint_recurrence ℓ
  change josephusThreeGap ℓ = padicValNat 2 (3 * a + 2) at hcount
  change 2 ^ (padicValNat 2 (3 * a + 2) + 1) * b + 2 ^ padicValNat 2 (3 * a + 2) =
    3 ^ padicValNat 2 (3 * a + 2) * (3 * a + 2) at hrec
  generalize hm : padicValNat 2 (3 * a + 2) = m at hcount hrec
  rw [hcount] at hgap ⊢
  have hs : 3 * a + 2 = Nat.divMaxPow (3 * a + 2) 2 * 2 ^ m := by
    rw [← hm, Nat.divMaxPow_mul_pow_padicValNat]
  generalize Nat.divMaxPow (3 * a + 2) 2 = t at hs
  have hb : 2 * b + 1 = t * 3 ^ m := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) m)
    rw [hs] at hrec
    rw [Nat.mul_add, ← Nat.mul_assoc, ← pow_succ, Nat.mul_one, hrec]
    ring
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · omega
    · exact hpos
  have hm1 : m = (m - 1) + 1 := by omega
  have ha1 : 1 ≤ a := (Nat.nth_mem_of_infinite infinite_fixedPoint ℓ).1
  have hq1 : baseThreeHalvesDigits (2 ^ 0 * 3 ^ (m - 1) * t - 1) =
      List.replicate (m - 1) 1 ++ 0 :: baseThreeHalvesDigits a :=
    digits_of_chain ht hs ha1 0 (m - 1) (by omega)
  have hb1 : 1 ≤ b := (Nat.nth_mem_of_infinite infinite_fixedPoint (ℓ + 1)).1
  have h3m : t * 3 ^ m = 3 * (2 ^ 0 * 3 ^ (m - 1) * t) := by
    conv_lhs => rw [hm1, pow_succ]
    ring
  have hstep : 2 * b = 3 * (2 ^ 0 * 3 ^ (m - 1) * t - 1) + 2 := by omega
  rw [digits_step (by omega) (by decide) hstep, hq1]
  simp only [List.cons_append]

end MetaMathlibExt
