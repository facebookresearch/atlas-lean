/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import MathlibExt.NumberTheory.JosephusFixedPointRecurrence
public import MathlibExt.NumberTheory.JosephusThreeHighExtremalRecurrences

/-!
# The Josephus function `J₃` between consecutive fixed points

`josephusThree_eq_of_mem_fixedPoint_interval` evaluates the Josephus function `J₃` at every `n`
with `a < n ≤ b`, where `a < b` are consecutive fixed points of `J₃`, by a closed formula in `b`
and the ceiling of a logarithm in base `3/2`.

The statement follows Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula
for Fixed Points of the Josephus Function*, INTEGERS 24 (2024), Article A115 (preprint
arXiv:2310.12984, where it is Theorem 4). `J₃` is `MetaMathlibExt.josephus 3`, and the paper's
increasing sequence of fixed points `n_p^{(ℓ)}` (`ℓ ≥ 1`) is `Nat.nth IsJosephusThreeFixedPoint`
at the zero-based index `ℓ - 1`.

The proof writes `3a + 2 = t 2^m` with `m = ν₂(3a + 2)` and takes `2b + 1 = t 3^m` from
`josephusThree_fixedPoint_recurrence`. The weights `wᵢ = t 3^i 2^(m-i)` (`i ≤ m`) grow by the
factor `3/2`, and an induction along the interval shows `J₃(n) = 3n + 1 - wᵢ` for the index `i`
with `2wᵢ < 3(2n + 1) ≤ 3wᵢ`; that index is the ceiling of the logarithm in the statement.
-/

namespace MetaMathlibExt

namespace josephusThree_eq_of_mem_fixedPoint_interval

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

-- After the fixed point `a`, `J₃(n) = 3n + 1 - wᵢ` with `wᵢ = t 3^i 2^(m-i)` and
-- `2wᵢ < 3(2n + 1) ≤ 3wᵢ`: the survivor advances by three until `2n + 2 = wᵢ`, then wraps to one
-- while the weight is multiplied by `3/2`; the odd weight `w_m = 2b + 1` is not met before `b`.
private theorem exists_weight {a b m t : ℕ} (ha₁ : 1 ≤ a) (haJ : josephus 3 a = a)
    (hs : 3 * a + 2 = t * 2 ^ m) (hb : 2 * b + 1 = t * 3 ^ m) :
    ∀ n, a + 1 ≤ n → n ≤ b → ∃ i ≤ m,
      2 * (t * 3 ^ i * 2 ^ (m - i)) < 3 * (2 * n + 1) ∧
        2 * n + 1 ≤ t * 3 ^ i * 2 ^ (m - i) ∧
          josephus 3 n + t * 3 ^ i * 2 ^ (m - i) = 3 * n + 1 := by
  intro n hn₁
  induction n, hn₁ using Nat.le_induction with
  | base =>
    intro _
    refine ⟨0, Nat.zero_le _, ?_⟩
    have hJ : josephus 3 (a + 1) = 2 := by
      rw [josephus_succ 3 a (by decide) ha₁, haJ,
        show a + 3 - 1 = 1 + (a + 1) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [pow_zero, mul_one, Nat.sub_zero, ← hs, hJ]
    omega
  | succ n hn ih =>
    intro hnb
    obtain ⟨i, him, h₁, h₂, h₃⟩ := ih (by omega)
    have hJ := josephus_succ 3 n (by decide) (by omega)
    by_cases hstep : 2 * n + 3 ≤ t * 3 ^ i * 2 ^ (m - i)
    · rw [Nat.mod_eq_of_lt (by omega)] at hJ
      exact ⟨i, him, by omega, by omega, by omega⟩
    · rcases Nat.lt_or_ge i m with him' | him'
      · obtain ⟨k, hk⟩ : ∃ k, m - i = k + 1 := ⟨m - i - 1, by omega⟩
        have hw : t * 3 ^ i * 2 ^ (m - i) = 2 * (t * 3 ^ i * 2 ^ k) := by
          rw [hk, pow_succ]
          ring
        have hw' : t * 3 ^ (i + 1) * 2 ^ (m - (i + 1)) = 3 * (t * 3 ^ i * 2 ^ k) := by
          rw [show m - (i + 1) = k by omega, pow_succ]
          ring
        rw [hw] at h₁ h₂ h₃ hstep
        rw [show josephus 3 n + 3 - 1 = n + 1 by omega, Nat.mod_self] at hJ
        refine ⟨i + 1, by omega, ?_⟩
        rw [hw', hJ]
        omega
      · obtain rfl : i = m := le_antisymm him him'
        rw [Nat.sub_self, pow_zero, mul_one] at hstep
        omega

end josephusThree_eq_of_mem_fixedPoint_interval

open josephusThree_eq_of_mem_fixedPoint_interval in
/-- **The Josephus function between consecutive fixed points.** For every natural number $\ell$,
let $a$ and $b$ be the $(\ell+1)$-th and $(\ell+2)$-th smallest fixed points of the Josephus
function $J_3$, and let $m = \nu_2(3a + 2)$ be the $2$-adic valuation of $3a + 2$. For every
natural number $n$ with $a + 1 \le n \le b$, put
$\mathfrak{m} = \lceil \log_{3/2}((2n + 1)/(3a + 2)) \rceil$; then, in the real numbers,
$$J_3(n) = 3n + 1 - \left(\tfrac{2}{3}\right)^{m - \mathfrak{m}} (2b + 1).$$

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *On the Recurrence Formula for Fixed
Points of the Josephus Function*, INTEGERS 24 (2024), Article A115, Theorem 3
(`integers-2024-A115-thm-3`). -/
public theorem josephusThree_eq_of_mem_fixedPoint_interval (ℓ n : ℕ)
    (hn₁ : Nat.nth IsJosephusThreeFixedPoint ℓ + 1 ≤ n)
    (hn₂ : n ≤ Nat.nth IsJosephusThreeFixedPoint (ℓ + 1)) :
    (josephus 3 n : ℝ) =
      3 * n + 1 -
        (2 / 3 : ℝ) ^
            ((padicValNat 2 (3 * Nat.nth IsJosephusThreeFixedPoint ℓ + 2) : ℤ) -
              ⌈Real.logb (3 / 2)
                ((2 * n + 1) / (3 * Nat.nth IsJosephusThreeFixedPoint ℓ + 2))⌉) *
          (2 * Nat.nth IsJosephusThreeFixedPoint (ℓ + 1) + 1) := by
  have ha : IsJosephusThreeFixedPoint (Nat.nth IsJosephusThreeFixedPoint ℓ) :=
    Nat.nth_mem_of_infinite infinite_fixedPoint ℓ
  have hrec := (josephusThree_fixedPoint_recurrence ℓ).2
  generalize Nat.nth IsJosephusThreeFixedPoint ℓ = a at ha hn₁ hrec ⊢
  generalize Nat.nth IsJosephusThreeFixedPoint (ℓ + 1) = b at hn₂ hrec ⊢
  generalize hm : padicValNat 2 (3 * a + 2) = m at hrec ⊢
  have hs : 3 * a + 2 = Nat.divMaxPow (3 * a + 2) 2 * 2 ^ m := by
    rw [← hm, Nat.divMaxPow_mul_pow_padicValNat]
  generalize Nat.divMaxPow (3 * a + 2) 2 = t at hs
  have hb : 2 * b + 1 = t * 3 ^ m := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) m)
    rw [hs] at hrec
    rw [Nat.mul_add, ← Nat.mul_assoc, ← pow_succ, Nat.mul_one, hrec]
    ring
  obtain ⟨i, him, h₁, h₂, h₃⟩ := exists_weight ha.1 ha.2 hs hb n hn₁ hn₂
  -- In the real numbers the weight is `wᵢ = (3/2)^i (3a + 2) = (2/3)^(m-i) (2b + 1)`.
  have hkey : (3 / 2 : ℝ) ^ i * (3 * a + 2) = (t * 3 ^ i * 2 ^ (m - i) : ℕ) := by
    have hs' : (3 * a + 2 : ℝ) = t * 2 ^ m := by exact_mod_cast hs
    rw [hs', show m = i + (m - i) by omega, pow_add, Nat.add_sub_cancel_left, div_pow]
    push_cast
    field_simp
  have hw : (2 / 3 : ℝ) ^ ((m : ℤ) - (i : ℤ)) * (2 * b + 1) =
      (t * 3 ^ i * 2 ^ (m - i) : ℕ) := by
    have hb' : (2 * b + 1 : ℝ) = t * 3 ^ m := by exact_mod_cast hb
    rw [← Nat.cast_sub him, zpow_natCast, hb', show m = i + (m - i) by omega, pow_add,
      Nat.add_sub_cancel_left, div_pow]
    push_cast
    field_simp
  generalize t * 3 ^ i * 2 ^ (m - i) = w at h₁ h₂ h₃ hkey hw
  have h₁' : (2 * w : ℝ) < 3 * (2 * n + 1) := by exact_mod_cast h₁
  have h₂' : (2 * n + 1 : ℝ) ≤ w := by exact_mod_cast h₂
  have h₃' : (josephus 3 n : ℝ) + w = 3 * n + 1 := by exact_mod_cast h₃
  have hpos : (0 : ℝ) < 3 * a + 2 := by positivity
  have hceil : ⌈Real.logb (3 / 2) ((2 * n + 1) / (3 * a + 2))⌉ = (i : ℤ) := by
    rw [Int.ceil_eq_iff]
    constructor
    · rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Int.cast_natCast,
        Real.rpow_sub_one (by norm_num), Real.rpow_natCast, lt_div_iff₀ hpos, div_mul_eq_mul_div,
        hkey, div_lt_iff₀ (by norm_num)]
      linarith
    · rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Int.cast_natCast,
        Real.rpow_natCast, div_le_iff₀ hpos, hkey]
      exact h₂'
  rw [hceil, hw]
  linarith

end MetaMathlibExt
