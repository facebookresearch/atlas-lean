/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LeonardoPTilings
import MathlibExt.NumberTheory.IncompleteLeonardoP
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Recurrence for incomplete Lucas-Leonardo p-numbers

The rational sum is a weighted difference of consecutive incomplete Leonardo p-numbers.
At the top cutoff, the shifted recurrence may need a smaller cutoff; the dropped terms vanish.
-/

namespace MetaMathlibExt

private theorem weighted_choose_eq (p n i : ℕ) (hn : 0 < n) :
    (n : ℚ) / ((n - p * i : ℕ) : ℚ) * ((n - p * i).choose i : ℚ) =
      ((p : ℚ) + 1) * ((n - p * i).choose i : ℚ) - p * ((n - 1 - p * i).choose i : ℚ) := by
  by_cases hi : i ≤ n - p * i
  · have hm : 0 < n - p * i := by
      by_contra! h
      have : i = 0 := by omega
      simp [this, Nat.not_le.mpr hn] at h
    obtain ⟨m, hm'⟩ : ∃ m, n - p * i = m + 1 := ⟨n - p * i - 1, by omega⟩
    have hpred : n - 1 - p * i = m := by omega
    have hn_eq : n = m + 1 + p * i := by omega
    have hchoose := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq m i)
    push_cast [Nat.cast_sub (show i ≤ m + 1 by omega)] at hchoose
    have hnum : (n : ℚ) = (m : ℚ) + 1 + p * i := by exact_mod_cast hn_eq
    have hden : (m : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [hm', hpred, Nat.cast_add, Nat.cast_one, hnum]
    field_simp [hden]
    linear_combination (p : ℚ) * hchoose
  · rw [Nat.choose_eq_zero_of_lt (show n - p * i < i by omega),
      Nat.choose_eq_zero_of_lt (show n - 1 - p * i < i by omega)]
    simp

private theorem incompleteLucasLeonardoP_eq_weighted (p n k : ℕ) (hn : 0 < n) :
    incompleteLucasLeonardoP p n k =
      ((p : ℚ) + 1) * (incompleteLeonardoP p n k : ℚ) -
        p * (incompleteLeonardoP p (n - 1) k : ℚ) := by
  unfold incompleteLucasLeonardoP incompleteLeonardoP
  push_cast
  simp only [weighted_choose_eq p n _ hn, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem incompleteLeonardoP_stable (p n j : ℕ) (hj : n < (j + 1) * (p + 1)) :
    incompleteLeonardoP p n (j + 1) = incompleteLeonardoP p n j := by
  rw [Nat.mul_succ, Nat.mul_comm (j + 1) p] at hj
  unfold incompleteLeonardoP
  rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show n - p * (j + 1) < j + 1 by omega)]
  simp

private theorem incompleteLeonardoP_prev_succ (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p + 1 < n) (hk : k ≤ n / (p + 1)) :
    incompleteLeonardoP p (n - 1) (k + 1) =
      incompleteLeonardoP p (n - 1 - 1) (k + 1) + incompleteLeonardoP p (n - 1 - p - 1) k +
        p := by
  by_cases hk' : k ≤ (n - 1) / (p + 1)
  · exact incompleteLeonardoP_succ p (n - 1) k hp (by omega) hk'
  · have hkpos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_of_not_ge hk')
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hle := (Nat.le_div_iff_mul_le (Nat.succ_pos p)).mp hk
    have hlt := (Nat.div_lt_iff_lt_mul (Nat.succ_pos p)).mp (Nat.lt_of_not_ge hk')
    change (j + 1) * (p + 1) ≤ n at hle
    change n - 1 < (j + 1) * (p + 1) at hlt
    -- The cutoff fits at n but not at n - 1, so n is exactly a multiple of p + 1.
    have heq : (j + 1) * (p + 1) = n := by omega
    have hsplit : j * (p + 1) + (p + 1) = n := by
      simpa only [Nat.add_mul, Nat.one_mul] using heq
    have hj : j ≤ (n - 1) / (p + 1) :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos p)).mpr (by change j * (p + 1) ≤ n - 1; omega)
    have hz : n - 1 < (j + 1 + 1) * (p + 1) := by
      rw [Nat.add_mul, Nat.one_mul, heq]
      omega
    rw [incompleteLeonardoP_stable p (n - 1) (j + 1) hz,
      incompleteLeonardoP_stable p (n - 1 - 1) (j + 1) (by omega),
      incompleteLeonardoP_stable p (n - 1 - p - 1) j (by omega)]
    exact incompleteLeonardoP_succ p (n - 1) j hp (by omega) hj

/-- **Recurrence for incomplete Lucas-Leonardo p-numbers.** For natural numbers $p \ge 1$,
$n > p + 1$ and $k \le \lfloor n/(p+1) \rfloor$, the incomplete Lucas-Leonardo $p$-numbers
$R_{p,m}(j)$ satisfy
$$
R_{p,n}(k + 1) = R_{p,n-1}(k + 1) + R_{p,n-p-1}(k) + p.
$$

At $n = p + 1$ the term $R_{p,0}(k)$ would contain the undefined summand
$\frac{0}{0} \binom{0}{0}$, so that case is excluded.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 17. -/
public theorem incompleteLucasLeonardoP_succ (p n k : ℕ) (hp : 1 ≤ p)
    (hn : p + 1 < n) (hk : k ≤ n / (p + 1)) :
    incompleteLucasLeonardoP p n (k + 1) =
      incompleteLucasLeonardoP p (n - 1) (k + 1) + incompleteLucasLeonardoP p (n - p - 1) k +
        p := by
  have h := congrArg (Int.cast : ℤ → ℚ) (incompleteLeonardoP_succ p n k hp (by omega) hk)
  have h' := congrArg (Int.cast : ℤ → ℚ) (incompleteLeonardoP_prev_succ p n k hp hn hk)
  push_cast at h h'
  rw [show n - 1 - p - 1 = n - p - 1 - 1 by omega] at h'
  rw [incompleteLucasLeonardoP_eq_weighted p n (k + 1) (by omega),
    incompleteLucasLeonardoP_eq_weighted p (n - 1) (k + 1) (by omega),
    incompleteLucasLeonardoP_eq_weighted p (n - p - 1) k (by omega)]
  linear_combination ((p : ℚ) + 1) * h - (p : ℚ) * h'

end MetaMathlibExt
