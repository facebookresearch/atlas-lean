/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.FareyStaircase
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Monovary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Bounds comparing the Farey staircase with `⌊nx⌋/n`

For `n ≥ 1` and `x : ℝ`, `MetaMathlibExt.fareyStaircase_le_floor_div` states that the Farey
staircase `A_n(x)` satisfies `A_n(x) ≤ ⌊nx⌋/n ≤ A_n(x) + (log n)/n`.

Statements from David Harry Richman, *Lower Rational Approximations and Farey Staircases*,
INTEGERS 24 (2024), Article A37 (primary text: arXiv:2303.02935).
-/

namespace MetaMathlibExt

@[expose] public section

private noncomputable def fgap (n : ℕ) (x : ℝ) : ℝ :=
  (⌊(n : ℝ) * x⌋ : ℝ) - ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k

private theorem fgap_add_intCast (n : ℕ) (x : ℝ) (m : ℤ) :
    fgap n (x + m) = fgap n x := by
  unfold fgap
  have hfloor : ∀ k : ℕ, ⌊(k : ℝ) * (x + m)⌋ = ⌊(k : ℝ) * x⌋ + k * m := by
    intro k
    have h1 : (k : ℝ) * (x + m) = (k : ℝ) * x + ((k : ℤ) * m : ℤ) := by
      push_cast
      ring
    rw [h1]
    rw [Int.floor_add_intCast]
  have hsum : ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * (x + m)⌋ : ℝ) / k
      = ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k + (n : ℝ) * m := by
    have hcongr : ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * (x + m)⌋ : ℝ) / k
        = ∑ k ∈ Finset.Icc (1 : ℕ) n, (((⌊(k : ℝ) * x⌋ : ℝ) / k) + ((k : ℝ) * m / k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hfloor k]
      push_cast
      rw [add_div]
    rw [hcongr, Finset.sum_add_distrib]
    congr 1
    have h2 : ∀ k ∈ Finset.Icc (1 : ℕ) n, ((k : ℝ) * m / k) = (m : ℝ) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk0 : (k : ℝ) ≠ 0 := by
        have : k ≠ 0 := by omega
        exact_mod_cast this
      field_simp
    rw [Finset.sum_congr rfl h2]
    simp [Finset.sum_const, Nat.card_Icc]
  have hfloor_n : (⌊(n : ℝ) * (x + m)⌋ : ℝ) = (⌊(n : ℝ) * x⌋ : ℝ) + (n : ℝ) * m := by
    rw [hfloor n]
    push_cast
    ring
  rw [hsum, hfloor_n]
  ring

private theorem fgap_eq_fgap_fract (n : ℕ) (x : ℝ) : fgap n x = fgap n (Int.fract x) := by
  have hx : x = Int.fract x + ⌊x⌋ := by
    have h := Int.floor_add_fract x
    linarith
  conv_lhs => rw [hx]
  exact fgap_add_intCast n (Int.fract x) ⌊x⌋

private theorem floor_eq_of_max {n d : ℕ} {x : ℝ} (hd1 : 1 ≤ d)
    (hdmax : ∀ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k ≤ (⌊(d : ℝ) * x⌋ : ℝ) / d)
    {k : ℕ} (hk : k ∈ Finset.Icc (1 : ℕ) n) :
    ⌊(k : ℝ) * ((⌊(d : ℝ) * x⌋ : ℝ) / d)⌋ = ⌊(k : ℝ) * x⌋ := by
  rw [Finset.mem_Icc] at hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  have hkpos : (0 : ℝ) < k := by
    have : (0 : ℝ) < (k : ℝ) := by
      have : (0 : ℕ) < k := by omega
      exact_mod_cast this
    exact this
  have hd0 : (d : ℝ) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast this
  have hdpos : (0 : ℝ) < d := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hx_le : (⌊(d : ℝ) * x⌋ : ℝ) / d ≤ x := by
    have h1 : (⌊(d : ℝ) * x⌋ : ℝ) ≤ (d : ℝ) * x := Int.floor_le _
    calc (⌊(d : ℝ) * x⌋ : ℝ) / d = ((⌊(d : ℝ) * x⌋ : ℝ)) / d := rfl
      _ ≤ ((d : ℝ) * x) / d := by gcongr
      _ = x := by field_simp
  have hge : (⌊(k : ℝ) * x⌋ : ℝ) / k ≤ (⌊(d : ℝ) * x⌋ : ℝ) / d :=
    hdmax k (Finset.mem_Icc.mpr hk)
  have h1 : (⌊(k : ℝ) * x⌋ : ℝ) ≤ (k : ℝ) * ((⌊(d : ℝ) * x⌋ : ℝ) / d) := by
    have h2 : (⌊(k : ℝ) * x⌋ : ℝ) / k * k ≤ ((⌊(d : ℝ) * x⌋ : ℝ) / d) * k := by
      apply mul_le_mul_of_nonneg_right hge (le_of_lt hkpos)
    rw [div_mul_cancel₀ _ hk0] at h2
    calc (⌊(k : ℝ) * x⌋ : ℝ) ≤ ((⌊(d : ℝ) * x⌋ : ℝ) / d) * k := h2
      _ = (k : ℝ) * ((⌊(d : ℝ) * x⌋ : ℝ) / d) := by ring
  have h2 : (k : ℝ) * ((⌊(d : ℝ) * x⌋ : ℝ) / d) ≤ (k : ℝ) * x := by
    apply mul_le_mul_of_nonneg_left hx_le (le_of_lt hkpos)
  apply le_antisymm
  · exact Int.floor_le_floor h2
  · rw [Int.le_floor]
    exact h1

private theorem fgap_eq_of_floor_eq {n : ℕ} {x x' : ℝ} (hn : 1 ≤ n)
    (h : ∀ k ∈ Finset.Icc (1 : ℕ) n, ⌊(k : ℝ) * x'⌋ = ⌊(k : ℝ) * x⌋) :
    fgap n x' = fgap n x := by
  unfold fgap
  have hn_mem : n ∈ Finset.Icc (1 : ℕ) n := Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
  have h_n : (⌊(n : ℝ) * x'⌋ : ℝ) = (⌊(n : ℝ) * x⌋ : ℝ) := by rw [h n hn_mem]
  have h_sum : ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x'⌋ : ℝ) / k
      = ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [h k hk]
  rw [h_n, h_sum]

private theorem xprime_mem_Ico {d : ℕ} {x : ℝ} (hd1 : 1 ≤ d) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ (⌊(d : ℝ) * x⌋ : ℝ) / d ∧ (⌊(d : ℝ) * x⌋ : ℝ) / d < 1 := by
  have hdpos : (0 : ℝ) < d := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have hdx0 : (0 : ℝ) ≤ (d : ℝ) * x := by positivity
  have hdx1 : (d : ℝ) * x < d := by
    calc (d : ℝ) * x < (d : ℝ) * 1 := by gcongr
      _ = d := by ring
  have hfl0 : (0 : ℝ) ≤ (⌊(d : ℝ) * x⌋ : ℝ) := by
    have : (0 : ℤ) ≤ ⌊(d : ℝ) * x⌋ := by
      rw [Int.le_floor]
      simpa using hdx0
    exact_mod_cast this
  have hfl1 : (⌊(d : ℝ) * x⌋ : ℝ) < d := by
    calc (⌊(d : ℝ) * x⌋ : ℝ) ≤ (d : ℝ) * x := Int.floor_le _
      _ < d := hdx1
  constructor
  · positivity
  · rw [div_lt_one hdpos]
    exact hfl1

private theorem fgap_le_of_int_mul {n m : ℕ} {x : ℝ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hint : (m : ℝ) * x = (⌊(m : ℝ) * x⌋ : ℝ))
    (ih : fgap m x ≤ ∑ k ∈ Finset.Icc (2 : ℕ) m, (1 : ℝ) / k) :
    fgap n x ≤ ∑ k ∈ Finset.Icc (2 : ℕ) n, (1 : ℝ) / k := by
  have h1le : (1 : ℕ) ≤ m + 1 := by omega
  have hm1le : m + 1 ≤ n + 1 := by omega
  have h2le : (2 : ℕ) ≤ m + 1 := by omega
  have hsplit1 : ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
      = ∑ k ∈ Finset.Icc (1 : ℕ) m, (⌊(k : ℝ) * x⌋ : ℝ) / k
        + ∑ k ∈ Finset.Icc (m + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k := by
    have h1 : Finset.Icc (1 : ℕ) n = Finset.Ico (1 : ℕ) (n + 1) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    have h2 : Finset.Icc (1 : ℕ) m = Finset.Ico (1 : ℕ) (m + 1) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    have h3 : Finset.Icc (m + 1) n = Finset.Ico (m + 1) (n + 1) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    rw [h1, h2, h3]
    exact (Finset.sum_Ico_consecutive _ h1le hm1le).symm
  have hsplit2 : ∑ k ∈ Finset.Icc (2 : ℕ) n, (1 : ℝ) / k
      = ∑ k ∈ Finset.Icc (2 : ℕ) m, (1 : ℝ) / k
        + ∑ k ∈ Finset.Icc (m + 1) n, (1 : ℝ) / k := by
    have h1 : Finset.Icc (2 : ℕ) n = Finset.Ico (2 : ℕ) (n + 1) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    have h2 : Finset.Icc (2 : ℕ) m = Finset.Ico (2 : ℕ) (m + 1) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    have h3 : Finset.Icc (m + 1) n = Finset.Ico (m + 1) (n + 1) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    rw [h1, h2, h3]
    exact (Finset.sum_Ico_consecutive _ h2le hm1le).symm
  have hfloor_eq : ⌊(n : ℝ) * x⌋ = ⌊(m : ℝ) * x⌋ + ⌊(((n - m : ℕ)) : ℝ) * x⌋ := by
    have hn_eq : (n : ℝ) = (m : ℝ) + (((n - m : ℕ)) : ℝ) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hmn]
    have hnx : (n : ℝ) * x = (⌊(m : ℝ) * x⌋ : ℝ) + (((n - m : ℕ)) : ℝ) * x := by
      linear_combination hint + x * hn_eq
    rw [hnx]
    rw [Int.floor_intCast_add]
  have hsecond : (⌊(((n - m : ℕ)) : ℝ) * x⌋ : ℝ)
      - ∑ k ∈ Finset.Icc (m + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
      ≤ ∑ k ∈ Finset.Icc (m + 1) n, (1 : ℝ) / k := by
    have h1 : ∀ k ∈ Finset.Icc (m + 1) n,
        -((⌊(k : ℝ) * x⌋ : ℝ) / k) ≤ -x + (1 : ℝ) / k := by
      intro k hk
      have hk_gt : (0 : ℝ) < k := by
        rw [Finset.mem_Icc] at hk
        have : (0 : ℕ) < k := by omega
        exact_mod_cast this
      have hfl : (k : ℝ) * x - 1 < (⌊(k : ℝ) * x⌋ : ℝ) := by
        have h := Int.lt_floor_add_one ((k : ℝ) * x)
        linarith
      have h2 : -((⌊(k : ℝ) * x⌋ : ℝ) / k) < -(((k : ℝ) * x - 1) / k) := by
        gcongr
      have h3 : -(((k : ℝ) * x - 1) / k) = -x + (1 : ℝ) / k := by
        field_simp
        ring
      linarith
    have hsum : -∑ k ∈ Finset.Icc (m + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
        ≤ -∑ k ∈ Finset.Icc (m + 1) n, x + ∑ k ∈ Finset.Icc (m + 1) n, (1 : ℝ) / k := by
      have hsum0 : ∑ k ∈ Finset.Icc (m + 1) n, (-((⌊(k : ℝ) * x⌋ : ℝ) / k))
          ≤ ∑ k ∈ Finset.Icc (m + 1) n, (-x + (1 : ℝ) / k) :=
        Finset.sum_le_sum h1
      simpa [Finset.sum_neg_distrib, Finset.sum_add_distrib] using hsum0
    have hcard : (Finset.Icc (m + 1) n).card = n - m := by
      rw [Nat.card_Icc]
      omega
    have hfloor_le : (⌊(((n - m : ℕ)) : ℝ) * x⌋ : ℝ) ≤ (((n - m : ℕ)) : ℝ) * x :=
      Int.floor_le _
    have hsum_x : ∑ k ∈ Finset.Icc (m + 1) n, x = (((n - m : ℕ)) : ℝ) * x := by
      rw [Finset.sum_const, hcard]
      simp [mul_comm]
    calc (⌊(((n - m : ℕ)) : ℝ) * x⌋ : ℝ)
          - ∑ k ∈ Finset.Icc (m + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
        ≤ (((n - m : ℕ)) : ℝ) * x
          - ∑ k ∈ Finset.Icc (m + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k := by linarith
      _ = (((n - m : ℕ)) : ℝ) * x
          + (-∑ k ∈ Finset.Icc (m + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k) := by ring
      _ ≤ (((n - m : ℕ)) : ℝ) * x
          + (-∑ k ∈ Finset.Icc (m + 1) n, x + ∑ k ∈ Finset.Icc (m + 1) n, (1 : ℝ) / k) := by
            gcongr
      _ = ∑ k ∈ Finset.Icc (m + 1) n, (1 : ℝ) / k := by
            rw [hsum_x]
            ring
  unfold fgap
  rw [hsplit1, hsplit2]
  have hfloor_cast : (⌊(n : ℝ) * x⌋ : ℝ)
      = (⌊(m : ℝ) * x⌋ : ℝ) + (⌊(((n - m : ℕ)) : ℝ) * x⌋ : ℝ) := by
    rw [hfloor_eq]
    push_cast
    ring
  rw [hfloor_cast]
  have hfgap_m : (⌊(m : ℝ) * x⌋ : ℝ) - ∑ k ∈ Finset.Icc (1 : ℕ) m, (⌊(k : ℝ) * x⌋ : ℝ) / k
      ≤ ∑ k ∈ Finset.Icc (2 : ℕ) m, (1 : ℝ) / k := ih
  linarith

private theorem fract_natCast_div_natCast {a d : ℕ} (hd0 : 0 < d) :
    Int.fract ((a : ℝ) / d) = ((a % d : ℕ) : ℝ) / d := by
  have hd0' : (d : ℝ) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast this
  have hdiv : a = d * (a / d) + a % d := (Nat.div_add_mod a d).symm
  have hmod_lt : a % d < d := Nat.mod_lt _ hd0
  have h1 : (a : ℝ) = (d : ℝ) * ((a / d : ℕ) : ℝ) + ((a % d : ℕ) : ℝ) := by
    conv_lhs => rw [hdiv]
    push_cast
    ring
  have h_eq : (a : ℝ) / d = ((a / d : ℕ) : ℝ) + ((a % d : ℕ) : ℝ) / d := by
    rw [h1]
    field_simp
  have hfrac0 : (0 : ℝ) ≤ ((a % d : ℕ) : ℝ) / d := by positivity
  have hfrac1 : ((a % d : ℕ) : ℝ) / d < 1 := by
    rw [div_lt_one (by positivity)]
    have : ((a % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmod_lt
    exact this
  rw [h_eq]
  have h_nat_int : ((a / d : ℕ) : ℝ) = ((((a / d : ℕ) : ℤ)) : ℝ) := by
    rw [Int.cast_natCast]
  rw [h_nat_int, Int.fract_intCast_add]
  exact Int.fract_eq_iff.mpr ⟨hfrac0, hfrac1, 0, by simp⟩

private theorem fgap_eq_sum_fract_of_int_mul {d : ℕ} {x : ℝ} (hd1 : 1 ≤ d)
    (hint : (d : ℝ) * x = (⌊(d : ℝ) * x⌋ : ℝ)) :
    fgap d x = ∑ k ∈ Finset.Icc (1 : ℕ) d, Int.fract ((k : ℝ) * x) / k := by
  unfold fgap
  have hcard : (Finset.Icc (1 : ℕ) d).card = d := by
    rw [Nat.card_Icc]
    omega
  have hsum_eq : ∑ k ∈ Finset.Icc (1 : ℕ) d, (⌊(k : ℝ) * x⌋ : ℝ) / k
      = (d : ℝ) * x - ∑ k ∈ Finset.Icc (1 : ℕ) d, Int.fract ((k : ℝ) * x) / k := by
    have hcongr : ∀ k ∈ Finset.Icc (1 : ℕ) d,
        (⌊(k : ℝ) * x⌋ : ℝ) / k = x - Int.fract ((k : ℝ) * x) / k := by
      intro k hk
      have hk0 : (k : ℝ) ≠ 0 := by
        rw [Finset.mem_Icc] at hk
        have : k ≠ 0 := by omega
        exact_mod_cast this
      have hfl : (⌊(k : ℝ) * x⌋ : ℝ) = (k : ℝ) * x - Int.fract ((k : ℝ) * x) := by
        have h := Int.floor_add_fract ((k : ℝ) * x)
        linarith
      rw [hfl]
      field_simp
    rw [Finset.sum_congr rfl hcongr]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_const, hcard]
    simp [mul_comm]
  rw [hsum_eq, ← hint]
  ring

private theorem sum_Icc_eq_sum_Fin {d : ℕ} (F : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) d, F k = ∑ i : Fin d, F (i.val + 1) := by
  have h_eq : Finset.Icc (1 : ℕ) d = Finset.image (fun i : Fin d => i.val + 1) Finset.univ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hk
      exact ⟨⟨k - 1, by omega⟩, Nat.sub_add_cancel hk.1⟩
    · rintro ⟨i, rfl⟩
      have hi := i.isLt
      omega
  rw [h_eq]
  rw [Finset.sum_image]
  intro a _ b _ hab
  simp only at hab
  have : a.val = b.val := by omega
  exact Fin.ext this

private theorem eq_of_mem_Icc_mod_eq {d A B : ℕ}
    (hA : A ∈ Finset.Icc (1 : ℕ) d) (hB : B ∈ Finset.Icc (1 : ℕ) d)
    (hmod : A % d = B % d) : A = B := by
  rw [Finset.mem_Icc] at hA hB
  by_cases hAd : A = d
  · by_cases hBd : B = d
    · rw [hAd, hBd]
    · have hAmod : A % d = 0 := by rw [hAd, Nat.mod_self]
      have hBmod : B % d = B := Nat.mod_eq_of_lt (by omega)
      omega
  · by_cases hBd : B = d
    · have hAmod : A % d = A := Nat.mod_eq_of_lt (by omega)
      have hBmod : B % d = 0 := by rw [hBd, Nat.mod_self]
      omega
    · have hAmod : A % d = A := Nat.mod_eq_of_lt (by omega)
      have hBmod : B % d = B := Nat.mod_eq_of_lt (by omega)
      omega

private theorem H_nat_injective {d p : ℕ} (hcop : Nat.Coprime p d) :
    Function.Injective (fun i : Fin d => ((i.val + 1) * p % d)) := by
  intro a b hab
  simp only at hab
  have ha_mem : a.val + 1 ∈ Finset.Icc (1 : ℕ) d := by
    rw [Finset.mem_Icc]
    constructor
    · omega
    · have ha_lt := a.isLt
      omega
  have hb_mem : b.val + 1 ∈ Finset.Icc (1 : ℕ) d := by
    rw [Finset.mem_Icc]
    constructor
    · omega
    · have hb_lt := b.isLt
      omega
  have hmod_eq : (a.val + 1) * p % d = (b.val + 1) * p % d := hab
  have hModeq : (a.val + 1) * p ≡ (b.val + 1) * p [MOD d] := hmod_eq
  have hgcd : Nat.gcd d p = 1 := by
    rw [Nat.gcd_comm]
    exact hcop
  have hcancel : (a.val + 1) ≡ (b.val + 1) [MOD d] :=
    Nat.ModEq.cancel_right_of_coprime hgcd hModeq
  have hmod_eq2 : (a.val + 1) % d = (b.val + 1) % d := hcancel
  have hAB : a.val + 1 = b.val + 1 :=
    eq_of_mem_Icc_mod_eq ha_mem hb_mem hmod_eq2
  have : a.val = b.val := by omega
  exact Fin.ext this

private theorem G_nat_injective {d : ℕ} :
    Function.Injective (fun i : Fin d => d - 1 - i.val) := by
  intro a b hab
  simp only at hab
  have ha_lt := a.isLt
  have hb_lt := b.isLt
  have : a.val = b.val := by omega
  exact Fin.ext this

private theorem monovary_one_div_succ_sub {d : ℕ} (hd1 : 1 ≤ d) :
    Monovary (fun i : Fin d => (1 : ℝ) / (i.val + 1))
      (fun i : Fin d => ((d - 1 - i.val : ℕ) : ℝ) / d) := by
  intro i j hij
  simp only at hij ⊢
  have hi := i.isLt
  have hj := j.isLt
  have hdpos : (0 : ℝ) < d := by
    have : (0 : ℕ) < d := by omega
    exact_mod_cast this
  have h1 : (d - 1 - i.val : ℕ) < d - 1 - j.val := by
    have h2 : ((d - 1 - i.val : ℕ) : ℝ) < ((d - 1 - j.val : ℕ) : ℝ) := by
      have h3 := (div_lt_div_iff_of_pos_right hdpos).mp hij
      exact h3
    exact_mod_cast h2
  have hji : j.val < i.val := by omega
  have hle : (j.val : ℝ) + 1 ≤ (i.val : ℝ) + 1 := by
    have : j.val + 1 ≤ i.val + 1 := by omega
    exact_mod_cast this
  have hpos : (0 : ℝ) < (j.val : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le hpos hle

private theorem sum_sub_div_eq_harmonic {d : ℕ} (hd1 : 1 ≤ d) :
    ∑ k ∈ Finset.Icc (1 : ℕ) d, (((d - k : ℕ) : ℝ) / d / k)
      = ∑ k ∈ Finset.Icc (2 : ℕ) d, (1 : ℝ) / k := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast this
  have h_eq : ∀ k ∈ Finset.Icc (1 : ℕ) d,
      (((d - k : ℕ) : ℝ) / d / k) = (1 : ℝ) / k - 1 / d := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : (k : ℝ) ≠ 0 := by
      have : k ≠ 0 := by omega
      exact_mod_cast this
    have hk_le : k ≤ d := hk.2
    have hcast : ((d - k : ℕ) : ℝ) = (d : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hk_le]
    rw [hcast]
    field_simp
  rw [Finset.sum_congr rfl h_eq]
  rw [Finset.sum_sub_distrib]
  have hcard : (Finset.Icc (1 : ℕ) d).card = d := by
    rw [Nat.card_Icc]
    omega
  have hsum_d : ∑ k ∈ Finset.Icc (1 : ℕ) d, (1 : ℝ) / d = 1 := by
    rw [Finset.sum_const, hcard]
    simp [div_eq_mul_inv]
    field_simp
  rw [hsum_d]
  have hsplit : ∑ k ∈ Finset.Icc (1 : ℕ) d, (1 : ℝ) / k
      = 1 + ∑ k ∈ Finset.Icc (2 : ℕ) d, (1 : ℝ) / k := by
    have h_eq2 : Finset.Icc (1 : ℕ) d = insert 1 (Finset.Icc (2 : ℕ) d) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [h_eq2]
    rw [Finset.sum_insert]
    · simp
    · simp
  rw [hsplit]
  ring

private theorem fgap_le_of_coprime {d p : ℕ} (hd1 : 1 ≤ d)
    (hcop : Nat.Coprime p d) :
    fgap d ((p : ℝ) / d) ≤ ∑ k ∈ Finset.Icc (2 : ℕ) d, (1 : ℝ) / k := by
  have hd0 : 0 < d := by omega
  have hd0' : (d : ℝ) ≠ 0 := by
    have : d ≠ 0 := by omega
    exact_mod_cast this
  set x' : ℝ := (p : ℝ) / d with hx'_def
  have hdx : (d : ℝ) * x' = (p : ℝ) := by
    rw [hx'_def]
    field_simp
  have hint : (d : ℝ) * x' = (⌊(d : ℝ) * x'⌋ : ℝ) := by
    rw [hdx]
    have hfloor : ⌊((p : ℕ) : ℝ)⌋ = ((p : ℕ) : ℤ) := by
      rw [← Int.cast_natCast, Int.floor_intCast]
    rw [hfloor, Int.cast_natCast]
  have hfgap_eq : fgap d x' = ∑ k ∈ Finset.Icc (1 : ℕ) d, Int.fract ((k : ℝ) * x') / k :=
    fgap_eq_sum_fract_of_int_mul hd1 hint
  have hfract_eq : ∀ k ∈ Finset.Icc (1 : ℕ) d,
      Int.fract ((k : ℝ) * x') = (((k * p % d : ℕ)) : ℝ) / d := by
    intro k hk
    have hkx : (k : ℝ) * x' = ((k * p : ℕ) : ℝ) / d := by
      rw [hx'_def]
      have h1 : (k : ℝ) * ((p : ℝ) / d) = ((k * p : ℕ) : ℝ) / d := by
        rw [Nat.cast_mul]
        field_simp
      exact h1
    rw [hkx]
    exact fract_natCast_div_natCast hd0
  rw [hfgap_eq]
  have hsum_eq : ∑ k ∈ Finset.Icc (1 : ℕ) d, Int.fract ((k : ℝ) * x') / k
      = ∑ k ∈ Finset.Icc (1 : ℕ) d, ((1 : ℝ) / k) * ((((k * p % d : ℕ)) : ℝ) / d) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hfract_eq k hk]
    ring
  rw [hsum_eq]
  have hFin_eq : ∑ k ∈ Finset.Icc (1 : ℕ) d, ((1 : ℝ) / k) * ((((k * p % d : ℕ)) : ℝ) / d)
      = ∑ i : Fin d, ((1 : ℝ) / (i.val + 1)) * ((((i.val + 1) * p % d : ℕ) : ℝ) / d) := by
    have := sum_Icc_eq_sum_Fin (d := d)
      (F := fun k => ((1 : ℝ) / k) * ((((k * p % d : ℕ)) : ℝ) / d))
    simpa using this
  rw [hFin_eq]
  have hG_mem : ∀ i : Fin d, d - 1 - i.val < d := by
    intro i
    have hi := i.isLt
    omega
  have hH_mem : ∀ i : Fin d, (i.val + 1) * p % d < d := by
    intro i
    exact Nat.mod_lt _ hd0
  set G : Fin d → Fin d := fun i => ⟨d - 1 - i.val, hG_mem i⟩ with hG_def
  set H : Fin d → Fin d := fun i => ⟨(i.val + 1) * p % d, hH_mem i⟩ with hH_def
  have hG_inj : Function.Injective G := by
    intro a b hab
    have hval : d - 1 - a.val = d - 1 - b.val := by
      have := congrArg Fin.val hab
      simpa [hG_def] using this
    exact G_nat_injective hval
  have hH_inj : Function.Injective H := by
    intro a b hab
    have hval : (a.val + 1) * p % d = (b.val + 1) * p % d := by
      have := congrArg Fin.val hab
      simpa [hH_def] using this
    exact H_nat_injective hcop hval
  have hG_bij : Function.Bijective G := (Finite.injective_iff_bijective).mp hG_inj
  have hH_bij : Function.Bijective H := (Finite.injective_iff_bijective).mp hH_inj
  set eG : Equiv.Perm (Fin d) := Equiv.ofBijective G hG_bij with heG_def
  set eH : Equiv.Perm (Fin d) := Equiv.ofBijective H hH_bij with heH_def
  set σ : Equiv.Perm (Fin d) := eH.trans eG.symm with hσ_def
  set f : Fin d → ℝ := fun i => (1 : ℝ) / (i.val + 1) with hf_def
  set g : Fin d → ℝ := fun i => ((d - 1 - i.val : ℕ) : ℝ) / d with hg_def
  set h : Fin d → ℝ := fun i => ((((i.val + 1) * p % d : ℕ)) : ℝ) / d with hh_def
  have hmono : Monovary f g := monovary_one_div_succ_sub hd1
  have hGH : ∀ i : Fin d, G (σ i) = H i := by
    intro i
    have h1 : σ i = eG.symm (H i) := by
      rw [hσ_def]
      simp [heH_def, heG_def]
    rw [h1]
    have h2 : eG.symm (H i) = (Equiv.ofBijective G hG_bij).symm (H i) := by rw [heG_def]
    rw [h2]
    exact Equiv.ofBijective_apply_symm_apply G hG_bij (H i)
  have h_eq : ∀ i : Fin d, h i = g (σ i) := by
    intro i
    have hval : (G (σ i)).val = (H i).val := congrArg Fin.val (hGH i)
    simp only [hh_def, hg_def, hG_def, hH_def] at hval ⊢
    rw [hval]
  have hrearr : ∑ i : Fin d, f i * h i ≤ ∑ i : Fin d, f i * g i := by
    have h1 : ∑ i : Fin d, f i * h i = ∑ i : Fin d, f i * g (σ i) := by
      apply Fintype.sum_congr
      intro i
      rw [h_eq i]
    rw [h1]
    exact Monovary.sum_mul_comp_perm_le_sum_mul hmono
  have hgoal_eq : ∑ i : Fin d, f i * h i
      = ∑ i : Fin d, ((1 : ℝ) / (i.val + 1)) * ((((i.val + 1) * p % d : ℕ) : ℝ) / d) := rfl
  have hmax_eq : ∑ i : Fin d, f i * g i = ∑ k ∈ Finset.Icc (2 : ℕ) d, (1 : ℝ) / k := by
    have h1 : ∀ i : Fin d, f i * g i
        = (fun k : ℕ => (((d - k : ℕ) : ℝ) / d / k)) (i.val + 1) := by
      intro i
      have hi := i.isLt
      have hsub : d - (i.val + 1) = d - 1 - i.val := by omega
      have hcast : (((i.val + 1 : ℕ)) : ℝ) = (i.val : ℝ) + 1 := by push_cast; ring
      simp only [hf_def, hg_def]
      rw [← hcast, hsub]
      ring
    have h2 : ∑ i : Fin d, f i * g i
        = ∑ k ∈ Finset.Icc (1 : ℕ) d, (((d - k : ℕ) : ℝ) / d / k) := by
      have h3 : ∑ i : Fin d, f i * g i
          = ∑ i : Fin d, (fun k : ℕ => (((d - k : ℕ) : ℝ) / d / k)) (i.val + 1) := by
        apply Fintype.sum_congr
        intro i
        exact h1 i
      rw [h3]
      have h4 := sum_Icc_eq_sum_Fin (d := d)
        (F := fun k : ℕ => (((d - k : ℕ) : ℝ) / d / k))
      rw [h4]
    rw [h2]
    exact sum_sub_div_eq_harmonic hd1
  rw [← hgoal_eq] at hrearr ⊢
  rw [hmax_eq] at hrearr
  exact hrearr

private theorem sum_floor_div_le_floor (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k ≤ (⌊(n : ℝ) * x⌋ : ℝ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · simp [hn]
    · by_cases hn1 : n = 1
      · simp [hn1]
      · have hn2 : 2 ≤ n := by omega
        have hne : (Finset.Icc (1 : ℕ) n).Nonempty :=
          Finset.nonempty_Icc.mpr (by omega)
        obtain ⟨d, hd_mem, hd_max⟩ :=
          Finset.exists_max_image (Finset.Icc (1 : ℕ) n)
            (fun k => (⌊(k : ℝ) * x⌋ : ℝ) / k) hne
        rw [Finset.mem_Icc] at hd_mem
        have hd1 : 1 ≤ d := hd_mem.1
        have hdn : d ≤ n := hd_mem.2
        have hd0 : d ≠ 0 := by omega
        have hsplit : ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
            = ∑ k ∈ Finset.Icc (1 : ℕ) (n - d), (⌊(k : ℝ) * x⌋ : ℝ) / k
              + ∑ k ∈ Finset.Icc (n - d + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k := by
          have h1 : Finset.Icc (1 : ℕ) n = Finset.Ico (1 : ℕ) (n + 1) := by
            rw [Finset.Ico_add_one_right_eq_Icc]
          have h2 : Finset.Icc (1 : ℕ) (n - d) = Finset.Ico (1 : ℕ) (n - d + 1) := by
            rw [Finset.Ico_add_one_right_eq_Icc]
          have h3 : Finset.Icc (n - d + 1) n = Finset.Ico (n - d + 1) (n + 1) := by
            rw [Finset.Ico_add_one_right_eq_Icc]
          rw [h1, h2, h3]
          have hle1 : 1 ≤ n - d + 1 := by omega
          have hle2 : n - d + 1 ≤ n + 1 := by omega
          exact (Finset.sum_Ico_consecutive _ hle1 hle2).symm
        rw [hsplit]
        have hfirst : ∑ k ∈ Finset.Icc (1 : ℕ) (n - d), (⌊(k : ℝ) * x⌋ : ℝ) / k
            ≤ (⌊(((n - d : ℕ)) : ℝ) * x⌋ : ℝ) := by
          by_cases h0 : n - d = 0
          · simp [h0]
          · exact ih (n - d) (by omega)
        have hsecond : ∑ k ∈ Finset.Icc (n - d + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
            ≤ (⌊(d : ℝ) * x⌋ : ℝ) := by
          have hcard : (Finset.Icc (n - d + 1) n).card = d := by
            rw [Nat.card_Icc]
            omega
          calc ∑ k ∈ Finset.Icc (n - d + 1) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
              ≤ ∑ k ∈ Finset.Icc (n - d + 1) n, (⌊(d : ℝ) * x⌋ : ℝ) / d := by
                apply Finset.sum_le_sum
                intro k hk
                rw [Finset.mem_Icc] at hk
                have hk_mem : k ∈ Finset.Icc (1 : ℕ) n :=
                  Finset.mem_Icc.mpr ⟨by omega, hk.2⟩
                exact hd_max k hk_mem
            _ = (⌊(d : ℝ) * x⌋ : ℝ) := by
                rw [Finset.sum_const, hcard]
                simp [div_eq_mul_inv]
                field_simp
        have hfloor : (⌊(((n - d : ℕ)) : ℝ) * x⌋ : ℝ) + (⌊(d : ℝ) * x⌋ : ℝ)
            ≤ (⌊(n : ℝ) * x⌋ : ℝ) := by
          have h1 : ((n : ℝ) * x) = (((n - d : ℕ)) : ℝ) * x + (d : ℝ) * x := by
            have hn_eq : (n : ℝ) = (((n - d : ℕ)) : ℝ) + (d : ℝ) := by
              rw [← Nat.cast_add, Nat.sub_add_cancel hdn]
            rw [hn_eq]
            ring
          have h2 : ⌊(((n - d : ℕ)) : ℝ) * x⌋ + ⌊(d : ℝ) * x⌋ ≤ ⌊(n : ℝ) * x⌋ := by
            rw [h1]
            exact Int.le_floor_add _ _
          exact_mod_cast h2
        linarith

private theorem harmonic_Icc_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc (2 : ℕ) n, (1 : ℝ) / k ≤ Real.log n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h2le : (2 : ℕ) ≤ n + 1 := by omega
    have hsplit : ∑ k ∈ Finset.Icc (2 : ℕ) (n + 1), (1 : ℝ) / k
        = ∑ k ∈ Finset.Icc (2 : ℕ) n, (1 : ℝ) / k + (1 : ℝ) / ((n : ℝ) + 1) := by
      rw [Finset.sum_Icc_succ_top h2le]
      congr 1
      congr 1
      norm_cast
    rw [hsplit]
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < ((n : ℝ)) / ((n : ℝ) + 1) := by positivity
      have hlog : Real.log (((n : ℝ)) / ((n : ℝ) + 1)) ≤ (((n : ℝ) / ((n : ℝ) + 1)) - 1) :=
        Real.log_le_sub_one_of_pos hpos
      have hdiv : ((n : ℝ) / ((n : ℝ) + 1)) - 1 = - ((1 : ℝ) / ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [hdiv] at hlog
      have hlog2 : Real.log (((n : ℝ)) / ((n : ℝ) + 1))
          = Real.log n - Real.log ((n : ℝ) + 1) := by
        rw [Real.log_div (by positivity) (by positivity)]
      rw [hlog2] at hlog
      linarith
    have hlog_cast : Real.log ((n + 1 : ℕ) : ℝ) = Real.log ((n : ℝ) + 1) := by
      congr 1
      norm_cast
    rw [hlog_cast]
    linarith

private theorem fgap_le_harmonic_of_mem_Ico (n : ℕ) :
    ∀ x : ℝ, 0 ≤ x → x < 1 → fgap n x ≤ ∑ k ∈ Finset.Icc (2 : ℕ) n, (1 : ℝ) / k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx0 hx1
    by_cases hn0 : n = 0
    · simp [fgap, hn0]
    · by_cases hn1 : n = 1
      · simp [fgap, hn1]
      · have hn2 : 2 ≤ n := by omega
        have hn1' : 1 ≤ n := by omega
        have hne : (Finset.Icc (1 : ℕ) n).Nonempty :=
          Finset.nonempty_Icc.mpr hn1'
        obtain ⟨d, hd_mem, hd_max⟩ :=
          Finset.exists_max_image (Finset.Icc (1 : ℕ) n)
            (fun k => (⌊(k : ℝ) * x⌋ : ℝ) / k) hne
        rw [Finset.mem_Icc] at hd_mem
        have hd1 : 1 ≤ d := hd_mem.1
        have hdn : d ≤ n := hd_mem.2
        set x' : ℝ := (⌊(d : ℝ) * x⌋ : ℝ) / d with hx'_def
        have hfloor_eq : ∀ k ∈ Finset.Icc (1 : ℕ) n, ⌊(k : ℝ) * x'⌋ = ⌊(k : ℝ) * x⌋ :=
          fun k hk => floor_eq_of_max hd1 hd_max hk
        have hfgap_eq : fgap n x = fgap n x' := by
          have h := fgap_eq_of_floor_eq hn1' hfloor_eq
          exact h.symm
        have hx'_mem := xprime_mem_Ico hd1 hx0 hx1
        have hd_int : (d : ℝ) * x' = (⌊(d : ℝ) * x'⌋ : ℝ) := by
          have hd_mem' : d ∈ Finset.Icc (1 : ℕ) n := Finset.mem_Icc.mpr ⟨hd1, hdn⟩
          have hdd : ⌊(d : ℝ) * x'⌋ = ⌊(d : ℝ) * x⌋ := hfloor_eq d hd_mem'
          have hdx' : (d : ℝ) * x' = (⌊(d : ℝ) * x⌋ : ℝ) := by
            rw [hx'_def]
            have hd0 : (d : ℝ) ≠ 0 := by
              have : d ≠ 0 := by omega
              exact_mod_cast this
            field_simp
          conv_lhs => rw [hdx']
          rw [← hdd]
        rw [hfgap_eq]
        by_cases hdn_eq : d = n
        · -- d = n case: rewrite goal to d
          rw [← hdn_eq]
          have hdx0 : (0 : ℝ) ≤ (d : ℝ) * x := by positivity
          have hdx1 : (d : ℝ) * x < d := by
            calc (d : ℝ) * x < (d : ℝ) * 1 := by gcongr
              _ = d := by ring
          have hp0 : (0 : ℤ) ≤ ⌊(d : ℝ) * x⌋ := by
            rw [Int.le_floor]
            simpa using hdx0
          have hpd : (⌊(d : ℝ) * x⌋ : ℝ) < d := by
            calc (⌊(d : ℝ) * x⌋ : ℝ) ≤ (d : ℝ) * x := Int.floor_le _
              _ < d := hdx1
          set p : ℕ := (⌊(d : ℝ) * x⌋).toNat with hp_def
          have hp_eq : (⌊(d : ℝ) * x⌋ : ℝ) = (p : ℝ) := by
            rw [hp_def]
            exact_mod_cast (Int.toNat_of_nonneg hp0).symm
          have hp_lt : p < d := by
            have : (p : ℝ) < d := by rw [← hp_eq]; exact hpd
            exact_mod_cast this
          have hx'_eq : x' = (p : ℝ) / d := by
            rw [hx'_def]
            rw [hp_eq]
          set g : ℕ := Nat.gcd p d with hg_def
          have hg_pos : 1 ≤ g := by
            have hg_dvd : g ∣ d := Nat.gcd_dvd_right p d
            have hd_pos : 0 < d := by omega
            have hg_ne0 : g ≠ 0 := by
              intro hg0
              rw [hg0] at hg_dvd
              rw [zero_dvd_iff] at hg_dvd
              omega
            omega
          by_cases hg1 : g = 1
          · have hcop : Nat.Coprime p d := hg_def.symm.trans hg1
            rw [hx'_eq]
            exact fgap_le_of_coprime hd1 hcop
          · have hg_gt : 1 < g := by omega
            set m : ℕ := d / g with hm_def
            have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right p d
            have hg_dvd_p : g ∣ p := Nat.gcd_dvd_left p d
            have hm_lt : m < d := by
              rw [hm_def]
              exact Nat.div_lt_self (by omega) hg_gt
            have hm1 : 1 ≤ m := by
              have h1 : g * (d / g) = d := Nat.mul_div_cancel' hg_dvd_d
              have h2 : d / g ≠ 0 := by
                intro h0
                rw [h0, mul_zero] at h1
                omega
              rw [hm_def]
              exact Nat.pos_of_ne_zero h2
            have hm_le : m ≤ d := by omega
            have hm_int : (m : ℝ) * x' = (⌊(m : ℝ) * x'⌋ : ℝ) := by
              have hd0 : (d : ℝ) ≠ 0 := by
                have : d ≠ 0 := by omega
                exact_mod_cast this
              have hg0 : (g : ℝ) ≠ 0 := by
                have : g ≠ 0 := by omega
                exact_mod_cast this
              have hd_nat : g * (d / g) = d := Nat.mul_div_cancel' hg_dvd_d
              have hp_nat : g * (p / g) = p := Nat.mul_div_cancel' hg_dvd_p
              have hd_real : (g : ℝ) * (d / g : ℕ) = (d : ℝ) := by exact_mod_cast hd_nat
              have hp_real : (g : ℝ) * (p / g : ℕ) = (p : ℝ) := by exact_mod_cast hp_nat
              have h_eq : (m : ℝ) * x' = ((p / g : ℕ) : ℝ) := by
                rw [hx'_eq, hm_def]
                field_simp
                linear_combination (p / g : ℕ) * hd_real - (d / g : ℕ) * hp_real
              rw [h_eq]
              have hfloor : ⌊(((p / g : ℕ)) : ℝ)⌋ = ((p / g : ℕ) : ℤ) := by
                rw [← Int.cast_natCast, Int.floor_intCast]
              rw [hfloor, Int.cast_natCast]
            have hm_lt_n : m < n := by omega
            have ih_m := ih m hm_lt_n x' hx'_mem.1 hx'_mem.2
            exact fgap_le_of_int_mul hm1 hm_le hm_int ih_m
        · have hd_lt : d < n := by omega
          have ih_d := ih d hd_lt x' hx'_mem.1 hx'_mem.2
          exact fgap_le_of_int_mul hd1 hdn hd_int ih_d

private theorem fgap_le_harmonic (n : ℕ) (x : ℝ) :
    fgap n x ≤ ∑ k ∈ Finset.Icc (2 : ℕ) n, (1 : ℝ) / k := by
  rw [fgap_eq_fgap_fract n x]
  exact fgap_le_harmonic_of_mem_Ico n (Int.fract x) (Int.fract_nonneg _) (Int.fract_lt_one _)

private theorem fgap_le_log {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    fgap n x ≤ Real.log n := by
  calc fgap n x ≤ ∑ k ∈ Finset.Icc (2 : ℕ) n, (1 : ℝ) / k := fgap_le_harmonic n x
    _ ≤ Real.log n := harmonic_Icc_le_log n hn

/-- **Bounds comparing the Farey staircase with $\lfloor nx \rfloor / n$.** For every natural
number $n \ge 1$ and every real number $x$, the Farey staircase $A_n$ of order $n$ satisfies
$A_n(x) \le \lfloor nx \rfloor / n \le A_n(x) + (\log n)/n$, where $\log$ is the natural
logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (a) (`integers-2024-A37-lem-8`). -/
public theorem fareyStaircase_le_floor_div {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    fareyStaircase n x ≤ ⌊(n : ℝ) * x⌋ / n ∧
      (⌊(n : ℝ) * x⌋ : ℝ) / n ≤ fareyStaircase n x + Real.log n / n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hsum_le : ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k ≤ (⌊(n : ℝ) * x⌋ : ℝ) :=
    sum_floor_div_le_floor n x
  have hfgap_le : (⌊(n : ℝ) * x⌋ : ℝ) - ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k
      ≤ Real.log n := fgap_le_log hn x
  have hlower : fareyStaircase n x ≤ ⌊(n : ℝ) * x⌋ / n := by
    unfold fareyStaircase
    have h1 : (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k
        ≤ (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ : ℝ) :=
      mul_le_mul_of_nonneg_left hsum_le hn_nonneg
    have h2 : (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ : ℝ) = ⌊(n : ℝ) * x⌋ / n := by
      rw [div_eq_mul_inv, mul_comm]
    calc (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k
        ≤ (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ : ℝ) := h1
      _ = ⌊(n : ℝ) * x⌋ / n := h2
  have hupper : (⌊(n : ℝ) * x⌋ : ℝ) / n ≤ fareyStaircase n x + Real.log n / n := by
    unfold fareyStaircase
    have h1 : (⌊(n : ℝ) * x⌋ : ℝ) ≤ ∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k + Real.log n := by
      linarith
    have h2 : (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ : ℝ)
        ≤ (n : ℝ)⁻¹ * (∑ k ∈ Finset.Icc (1 : ℕ) n, (⌊(k : ℝ) * x⌋ : ℝ) / k + Real.log n) :=
      mul_le_mul_of_nonneg_left h1 hn_nonneg
    rw [mul_add] at h2
    have h3 : (⌊(n : ℝ) * x⌋ : ℝ) / n = (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ : ℝ) := by
      rw [div_eq_mul_inv, mul_comm]
    have h4 : Real.log n / n = (n : ℝ)⁻¹ * Real.log n := by
      rw [div_eq_mul_inv, mul_comm]
    rw [h3, h4]
    exact h2
  exact ⟨hlower, hupper⟩

end

end MetaMathlibExt
