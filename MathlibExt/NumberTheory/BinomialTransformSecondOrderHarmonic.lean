/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace MetaMathlibExt

private theorem key_prod (s : ℂ) (n m : ℕ) :
    (Finset.range (m + 1)).prod (fun j => s + (n : ℂ) - (j : ℂ))
      = (s + (n : ℂ)) * (Finset.range m).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ)) := by
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring

private theorem partial_alt_sum (s : ℂ) (n m : ℕ) :
    (∑ k ∈ Finset.Icc 0 m,
      (-1 : ℂ) ^ k * ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ)) / (Nat.factorial k : ℂ)))
      = (-1 : ℂ) ^ m * ((Finset.range m).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ)) / (Nat.factorial m : ℂ)) := by
  induction m with
  | zero =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ m + 1)
      (fun k => (-1 : ℂ) ^ k * ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ)) / (Nat.factorial k : ℂ)))]
    rw [ih, key_prod s n m]
    have hB : (Finset.range (m + 1)).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ))
        = ((Finset.range m).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ))) * (s + (n : ℂ) - 1 - (m : ℂ)) := by
      exact Finset.prod_range_succ (fun j => s + (n : ℂ) - 1 - (j : ℂ)) m
    rw [hB, Nat.factorial_succ]
    push_cast
    have hfact : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    rw [pow_succ]
    field_simp
    ring

private theorem tri_swap (a b : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, a k * (∑ j ∈ Finset.Icc 1 k, b j))
      = ∑ j ∈ Finset.Icc 1 n, b j * (∑ k ∈ Finset.Icc j n, a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpeel : ∀ (f : ℕ → ℂ), (∑ k ∈ Finset.Icc 1 (n + 1), f k)
        = (∑ k ∈ Finset.Icc 1 n, f k) + f (n + 1) :=
      fun f => Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1) f
    rw [hpeel (fun k => a k * (∑ j ∈ Finset.Icc 1 k, b j))]
    rw [hpeel (fun j => b j * (∑ k ∈ Finset.Icc j (n + 1), a k))]
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hinner : ∀ j ∈ Finset.Icc 1 n,
        (∑ k ∈ Finset.Icc j (n + 1), a k) = (∑ k ∈ Finset.Icc j n, a k) + a (n + 1) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      exact Finset.sum_Icc_succ_top (by omega : j ≤ n + 1) a
    have hsum : (∑ j ∈ Finset.Icc 1 n, b j * (∑ k ∈ Finset.Icc j (n + 1), a k))
        = (∑ j ∈ Finset.Icc 1 n, b j * (∑ k ∈ Finset.Icc j n, a k))
          + (∑ j ∈ Finset.Icc 1 n, b j) * a (n + 1) := by
      trans ∑ j ∈ Finset.Icc 1 n, (b j * (∑ k ∈ Finset.Icc j n, a k) + b j * a (n + 1))
      · exact Finset.sum_congr rfl (fun j hj => by rw [hinner j hj, mul_add])
      · rw [Finset.sum_add_distrib, Finset.sum_mul]
    rw [hsum, hpeel b, ih]
    ring

private theorem icc_split (a : ℕ → ℂ) (j n : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (∑ k ∈ Finset.Icc j n, a k) + (∑ k ∈ Finset.Icc 0 (j - 1), a k)
      = ∑ k ∈ Finset.Icc 0 n, a k := by
  have e1 : Finset.Icc j n = Finset.Ico j (n + 1) := (Finset.Ico_add_one_right_eq_Icc j n).symm
  have e2 : Finset.Icc 0 (j - 1) = Finset.Ico 0 j := by
    have : j - 1 + 1 = j := by omega
    rw [← this]
    exact (Finset.Ico_add_one_right_eq_Icc 0 (j - 1)).symm
  have e3 : Finset.Icc 0 n = Finset.Ico 0 (n + 1) := (Finset.Ico_add_one_right_eq_Icc 0 n).symm
  rw [e1, e2, e3, add_comm]
  exact Finset.sum_Ico_consecutive a (by omega : 0 ≤ j) (by omega : j ≤ n + 1)

private theorem add_ne_zero_of_hs (s : ℂ) (n : ℕ) (hn : 0 < n)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) : s + (n : ℂ) ≠ 0 := by
  have hns := hs (n - 1)
  have hn1 : n = (n - 1) + 1 := by omega
  rw [hn1] at hns ⊢
  push_cast at hns ⊢
  intro h
  apply hns
  linear_combination h

private theorem ratio_term (s : ℂ) (n j : ℕ) (hsn : s + (n : ℂ) ≠ 0) (hj : 1 ≤ j) :
    (1 : ℂ) / (j : ℂ) ^ 2 * ((-1 : ℂ) ^ (j - 1) *
      ((Finset.range (j - 1)).prod (fun i => s + (n : ℂ) - 1 - (i : ℂ)) / ((Nat.factorial (j - 1) : ℕ) : ℂ)))
    = 1 / (s + (n : ℂ)) * ((-1 : ℂ) ^ (j - 1) *
      (((Finset.range j).prod (fun i => s + (n : ℂ) - (i : ℂ))) / ((Nat.factorial j : ℕ) : ℂ)) / (j : ℂ)) := by
  have hkey := key_prod s n (j - 1)
  rw [Nat.sub_add_cancel hj] at hkey
  have hB : (Finset.range (j - 1)).prod (fun i => s + (n : ℂ) - 1 - (i : ℂ))
      = ((Finset.range j).prod (fun i => s + (n : ℂ) - (i : ℂ))) / (s + (n : ℂ)) := by
    rw [eq_div_iff hsn]
    linear_combination -hkey
  rw [hB]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have es : t.succ = t + 1 := rfl
  rw [es, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hfact : ((Nat.factorial t : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero t)
  have ht1 : ((t : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero t
  field_simp

private theorem alt_sum_range_choose_eq_zero (m : ℕ) (hm : m ≠ 0) :
    (∑ u ∈ Finset.range (m + 1), (-1 : ℂ) ^ u * ((m.choose u : ℕ) : ℂ)) = 0 := by
  have h := Int.alternating_sum_range_choose_of_ne hm
  exact_mod_cast h

private theorem alt_tail_eq_one (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * (((n + 1).choose (i + 1) : ℕ) : ℂ)) = 1 := by
  have hfull := alt_sum_range_choose_eq_zero (n + 1) (by omega : n + 1 ≠ 0)
  rw [Finset.sum_range_succ'] at hfull
  have h0 : (-1 : ℂ) ^ (0 : ℕ) * ((((n + 1).choose 0 : ℕ)) : ℂ) = 1 := by simp
  rw [h0] at hfull
  have h2 : (∑ u ∈ Finset.range (n + 1), (-1 : ℂ) ^ (u + 1) * (((n + 1).choose (u + 1) : ℕ) : ℂ))
      + (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * (((n + 1).choose (i + 1) : ℕ) : ℂ)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro u _
    rw [pow_succ]
    ring
  linear_combination h2 - hfull

private theorem second_piece (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 (n + 1), (-1 : ℂ) ^ (j - 1) * ((n.choose (j - 1) : ℕ) : ℂ) / (j : ℂ))
      = 1 / ((n : ℂ) + 1) := by
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← Finset.Ico_add_one_right_eq_Icc 1 (n + 1), Finset.sum_Ico_eq_sum_range]
  have e1 : n + 1 + 1 - 1 = n + 1 := by omega
  rw [e1]
  have habs : ∀ i ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ (1 + i - 1) * ((n.choose (1 + i - 1) : ℕ) : ℂ) / ((1 : ℕ) + i : ℕ)
        = (1 / ((n : ℂ) + 1)) * ((-1 : ℂ) ^ i * (((n + 1).choose (i + 1) : ℕ) : ℂ)) := by
    intro i _
    have e2 : 1 + i - 1 = i := by omega
    rw [e2]
    have hcast : ((1 : ℕ) + i : ℕ) = ((i : ℂ) + 1) := by push_cast; ring
    rw [hcast]
    have hi1 : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    have hnat := Nat.add_one_mul_choose_eq n i
    have hnatC := congrArg (Nat.cast : ℕ → ℂ) hnat
    push_cast at hnatC
    field_simp
    linear_combination hnatC
  rw [Finset.sum_congr rfl habs, ← Finset.mul_sum, alt_tail_eq_one, mul_one]

private theorem classical_order_one (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Icc 1 N, (-1 : ℂ) ^ (j - 1) * ((N.choose j : ℕ) : ℂ) / (j : ℂ))
      = ∑ i ∈ Finset.Icc 1 N, (1 : ℂ) / (i : ℂ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    norm_num [Nat.choose_self]
  | succ n hn ih =>
    have hpascal : ∀ j ∈ Finset.Icc 1 (n + 1),
        ((n + 1).choose j : ℂ) = ((n.choose j : ℕ) : ℂ) + ((n.choose (j - 1) : ℕ) : ℂ) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have e : t.succ - 1 = t := by omega
      rw [e, show n + 1 = n.succ from rfl]
      have h := Nat.choose_succ_succ n t
      have hC := congrArg (Nat.cast : ℕ → ℂ) h
      push_cast at hC
      linear_combination hC
    have hsplit : (∑ j ∈ Finset.Icc 1 (n + 1),
          (-1 : ℂ) ^ (j - 1) * (((n + 1).choose j : ℕ) : ℂ) / (j : ℂ))
        = (∑ j ∈ Finset.Icc 1 (n + 1), (-1 : ℂ) ^ (j - 1) * ((n.choose j : ℕ) : ℂ) / (j : ℂ))
          + (∑ j ∈ Finset.Icc 1 (n + 1), (-1 : ℂ) ^ (j - 1) * ((n.choose (j - 1) : ℕ) : ℂ) / (j : ℂ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hpascal j hj]
      ring
    have hfirst : (∑ j ∈ Finset.Icc 1 (n + 1), (-1 : ℂ) ^ (j - 1) * ((n.choose j : ℕ) : ℂ) / (j : ℂ))
        = ∑ i ∈ Finset.Icc 1 n, (1 : ℂ) / (i : ℂ) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hz : (-1 : ℂ) ^ (n + 1 - 1) * ((n.choose (n + 1) : ℕ) : ℂ) / ((n + 1 : ℕ) : ℂ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt (by omega : n < n + 1)]
        simp
      rw [hz, add_zero]
      exact ih
    have hRHS : (∑ i ∈ Finset.Icc 1 (n + 1), (1 : ℂ) / (i : ℂ))
        = (∑ i ∈ Finset.Icc 1 n, (1 : ℂ) / (i : ℂ)) + 1 / ((n : ℂ) + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have e : ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
      rw [e]
    rw [hsplit, second_piece, hfirst, hRHS, add_comm]

private theorem hockey (r t : ℕ) :
    (∑ j ∈ Finset.range (t + 1), (((r + j).choose j : ℕ) : ℂ))
      = (((r + t + 1).choose t : ℕ) : ℂ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    have h := Nat.choose_succ_succ (r + t + 1) t
    exact_mod_cast h.symm

private theorem icc1_to_range (t : ℕ) (g : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 t, g k) = ∑ i ∈ Finset.range t, g (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 t, Finset.sum_Ico_eq_sum_range]
  have e : t + 1 - 1 = t := by omega
  rw [e]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm 1 i]

private theorem m_sum_eq (n t : ℕ) (_h1 : 1 ≤ t) (htn : t + 1 ≤ n) :
    (∑ k ∈ Finset.Icc 1 t, (((n - k).choose (t - k) : ℕ) : ℂ) / ((t + 1 - k : ℕ) : ℂ))
      = ((((n.choose t : ℕ)) : ℂ) - 1) / ((n : ℂ) - (t : ℂ)) := by
  have hntC : ((n : ℂ) - (t : ℂ)) ≠ 0 := by
    have hne : ((n - t : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have e : ((n - t : ℕ) : ℂ) = (n : ℂ) - (t : ℂ) := Nat.cast_sub (by omega : t ≤ n)
    rw [e] at hne
    exact hne
  rw [icc1_to_range]
  have term_simp : ∀ i ∈ Finset.range t,
      ((((n - (t - 1 - i + 1)).choose (t - (t - 1 - i + 1)) : ℕ)) : ℂ)
        / (((t + 1 - (t - 1 - i + 1) : ℕ)) : ℂ)
      = ((((n - t + i).choose i : ℕ)) : ℂ) / (((i + 1 : ℕ)) : ℂ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e1 : n - (t - 1 - i + 1) = n - t + i := by omega
    have e2 : t - (t - 1 - i + 1) = i := by omega
    have e3 : t + 1 - (t - 1 - i + 1) = i + 1 := by omega
    rw [e1, e2, e3]
  rw [← Finset.sum_range_reflect]
  rw [Finset.sum_congr rfl term_simp]
  have term_abs : ∀ i ∈ Finset.range t,
      ((((n - t + i).choose i : ℕ)) : ℂ) / (((i + 1 : ℕ)) : ℂ)
      = (1 / ((n : ℂ) - (t : ℂ))) * ((((n - t + i).choose (i + 1) : ℕ)) : ℂ) := by
    intro i _
    have hi1 : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    have hnat := Nat.choose_succ_right_eq (n - t + i) i
    have eAi : n - t + i - i = n - t := by omega
    rw [eAi] at hnat
    have hnatC := congrArg (Nat.cast : ℕ → ℂ) hnat
    push_cast at hnatC
    have ecast : ((n - t : ℕ) : ℂ) = (n : ℂ) - (t : ℂ) := Nat.cast_sub (by omega : t ≤ n)
    rw [ecast] at hnatC
    have ecast2 : ((i + 1 : ℕ) : ℂ) = (i : ℂ) + 1 := by push_cast; ring
    rw [ecast2, div_mul_eq_mul_div, one_mul, div_eq_div_iff hi1 hntC]
    linear_combination -hnatC
  rw [Finset.sum_congr rfl term_abs, ← Finset.mul_sum]
  have h5 : (∑ i ∈ Finset.range t, ((((n - t + i).choose (i + 1) : ℕ)) : ℂ))
      = (((n.choose t : ℕ)) : ℂ) - 1 := by
    have hh := hockey (n - t - 1) t
    have en : n - t - 1 + t + 1 = n := by omega
    rw [en] at hh
    rw [Finset.sum_range_succ'] at hh
    simp only [add_zero, Nat.choose_zero_right, Nat.cast_one] at hh
    have hcast : ∀ j ∈ Finset.range t,
        ((((n - t - 1 + (j + 1)).choose (j + 1) : ℕ)) : ℂ)
          = ((((n - t + j).choose (j + 1) : ℕ)) : ℂ) := by
      intro j _
      have e : n - t - 1 + (j + 1) = n - t + j := by omega
      rw [e]
    rw [Finset.sum_congr rfl hcast] at hh
    linear_combination hh
  rw [h5]
  ring

private theorem sum_Icc_succ_left (f : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Icc a b, f i) = f a + ∑ i ∈ Finset.Icc (a + 1) b, f i := by
  have hset : Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hside : a ∉ Finset.Icc (a + 1) b := by
    rw [Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert hside]

private theorem t_identity_base (n : ℕ) (h1n : 1 ≤ n) :
    (∑ k ∈ Finset.Icc 1 1, (((n - k).choose (1 - k) : ℕ) : ℂ) / (k : ℂ))
      = (((n.choose 1 : ℕ)) : ℂ) * (∑ i ∈ Finset.Icc (n - 1 + 1) n, (1 : ℂ) / (i : ℂ)) := by
  have e : n - 1 + 1 = n := by omega
  have e0 : (1 : ℕ) - 1 = 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Finset.Icc_self, Finset.sum_singleton, e0, Nat.choose_zero_right,
    e, Finset.Icc_self, Finset.sum_singleton, Nat.choose_one_right]
  simp only [Nat.cast_one, div_one, mul_one_div_cancel hnC]

private theorem t_identity_step (n t : ℕ) (h1 : 1 ≤ t) (htn : t + 1 ≤ n)
    (ih : (∑ k ∈ Finset.Icc 1 t, (((n - k).choose (t - k) : ℕ) : ℂ) / (k : ℂ))
      = (((n.choose t : ℕ)) : ℂ) * (∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ))) :
    (∑ k ∈ Finset.Icc 1 (t + 1), (((n - k).choose (t + 1 - k) : ℕ) : ℂ) / (k : ℂ))
      = (((n.choose (t + 1) : ℕ)) : ℂ)
        * (∑ i ∈ Finset.Icc (n - (t + 1) + 1) n, (1 : ℂ) / (i : ℂ)) := by
  have hntC : ((n : ℂ) - (t : ℂ)) ≠ 0 := by
    have hne : ((n - t : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have e : ((n - t : ℕ) : ℂ) = (n : ℂ) - (t : ℂ) := Nat.cast_sub (by omega : t ≤ n)
    rw [e] at hne
    exact hne
  have ht1 : ((t : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero t
  have per_k : ∀ k ∈ Finset.Icc 1 t,
      ((((n - k).choose (t + 1 - k) : ℕ)) : ℂ) / (k : ℂ)
        = (((n : ℂ) - (t : ℂ)) / ((t : ℂ) + 1)) *
          (((((n - k).choose (t - k) : ℕ)) : ℂ) / (k : ℂ)
            + ((((n - k).choose (t - k) : ℕ)) : ℂ) / (((t + 1 - k : ℕ)) : ℂ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have e1 : t + 1 - k = (t - k) + 1 := by omega
    have e2 : (n - k) - (t - k) = n - t := by omega
    have hnat := Nat.choose_succ_right_eq (n - k) (t - k)
    rw [← e1, e2] at hnat
    have hnatC := congrArg (Nat.cast : ℕ → ℂ) hnat
    push_cast at hnatC
    have ecastD : ((n - t : ℕ) : ℂ) = (n : ℂ) - (t : ℂ) := Nat.cast_sub (by omega : t ≤ n)
    rw [ecastD] at hnatC
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have htkC : (((t + 1 - k : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : t + 1 - k ≠ 0)
    have hcomb : ((((n - k).choose (t - k) : ℕ)) : ℂ) / (k : ℂ)
        + ((((n - k).choose (t - k) : ℕ)) : ℂ) / (((t + 1 - k : ℕ)) : ℂ)
        = ((((n - k).choose (t - k) : ℕ)) : ℂ) * ((((t + 1 - k : ℕ)) : ℂ) + (k : ℂ))
          / ((k : ℂ) * (((t + 1 - k : ℕ)) : ℂ)) := by
      field_simp
    have ecastW : (((t + 1 - k : ℕ)) : ℂ) + (k : ℂ) = (t : ℂ) + 1 := by
      have e : t + 1 - k + k = t + 1 := by omega
      have h1c : (((t + 1 - k + k : ℕ)) : ℂ) = (((t + 1 : ℕ)) : ℂ) := by rw [e]
      have h2c : (((t + 1 - k + k : ℕ)) : ℂ)
        = (((t + 1 - k : ℕ)) : ℂ) + (k : ℂ) := Nat.cast_add _ _
      have h3c : (((t + 1 : ℕ)) : ℂ) = (t : ℂ) + 1 := by push_cast; ring
      rw [h2c] at h1c
      rw [h3c] at h1c
      exact h1c
    have hcancel : (((n : ℂ) - (t : ℂ)) / ((t : ℂ) + 1))
        * (((((n - k).choose (t - k) : ℕ)) : ℂ) * (((t : ℂ) + 1))
          / ((k : ℂ) * (((t + 1 - k : ℕ)) : ℂ)))
        * (k : ℂ)
        = (((n : ℂ) - (t : ℂ))) * ((((n - k).choose (t - k) : ℕ)) : ℂ)
          / (((t + 1 - k : ℕ)) : ℂ) := by
      field_simp
    rw [div_eq_iff hkC, hcomb, ecastW, hcancel, eq_comm, div_eq_iff htkC]
    linear_combination -hnatC
  have hsum : (∑ k ∈ Finset.Icc 1 t, ((((n - k).choose (t + 1 - k) : ℕ)) : ℂ) / (k : ℂ))
      = (((n : ℂ) - (t : ℂ)) / ((t : ℂ) + 1)) *
        ((∑ k ∈ Finset.Icc 1 t, ((((n - k).choose (t - k) : ℕ)) : ℂ) / (k : ℂ))
          + (∑ k ∈ Finset.Icc 1 t, ((((n - k).choose (t - k) : ℕ)) : ℂ)
            / (((t + 1 - k : ℕ)) : ℂ))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k hk => by rw [per_k k hk]; ring)
  have hlast : ((((n - (t + 1)).choose (t + 1 - (t + 1)) : ℕ)) : ℂ) / (((t + 1 : ℕ)) : ℂ)
      = 1 / ((t : ℂ) + 1) := by
    have e0 : t + 1 - (t + 1) = 0 := by omega
    have ecastT : (((t + 1 : ℕ)) : ℂ) = (t : ℂ) + 1 := by push_cast; ring
    rw [e0, Nat.choose_zero_right, Nat.cast_one, ecastT]
  have habsC : ((((n.choose (t + 1) : ℕ))) : ℂ)
      = ((((n.choose t : ℕ))) : ℂ) * ((n : ℂ) - (t : ℂ)) / ((t : ℂ) + 1) := by
    have hnat := Nat.choose_succ_right_eq n t
    have hnatC := congrArg (Nat.cast : ℕ → ℂ) hnat
    push_cast at hnatC
    have ecastD : ((n - t : ℕ) : ℂ) = (n : ℂ) - (t : ℂ) := Nat.cast_sub (by omega : t ≤ n)
    rw [ecastD] at hnatC
    rw [eq_div_iff ht1]
    linear_combination hnatC
  have eA : n - (t + 1) + 1 = n - t := by omega
  have epeel := sum_Icc_succ_left (fun i => (1 : ℂ) / (i : ℂ)) (n - t) n (by omega : n - t ≤ n)
  have ecastD2 : (((n - t : ℕ)) : ℂ) = (n : ℂ) - (t : ℂ) := Nat.cast_sub (by omega : t ≤ n)
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), hsum, ih,
    m_sum_eq n t h1 htn, hlast, habsC, eA, epeel, ecastD2]
  field_simp
  ring

private theorem t_identity_nat (n t : ℕ) (h1 : 1 ≤ t) (htn : t ≤ n) :
    (∑ k ∈ Finset.Icc 1 t, (((n - k).choose (t - k) : ℕ) : ℂ) / (k : ℂ))
      = (((n.choose t : ℕ)) : ℂ) * (∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ)) := by
  revert h1 htn
  induction t with
  | zero =>
    intro h1 _
    omega
  | succ t ih =>
    intro h1 htn
    by_cases ht0 : t = 0
    · subst ht0
      exact t_identity_base n (by omega : 1 ≤ n)
    · exact t_identity_step n t (by omega) (by omega) (ih (by omega) (by omega))

private theorem prod_sub_eq_descFactorial (m j : ℕ) :
    (Finset.range j).prod (fun i => (m : ℂ) - (i : ℂ)) = ((m.descFactorial j : ℕ) : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hjm : j ≤ m
    · rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
      have e : ((m - j : ℕ) : ℂ) = (m : ℂ) - (j : ℂ) := Nat.cast_sub hjm
      push_cast
      rw [e]
      ring
    · have h1 : (Finset.range (j + 1)).prod (fun i => (m : ℂ) - (i : ℂ)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : m < j + 1))
        simp
      have h2 : m.descFactorial (j + 1) = 0 := by
        rw [Nat.descFactorial_eq_zero_iff_lt]
        omega
      rw [h1, h2, Nat.cast_zero]

private theorem prod_div_factorial_eq_choose (m j : ℕ) :
    (Finset.range j).prod (fun i => (m : ℂ) - (i : ℂ)) / ((Nat.factorial j : ℕ) : ℂ)
      = (((m.choose j : ℕ)) : ℂ) := by
  rw [prod_sub_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have hfact : (((Nat.factorial j : ℕ)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  push_cast
  field_simp

private theorem t_identity_div (n t : ℕ) (h1 : 1 ≤ t) (htn : t ≤ n) :
    (∑ k ∈ Finset.Icc 1 t,
        ((((t - 1).choose (k - 1) : ℕ)) : ℂ) / ((k : ℂ) ^ 2 * (((n.choose k : ℕ)) : ℂ)))
      = (1 / (t : ℂ)) * (∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ)) := by
  have hT : (t : ℂ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  have hCt : ((((n.choose t : ℕ))) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos (by omega : t ≤ n)))
  have hterm : ∀ k ∈ Finset.Icc 1 t,
      ((((t - 1).choose (k - 1) : ℕ)) : ℂ)
        / ((k : ℂ) ^ 2 * (((n.choose k : ℕ)) : ℂ))
      = (1 / ((t : ℂ) * ((((n.choose t : ℕ))) : ℂ)))
        * (((((n - k).choose (t - k) : ℕ)) : ℂ) / (k : ℂ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have ha := Nat.add_one_mul_choose_eq (t - 1) (k - 1)
    have e1 : t - 1 + 1 = t := by omega
    have e2 : k - 1 + 1 = k := by omega
    rw [e1, e2] at ha
    have hb : n.choose t * t.choose k = n.choose k * (n - k).choose (t - k) :=
      Nat.choose_mul (by omega : k ≤ t)
    have hnat : t * (t - 1).choose (k - 1) * n.choose t
        = k * (n.choose k * (n - k).choose (t - k)) := by
      linear_combination k * hb + n.choose t * ha
    have hnatC := congrArg (Nat.cast : ℕ → ℂ) hnat
    push_cast at hnatC
    have hK : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hCn : ((((n.choose k : ℕ))) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos (by omega : k ≤ n)))
    have hrhs : (1 / ((t : ℂ) * ((((n.choose t : ℕ))) : ℂ)))
          * (((((n - k).choose (t - k) : ℕ)) : ℂ) / (k : ℂ))
        = ((((n - k).choose (t - k) : ℕ)) : ℂ)
          / (((t : ℂ) * (((n.choose t : ℕ))) : ℂ) * (k : ℂ)) := by
      field_simp
    have hD1 : ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hK) hCn
    have hD2 : (((t : ℂ) * (((n.choose t : ℕ))) : ℂ) * (k : ℂ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hT hCt) hK
    rw [hrhs, div_eq_div_iff hD1 hD2]
    linear_combination (k : ℂ) * hnatC
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, t_identity_nat n t h1 htn]
  field_simp

private theorem neg_one_pow_mul (k : ℕ) (hk : 1 ≤ k) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ (k - 1) = -1 := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
  have hsq : (-1 : ℂ) ^ u * (-1 : ℂ) ^ u = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination -hsq

private theorem btilde_neg_le (t k : ℕ) (hk1 : 1 ≤ k) (hkt : k ≤ t) :
    (Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ))
      / ((((Nat.factorial (k - 1) : ℕ))) : ℂ)
      = (-1 : ℂ) ^ (k - 1) * ((((t - 1).choose (k - 1) : ℕ)) : ℂ) := by
  have ecast : ((t - k + 1 : ℕ) : ℂ) = (t : ℂ) - (k : ℂ) + 1 := by
    have h1c : ((t - k + 1 : ℕ) : ℂ) = ((t - k : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [h1c, Nat.cast_sub (by omega : k ≤ t)]
  have hfactor : ∀ i ∈ Finset.range (k - 1),
      (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ) = (-1) * ((((t - k + 1 : ℕ)) : ℂ) + (i : ℂ)) := by
    intro i _
    rw [ecast]
    ring
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, mul_div_assoc]
  congr 1
  have hrev : (Finset.range (k - 1)).prod (fun i => (((t - k + 1 : ℕ)) : ℂ) + (i : ℂ))
      = (Finset.range (k - 1)).prod (fun i => (((t - 1 : ℕ)) : ℂ) - (i : ℂ)) := by
    rw [← Finset.prod_range_reflect]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    show (((t - k + 1 : ℕ)) : ℂ) + ((((k - 1 - 1 - i : ℕ))) : ℂ)
      = (((t - 1 : ℕ)) : ℂ) - (i : ℂ)
    have eN : (t - k + 1) + ((k - 1 - 1 - i)) = (t - 1) - i := by omega
    have hcast : ((((t - k + 1) + ((k - 1 - 1 - i)) : ℕ)) : ℂ) = ((((t - 1) - i : ℕ)) : ℂ) := by
      rw [eN]
    have hsplit : ((((t - k + 1) + ((k - 1 - 1 - i)) : ℕ)) : ℂ)
      = (((t - k + 1 : ℕ)) : ℂ) + ((((k - 1 - 1 - i : ℕ))) : ℂ) := Nat.cast_add _ _
    rw [hsplit] at hcast
    have esub : ((((t - 1) - i : ℕ)) : ℂ) = (((t - 1 : ℕ)) : ℂ) - (i : ℂ) :=
      Nat.cast_sub (by omega : i ≤ t - 1)
    rw [esub] at hcast
    exact hcast
  rw [hrev]
  exact prod_div_factorial_eq_choose (t - 1) (k - 1)

private theorem btilde_neg_gt (t k : ℕ) (h1 : 1 ≤ t) (hkt : t + 1 ≤ k) :
    (Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ)) = 0 := by
  have e : ((k - 1 - t : ℕ) : ℂ) = (k : ℂ) - (t : ℂ) - 1 := by
    have h1c : ((k - 1 - t + (t + 1) : ℕ) : ℂ) = ((k : ℕ) : ℂ) := by
      have e0 : k - 1 - t + (t + 1) = k := by omega
      rw [e0]
    have h2c : ((k - 1 - t + (t + 1) : ℕ) : ℂ)
      = ((k - 1 - t : ℕ) : ℂ) + (((t + 1 : ℕ)) : ℂ) := Nat.cast_add _ _
    rw [h2c] at h1c
    have h3c : (((t + 1 : ℕ)) : ℂ) = (t : ℂ) + 1 := by push_cast; ring
    rw [h3c] at h1c
    linear_combination h1c
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : k - 1 - t < k - 1))
  show (-(t : ℂ)) + (k : ℂ) - 1 - (((k - 1 - t : ℕ)) : ℂ) = 0
  rw [e]
  ring

private theorem stilde_neg (n t : ℕ) (h1 : 1 ≤ t) (htn : t ≤ n) :
    (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℂ) ^ k
          * ((Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ))
            / ((((Nat.factorial (k - 1) : ℕ))) : ℂ))
          / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)))
      = -((∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ)) / (t : ℂ)) := by
  have hsplit : (∑ k ∈ Finset.Icc 1 n,
          (-1 : ℂ) ^ k
            * ((Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ))
              / ((((Nat.factorial (k - 1) : ℕ))) : ℂ))
            / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)))
      = (∑ k ∈ Finset.Icc 1 t,
          (-1 : ℂ) ^ k
            * ((Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ))
              / ((((Nat.factorial (k - 1) : ℕ))) : ℂ))
            / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)))
        + (∑ k ∈ Finset.Icc (t + 1) n,
          (-1 : ℂ) ^ k
            * ((Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ))
              / ((((Nat.factorial (k - 1) : ℕ))) : ℂ))
            / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ))) := by
    have e1 : Finset.Icc 1 n = Finset.Ico 1 (n + 1) :=
      (Finset.Ico_add_one_right_eq_Icc 1 n).symm
    have e2 : Finset.Icc 1 t = Finset.Ico 1 (t + 1) :=
      (Finset.Ico_add_one_right_eq_Icc 1 t).symm
    have e3 : Finset.Icc (t + 1) n = Finset.Ico (t + 1) (n + 1) :=
      (Finset.Ico_add_one_right_eq_Icc (t + 1) n).symm
    rw [e1, e2, e3]
    exact (Finset.sum_Ico_consecutive _ (by omega : 1 ≤ t + 1) (by omega : t + 1 ≤ n + 1)).symm
  have hzero : (∑ k ∈ Finset.Icc (t + 1) n,
        (-1 : ℂ) ^ k
          * ((Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ))
            / ((((Nat.factorial (k - 1) : ℕ))) : ℂ))
          / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [btilde_neg_gt t k h1 (by omega : t + 1 ≤ k), zero_div, mul_zero, zero_div]
  have hterm : ∀ k ∈ Finset.Icc 1 t,
      (-1 : ℂ) ^ k
        * ((Finset.range (k - 1)).prod (fun i => (-(t : ℂ)) + (k : ℂ) - 1 - (i : ℂ))
          / ((((Nat.factorial (k - 1) : ℕ))) : ℂ))
        / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ))
      = -(((((t - 1).choose (k - 1) : ℕ)) : ℂ)
        / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ))) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [btilde_neg_le t k (by omega : 1 ≤ k) (by omega : k ≤ t), ← mul_assoc,
      neg_one_pow_mul k (by omega : 1 ≤ k)]
    ring
  rw [hsplit, hzero, add_zero, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib,
    t_identity_div n t h1 htn]
  ring

private noncomputable def H1 (n : ℕ) : ℂ := ∑ i ∈ Finset.Icc 1 n, (1 : ℂ) / (i : ℂ)

private noncomputable def LHSstar (n : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (j - 1)
    * ((Finset.range j).prod (fun i => s + (n : ℂ) - (i : ℂ))
      / ((((Nat.factorial j : ℕ))) : ℂ)) / (j : ℂ)

private noncomputable def Sstar (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, ((-1 : ℂ) ^ k
    * ((Finset.range (k - 1)).prod (fun i => s + (k : ℂ) - 1 - (i : ℂ))
      / ((((Nat.factorial (k - 1) : ℕ))) : ℂ)))
    / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ))

private noncomputable def Qpoly (n j : ℕ) : Polynomial ℂ :=
  Polynomial.C (((-1 : ℂ) ^ (j - 1)) / (j : ℂ))
    * ((Finset.range j).prod (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))
      * Polynomial.C ((((Nat.factorial j : ℕ)) : ℂ)⁻¹))

private noncomputable def Rpoly (n k : ℕ) : Polynomial ℂ :=
  Polynomial.C (((-1 : ℂ) ^ k) / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)))
    * ((Finset.range (k - 1)).prod
        (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))
      * Polynomial.C ((((Nat.factorial (k - 1) : ℕ)) : ℂ)⁻¹))

private noncomputable def Presid (n : ℕ) : Polynomial ℂ :=
  (∑ j ∈ Finset.Icc 1 n, Qpoly n j)
    + Polynomial.X * (∑ k ∈ Finset.Icc 1 n, Rpoly n k)
    - Polynomial.C (H1 n)

private theorem Qpoly_eval (n j : ℕ) (s : ℂ) :
    (Qpoly n j).eval s = (-1 : ℂ) ^ (j - 1)
      * ((Finset.range j).prod (fun i => s + (n : ℂ) - (i : ℂ))
        / ((((Nat.factorial j : ℕ))) : ℂ)) / (j : ℂ) := by
  unfold Qpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_prod, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.range j,
    s + ((n : ℂ) - (i : ℂ)) = s + (n : ℂ) - (i : ℂ))]
  ring

private theorem Rpoly_eval (n k : ℕ) (s : ℂ) :
    (Rpoly n k).eval s = ((-1 : ℂ) ^ k
      * ((Finset.range (k - 1)).prod (fun i => s + (k : ℂ) - 1 - (i : ℂ))
        / ((((Nat.factorial (k - 1) : ℕ))) : ℂ)))
      / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)) := by
  unfold Rpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_prod, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.range (k - 1),
    s + ((k : ℂ) - 1 - (i : ℂ)) = s + (k : ℂ) - 1 - (i : ℂ))]
  ring

private theorem Presid_eval (n : ℕ) (s : ℂ) :
    (Presid n).eval s = LHSstar n s + s * Sstar n s - H1 n := by
  have eQ : ∀ j ∈ Finset.Icc 1 n, (Qpoly n j).eval s
      = (-1 : ℂ) ^ (j - 1)
        * ((Finset.range j).prod (fun i => s + (n : ℂ) - (i : ℂ))
          / ((((Nat.factorial j : ℕ))) : ℂ)) / (j : ℂ) :=
    fun j _ => Qpoly_eval n j s
  have eR : ∀ k ∈ Finset.Icc 1 n, (Rpoly n k).eval s
      = ((-1 : ℂ) ^ k
        * ((Finset.range (k - 1)).prod (fun i => s + (k : ℂ) - 1 - (i : ℂ))
          / ((((Nat.factorial (k - 1) : ℕ))) : ℂ)))
        / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)) :=
    fun k _ => Rpoly_eval n k s
  unfold Presid LHSstar Sstar H1
  rw [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, Polynomial.eval_X,
    Polynomial.eval_C, Finset.sum_congr rfl eQ, Finset.sum_congr rfl eR]

private theorem poly_sum_natDegree_le (s : Finset ℕ) (f : ℕ → Polynomial ℂ) (b : ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ b) : (∑ i ∈ s, f i).natDegree ≤ b := by
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro h
    simp
  · intro a t hat ih h
    rw [Finset.sum_insert hat]
    have h1 := h _ (Finset.mem_insert_self a t)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le h1 h2)

private theorem qdeg (n j : ℕ) : (Qpoly n j).natDegree ≤ j := by
  unfold Qpoly
  have h1 : (Polynomial.C (((-1 : ℂ) ^ (j - 1)) / (j : ℂ))
      * ((Finset.range j).prod (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))
        * Polynomial.C ((((Nat.factorial j : ℕ)) : ℂ)⁻¹))).natDegree
      ≤ (((Finset.range j).prod (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))
        * Polynomial.C ((((Nat.factorial j : ℕ)) : ℂ)⁻¹))).natDegree :=
    Polynomial.natDegree_C_mul_le _ _
  have h2 : (((Finset.range j).prod
      (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))
      * Polynomial.C ((((Nat.factorial j : ℕ)) : ℂ)⁻¹))).natDegree
      ≤ ((Finset.range j).prod
        (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))).natDegree := by
    have h := Polynomial.natDegree_mul_le
      (p := (Finset.range j).prod (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ))))
      (q := Polynomial.C ((((Nat.factorial j : ℕ)) : ℂ)⁻¹))
    rw [Polynomial.natDegree_C] at h
    omega
  have h3 : ((Finset.range j).prod
      (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))).natDegree ≤ j := by
    have hle : ((Finset.range j).prod
        (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))).natDegree
        ≤ (∑ i ∈ Finset.range j,
          (Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ))).natDegree) :=
      Polynomial.natDegree_prod_le _ _
    have hsum : (∑ i ∈ Finset.range j,
        (Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ))).natDegree) ≤ j := by
      have each : ∀ i ∈ Finset.range j,
          (Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ))).natDegree ≤ 1 := by
        intro i _
        have h := Polynomial.natDegree_add_le Polynomial.X
          (Polynomial.C ((n : ℂ) - (i : ℂ)))
        rw [Polynomial.natDegree_X, Polynomial.natDegree_C] at h
        omega
      have hle1 : (∑ i ∈ Finset.range j,
            (Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ))).natDegree)
          ≤ ∑ _i ∈ Finset.range j, 1 := by
        apply Finset.sum_le_sum
        exact each
      have hle2 : (∑ _i ∈ Finset.range j, (1 : ℕ)) = j := by simp
      omega
    exact le_trans hle hsum
  omega

private theorem rdeg (n k : ℕ) : (Rpoly n k).natDegree ≤ k - 1 := by
  unfold Rpoly
  have h1 : (Polynomial.C (((-1 : ℂ) ^ k) / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)))
      * ((Finset.range (k - 1)).prod
          (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))
        * Polynomial.C ((((Nat.factorial (k - 1) : ℕ)) : ℂ)⁻¹))).natDegree
      ≤ (((Finset.range (k - 1)).prod
          (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))
        * Polynomial.C ((((Nat.factorial (k - 1) : ℕ)) : ℂ)⁻¹))).natDegree :=
    Polynomial.natDegree_C_mul_le _ _
  have h2 : (((Finset.range (k - 1)).prod
      (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))
      * Polynomial.C ((((Nat.factorial (k - 1) : ℕ)) : ℂ)⁻¹))).natDegree
      ≤ ((Finset.range (k - 1)).prod
        (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))).natDegree := by
    have h := Polynomial.natDegree_mul_le
      (p := (Finset.range (k - 1)).prod
        (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ))))
      (q := Polynomial.C ((((Nat.factorial (k - 1) : ℕ)) : ℂ)⁻¹))
    rw [Polynomial.natDegree_C] at h
    omega
  have h3 : ((Finset.range (k - 1)).prod
      (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))).natDegree ≤ k - 1 := by
    have hle : ((Finset.range (k - 1)).prod
        (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))).natDegree
        ≤ (∑ i ∈ Finset.range (k - 1),
          (Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ))).natDegree) :=
      Polynomial.natDegree_prod_le _ _
    have hsum : (∑ i ∈ Finset.range (k - 1),
        (Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ))).natDegree) ≤ k - 1 := by
      have each : ∀ i ∈ Finset.range (k - 1),
          (Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ))).natDegree ≤ 1 := by
        intro i _
        have h := Polynomial.natDegree_add_le Polynomial.X
          (Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))
        rw [Polynomial.natDegree_X, Polynomial.natDegree_C] at h
        omega
      have hle1 : (∑ i ∈ Finset.range (k - 1),
            (Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ))).natDegree)
          ≤ ∑ _i ∈ Finset.range (k - 1), 1 := by
        apply Finset.sum_le_sum
        exact each
      have hle2 : (∑ _i ∈ Finset.range (k - 1), (1 : ℕ)) = k - 1 := by simp
      omega
    exact le_trans hle hsum
  omega

private theorem Presid_natDegree_le (n : ℕ) (_hn : 1 ≤ n) : (Presid n).natDegree ≤ n := by
  have hQ : ∀ j ∈ Finset.Icc 1 n, (Qpoly n j).natDegree ≤ n := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact le_trans (qdeg n j) (by omega)
  have hR : ∀ k ∈ Finset.Icc 1 n, (Polynomial.X * Rpoly n k).natDegree ≤ n := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have e1 : (Polynomial.X * Rpoly n k).natDegree ≤ 1 + (k - 1) := by
      have h := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℂ)) (q := Rpoly n k)
      rw [Polynomial.natDegree_X] at h
      exact le_trans h (Nat.add_le_add_left (rdeg n k) 1)
    omega
  have hS1 : (∑ j ∈ Finset.Icc 1 n, Qpoly n j).natDegree ≤ n :=
    poly_sum_natDegree_le _ _ _ hQ
  have hS2 : (∑ k ∈ Finset.Icc 1 n, Polynomial.X * Rpoly n k).natDegree ≤ n :=
    poly_sum_natDegree_le _ _ _ hR
  have eP : Presid n
      = (∑ j ∈ Finset.Icc 1 n, Qpoly n j)
        + (∑ k ∈ Finset.Icc 1 n, Polynomial.X * Rpoly n k)
        - Polynomial.C (H1 n) := by
    unfold Presid
    rw [Finset.mul_sum]
  rw [eP]
  have hadd := Polynomial.natDegree_add_le (∑ j ∈ Finset.Icc 1 n, Qpoly n j)
    (∑ k ∈ Finset.Icc 1 n, Polynomial.X * Rpoly n k)
  have hC0 : (Polynomial.C (H1 n)).natDegree = 0 := Polynomial.natDegree_C _
  have hsub := Polynomial.natDegree_sub_le
    ((∑ j ∈ Finset.Icc 1 n, Qpoly n j)
      + (∑ k ∈ Finset.Icc 1 n, Polynomial.X * Rpoly n k))
    (Polynomial.C (H1 n))
  omega

private theorem Presid_eval_zero (n : ℕ) (hn : 1 ≤ n) : (Presid n).eval 0 = 0 := by
  have hL : LHSstar n 0 = H1 n := by
    have eprod : ∀ j ∈ Finset.Icc 1 n,
        (Finset.range j).prod (fun i => (0 : ℂ) + (n : ℂ) - (i : ℂ))
        = (Finset.range j).prod (fun i => (n : ℂ) - (i : ℂ)) := by
      intro j _
      apply Finset.prod_congr rfl
      intro i _
      ring
    have hsum : LHSstar n 0
        = (∑ j ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (j - 1) * ((((n.choose j : ℕ))) : ℂ) / (j : ℂ)) := by
      unfold LHSstar
      apply Finset.sum_congr rfl
      intro j hj
      rw [eprod j hj, prod_div_factorial_eq_choose n j]
    rw [hsum]
    exact classical_order_one n hn
  rw [Presid_eval n 0, hL]
  ring

private theorem Presid_eval_neg (n t : ℕ) (h1 : 1 ≤ t) (htn : t ≤ n) :
    (Presid n).eval (-(t : ℂ)) = 0 := by
  have hL : LHSstar n (-(t : ℂ)) = ∑ i ∈ Finset.Icc 1 (n - t), (1 : ℂ) / (i : ℂ) := by
    have e1 : ∀ j ∈ Finset.Icc 1 n,
        (-1 : ℂ) ^ (j - 1)
          * ((Finset.range j).prod (fun i => (-(t : ℂ)) + (n : ℂ) - (i : ℂ))
            / ((((Nat.factorial j : ℕ))) : ℂ)) / (j : ℂ)
        = (-1 : ℂ) ^ (j - 1) * ((((n - t).choose j : ℕ)) : ℂ) / (j : ℂ) := by
      intro j _
      have eprod : (Finset.range j).prod (fun i => (-(t : ℂ)) + (n : ℂ) - (i : ℂ))
          = (Finset.range j).prod (fun i => ((((n - t : ℕ))) : ℂ) - (i : ℂ)) := by
        apply Finset.prod_congr rfl
        intro i _
        have ecast : ((((n - t : ℕ))) : ℂ) = (n : ℂ) - (t : ℂ) :=
          Nat.cast_sub (by omega : t ≤ n)
        rw [ecast]
        ring
      rw [eprod, prod_div_factorial_eq_choose (n - t) j]
    have hsum : LHSstar n (-(t : ℂ))
        = (∑ j ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (j - 1) * ((((n - t).choose j : ℕ)) : ℂ) / (j : ℂ)) :=
      Finset.sum_congr rfl e1
    have erestrict : (∑ j ∈ Finset.Icc 1 n,
          (-1 : ℂ) ^ (j - 1) * ((((n - t).choose j : ℕ)) : ℂ) / (j : ℂ))
        = ∑ i ∈ Finset.Icc 1 (n - t), (1 : ℂ) / (i : ℂ) := by
      by_cases hnt0 : n - t = 0
      · have hL0 : (∑ j ∈ Finset.Icc 1 n,
              (-1 : ℂ) ^ (j - 1) * ((((n - t).choose j : ℕ)) : ℂ) / (j : ℂ)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [Finset.mem_Icc] at hj
          rw [hnt0]
          have hC0 : (0 : ℕ).choose j = 0 :=
            Nat.choose_eq_zero_of_lt (by omega : 0 < j)
          rw [hC0]
          simp
        have hR0 : (∑ i ∈ Finset.Icc 1 (n - t), (1 : ℂ) / (i : ℂ)) = 0 := by
          rw [hnt0, Finset.Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
        rw [hL0, hR0]
      · have hsub : (∑ j ∈ Finset.Icc 1 (n - t),
              (-1 : ℂ) ^ (j - 1) * ((((n - t).choose j : ℕ)) : ℂ) / (j : ℂ))
            = (∑ j ∈ Finset.Icc 1 n,
              (-1 : ℂ) ^ (j - 1) * ((((n - t).choose j : ℕ)) : ℂ) / (j : ℂ)) := by
          apply Finset.sum_subset (fun x hx => by
            rw [Finset.mem_Icc] at hx ⊢
            omega)
          intro j hj hjn
          rw [Finset.mem_Icc] at hj
          have hjlt : n - t < j := by
            rw [Finset.mem_Icc] at hjn
            omega
          have hC0 : ((n - t).choose j : ℕ) = 0 := Nat.choose_eq_zero_of_lt hjlt
          rw [hC0]
          simp
        rw [← hsub]
        exact classical_order_one (n - t) (by omega : 1 ≤ n - t)
    exact hsum.trans erestrict
  have hS : Sstar n (-(t : ℂ))
      = -((∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ)) / (t : ℂ)) :=
    stilde_neg n t h1 htn
  have hH : H1 n = (∑ i ∈ Finset.Icc 1 (n - t), (1 : ℂ) / (i : ℂ))
      + (∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ)) := by
    unfold H1
    have e1 : Finset.Icc 1 n = Finset.Ico 1 (n + 1) :=
      (Finset.Ico_add_one_right_eq_Icc 1 n).symm
    have e2 : Finset.Icc 1 (n - t) = Finset.Ico 1 (n - t + 1) :=
      (Finset.Ico_add_one_right_eq_Icc 1 (n - t)).symm
    have e3 : Finset.Icc (n - t + 1) n = Finset.Ico (n - t + 1) (n + 1) :=
      (Finset.Ico_add_one_right_eq_Icc (n - t + 1) n).symm
    rw [e1, e2, e3]
    exact (Finset.sum_Ico_consecutive _ (by omega : 1 ≤ n - t + 1)
      (by omega : n - t + 1 ≤ n + 1)).symm
  have hT : (t : ℂ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  have eS : (-(t : ℂ)) * (-((∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ)) / (t : ℂ)))
      = (∑ i ∈ Finset.Icc (n - t + 1) n, (1 : ℂ) / (i : ℂ)) := by
    field_simp
  rw [Presid_eval n (-(t : ℂ)), hL, hS, hH, eS]
  ring

private theorem Presid_eq_zero (n : ℕ) (hn : 1 ≤ n) : Presid n = 0 := by
  have hfinj : Function.Injective (fun i : Fin (n + 1) => -((((i.val : ℕ))) : ℂ)) := by
    intro a b hab
    simp only [neg_inj] at hab
    have hcast : a.val = b.val := Nat.cast_injective hab
    exact Fin.ext hcast
  have hroots : ∀ i : Fin (n + 1), (Presid n).eval (-((((i.val : ℕ))) : ℂ)) = 0 := by
    intro i
    by_cases hi0 : i.val = 0
    · rw [hi0]
      simp only [Nat.cast_zero, neg_zero]
      exact Presid_eval_zero n hn
    · exact Presid_eval_neg n (i.val) (by omega) (by have h := i.isLt; omega)
  have hcard : (Presid n).natDegree < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]
    have h := Presid_natDegree_le n hn
    omega
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hfinj hroots hcard

private theorem resid_eq (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    LHSstar n s = H1 n - s * Sstar n s := by
  have hP0 := Presid_eq_zero n hn
  have heval : (Presid n).eval s = 0 := by
    rw [hP0]
    simp
  rw [Presid_eval n s] at heval
  linear_combination heval

/--
**Alternating binomial transform of second-order harmonic numbers.** For a natural number
$m$ let $H_m = \sum_{j=1}^{m} 1/j$ and $H_m^{(2)} = \sum_{j=1}^{m} 1/j^2$, and for
$z \in \mathbb{C}$ and a natural number $r$ let $\binom{z}{r} = z(z-1)\cdots(z-r+1)/r!$, the
empty product for $r = 0$ being $1$. Let $s \in \mathbb{C}$ with $s \ne -m$ for every positive
integer $m$, and let $n \ge 1$. Then
$$\sum_{k=1}^{n} (-1)^k \binom{s+n}{k} H_k^{(2)} =
(-1)^n \binom{s+n-1}{n} H_n^{(2)} -
\frac{1}{s+n} \Bigl(H_n -
s \sum_{k=1}^{n} \frac{(-1)^k \binom{s+k-1}{k-1}}{k^2 \binom{n}{k}}\Bigr).$$

Source: Necdet Batır, "Finite Binomial Sum Identities with Harmonic Numbers,"
Journal of Integer Sequences 24 (2021), Article 21.4.3, Proposition 6 (label
`Proposition6`), equation (2.8), lines 260–267,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Batir2/batir13.tex
Proves `Wanted` entry `binomial_transform_second_order_harmonic_numbers`.
-/
theorem binomial_transform_second_order_harmonic_numbers
    (s : ℂ) (n : ℕ) (hn : 0 < n)
    (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ)) :
    (∑ k ∈ Finset.Icc 1 n,
        (-1 : ℂ) ^ k *
          ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ)) /
            (Nat.factorial k : ℂ)) *
          (∑ j ∈ Finset.Icc 1 k, (1 : ℂ) / (j : ℂ) ^ 2)) =
      (-1 : ℂ) ^ n *
          ((Finset.range n).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ)) /
            (Nat.factorial n : ℂ)) *
          (∑ j ∈ Finset.Icc 1 n, (1 : ℂ) / (j : ℂ) ^ 2) -
        1 / (s + (n : ℂ)) *
          ((∑ j ∈ Finset.Icc 1 n, (1 : ℂ) / (j : ℂ)) -
            s * ∑ k ∈ Finset.Icc 1 n,
              ((-1 : ℂ) ^ k *
                  ((Finset.range (k - 1)).prod
                      (fun j => s + (k : ℂ) - 1 - (j : ℂ)) /
                    (Nat.factorial (k - 1) : ℂ))) /
                ((k : ℂ) ^ 2 * (n.choose k : ℂ))) := by
  have hsn : s + (n : ℂ) ≠ 0 := add_ne_zero_of_hs s n hn hs
  have hswap : (∑ k ∈ Finset.Icc 1 n,
        ((-1 : ℂ) ^ k * ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ))
          / (Nat.factorial k : ℂ)))
          * (∑ j ∈ Finset.Icc 1 k, (1 : ℂ) / (j : ℂ) ^ 2))
      = ∑ j ∈ Finset.Icc 1 n, ((1 : ℂ) / (j : ℂ) ^ 2) * (∑ k ∈ Finset.Icc j n,
        ((-1 : ℂ) ^ k * ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ))
          / (Nat.factorial k : ℂ)))) :=
    tri_swap _ _ n
  have hinner : ∀ j ∈ Finset.Icc 1 n,
      (∑ k ∈ Finset.Icc j n,
        ((-1 : ℂ) ^ k * ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ))
          / (Nat.factorial k : ℂ))))
      = (-1 : ℂ) ^ n * ((Finset.range n).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ))
          / (Nat.factorial n : ℂ))
        - (-1 : ℂ) ^ (j - 1) * ((Finset.range (j - 1)).prod
            (fun j => s + (n : ℂ) - 1 - (j : ℂ)) / (Nat.factorial (j - 1) : ℂ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hsplit := icc_split (fun k => (-1 : ℂ) ^ k
      * ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ))
        / (Nat.factorial k : ℂ))) j n hj.1 hj.2
    have h0n := partial_alt_sum s n n
    have h0j := partial_alt_sum s n (j - 1)
    linear_combination hsplit + h0n - h0j
  have hdistrib : (∑ j ∈ Finset.Icc 1 n, ((1 : ℂ) / (j : ℂ) ^ 2) * (∑ k ∈ Finset.Icc j n,
        ((-1 : ℂ) ^ k * ((Finset.range k).prod (fun j => s + (n : ℂ) - (j : ℂ))
          / (Nat.factorial k : ℂ)))))
      = ((-1 : ℂ) ^ n * ((Finset.range n).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ))
          / (Nat.factorial n : ℂ))) * (∑ j ∈ Finset.Icc 1 n, (1 : ℂ) / (j : ℂ) ^ 2)
        - ∑ j ∈ Finset.Icc 1 n, ((1 : ℂ) / (j : ℂ) ^ 2)
          * (((-1 : ℂ) ^ (j - 1)) * ((Finset.range (j - 1)).prod
            (fun j => s + (n : ℂ) - 1 - (j : ℂ)) / (Nat.factorial (j - 1) : ℂ))) := by
    trans (∑ j ∈ Finset.Icc 1 n,
      (((-1 : ℂ) ^ n * ((Finset.range n).prod (fun j => s + (n : ℂ) - 1 - (j : ℂ))
          / (Nat.factorial n : ℂ))) * ((1 : ℂ) / (j : ℂ) ^ 2)
        - ((1 : ℂ) / (j : ℂ) ^ 2)
          * (((-1 : ℂ) ^ (j - 1)) * ((Finset.range (j - 1)).prod
            (fun j => s + (n : ℂ) - 1 - (j : ℂ)) / (Nat.factorial (j - 1) : ℂ)))))
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hinner j hj]
      ring
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hR : (∑ j ∈ Finset.Icc 1 n, ((1 : ℂ) / (j : ℂ) ^ 2)
        * (((-1 : ℂ) ^ (j - 1)) * ((Finset.range (j - 1)).prod
          (fun j => s + (n : ℂ) - 1 - (j : ℂ)) / (Nat.factorial (j - 1) : ℂ))))
      = (1 / (s + (n : ℂ))) * LHSstar n s := by
    unfold LHSstar
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact ratio_term s n j hsn hj.1
  rw [hswap, hdistrib, hR, resid_eq n (by omega) s]
  rfl

end MetaMathlibExt
