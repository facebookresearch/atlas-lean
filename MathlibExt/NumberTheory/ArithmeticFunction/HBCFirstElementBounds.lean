/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# First-element bounds for HBC-admissible tuples

Compare the reciprocal factors with telescoping products of steps one, two, or three.
In the prime case, the quotients by three strictly increase once the primes exceed three.
-/

namespace MetaMathlibExt

open Finset

private theorem first_add_step_le {k : ℕ} (hk : 0 < k) (f : Fin k → ℕ) (d : ℕ)
    (hstep : ∀ (j : ℕ) (hj : j + 1 < k),
      f ⟨j, Nat.lt_of_succ_lt hj⟩ + d ≤ f ⟨j + 1, hj⟩) (i : Fin k) :
    f ⟨0, hk⟩ + d * i.val ≤ f i := by
  obtain ⟨j, hj⟩ := i
  induction j with
  | zero => simp
  | succ j ih =>
    simpa only [Nat.mul_succ, ← Nat.add_assoc] using
      (Nat.add_le_add_right (ih (Nat.lt_of_succ_lt hj)) d).trans (hstep j hj)

private theorem telescope_ratios {a d : ℚ} (hd : 0 ≤ d) (ha : d < a) (k : ℕ) :
    (∏ i : Fin k, (a - d + d * (i : ℕ)) / (a + d * (i : ℕ))) =
      (a - d) / (a - d + d * k) := by
  induction k with
  | zero => simp [div_self (sub_pos.mpr ha).ne']
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_succ]
    have hn : (0 : ℚ) ≤ k := by positivity
    have h1 : 0 < a - d + d * k := add_pos_of_pos_of_nonneg (sub_pos.mpr ha) (mul_nonneg hd hn)
    have h2 : 0 < a + d * k := add_pos_of_pos_of_nonneg (hd.trans_lt ha) (mul_nonneg hd hn)
    rw [show a - d + d * ((k : ℚ) + 1) = a + d * k by ring]
    field_simp [h1.ne', h2.ne']

private theorem ratio_le_sub_div {a q d : ℚ} (ha : 0 < a) (hd : 0 ≤ d) (haq : a ≤ q) :
    (a - d) / a ≤ 1 - d / q := by
  rw [sub_div, div_self ha.ne']
  exact sub_le_sub_left (div_le_div_of_nonneg_left hd ha haq) 1

private theorem strict_telescope_bound {k : ℕ} (hk : 0 < k) {a d : ℚ} (hd : 0 ≤ d) (ha : d < a)
    (f : Fin k → ℚ) (hf : ∀ i, 0 ≤ f i) (hhalf : ∏ i, f i ≤ 1 / 2) (e : ℕ)
    (hterm : ∀ i : Fin k, (a - d + d * (i : ℕ)) / (a + d * (i : ℕ)) < f i ^ e) :
    a - d < (1 / 2 : ℚ) ^ e * (a - d + d * k) := by
  have hpos (j : ℕ) : 0 < a - d + d * j :=
    add_pos_of_pos_of_nonneg (sub_pos.mpr ha) (mul_nonneg hd (by positivity))
  have hratio (i : Fin k) : 0 < (a - d + d * (i : ℕ)) / (a + d * (i : ℕ)) :=
    div_pos (hpos i) (add_pos_of_pos_of_nonneg (hd.trans_lt ha) (mul_nonneg hd (by positivity)))
  have hprod := Finset.prod_lt_prod_of_nonempty₀ (s := univ)
    (fun i _ ↦ hratio i) (fun i _ ↦ hterm i) ⟨⟨0, hk⟩, mem_univ _⟩
  rw [telescope_ratios hd ha, Finset.prod_pow] at hprod
  exact (div_lt_iff₀ (hpos k)).mp
    (hprod.trans_le (pow_le_pow_left₀ (prod_nonneg (fun i _ ↦ hf i)) hhalf e))

private theorem prime_not_zero_mod_three {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : p % 3 ≠ 0 := by
  intro hz
  exact (ne_of_gt hp3) ((hp.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero hz))

private theorem prime_thirds_strict {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 < p) (hpq : p < q) : p / 3 < q / 3 := by
  have hpo := hp.eq_two_or_odd.resolve_left (by omega)
  have hqo := hq.eq_two_or_odd.resolve_left (by omega)
  have hpm := prime_not_zero_mod_three hp hp3
  have hqm := prime_not_zero_mod_three hq (hp3.trans hpq)
  omega

@[expose] public section

/-- **First-element bounds for HBC-admissible tuples at $1/2$.** Let $k \ge 1$ and let
$y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le 1/2 < \prod_{i=1}^{k-1} (1 - 1/y_i)$. Then $y_1 \le k + 1$; if
every $y_i$ is odd, then $y_1 < 2(k + 3)/3$; and if every $y_i$ is prime, then $y_1 < 3k/7 + 3$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 5 (`integers-2024-A114-lem-5`). -/
public theorem hbcAdmissible_half_first_le (k : ℕ) (hk : 0 < k) (y : Fin k → ℕ)
    (hmono : StrictMono y) (hpos : ∀ i, 0 < y i)
    (hle : ∏ i, (1 - 1 / (y i : ℚ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k - 1),
      (1 - 1 / (y i : ℚ))) :
    y ⟨0, hk⟩ ≤ k + 1 ∧
      ((∀ i, Odd (y i)) → (y ⟨0, hk⟩ : ℚ) < 2 * (k + 3) / 3) ∧
      ((∀ i, (y i).Prime) → (y ⟨0, hk⟩ : ℚ) < 3 * k / 7 + 3) := by
  let a := y ⟨0, hk⟩
  let f : Fin k → ℚ := fun i ↦ 1 - 1 / (y i : ℚ)
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hf (i : Fin k) : 0 ≤ f i := by
    have hy : (1 : ℚ) ≤ y i := by exact_mod_cast hpos i
    exact sub_nonneg.mpr ((div_le_one₀ (zero_lt_one.trans_le hy)).mpr hy)
  change a ≤ k + 1 ∧
    ((∀ i, Odd (y i)) → (a : ℚ) < 2 * (k + 3) / 3) ∧
    ((∀ i, (y i).Prime) → (a : ℚ) < 3 * k / 7 + 3)
  refine ⟨?_, ?_, ?_⟩
  · by_cases ha : 1 < a
    · have haq : (1 : ℚ) < a := by exact_mod_cast ha
      have hstep := first_add_step_le hk y 1 (fun j hj ↦ by
        have h := hmono (show (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin k) < ⟨j + 1, hj⟩ from
          Nat.lt_succ_self j)
        omega)
      have hfactor (i : Fin k) : ((a : ℚ) - 1 + (i : ℕ)) / ((a : ℚ) + (i : ℕ)) ≤ f i := by
        have hy : (a : ℚ) + (i : ℕ) ≤ (y i : ℚ) := by
          exact_mod_cast (show a + i.val ≤ y i by simpa only [one_mul] using hstep i)
        simpa only [add_sub_right_comm] using
          (ratio_le_sub_div (a := (a : ℚ) + (i : ℕ)) (q := y i) (d := 1)
            (by positivity) zero_le_one hy)
      have hprod := Finset.prod_le_prod₀ (s := univ)
        (fun i (_ : i ∈ (univ : Finset (Fin k))) ↦
          div_nonneg (add_nonneg (sub_nonneg.mpr haq.le) (by positivity)) (by positivity))
        (fun i _ ↦ hfactor i)
      have htel := telescope_ratios (d := 1) zero_le_one haq k
      simp only [one_mul] at htel
      rw [htel] at hprod
      have hden : (0 : ℚ) < (a : ℚ) - 1 + k := by linarith
      have hz := (div_le_iff₀ hden).mp (hprod.trans hle)
      have hbound : (a : ℚ) ≤ (k : ℚ) + 1 := by linarith
      exact_mod_cast hbound
    · by_cases hlong : 1 < k
      · have ha1 : y ⟨0, hk⟩ = 1 := by
          change a = 1
          have hpa : 0 < a := hpos ⟨0, hk⟩
          omega
        have hmem : (⟨0, hk⟩ : Fin k) ∈ univ.filter (fun i : Fin k => (i : ℕ) < k - 1) :=
          mem_filter.mpr ⟨mem_univ _, by change 0 < k - 1; omega⟩
        have hz : 1 - 1 / (y ⟨0, hk⟩ : ℚ) = 0 := by norm_num [ha1]
        rw [Finset.prod_eq_zero (f := fun i : Fin k => 1 - 1 / (y i : ℚ)) hmem hz] at hlt
        norm_num at hlt
      · omega
  · intro hodd
    by_cases ha : 2 < a
    · have haq : (2 : ℚ) < a := by exact_mod_cast ha
      have hstep := first_add_step_le hk y 2 (fun j hj ↦ by
        have h := hmono (show (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin k) < ⟨j + 1, hj⟩ from
          Nat.lt_succ_self j)
        obtain ⟨u, hu⟩ := hodd ⟨j, Nat.lt_of_succ_lt hj⟩
        obtain ⟨v, hv⟩ := hodd ⟨j + 1, hj⟩
        omega)
      have hfactor (i : Fin k) :
          ((a : ℚ) - 2 + 2 * (i : ℕ)) / ((a : ℚ) + 2 * (i : ℕ)) < f i ^ 2 := by
        have hy : (a : ℚ) + 2 * (i : ℕ) ≤ (y i : ℚ) := by exact_mod_cast hstep i
        have hq : (0 : ℚ) < y i := by exact_mod_cast hpos i
        have hbase := ratio_le_sub_div (a := (a : ℚ) + 2 * (i : ℕ)) (q := y i) (d := 2)
          (by positivity) (by norm_num) hy
        rw [add_sub_right_comm] at hbase
        refine hbase.trans_lt ?_
        change 1 - 2 / (y i : ℚ) < (1 - 1 / (y i : ℚ)) ^ 2
        field_simp
        nlinarith
      have hb := strict_telescope_bound hk (by norm_num : (0 : ℚ) ≤ 2) haq f hf hle 2 hfactor
      norm_num at hb ⊢
      linarith
    · have ha' : (a : ℚ) ≤ 2 := by exact_mod_cast (show a ≤ 2 by omega)
      linarith
  · intro hp
    by_cases ha : 3 < a
    · have haq : (3 : ℚ) < a := by exact_mod_cast ha
      have hlarge (i : Fin k) : 3 < y i := by
        exact ha.trans_le (hmono.monotone (show (⟨0, hk⟩ : Fin k) ≤ i from Nat.zero_le _))
      have hstep := first_add_step_le hk (fun i ↦ y i / 3) 1 (fun j hj ↦ by
        have hy := hmono (show (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin k) < ⟨j + 1, hj⟩ from
          Nat.lt_succ_self j)
        exact Nat.succ_le_of_lt (prime_thirds_strict (hp _) (hp _) (hlarge _) hy))
      have hposition (i : Fin k) : a + 3 * i.val ≤ y i + 1 := by
        have hrank : a / 3 + i.val ≤ y i / 3 := by simpa only [one_mul] using hstep i
        have hmod := prime_not_zero_mod_three (hp i) (hlarge i)
        omega
      have hfactor (i : Fin k) :
          ((a : ℚ) - 3 + 3 * (i : ℕ)) / ((a : ℚ) + 3 * (i : ℕ)) < f i ^ 3 := by
        have hy : (a : ℚ) + 3 * (i : ℕ) ≤ (y i : ℚ) + 1 := by exact_mod_cast hposition i
        have hq : (1 : ℚ) < y i := by exact_mod_cast (hp i).one_lt
        have hbase := ratio_le_sub_div (a := (a : ℚ) + 3 * (i : ℕ)) (q := (y i : ℚ) + 1)
          (d := 3) (by positivity) (by norm_num) hy
        rw [add_sub_right_comm] at hbase
        refine hbase.trans_lt ?_
        change 1 - 3 / ((y i : ℚ) + 1) < (1 - 1 / (y i : ℚ)) ^ 3
        field_simp
        nlinarith
      have hb := strict_telescope_bound hk (by norm_num : (0 : ℚ) ≤ 3) haq f hf hle 3 hfactor
      norm_num at hb ⊢
      linarith
    · have ha' : (a : ℚ) ≤ 3 := by exact_mod_cast (show a ≤ 3 by omega)
      linarith

end

end MetaMathlibExt
