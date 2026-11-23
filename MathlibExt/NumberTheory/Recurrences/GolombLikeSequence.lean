/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Closed forms for Golomb-like sequences

This file proves existence, uniqueness, and the block closed form for strictly increasing
positive-integer solutions of `f (f n) = y * n + z`.
-/

@[expose] public section

namespace MetaMathlibExt

private def glk_c (y z : ℤ) : ℤ :=
  (y + z - 1) / 2

private theorem glk_c_spec
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    1 ≤ glk_c y z ∧ 2 * glk_c y z = y + z - 1 := by
  simp only [glk_c]
  omega

private def glk_l (y z : ℤ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => y * glk_l y z k + z

private theorem glk_l_one_le
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) : ∀ k, 1 ≤ glk_l y z k := by
  intro k
  induction k with
  | zero => simp [glk_l]
  | succ k ih =>
    rw [glk_l]
    nlinarith

private theorem glk_l_strict_step
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (k : ℕ) :
    glk_l y z k < glk_l y z (k + 1) := by
  rw [glk_l]
  have hk := glk_l_one_le y z hy hz k
  nlinarith

private theorem glk_l_strictMono
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) : StrictMono (glk_l y z) :=
  strictMono_nat_of_lt_succ (glk_l_strict_step y z hy hz)

private theorem glk_l_growth
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (k : ℕ) :
    (k : ℤ) + 1 ≤ glk_l y z k := by
  induction k with
  | zero => simp [glk_l]
  | succ k ih =>
    have hstep := glk_l_strict_step y z hy hz k
    norm_num at ih ⊢
    omega

private theorem glk_l_unbounded
    (y z x : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) :
    ∃ k : ℕ, x < glk_l y z (k + 1) := by
  refine ⟨x.toNat, ?_⟩
  have hg := glk_l_growth y z hy hz (x.toNat + 1)
  by_cases hx : 0 ≤ x
  · norm_num at hg ⊢
    simp [max_eq_left hx] at hg
    omega
  · have hto : x.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [hto] at hg ⊢
    norm_num at hg ⊢
    omega

private theorem glk_l_closed
    (y z : ℤ) (k : ℕ) :
    (y - 1) * glk_l y z k = (y + z - 1) * y ^ k - z := by
  induction k with
  | zero =>
    simp only [glk_l, pow_zero, mul_one]
    ring
  | succ k ih =>
    rw [glk_l, pow_succ]
    linear_combination y * ih

private theorem glk_l_succ
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) (k : ℕ) :
    glk_l y z (k + 1) = glk_l y z k + 2 * glk_c y z * y ^ k := by
  have hc := (glk_c_spec y z hz hpar).2
  induction k with
  | zero =>
    simp [glk_l]
    omega
  | succ k ih =>
    have hrec : glk_l y z (k + 1) = y * glk_l y z k + z := by
      rw [glk_l]
    calc
      glk_l y z (k + 2) = y * glk_l y z (k + 1) + z := by rw [glk_l]
      _ = y * (glk_l y z k + 2 * glk_c y z * y ^ k) + z := by rw [ih]
      _ = (y * glk_l y z k + z) + 2 * glk_c y z * y ^ (k + 1) := by
        rw [pow_succ]
        ring
      _ = glk_l y z (k + 1) + 2 * glk_c y z * y ^ (k + 1) := by rw [hrec]

private def glk_a (y z : ℤ) (k : ℕ) : ℤ :=
  glk_l y z k + glk_c y z * y ^ k

private theorem glk_l_succ_eq_a_add
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) (k : ℕ) :
    glk_l y z (k + 1) = glk_a y z k + glk_c y z * y ^ k := by
  rw [glk_a, glk_l_succ y z hz hpar k]
  ring

private noncomputable def glk_index
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) : ℕ :=
  Nat.find (glk_l_unbounded y z x hy hz)

private theorem glk_locate
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) (hx : 1 ≤ x) :
    glk_l y z (glk_index y z hy hz x) ≤ x ∧
      x < glk_l y z (glk_index y z hy hz x + 1) := by
  let H := glk_l_unbounded y z x hy hz
  change glk_l y z (Nat.find H) ≤ x ∧ x < glk_l y z (Nat.find H + 1)
  refine ⟨?_, Nat.find_spec H⟩
  cases hk : Nat.find H with
  | zero => simp [glk_l, hx]
  | succ k =>
    have hklt : k < Nat.find H := by omega
    have hmin := Nat.find_min H hklt
    change ¬x < glk_l y z (k + 1) at hmin
    simpa [hk] using le_of_not_gt hmin

private theorem glk_index_eq
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) (k : ℕ)
    (hlow : glk_l y z k ≤ x) (hupp : x < glk_l y z (k + 1)) :
    glk_index y z hy hz x = k := by
  unfold glk_index
  apply (Nat.find_eq_iff (glk_l_unbounded y z x hy hz)).2
  refine ⟨hupp, ?_⟩
  intro n hn hbad
  have hmono := (glk_l_strictMono y z hy hz).monotone
  have hle : glk_l y z (n + 1) ≤ glk_l y z k := by
    apply hmono
    omega
  omega

private noncomputable def glk_v
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) : ℤ :=
  let k := glk_index y z hy hz x
  if x < glk_a y z k then
    glk_l y z (k + 1) + x - glk_a y z k
  else
    glk_l y z (k + 1) + y * (x - glk_a y z k)

private theorem glk_v_of_mem
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (x : ℤ) (k : ℕ)
    (hlow : glk_l y z k ≤ x) (hupp : x < glk_l y z (k + 1)) :
    glk_v y z hy hz x = if x < glk_a y z k then
      glk_l y z (k + 1) + x - glk_a y z k
    else
      glk_l y z (k + 1) + y * (x - glk_a y z k) := by
  rw [glk_v, glk_index_eq y z hy hz x k hlow hupp]

private theorem glk_v_pos
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (x : ℤ) (hx : 1 ≤ x) : 0 < glk_v y z hy hz x := by
  let k := glk_index y z hy hz x
  have hloc := glk_locate y z hy hz x hx
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hcpow : 0 < glk_c y z * y ^ k := by
    exact mul_pos (by exact (glk_c_spec y z hz hpar).1) (pow_pos (by omega) k)
  change 0 < if x < glk_a y z k then
    glk_l y z (k + 1) + x - glk_a y z k
  else
    glk_l y z (k + 1) + y * (x - glk_a y z k)
  split_ifs with hleft
  · unfold glk_a at hnext ⊢
    nlinarith [hloc.1]
  · have hl := glk_l_one_le y z hy hz (k + 1)
    nlinarith

private def glk_toPNat (x : ℤ) (hx : 0 < x) : ℕ+ :=
  ⟨x.toNat, by
    have hcast := Int.toNat_of_nonneg hx.le
    apply Int.natCast_pos.mp
    simpa [hcast] using hx⟩

@[simp] private theorem glk_toPNat_val (x : ℤ) (hx : 0 < x) :
    (↑((glk_toPNat x hx).val) : ℤ) = x := by
  simp [glk_toPNat, Int.toNat_of_nonneg hx.le]

private noncomputable def glk_f
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    ℕ+ → ℕ+ := fun n =>
  glk_toPNat (glk_v y z hy hz n.val)
    (glk_v_pos y z hy hz hpar n.val (by exact_mod_cast n.pos))

private theorem glk_f_val
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (n : ℕ+) :
    (↑((glk_f y z hy hz hpar n).val) : ℤ) = glk_v y z hy hz n.val := by
  simp [glk_f]

private theorem glk_v_step
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (x : ℤ) (hx : 1 ≤ x) :
    glk_v y z hy hz (x + 1) = glk_v y z hy hz x + 1 ∨
      glk_v y z hy hz (x + 1) = glk_v y z hy hz x + y := by
  let k := glk_index y z hy hz x
  have hloc := glk_locate y z hy hz x hx
  change glk_l y z k ≤ x ∧ x < glk_l y z (k + 1) at hloc
  have hcpow : 0 < glk_c y z * y ^ k :=
    mul_pos (by exact (glk_c_spec y z hz hpar).1) (pow_pos (by omega) k)
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hvx := glk_v_of_mem y z hy hz x k hloc.1 hloc.2
  by_cases hblock : x + 1 < glk_l y z (k + 1)
  · have hvnext := glk_v_of_mem y z hy hz (x + 1) k (by omega) hblock
    by_cases hleft : x < glk_a y z k
    · left
      rw [hvx, hvnext]
      by_cases hleft' : x + 1 < glk_a y z k
      · simp [hleft, hleft']
        ring
      · have heq : x + 1 = glk_a y z k := by omega
        simp [hleft, heq]
        omega
    · right
      rw [hvx, hvnext]
      have hleft' : ¬x + 1 < glk_a y z k := by omega
      simp [hleft, hleft']
      ring
  · have hboundary : x + 1 = glk_l y z (k + 1) := by omega
    have hupp := glk_l_strict_step y z hy hz (k + 1)
    have hvnext := glk_v_of_mem y z hy hz (x + 1) (k + 1) (by omega) (by omega)
    have hnotleft : ¬x < glk_a y z k := by
      unfold glk_a at hnext ⊢
      nlinarith
    have hnextleft : x + 1 < glk_a y z (k + 1) := by
      rw [hboundary]
      unfold glk_a
      exact lt_add_of_pos_right _
        (mul_pos (lt_of_lt_of_le Int.zero_lt_one (glk_c_spec y z hz hpar).1)
          (pow_pos (by omega : 0 < y) (k + 1)))
    right
    rw [hvx, hvnext]
    rw [ite_eq_right hnotleft, ite_eq_left hnextleft]
    have hmid := glk_l_succ_eq_a_add y z hz hpar (k + 1)
    have hxEq : x = glk_l y z (k + 1) - 1 := by omega
    rw [hxEq, hmid]
    unfold glk_a at hnext ⊢
    rw [hnext, pow_succ]
    ring

private theorem glk_v_comp
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (x : ℤ) (hx : 1 ≤ x) :
    glk_v y z hy hz (glk_v y z hy hz x) = y * x + z := by
  let k := glk_index y z hy hz x
  have hloc := glk_locate y z hy hz x hx
  change glk_l y z k ≤ x ∧ x < glk_l y z (k + 1) at hloc
  have hcpow : 0 < glk_c y z * y ^ k :=
    mul_pos (by exact (glk_c_spec y z hz hpar).1) (pow_pos (by omega) k)
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hvx := glk_v_of_mem y z hy hz x k hloc.1 hloc.2
  have hlrec : glk_l y z (k + 1) = y * glk_l y z k + z := by rw [glk_l]
  by_cases hleft : x < glk_a y z k
  · rw [hvx]
    simp only [hleft, ↓reduceIte]
    have hvlow : glk_l y z k ≤
        glk_l y z (k + 1) + x - glk_a y z k := by
      unfold glk_a at hnext ⊢
      nlinarith
    have hvupp : glk_l y z (k + 1) + x - glk_a y z k <
        glk_l y z (k + 1) := by omega
    rw [glk_v_of_mem y z hy hz _ k hvlow hvupp]
    have hvright : ¬glk_l y z (k + 1) + x - glk_a y z k < glk_a y z k := by
      unfold glk_a at hnext ⊢
      nlinarith
    rw [ite_eq_right hvright]
    unfold glk_a at hnext ⊢
    nlinarith
  · rw [hvx]
    simp only [hleft, ↓reduceIte]
    have hvlow : glk_l y z (k + 1) ≤
        glk_l y z (k + 1) + y * (x - glk_a y z k) := by
      nlinarith
    have hanext : glk_a y z (k + 1) =
        glk_l y z (k + 1) + glk_c y z * y ^ (k + 1) := by rfl
    have hvupp : glk_l y z (k + 1) + y * (x - glk_a y z k) <
        glk_l y z (k + 2) := by
      have hmid := glk_l_succ_eq_a_add y z hz hpar (k + 1)
      rw [hmid]
      unfold glk_a at hnext ⊢
      rw [pow_succ]
      nlinarith
    rw [glk_v_of_mem y z hy hz _ (k + 1) hvlow hvupp]
    have hvleft : glk_l y z (k + 1) + y * (x - glk_a y z k) <
        glk_a y z (k + 1) := by
      rw [hanext]
      unfold glk_a at hnext ⊢
      rw [pow_succ]
      nlinarith
    rw [ite_eq_left hvleft]
    have hmid := glk_l_succ_eq_a_add y z hz hpar (k + 1)
    rw [hmid]
    unfold glk_a at hnext ⊢
    rw [pow_succ]
    nlinarith [hlrec]

private def glk_seq (f : ℕ+ → ℕ+) (n : ℕ) : ℕ :=
  (f n.succPNat).val

private theorem glk_seq_strict_of_strict (f : ℕ+ → ℕ+) (hf : StrictMono f) :
    StrictMono (glk_seq f) := by
  intro a b hab
  have hp : a.succPNat < b.succPNat := by simpa using hab
  simpa [glk_seq] using hf hp

private theorem glk_strict_of_seq_strict (f : ℕ+ → ℕ+)
    (hf : StrictMono (glk_seq f)) : StrictMono f := by
  intro a b hab
  have hp : a.natPred < b.natPred := by
    have ha := a.pos
    have hb := b.pos
    change a.val - 1 < b.val - 1
    exact (Nat.sub_lt_sub_iff_right (by omega)).2 hab
  simpa [glk_seq] using hf hp

private theorem glk_v_one
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    glk_v y z hy hz 1 = glk_c y z + 1 := by
  have hsum : 2 ≤ y + z := by omega
  have hv := glk_v_of_mem y z hy hz 1 0 (by simp [glk_l]) (by simp [glk_l]; omega)
  have hc := glk_c_spec y z hz hpar
  rw [hv]
  have hleft : (1 : ℤ) < glk_a y z 0 := by
    simp [glk_a, glk_l]
    omega
  simp [glk_a, glk_l]
  omega

private theorem glk_f_seq_step
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (n : ℕ) :
    glk_seq (glk_f y z hy hz hpar) (n + 1) =
        glk_seq (glk_f y z hy hz hpar) n + 1 ∨
      glk_seq (glk_f y z hy hz hpar) (n + 1) =
        glk_seq (glk_f y z hy hz hpar) n + y.toNat := by
  have hs := glk_v_step y z hy hz hpar ((n : ℤ) + 1) (by omega)
  have hn := glk_f_val y z hy hz hpar n.succPNat
  have hn1 := glk_f_val y z hy hz hpar (n + 1).succPNat
  have hycast : (↑y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
  norm_num [glk_seq] at hn hn1
  rcases hs with hs | hs
  · left
    apply Int.ofNat_inj.mp
    simp only [glk_seq]
    push_cast
    rw [hn, hn1]
    exact hs
  · right
    apply Int.ofNat_inj.mp
    simp only [glk_seq]
    push_cast
    rw [hn, hn1, hycast]
    exact hs

private theorem glk_f_strictMono
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    StrictMono (glk_f y z hy hz hpar) := by
  apply glk_strict_of_seq_strict
  apply strictMono_nat_of_lt_succ
  intro n
  rcases glk_f_seq_step y z hy hz hpar n with h | h
  · omega
  · have hycast : (↑y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hyNat : 2 ≤ y.toNat := by omega
    omega

private theorem glk_f_one
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    (↑((glk_f y z hy hz hpar 1).val) : ℤ) = glk_c y z + 1 := by
  calc
    (↑((glk_f y z hy hz hpar 1).val) : ℤ) = glk_v y z hy hz 1 := by
      simpa using glk_f_val y z hy hz hpar (1 : ℕ+)
    _ = glk_c y z + 1 := glk_v_one y z hy hz hpar

private theorem glk_f_comp
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (n : ℕ+) :
    (↑((glk_f y z hy hz hpar (glk_f y z hy hz hpar n)).val) : ℤ) =
      y * (↑n.val : ℤ) + z := by
  calc
    (↑((glk_f y z hy hz hpar (glk_f y z hy hz hpar n)).val) : ℤ) =
        glk_v y z hy hz (↑((glk_f y z hy hz hpar n).val) : ℤ) :=
      glk_f_val y z hy hz hpar _
    _ = glk_v y z hy hz (glk_v y z hy hz n.val) := by
      rw [glk_f_val y z hy hz hpar n]
    _ = y * (↑n.val : ℤ) + z :=
      glk_v_comp y z hy hz hpar n.val (by exact_mod_cast n.pos)

private theorem glk_strict_interval
    (q : ℕ → ℕ) (hq : StrictMono q) (a b m r d : ℕ)
    (ham : a ≤ m) (hmb : m ≤ b) (hab : b = a + d)
    (hqa : q a = r) (hqb : q b = r + d) :
    q m = r + (m - a) := by
  have hlo := hq.add_le_nat (m - a) a
  rw [Nat.sub_add_cancel ham, hqa] at hlo
  have hhi := hq.add_le_nat (b - m) m
  rw [Nat.sub_add_cancel hmb, hqb] at hhi
  omega

private theorem glk_seq_initial
    (C Y : ℕ) (q : ℕ → ℕ) (hq : StrictMono q)
    (hq0 : q 0 = C + 1)
    (hcomp : ∀ n, q (q n - 1) = Y * n + 2 * C + 1)
    (m : ℕ) (hm : m < C + 1) :
    q m = C + 1 + m := by
  have hmC : m ≤ C := by omega
  have hlo := hq.add_le_nat m 0
  simp only [Nat.add_zero, hq0] at hlo
  have hqC : q C = 2 * C + 1 := by
    simpa [hq0] using hcomp 0
  have hhi := hq.add_le_nat (C - m) m
  rw [Nat.sub_add_cancel hmC, hqC] at hhi
  omega

private theorem glk_unique_seq
    (C Y : ℕ) (hC : 1 ≤ C) (hY : 2 ≤ Y)
    (F q : ℕ → ℕ) (hF : StrictMono F) (hq : StrictMono q)
    (hF0 : F 0 = C + 1) (hq0 : q 0 = C + 1)
    (hFcomp : ∀ n, F (F n - 1) = Y * n + 2 * C + 1)
    (hqcomp : ∀ n, q (q n - 1) = Y * n + 2 * C + 1)
    (hFstep : ∀ n, F (n + 1) = F n + 1 ∨ F (n + 1) = F n + Y) :
    q = F := by
  funext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < C + 1
    · rw [glk_seq_initial C Y q hq hq0 hqcomp m hm,
        glk_seq_initial C Y F hF hF0 hFcomp m hm]
    · have hmC : C + 1 ≤ m := by omega
      have hex : ∃ n : ℕ, m + 1 < q (n + 1) := by
        refine ⟨m, ?_⟩
        have hgrow := hq.add_le_nat (m + 1) 0
        simp only [Nat.add_zero, hq0] at hgrow
        omega
      let n := Nat.find hex
      have hupp : m + 1 < q (n + 1) := Nat.find_spec hex
      have hlow : q n ≤ m + 1 := by
        by_cases hn : n = 0
        · rw [hn, hq0]
          omega
        · have hpred : n - 1 < Nat.find hex := by
            change n - 1 < n
            omega
          have hmin := Nat.find_min hex hpred
          change ¬m + 1 < q (n - 1 + 1) at hmin
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hmin
          omega
      by_cases heq : q n = m + 1
      · have hgrow := hq.add_le_nat n 0
        simp only [Nat.add_zero, hq0] at hgrow
        have hnm : n < m := by omega
        have ihn := ih n hnm
        have hgm : q m = Y * n + 2 * C + 1 := by
          have hc := hqcomp n
          have hind : q n - 1 = m := by omega
          rwa [hind] at hc
        have hFm : F m = Y * n + 2 * C + 1 := by
          have hc := hFcomp n
          have hFn : F n = m + 1 := by omega
          rw [hFn] at hc
          simpa using hc
        omega
      · have hinterior : q n < m + 1 := by omega
        have hgrow := hq.add_le_nat n 0
        simp only [Nat.add_zero, hq0] at hgrow
        have hnm : n < m := by omega
        have hn1m : n + 1 < m := by omega
        have ihn := ih n hnm
        have ihn1 := ih (n + 1) hn1m
        have hgap : q (n + 1) = q n + Y := by
          rcases hFstep n with hs | hs
          · omega
          · omega
        have hqnpos : 1 ≤ q n := by omega
        have ham : q n - 1 ≤ m := by omega
        have hmb : m ≤ q (n + 1) - 1 := by omega
        have hab : q (n + 1) - 1 = (q n - 1) + Y := by omega
        have hqa := hqcomp n
        have hqb := hqcomp (n + 1)
        simp only [Nat.mul_add, Nat.mul_one] at hqb
        have hqm := glk_strict_interval q hq (q n - 1) (q (n + 1) - 1) m
          (Y * n + 2 * C + 1) Y ham hmb hab hqa (by omega)
        have hFa : F (q n - 1) = Y * n + 2 * C + 1 := by
          rw [ihn]
          exact hFcomp n
        have hFb : F (q (n + 1) - 1) = Y * n + 2 * C + 1 + Y := by
          rw [ihn1]
          have hc := hFcomp (n + 1)
          simp only [Nat.mul_add, Nat.mul_one] at hc
          omega
        have hFm := glk_strict_interval F hF (q n - 1) (q (n + 1) - 1) m
          (Y * n + 2 * C + 1) Y ham hmb hab hFa hFb
        omega

private theorem glk_initial_int
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (f : ℕ+ → ℕ+)
    (hone : (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2) :
    (↑((f 1).val) : ℤ) = glk_c y z + 1 := by
  have hc := (glk_c_spec y z hz hpar).2
  have hrat : ((y : ℚ) + (z : ℚ) + 1) / 2 = (glk_c y z : ℚ) + 1 := by
    apply (div_eq_iff (by norm_num : (2 : ℚ) ≠ 0)).2
    exact_mod_cast (by omega : y + z + 1 = (glk_c y z + 1) * 2)
  rw [hrat] at hone
  exact_mod_cast hone

private theorem glk_seq_zero_of_initial_int
    (y z : ℤ) (f : ℕ+ → ℕ+)
    (h : (↑((f 1).val) : ℤ) = glk_c y z + 1) :
    glk_seq f 0 = (glk_c y z).toNat + 1 := by
  have hcpos : 0 ≤ glk_c y z := by
    have hfpos := (f 1).pos
    have hfposInt : (1 : ℤ) ≤ (↑((f 1).val) : ℤ) := by exact_mod_cast hfpos
    omega
  unfold glk_seq
  rw [show (0 : ℕ).succPNat = (1 : ℕ+) by rfl]
  apply Int.ofNat_inj.mp
  push_cast
  simpa [glk_seq, Int.ofNat_toNat, max_eq_left hcpos] using h

private theorem glk_seq_comp
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (f : ℕ+ → ℕ+)
    (hcomp : ∀ n : ℕ+, (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z)
    (n : ℕ) :
    glk_seq f (glk_seq f n - 1) =
      y.toNat * n + 2 * (glk_c y z).toNat + 1 := by
  have hc := glk_c_spec y z hz hpar
  have hycast : (↑y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
  have hccast : (↑(glk_c y z).toNat : ℤ) = glk_c y z :=
    Int.toNat_of_nonneg (by omega)
  have hrec := hcomp n.succPNat
  have hleft : (↑(glk_seq f (glk_seq f n - 1)) : ℤ) =
      y * ((n : ℤ) + 1) + z := by
    have hp : (glk_seq f n - 1).succPNat = f n.succPNat := by
      change ((f n.succPNat).val - 1).succPNat = f n.succPNat
      exact PNat.succPNat_natPred _
    change (↑((f (glk_seq f n - 1).succPNat).val) : ℤ) =
      y * ((n : ℤ) + 1) + z
    rw [hp]
    simpa using hrec
  apply Int.ofNat_inj.mp
  push_cast
  rw [hleft, hycast, hccast]
  ring_nf
  omega

private theorem glk_f_unique
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (f : ℕ+ → ℕ+) (hf : StrictMono f)
    (hone : (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2)
    (hcomp : ∀ n : ℕ+, (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) :
    f = glk_f y z hy hz hpar := by
  let C := (glk_c y z).toNat
  let Y := y.toNat
  have hc := glk_c_spec y z hz hpar
  have hCcast : (↑C : ℤ) = glk_c y z := Int.toNat_of_nonneg (by omega)
  have hYcast : (↑Y : ℤ) = y := Int.toNat_of_nonneg (by omega)
  have hC : 1 ≤ C := by omega
  have hY : 2 ≤ Y := by omega
  have hf0int := glk_initial_int y z hz hpar f hone
  have hF0int := glk_f_one y z hy hz hpar
  have hf0 := glk_seq_zero_of_initial_int y z f hf0int
  have hF0 := glk_seq_zero_of_initial_int y z (glk_f y z hy hz hpar) hF0int
  change glk_seq f 0 = C + 1 at hf0
  change glk_seq (glk_f y z hy hz hpar) 0 = C + 1 at hF0
  have hseq := glk_unique_seq C Y hC hY
    (glk_seq (glk_f y z hy hz hpar)) (glk_seq f)
    (glk_seq_strict_of_strict _ (glk_f_strictMono y z hy hz hpar))
    (glk_seq_strict_of_strict f hf) hF0 hf0
    (by
      intro n
      exact glk_seq_comp y z hy hz hpar _ (glk_f_comp y z hy hz hpar) n)
    (by
      intro n
      exact glk_seq_comp y z hy hz hpar f hcomp n)
    (glk_f_seq_step y z hy hz hpar)
  funext n
  have hn := congrFun hseq n.natPred
  simpa [glk_seq] using hn

private theorem glk_block_formula
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (k : ℕ) (j : ℤ)
    (hlow : -(glk_c y z * y ^ k) ≤ j) (hupp : j < glk_c y z * y ^ k) :
    ∃ m : ℕ+,
      (↑m.val : ℤ) = glk_a y z k + j ∧
      (↑((glk_f y z hy hz hpar m).val) : ℤ) =
        glk_l y z (k + 1) + if j < 0 then j else y * j := by
  have hnext := glk_l_succ_eq_a_add y z hz hpar k
  have hxlow : glk_l y z k ≤ glk_a y z k + j := by
    unfold glk_a at hnext ⊢
    nlinarith
  have hxupp : glk_a y z k + j < glk_l y z (k + 1) := by omega
  have hxpos : 0 < glk_a y z k + j :=
    lt_of_lt_of_le Int.zero_lt_one (le_trans (glk_l_one_le y z hy hz k) hxlow)
  let m := glk_toPNat (glk_a y z k + j) hxpos
  refine ⟨m, glk_toPNat_val _ _, ?_⟩
  rw [glk_f_val]
  rw [glk_toPNat_val, glk_v_of_mem y z hy hz _ k hxlow hxupp]
  by_cases hj : j < 0
  · simp [hj]
    ring
  · simp [hj]

private theorem glk_c_rat
    (y z : ℤ) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    (glk_c y z : ℚ) = ((y : ℚ) + (z : ℚ) - 1) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
  exact_mod_cast (by
    have hc := (glk_c_spec y z hz hpar).2
    omega : glk_c y z * 2 = y + z - 1)

private theorem glk_l_rat (y z : ℤ) (hy : 2 ≤ y) (k : ℕ) :
    (glk_l y z k : ℚ) =
      ((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1) * (y : ℚ) ^ k -
        (z : ℚ) / ((y : ℚ) - 1) := by
  have hden : (y : ℚ) - 1 ≠ 0 := by exact_mod_cast (by omega : y - 1 ≠ 0)
  field_simp [hden]
  exact_mod_cast (by
    simpa [mul_comm] using glk_l_closed y z k :
      glk_l y z k * (y - 1) = (y + z - 1) * y ^ k - z)

private theorem glk_a_rat
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (k : ℕ) :
    (glk_a y z k : ℚ) =
      (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
        (2 * ((y : ℚ) - 1))) * (y : ℚ) ^ k -
        (z : ℚ) / ((y : ℚ) - 1) := by
  have hden : (y : ℚ) - 1 ≠ 0 := by exact_mod_cast (by omega : y - 1 ≠ 0)
  rw [glk_a]
  push_cast
  rw [glk_l_rat y z hy k]
  have hc := glk_c_rat y z hz hpar
  rw [hc]
  field_simp [hden]
  ring

private theorem glk_offset_rat (y j : ℤ) :
    (if j < 0 then (j : ℚ) else (y : ℚ) * (j : ℚ)) =
      ((y : ℚ) + 1) * (j : ℚ) / 2 +
        ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
  by_cases hj : j < 0
  · have hjq : (j : ℚ) < 0 := by exact_mod_cast hj
    rw [ite_eq_left hj, abs_of_neg hjq]
    ring
  · have hjq : 0 ≤ (j : ℚ) := by exact_mod_cast (by omega : 0 ≤ j)
    rw [ite_eq_right hj, abs_of_nonneg hjq]
    ring

private theorem glk_closed_form
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2)
    (k : ℕ) (j : ℤ)
    (hlow : -(((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k ≤ (j : ℚ))
    (hupp : (j : ℚ) < (((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k) :
    ∃ m : ℕ+,
      (↑m.val : ℚ) =
          (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
            (2 * ((y : ℚ) - 1))) *
            (y : ℚ) ^ k -
          (z : ℚ) / ((y : ℚ) - 1) + (j : ℚ) ∧
      (↑((glk_f y z hy hz hpar m).val) : ℚ) =
          (((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1)) *
            (y : ℚ) ^ (k + 1) -
          (z : ℚ) / ((y : ℚ) - 1) +
          ((y : ℚ) + 1) * (j : ℚ) / 2 +
          ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
  have hcq := glk_c_rat y z hz hpar
  have hlowInt : -(glk_c y z * y ^ k) ≤ j := by
    rw [← hcq] at hlow
    have h : -glk_c y z * y ^ k ≤ j := by exact_mod_cast hlow
    simpa only [neg_mul] using h
  have huppInt : j < glk_c y z * y ^ k := by
    rw [← hcq] at hupp
    exact_mod_cast hupp
  obtain ⟨m, hm, hfm⟩ := glk_block_formula y z hy hz hpar k j hlowInt huppInt
  refine ⟨m, ?_, ?_⟩
  · have hmQ : (↑m.val : ℚ) = (glk_a y z k : ℚ) + (j : ℚ) := by
      exact_mod_cast hm
    rw [glk_a_rat y z hy hz hpar k] at hmQ
    exact hmQ
  · have hfmQ : (↑((glk_f y z hy hz hpar m).val) : ℚ) =
        (glk_l y z (k + 1) : ℚ) +
          if j < 0 then (j : ℚ) else (y : ℚ) * (j : ℚ) := by
      by_cases hj : j < 0
      · rw [ite_eq_left hj]
        simp only [hj, ↓reduceIte] at hfm
        exact_mod_cast hfm
      · rw [ite_eq_right hj]
        simp only [hj, ↓reduceIte] at hfm
        exact_mod_cast hfm
    rw [glk_l_rat y z hy (k + 1), glk_offset_rat y j] at hfmQ
    simpa only [add_assoc] using hfmQ

private theorem glk_f_one_rat
    (y z : ℤ) (hy : 2 ≤ y) (hz : 2 - y ≤ z) (hpar : y % 2 ≠ z % 2) :
    (↑((glk_f y z hy hz hpar 1).val) : ℚ) =
      ((y : ℚ) + (z : ℚ) + 1) / 2 := by
  have hInt := glk_f_one y z hy hz hpar
  have hRat : (↑((glk_f y z hy hz hpar 1).val) : ℚ) =
      (glk_c y z : ℚ) + 1 := by
    exact_mod_cast hInt
  rw [glk_c_rat y z hz hpar] at hRat
  calc
    (↑((glk_f y z hy hz hpar 1).val) : ℚ) =
        ((y : ℚ) + (z : ℚ) - 1) / 2 + 1 := hRat
    _ = ((y : ℚ) + (z : ℚ) + 1) / 2 := by ring

/--
**Closed form for Golomb-like sequences.** Let $y$ and $z$ be integers of opposite parity with
$y \ge 2$ and $z \ge 2 - y$, and put $c = (y + z - 1)/2$. There is exactly one strictly
increasing function $f$ from the positive integers to the positive integers such that
$f(1) = (y + z + 1)/2$ and $f(f(n)) = yn + z$ for every positive integer $n$. Moreover, for
every such $f$, every natural number $k$ and every integer $j$ with $-c\,y^k \le j < c\,y^k$,
the rational number
$$m = \frac{(y+1)\,c}{y-1}\, y^k - \frac{z}{y-1} + j$$
is a positive integer and
$$f(m) = \frac{2c}{y-1}\, y^{k+1} - \frac{z}{y-1} + \frac{(y+1)\,j}{2} + \frac{(y-1)\,|j|}{2}.$$

Proof: The construction tiles the positive integers by the source's blocks and verifies the
two slope regimes, followed by strong-induction uniqueness, as in Cloitre–Sloane–Vandermast,
Theorem Th1 and equations (Eq48a), (Eq48).

Source: Benoit Cloitre, N. J. A. Sloane, and Matthew J. Vandermast,
"Numerical Analogues of Aronson's Sequence," Journal of Integer
Sequences 6 (2003), Article 03.2.2, Theorem (label Th1), equations
(Eq48a) and (Eq48), lines 584–603,
https://cs.uwaterloo.ca/journals/JIS/VOL6/Cloitre/cloitre2.tex
-/
public theorem golomb_like_closed_form
    (y z : ℤ)
    (hy : 2 ≤ y)
    (hz : 2 - y ≤ z)
    (hpar : y % 2 ≠ z % 2) :
    (∃! f : ℕ+ → ℕ+,
      StrictMono f ∧
      (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 ∧
      ∀ n : ℕ+,
        (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) ∧
    ∀ f : ℕ+ → ℕ+,
      StrictMono f →
      (↑((f 1).val) : ℚ) = ((y : ℚ) + (z : ℚ) + 1) / 2 →
      (∀ n : ℕ+,
        (↑((f (f n)).val) : ℤ) = y * (↑n.val : ℤ) + z) →
      ∀ k : ℕ, ∀ j : ℤ,
        -(((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k ≤ (j : ℚ) →
        (j : ℚ) < (((y : ℚ) + (z : ℚ) - 1) / 2) * (y : ℚ) ^ k →
        ∃ m : ℕ+,
          (↑m.val : ℚ) =
              (((y : ℚ) + 1) * ((y : ℚ) + (z : ℚ) - 1) /
                (2 * ((y : ℚ) - 1))) *
                (y : ℚ) ^ k -
              (z : ℚ) / ((y : ℚ) - 1) + (j : ℚ) ∧
          (↑((f m).val) : ℚ) =
              (((y : ℚ) + (z : ℚ) - 1) / ((y : ℚ) - 1)) *
                (y : ℚ) ^ (k + 1) -
              (z : ℚ) / ((y : ℚ) - 1) +
              ((y : ℚ) + 1) * (j : ℚ) / 2 +
              ((y : ℚ) - 1) * |(j : ℚ)| / 2 := by
  constructor
  · refine ⟨glk_f y z hy hz hpar, ?_, ?_⟩
    · exact ⟨glk_f_strictMono y z hy hz hpar, glk_f_one_rat y z hy hz hpar,
        glk_f_comp y z hy hz hpar⟩
    · intro f hf
      exact glk_f_unique y z hy hz hpar f hf.1 hf.2.1 hf.2.2
  · intro f hf hone hcomp k j hlow hupp
    rw [glk_f_unique y z hy hz hpar f hf hone hcomp]
    exact glk_closed_form y z hy hz hpar k j hlow hupp

end MetaMathlibExt
