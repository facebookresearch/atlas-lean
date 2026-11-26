/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.QuadraticForms.LegendreThreeSquare
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.MultiplicativeAdditiveEightSquares
import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquares
import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresRigidity
import MathlibExt.NumberTheory.MultiplicativeAdditiveThreePairedSquares
import MathlibExt.NumberTheory.SixAndEightNonzeroSquares

/-!
# Dubouis's theorem on sums of nonzero squares

For `m ≥ 4`, a positive integer is a sum of `m` squares of positive integers if and only
if it lies outside the exceptional set `E_m` (`sum_nonzero_squares_iff_not_mem_exceptional`).
Sums of four nonzero squares come from Legendre's three-square theorem with residues forcing
every root to be nonzero; sums of five from sums of four; for `m ≥ 6`, from sums of six
with ones appended.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 1 (`integers-2026-A121-lem-1`), quoting
Dubouis (1911).
-/

namespace MetaMathlibExt

private theorem one_le_sq_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a ^ 2 := by
  have h : 1 ≤ a := Nat.pos_of_ne_zero ha
  simpa using Nat.pow_le_pow_left h 2

private theorem append_ones (m n k : ℕ)
    (h : ∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) :
    ∃ a : Fin (m + k) → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n + k := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    obtain ⟨a, ha0, hsum⟩ := ih
    have heq : m + (k + 1) = (m + k) + 1 := by omega
    rw [heq]
    refine ⟨Fin.cons 1 a, ?_, ?_⟩
    · rw [Fin.forall_fin_succ]
      constructor
      · rw [Fin.cons_zero]
        exact one_ne_zero
      · intro i
        rw [Fin.cons_succ]
        exact ha0 i
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum, one_pow]
      omega

private theorem fin_of_list (l : List ℕ) (n : ℕ) (hzero : 0 ∉ l)
    (hsum : (l.map (· ^ 2)).sum = n) :
    ∃ a : Fin l.length → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  refine ⟨fun i => l[i.val], fun i hi => hzero (hi ▸ List.getElem_mem i.isLt), ?_⟩
  rw [← List.sum_ofFn]
  simpa only [List.map_ofFn, Function.comp_def] using
    (congrArg (fun xs : List ℕ => (xs.map (· ^ 2)).sum)
      (List.ofFn_getElem (xs := l))).trans hsum

private theorem counts_of_list (l : List ℕ) :
    (∀ a ∈ l, 1 ≤ a ∧ a ≤ 6) →
      ∃ x y z w v : ℕ, (l.map (· ^ 2)).sum = l.length + 3 * x + 8 * y +
        15 * z + 24 * w + 35 * v ∧ x + y + z + w + v ≤ l.length := by
  induction l with
  | nil => intro _; exact ⟨0, 0, 0, 0, 0, by simp, by simp⟩
  | cons a l ih =>
    intro hall
    have ha : 1 ≤ a ∧ a ≤ 6 := hall a (by simp)
    have hl : ∀ b ∈ l, 1 ≤ b ∧ b ≤ 6 := fun b hb => hall b (List.mem_cons.mpr (Or.inr hb))
    obtain ⟨x, y, z, w, v, hsum, hle⟩ := ih hl
    have ha1 : 1 ≤ a := ha.1
    have ha2 : a ≤ 6 := ha.2
    interval_cases a
    · have hk : (1 : ℕ) ^ 2 = 1 := by decide
      exact ⟨x, y, z, w, v, by simp only [List.map_cons, List.sum_cons, List.length_cons]; omega,
        by simp only [List.length_cons]; omega⟩
    · have hk : (2 : ℕ) ^ 2 = 4 := by decide
      exact ⟨x + 1, y, z, w, v,
        by simp only [List.map_cons, List.sum_cons, List.length_cons]; omega,
        by simp only [List.length_cons]; omega⟩
    · have hk : (3 : ℕ) ^ 2 = 9 := by decide
      exact ⟨x, y + 1, z, w, v,
        by simp only [List.map_cons, List.sum_cons, List.length_cons]; omega,
        by simp only [List.length_cons]; omega⟩
    · have hk : (4 : ℕ) ^ 2 = 16 := by decide
      exact ⟨x, y, z + 1, w, v,
        by simp only [List.map_cons, List.sum_cons, List.length_cons]; omega,
        by simp only [List.length_cons]; omega⟩
    · have hk : (5 : ℕ) ^ 2 = 25 := by decide
      exact ⟨x, y, z, w + 1, v,
        by simp only [List.map_cons, List.sum_cons, List.length_cons]; omega,
        by simp only [List.length_cons]; omega⟩
    · have hk : (6 : ℕ) ^ 2 = 36 := by decide
      exact ⟨x, y, z, w, v + 1,
        by simp only [List.map_cons, List.sum_cons, List.length_cons]; omega,
        by simp only [List.length_cons]; omega⟩

private theorem bounded_counts (m n : ℕ) (a : Fin m → ℕ)
    (ha : ∀ i, a i ≠ 0) (hs : ∑ i, a i ^ 2 = n) (hn : n ≤ m + 37) :
    ∃ x y z w v : ℕ, n = m + 3 * x + 8 * y + 15 * z + 24 * w + 35 * v ∧
      x + y + z + w + v ≤ m := by
  have hge1 : ∀ i, 1 ≤ a i := fun i => Nat.pos_of_ne_zero (ha i)
  have hsq1 : ∀ i, 1 ≤ (a i) ^ 2 := fun i => one_le_sq_of_ne_zero (a i) (ha i)
  have hbound : ∀ i, a i ≤ 6 := by
    intro i
    have hadd : (a i) ^ 2 + ∑ x ∈ Finset.univ.erase i, (a x) ^ 2 = ∑ x, (a x) ^ 2 :=
      Finset.add_sum_erase Finset.univ (fun j => (a j) ^ 2) (Finset.mem_univ i)
    have hsum_eq : (a i) ^ 2 + ∑ j ∈ Finset.univ.erase i, (a j) ^ 2 = n := by
      rw [hs] at hadd
      exact hadd
    have hcard : (Finset.univ.erase i).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hge : m - 1 ≤ ∑ j ∈ Finset.univ.erase i, (a j) ^ 2 := by
      have h1 : ∑ _j ∈ Finset.univ.erase i, (1 : ℕ) ≤ ∑ j ∈ Finset.univ.erase i, (a j) ^ 2 :=
        Finset.sum_le_sum (fun j _ => hsq1 j)
      rw [Finset.sum_const, hcard] at h1
      simpa using h1
    have ha2 : (a i) ^ 2 ≤ 38 := by omega
    by_contra hcon
    have h7 : 7 ≤ a i := by omega
    have h2 := Nat.pow_le_pow_left h7 2
    have h49 : (7 : ℕ) ^ 2 = 49 := by decide
    omega
  have hmem : ∀ b ∈ List.ofFn a, 1 ≤ b ∧ b ≤ 6 := by
    intro b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨hge1 i, hbound i⟩
  obtain ⟨x, y, z, w, v, hsum, hle⟩ := counts_of_list (List.ofFn a) hmem
  have hlen : (List.ofFn a).length = m := List.length_ofFn
  have hmap : ((List.ofFn a).map (· ^ 2)).sum = n := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact hs
  rw [hlen] at hle
  rw [hlen, hmap] at hsum
  exact ⟨x, y, z, w, v, hsum, hle⟩

private theorem four_small_excluded (n : ℕ)
    (hn : n ∈ ({1, 2, 3, 5, 6, 9, 11, 14, 17, 29, 41} : Set ℕ)) :
    ¬ ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  rintro ⟨a, ha0, hsum⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  have h42 : n ≤ 4 + 37 := by omega
  obtain ⟨x, y, z, w, v, heq, hle⟩ := bounded_counts 4 n a ha0 hsum h42
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (have hv : v ≤ 1 := by omega
     have hw : w ≤ 1 := by omega
     have hz : z ≤ 2 := by omega
     interval_cases v <;> interval_cases w <;> interval_cases z <;> omega)

private theorem five_excluded (n : ℕ)
    (hn : n ∈ ({1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33} : Set ℕ)) :
    ¬ ∃ a : Fin 5 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  rintro ⟨a, ha0, hsum⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  have h42 : n ≤ 5 + 37 := by omega
  obtain ⟨x, y, z, w, v, heq, hle⟩ := bounded_counts 5 n a ha0 hsum h42
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (have hv : v = 0 := by omega
     have hw : w ≤ 1 := by omega
     have hz : z ≤ 1 := by omega
     interval_cases w <;> interval_cases z <;> omega)

private theorem square_mod_eight (a : ℕ) :
    a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h8 : a % 8 < 8 := Nat.mod_lt a (by decide)
  have hmem : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨
      a % 8 = 6 ∨ a % 8 = 7 := by omega
  rcases hmem with h | h | h | h | h | h | h | h <;> rw [Nat.pow_mod, h] <;> decide

private theorem even_of_square_mod_eight (a : ℕ) (ha : a ^ 2 % 8 ≠ 1) :
    a % 2 = 0 := by
  have hsq := square_mod_eight a
  have heven : a ^ 2 % 2 = 0 := by
    rcases hsq with h | h | h
    · omega
    · exact absurd h ha
    · omega
  have hpow : a ^ 2 % 2 = ((a % 2) ^ 2) % 2 := Nat.pow_mod a 2 2
  have h01 : a % 2 = 0 ∨ a % 2 = 1 := by
    have h2 : a % 2 < 2 := Nat.mod_lt a (by decide)
    omega
  rcases h01 with h0 | h0
  · exact h0
  · exfalso
    rw [heven, h0] at hpow
    simp at hpow

private theorem four_roots_even (a : Fin 4 → ℕ) (ha : (∑ i, a i ^ 2) % 8 = 0) :
    ∀ i, a i % 2 = 0 := by
  simp only [Fin.sum_univ_four] at ha
  have s0 := square_mod_eight (a 0)
  have s1 := square_mod_eight (a 1)
  have s2 := square_mod_eight (a 2)
  have s3 := square_mod_eight (a 3)
  have e0 : (a 0) ^ 2 % 8 ≠ 1 := by
    intro hc
    rcases s1 with h | h | h <;> rcases s2 with h' | h' | h' <;>
      rcases s3 with h'' | h'' | h'' <;> omega
  have e1 : (a 1) ^ 2 % 8 ≠ 1 := by
    intro hc
    rcases s0 with h | h | h <;> rcases s2 with h' | h' | h' <;>
      rcases s3 with h'' | h'' | h'' <;> omega
  have e2 : (a 2) ^ 2 % 8 ≠ 1 := by
    intro hc
    rcases s0 with h | h | h <;> rcases s1 with h' | h' | h' <;>
      rcases s3 with h'' | h'' | h'' <;> omega
  have e3 : (a 3) ^ 2 % 8 ≠ 1 := by
    intro hc
    rcases s0 with h | h | h <;> rcases s1 with h' | h' | h' <;>
      rcases s2 with h'' | h'' | h'' <;> omega
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> decide
  rcases hi with rfl | rfl | rfl | rfl
  · exact even_of_square_mod_eight _ e0
  · exact even_of_square_mod_eight _ e1
  · exact even_of_square_mod_eight _ e2
  · exact even_of_square_mod_eight _ e3

private theorem halve_four (k : ℕ)
    (h : ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 4 * k)
    (hk : (4 * k) % 8 = 0) :
    ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = k := by
  obtain ⟨a, ha0, hsum⟩ := h
  have h8 : (∑ i, a i ^ 2) % 8 = 0 := by rw [hsum]; exact hk
  have heven : ∀ i, a i % 2 = 0 := four_roots_even a h8
  refine ⟨fun i => a i / 2, ?_, ?_⟩
  · intro i
    change a i / 2 ≠ 0
    intro hi
    have h2 := Nat.div_add_mod (a i) 2
    have he := heven i
    have hne := ha0 i
    omega
  · change ∑ i, (a i / 2) ^ 2 = k
    have hai : ∀ i, a i = 2 * (a i / 2) := by
      intro i
      have h2 := Nat.div_add_mod (a i) 2
      have he := heven i
      omega
    have hsum2 : ∑ i, a i ^ 2 = ∑ i, (2 * (a i / 2)) ^ 2 := by
      simp only [← hai]
    rw [hsum] at hsum2
    have hexpand : ∑ i, (2 * (a i / 2)) ^ 2 = 4 * ∑ i, (a i / 2) ^ 2 := by
      simp only [Finset.mul_sum, mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
    rw [hexpand] at hsum2
    omega

private theorem scaled_excluded (b r : ℕ) (hb : b = 2 ∨ b = 6 ∨ b = 14) :
    ¬ ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = b * 4 ^ r := by
  induction r with
  | zero =>
    intro h
    rcases hb with rfl | rfl | rfl
    · exact four_small_excluded 2 (by simp) (by simpa using h)
    · exact four_small_excluded 6 (by simp) (by simpa using h)
    · exact four_small_excluded 14 (by simp) (by simpa using h)
  | succ r ih =>
    intro h
    have heq : b * 4 ^ (r + 1) = 4 * (b * 4 ^ r) := by
      rw [pow_succ]
      ac_rfl
    rw [heq] at h
    have hbeven : b % 2 = 0 := by
      rcases hb with rfl | rfl | rfl <;> decide
    have hmod : (b * 4 ^ r) % 2 = 0 := by
      rw [Nat.mul_mod, hbeven]
      simp
    have hk : (4 * (b * 4 ^ r)) % 8 = 0 := by omega
    exact ih (halve_four (b * 4 ^ r) h hk)

private theorem four_not_exceptional (n : ℕ)
    (h : ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) :
    n ∉ ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
      {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r} := by
  intro hmem
  rw [Set.mem_union] at hmem
  rcases hmem with hfin | ⟨r, hr | hr | hr⟩
  · have hsmall : n ∈ ({1, 2, 3, 5, 6, 9, 11, 14, 17, 29, 41} : Set ℕ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfin ⊢
      tauto
    exact four_small_excluded n hsmall h
  · exact scaled_excluded 2 r (Or.inl rfl) (by simpa [hr] using h)
  · exact scaled_excluded 6 r (Or.inr (Or.inl rfl)) (by simpa [hr] using h)
  · exact scaled_excluded 14 r (Or.inr (Or.inr rfl)) (by simpa [hr] using h)

private theorem avoids_legendre_obstruction (M : ℕ) (hM : M % 8 = 3 ∨ M % 8 = 6) :
    ¬∃ a b : ℕ, M = 4 ^ a * (8 * b + 7) := by
  rintro ⟨a, b, hab⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [pow_zero, one_mul] at hab
    omega
  · have ha0 : a ≠ 0 := by omega
    have hdvd : 4 ∣ M := by
      rw [hab]
      exact dvd_mul_of_dvd_left (dvd_pow_self 4 ha0) _
    omega

private theorem ne_zero_of_three_sq_mod_three {x y z M : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = M) (hM : M % 8 = 3) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have s0 := square_mod_eight x
  have s1 := square_mod_eight y
  have s2 := square_mod_eight z
  have e : x ^ 2 % 8 = 1 ∧ y ^ 2 % 8 = 1 ∧ z ^ 2 % 8 = 1 := by
    rcases s0 with h0 | h0 | h0 <;> rcases s1 with h1 | h1 | h1 <;>
      rcases s2 with h2 | h2 | h2 <;> omega
  obtain ⟨e0, e1, e2⟩ := e
  have nx : x ≠ 0 := by
    intro hx
    simp [hx] at e0
  have ny : y ≠ 0 := by
    intro hy
    simp [hy] at e1
  have nz : z ≠ 0 := by
    intro hz
    simp [hz] at e2
  exact ⟨nx, ny, nz⟩

private theorem ne_zero_of_three_sq_mod_six {x y z M : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = M) (hM : M % 8 = 6) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have s0 := square_mod_eight x
  have s1 := square_mod_eight y
  have s2 := square_mod_eight z
  have e : (x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4) ∧ (y ^ 2 % 8 = 1 ∨ y ^ 2 % 8 = 4) ∧
      (z ^ 2 % 8 = 1 ∨ z ^ 2 % 8 = 4) := by
    rcases s0 with h0 | h0 | h0 <;> rcases s1 with h1 | h1 | h1 <;>
      rcases s2 with h2 | h2 | h2 <;> omega
  obtain ⟨e0, e1, e2⟩ := e
  have nx : x ≠ 0 := by
    intro hx
    simp [hx] at e0
  have ny : y ≠ 0 := by
    intro hy
    simp [hy] at e1
  have nz : z ≠ 0 := by
    intro hz
    simp [hz] at e2
  exact ⟨nx, ny, nz⟩

private theorem four_times_odd (k : ℕ) (hk : k % 2 = 1) :
    ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = 4 * k := by
  have hk1 : 1 ≤ k := by omega
  have hN3 : (4 * k - 1) % 8 = 3 := by omega
  have hNavoid := avoids_legendre_obstruction (4 * k - 1) (Or.inl hN3)
  obtain ⟨x, y, z, hxyz⟩ :=
    Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven (4 * k - 1) hNavoid
  obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_three hxyz hN3
  have e3 : (1 : ℕ) ^ 2 = 1 := by decide
  refine fin_of_list [x, y, z, 1] (4 * k) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    omega

private theorem four_small_representation (n : ℕ) (hn : 0 < n) (hb : n ≤ 41)
    (h : n ∉ ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
      {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r}) :
    ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  interval_cases n
  · simp at h
  · exact (h (Or.inr ⟨0, Or.inl (by decide)⟩)).elim
  · simp at h
  · exact fin_of_list [1, 1, 1, 1] 4 (by decide) (by decide)
  · simp at h
  · exact (h (Or.inr ⟨0, Or.inr (Or.inl (by decide))⟩)).elim
  · exact fin_of_list [2, 1, 1, 1] 7 (by decide) (by decide)
  · exact (h (Or.inr ⟨1, Or.inl (by decide)⟩)).elim
  · simp at h
  · exact fin_of_list [2, 2, 1, 1] 10 (by decide) (by decide)
  · simp at h
  · exact fin_of_list [3, 1, 1, 1] 12 (by decide) (by decide)
  · exact fin_of_list [2, 2, 2, 1] 13 (by decide) (by decide)
  · exact (h (Or.inr ⟨0, Or.inr (Or.inr (by decide))⟩)).elim
  · exact fin_of_list [3, 2, 1, 1] 15 (by decide) (by decide)
  · exact fin_of_list [2, 2, 2, 2] 16 (by decide) (by decide)
  · simp at h
  · exact fin_of_list [3, 2, 2, 1] 18 (by decide) (by decide)
  · exact fin_of_list [4, 1, 1, 1] 19 (by decide) (by decide)
  · exact fin_of_list [3, 3, 1, 1] 20 (by decide) (by decide)
  · exact fin_of_list [3, 2, 2, 2] 21 (by decide) (by decide)
  · exact fin_of_list [4, 2, 1, 1] 22 (by decide) (by decide)
  · exact fin_of_list [3, 3, 2, 1] 23 (by decide) (by decide)
  · exact (h (Or.inr ⟨1, Or.inr (Or.inl (by decide))⟩)).elim
  · exact fin_of_list [4, 2, 2, 1] 25 (by decide) (by decide)
  · exact fin_of_list [3, 3, 2, 2] 26 (by decide) (by decide)
  · exact fin_of_list [4, 3, 1, 1] 27 (by decide) (by decide)
  · exact fin_of_list [4, 2, 2, 2] 28 (by decide) (by decide)
  · simp at h
  · exact fin_of_list [4, 3, 2, 1] 30 (by decide) (by decide)
  · exact fin_of_list [5, 2, 1, 1] 31 (by decide) (by decide)
  · exact (h (Or.inr ⟨2, Or.inl (by decide)⟩)).elim
  · exact fin_of_list [4, 3, 2, 2] 33 (by decide) (by decide)
  · exact fin_of_list [5, 2, 2, 1] 34 (by decide) (by decide)
  · exact fin_of_list [4, 3, 3, 1] 35 (by decide) (by decide)
  · exact fin_of_list [5, 3, 1, 1] 36 (by decide) (by decide)
  · exact fin_of_list [4, 4, 2, 1] 37 (by decide) (by decide)
  · exact fin_of_list [4, 3, 3, 2] 38 (by decide) (by decide)
  · exact fin_of_list [5, 3, 2, 1] 39 (by decide) (by decide)
  · exact fin_of_list [4, 4, 2, 2] 40 (by decide) (by decide)
  · simp at h

private theorem four_representation (n : ℕ) (hn : 0 < n)
    (h : n ∉ ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
      {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r}) :
    ∃ a : Fin 4 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  revert hn h
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn h
    by_cases hle : n ≤ 41
    · exact four_small_representation n hn hle h
    · by_cases h4 : 4 ∣ n
      · obtain ⟨k, rfl⟩ := h4
        by_cases hodd : k % 2 = 1
        · exact four_times_odd k hodd
        · have hkeven : k % 2 = 0 := by
            have h2 : k % 2 < 2 := Nat.mod_lt k (by decide)
            omega
          have hkpos : 0 < k := by omega
          have hklt : k < 4 * k := by omega
          have hkexc : k ∉ ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
              {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r} := by
            intro hmem
            rw [Set.mem_union] at hmem
            rcases hmem with hfin | ⟨r, hr⟩
            · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfin
              rcases hfin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
            · apply h
              rw [Set.mem_union]
              right
              refine ⟨r + 1, ?_⟩
              rcases hr with hr | hr | hr
              · exact Or.inl (by rw [hr, pow_succ]; omega)
              · exact Or.inr (Or.inl (by rw [hr, pow_succ]; omega))
              · exact Or.inr (Or.inr (by rw [hr, pow_succ]; omega))
          obtain ⟨b, hb0, hsum⟩ := ih k hklt hkpos hkexc
          refine ⟨fun i => 2 * b i, ?_, ?_⟩
          · intro i
            change 2 * b i ≠ 0
            intro hi
            exact hb0 i (by omega)
          · change ∑ i, (2 * b i) ^ 2 = 4 * k
            have hexpand : ∑ i, (2 * b i) ^ 2 = 4 * ∑ i, (b i) ^ 2 := by
              simp only [Finset.mul_sum, mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            rw [hexpand, hsum]
      · have hn8 : n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨
            n % 8 = 7 := by
          have h8 : n % 8 < 8 := Nat.mod_lt n (by decide)
          have h4' : n % 4 ≠ 0 := by omega
          omega
        rcases hn8 with h1 | h2 | h3 | h5 | h6 | h7
        · have hn32 : n % 32 = 1 ∨ n % 32 = 9 ∨ n % 32 = 17 ∨ n % 32 = 25 := by
            have h32 : n % 32 < 32 := Nat.mod_lt n (by decide)
            omega
          rcases hn32 with h32 | h32 | h32 | h32
          · have hM6 : ((n - 9) / 4) % 8 = 6 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 9) / 4) (Or.inr hM6)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 9) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_six hxyz hM6
            have hn_eq : n = 4 * ((n - 9) / 4) + 9 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (3 : ℕ) ^ 2 = 9 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 3] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
          · have hM6 : ((n - 49) / 4) % 8 = 6 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 49) / 4) (Or.inr hM6)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 49) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_six hxyz hM6
            have hn_eq : n = 4 * ((n - 49) / 4) + 49 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (7 : ℕ) ^ 2 = 49 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 7] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
          · have hM6 : ((n - 25) / 4) % 8 = 6 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 25) / 4) (Or.inr hM6)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 25) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_six hxyz hM6
            have hn_eq : n = 4 * ((n - 25) / 4) + 25 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (5 : ℕ) ^ 2 = 25 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 5] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
          · have hM6 : ((n - 1) / 4) % 8 = 6 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 1) / 4) (Or.inr hM6)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 1) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_six hxyz hM6
            have hn_eq : n = 4 * ((n - 1) / 4) + 1 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (1 : ℕ) ^ 2 = 1 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 1] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
        · have hN6 : (n - 4) % 8 = 6 := by omega
          have hNavoid := avoids_legendre_obstruction (n - 4) (Or.inr hN6)
          obtain ⟨x, y, z, hxyz⟩ :=
            Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven (n - 4) hNavoid
          obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_six hxyz hN6
          have e3 : (2 : ℕ) ^ 2 = 4 := by decide
          refine fin_of_list [x, y, z, 2] n ?_ ?_
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            omega
          · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
            omega
        · have hN3 : (n - 16) % 8 = 3 := by omega
          have hNavoid := avoids_legendre_obstruction (n - 16) (Or.inl hN3)
          obtain ⟨x, y, z, hxyz⟩ :=
            Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven (n - 16) hNavoid
          obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_three hxyz hN3
          have e3 : (4 : ℕ) ^ 2 = 16 := by decide
          refine fin_of_list [x, y, z, 4] n ?_ ?_
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            omega
          · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
            omega
        · have hn32 : n % 32 = 5 ∨ n % 32 = 13 ∨ n % 32 = 21 ∨ n % 32 = 29 := by
            have h32 : n % 32 < 32 := Nat.mod_lt n (by decide)
            omega
          rcases hn32 with h32 | h32 | h32 | h32
          · have hM3 : ((n - 25) / 4) % 8 = 3 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 25) / 4) (Or.inl hM3)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 25) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_three hxyz hM3
            have hn_eq : n = 4 * ((n - 25) / 4) + 25 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (5 : ℕ) ^ 2 = 25 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 5] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
          · have hM3 : ((n - 1) / 4) % 8 = 3 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 1) / 4) (Or.inl hM3)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 1) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_three hxyz hM3
            have hn_eq : n = 4 * ((n - 1) / 4) + 1 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (1 : ℕ) ^ 2 = 1 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 1] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
          · have hM3 : ((n - 9) / 4) % 8 = 3 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 9) / 4) (Or.inl hM3)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 9) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_three hxyz hM3
            have hn_eq : n = 4 * ((n - 9) / 4) + 9 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (3 : ℕ) ^ 2 = 9 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 3] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
          · have hM3 : ((n - 49) / 4) % 8 = 3 := by omega
            have hMavoid := avoids_legendre_obstruction ((n - 49) / 4) (Or.inl hM3)
            obtain ⟨x, y, z, hxyz⟩ :=
              Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven ((n - 49) / 4)
                hMavoid
            obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_three hxyz hM3
            have hn_eq : n = 4 * ((n - 49) / 4) + 49 := by omega
            have e0 : (2 * x) ^ 2 = 4 * x ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e1 : (2 * y) ^ 2 = 4 * y ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e2 : (2 * z) ^ 2 = 4 * z ^ 2 := by
              rw [mul_pow, show (2 : ℕ) ^ 2 = 4 from by decide]
            have e3 : (7 : ℕ) ^ 2 = 49 := by decide
            refine fin_of_list [2 * x, 2 * y, 2 * z, 7] n ?_ ?_
            · simp only [List.mem_cons, List.not_mem_nil, or_false]
              omega
            · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
              omega
        · have hN6 : (n - 16) % 8 = 6 := by omega
          have hNavoid := avoids_legendre_obstruction (n - 16) (Or.inr hN6)
          obtain ⟨x, y, z, hxyz⟩ :=
            Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven (n - 16) hNavoid
          obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_six hxyz hN6
          have e3 : (4 : ℕ) ^ 2 = 16 := by decide
          refine fin_of_list [x, y, z, 4] n ?_ ?_
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            omega
          · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
            omega
        · have hN3 : (n - 4) % 8 = 3 := by omega
          have hNavoid := avoids_legendre_obstruction (n - 4) (Or.inl hN3)
          obtain ⟨x, y, z, hxyz⟩ :=
            Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven (n - 4) hNavoid
          obtain ⟨hx0, hy0, hz0⟩ := ne_zero_of_three_sq_mod_three hxyz hN3
          have e3 : (2 : ℕ) ^ 2 = 4 := by decide
          refine fin_of_list [x, y, z, 2] n ?_ ?_
          · simp only [List.mem_cons, List.not_mem_nil, or_false]
            omega
          · simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
            omega

private theorem append_square (m n b : ℕ) (hb : b ≠ 0)
    (h : ∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) :
    ∃ a : Fin (m + 1) → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n + b ^ 2 := by
  obtain ⟨a, ha0, hsum⟩ := h
  refine ⟨Fin.cons b a, ?_, ?_⟩
  · rw [Fin.forall_fin_succ]
    constructor
    · rw [Fin.cons_zero]
      exact hb
    · intro i
      rw [Fin.cons_succ]
      exact ha0 i
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum]
    omega

private theorem odd_avoids_four (n : ℕ) (hn : 30 ≤ n) (h41 : n ≠ 41)
    (hodd : n % 2 = 1) :
    n ∉ ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
      {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r} := by
  intro hmem
  rw [Set.mem_union] at hmem
  rcases hmem with hfin | ⟨r, hr⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfin
    omega
  · rcases hr with hr | hr | hr <;> omega

private theorem five_large (n : ℕ) (hn : 34 ≤ n) :
    ∃ a : Fin 5 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  by_cases h42 : n = 42
  · subst h42
    exact fin_of_list [4, 3, 3, 2, 2] 42 (by decide) (by decide)
  · by_cases h45 : n = 45
    · subst h45
      exact fin_of_list [5, 3, 3, 1, 1] 45 (by decide) (by decide)
    · by_cases heven : n % 2 = 0
      · have hodd : (n - 1) % 2 = 1 := by omega
        have h30 : 30 ≤ n - 1 := by omega
        have h41 : n - 1 ≠ 41 := by omega
        have h1pos : 0 < n - 1 := by omega
        have hnavoid := odd_avoids_four (n - 1) h30 h41 hodd
        obtain ⟨a, ha0, hsum⟩ := four_representation (n - 1) h1pos hnavoid
        have happend := append_square 4 (n - 1) 1 one_ne_zero ⟨a, ha0, hsum⟩
        have heq : (n - 1) + 1 = n := by omega
        simpa [heq] using happend
      · have hodd : n % 2 = 1 := by
          have h2 : n % 2 < 2 := Nat.mod_lt n (by decide)
          omega
        have hodd4 : (n - 4) % 2 = 1 := by omega
        have h30 : 30 ≤ n - 4 := by omega
        have h41 : n - 4 ≠ 41 := by omega
        have h4pos : 0 < n - 4 := by omega
        have hnavoid := odd_avoids_four (n - 4) h30 h41 hodd4
        obtain ⟨a, ha0, hsum⟩ := four_representation (n - 4) h4pos hnavoid
        have happend := append_square 4 (n - 4) 2 (by decide) ⟨a, ha0, hsum⟩
        have heq : (n - 4) + 4 = n := by omega
        simpa [heq] using happend

private theorem five_squares (n : ℕ) (hn : 0 < n) :
    (∃ a : Fin 5 → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) ↔
      n ∉ ({1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33} : Set ℕ) := by
  constructor
  · rintro ⟨a, ha0, hsum⟩ hmem
    exact five_excluded n hmem ⟨a, ha0, hsum⟩
  · intro h
    by_cases h34 : 34 ≤ n
    · exact five_large n h34
    · have hle : n ≤ 33 := by omega
      interval_cases n
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · exact fin_of_list [1, 1, 1, 1, 1] 5 (by decide) (by decide)
      · simp at h
      · simp at h
      · exact fin_of_list [2, 1, 1, 1, 1] 8 (by decide) (by decide)
      · simp at h
      · simp at h
      · exact fin_of_list [2, 2, 1, 1, 1] 11 (by decide) (by decide)
      · simp at h
      · exact fin_of_list [3, 1, 1, 1, 1] 13 (by decide) (by decide)
      · exact fin_of_list [2, 2, 2, 1, 1] 14 (by decide) (by decide)
      · simp at h
      · exact fin_of_list [3, 2, 1, 1, 1] 16 (by decide) (by decide)
      · exact fin_of_list [2, 2, 2, 2, 1] 17 (by decide) (by decide)
      · simp at h
      · exact fin_of_list [3, 2, 2, 1, 1] 19 (by decide) (by decide)
      · exact fin_of_list [4, 1, 1, 1, 1] 20 (by decide) (by decide)
      · exact fin_of_list [3, 3, 1, 1, 1] 21 (by decide) (by decide)
      · exact fin_of_list [3, 2, 2, 2, 1] 22 (by decide) (by decide)
      · exact fin_of_list [4, 2, 1, 1, 1] 23 (by decide) (by decide)
      · exact fin_of_list [3, 3, 2, 1, 1] 24 (by decide) (by decide)
      · exact fin_of_list [3, 2, 2, 2, 2] 25 (by decide) (by decide)
      · exact fin_of_list [4, 2, 2, 1, 1] 26 (by decide) (by decide)
      · exact fin_of_list [3, 3, 2, 2, 1] 27 (by decide) (by decide)
      · exact fin_of_list [4, 3, 1, 1, 1] 28 (by decide) (by decide)
      · exact fin_of_list [4, 2, 2, 2, 1] 29 (by decide) (by decide)
      · exact fin_of_list [3, 3, 2, 2, 2] 30 (by decide) (by decide)
      · exact fin_of_list [4, 3, 2, 1, 1] 31 (by decide) (by decide)
      · exact fin_of_list [5, 2, 1, 1, 1] 32 (by decide) (by decide)
      · simp at h

private theorem large_representation (m n : ℕ) (hm : 6 ≤ m) (hn : m + 14 ≤ n) :
    ∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨a, ha0, hsum⟩ := sum_six_and_eight_nonzero_squares.1 (n - k) (by omega)
  have happend := append_ones 6 (n - k) k ⟨a, ha0, hsum⟩
  have heq : (n - k) + k = n := Nat.sub_add_cancel (by omega)
  simpa [heq] using happend

private theorem small_representation (m t : ℕ) (hm : 6 ≤ m)
    (ht : t = 0 ∨ t = 3 ∨ t = 6 ∨ t = 8 ∨ t = 9 ∨ t = 11 ∨ t = 12) :
    ∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = m + t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hbase := fin_of_list [1, 1, 1, 1, 1, 1] 6 (by decide) (by decide)
    obtain ⟨b, hb0, hbsum⟩ := append_ones 6 6 k hbase
    exact ⟨b, hb0, by omega⟩
  · have hbase := fin_of_list [2, 1, 1, 1, 1, 1] 9 (by decide) (by decide)
    obtain ⟨b, hb0, hbsum⟩ := append_ones 6 9 k hbase
    exact ⟨b, hb0, by omega⟩
  · have hbase := fin_of_list [2, 2, 1, 1, 1, 1] 12 (by decide) (by decide)
    obtain ⟨b, hb0, hbsum⟩ := append_ones 6 12 k hbase
    exact ⟨b, hb0, by omega⟩
  · have hbase := fin_of_list [3, 1, 1, 1, 1, 1] 14 (by decide) (by decide)
    obtain ⟨b, hb0, hbsum⟩ := append_ones 6 14 k hbase
    exact ⟨b, hb0, by omega⟩
  · have hbase := fin_of_list [2, 2, 2, 1, 1, 1] 15 (by decide) (by decide)
    obtain ⟨b, hb0, hbsum⟩ := append_ones 6 15 k hbase
    exact ⟨b, hb0, by omega⟩
  · have hbase := fin_of_list [3, 2, 1, 1, 1, 1] 17 (by decide) (by decide)
    obtain ⟨b, hb0, hbsum⟩ := append_ones 6 17 k hbase
    exact ⟨b, hb0, by omega⟩
  · have hbase := fin_of_list [2, 2, 2, 2, 1, 1] 18 (by decide) (by decide)
    obtain ⟨b, hb0, hbsum⟩ := append_ones 6 18 k hbase
    exact ⟨b, hb0, by omega⟩

private theorem six_or_more (m n : ℕ) (hm : 6 ≤ m) (hn : 0 < n) :
    (∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) ↔
      n ∉ Set.Ico 1 m ∪ {m + 1, m + 2, m + 4, m + 5, m + 7, m + 10, m + 13} := by
  constructor
  · rintro ⟨a, ha0, hsum⟩ hmem
    rw [Set.mem_union] at hmem
    rcases hmem with hico | hexc
    · rw [Set.mem_Ico] at hico
      have hge : m ≤ n := by
        have h1 : ∑ _i ∈ (Finset.univ : Finset (Fin m)), (1 : ℕ) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin m)), (a i) ^ 2 :=
          Finset.sum_le_sum (fun i _ => one_le_sq_of_ne_zero (a i) (ha0 i))
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum] at h1
        simpa using h1
      omega
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hexc
      have hn37 : n ≤ m + 37 := by omega
      obtain ⟨x, y, z, w, v, heq, _⟩ := bounded_counts m n a ha0 hsum hn37
      rcases hexc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (have hv : v = 0 := by omega
         have hw : w = 0 := by omega
         have hz : z = 0 := by omega
         omega)
  · intro h
    have hnm : m ≤ n := by
      by_contra hcon
      have hlt : n < m := by omega
      have hmem : n ∈ Set.Ico 1 m ∪ {m + 1, m + 2, m + 4, m + 5, m + 7, m + 10,
        m + 13} := by
        rw [Set.mem_union]
        exact Or.inl (Set.mem_Ico.mpr ⟨hn, hlt⟩)
      exact h hmem
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hexc7 : t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 4 ∧ t ≠ 5 ∧ t ≠ 7 ∧ t ≠ 10 ∧ t ≠ 13 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (intro ht1
         subst ht1
         apply h
         rw [Set.mem_union]
         right
         simp)
    by_cases h14 : 14 ≤ t
    · exact large_representation m (m + t) hm (by omega)
    · have hsmall : t = 0 ∨ t = 3 ∨ t = 6 ∨ t = 8 ∨ t = 9 ∨ t = 11 ∨ t = 12 := by
        obtain ⟨e1, e2, e4, e5, e7, e10, e13⟩ := hexc7
        have ht13 : t ≤ 13 := by omega
        omega
      exact small_representation m t hm hsmall

/-- **Dubouis's theorem on sums of nonzero squares.** Let $m \ge 4$ and let $n$ be a positive
integer. Then $n$ is a sum of $m$ squares of positive integers if and only if $n$ does not lie in
the exceptional set $E_m$, where
$E_4 = \{1, 3, 5, 9, 11, 17, 29, 41\} \cup \{2 \cdot 4^r, 6 \cdot 4^r, 14 \cdot 4^r : r \ge 0\}$,
$E_5 = \{1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33\}$, and for $m \ge 6$,
$E_m = \{1, \dots, m - 1\} \cup \{m + 1, m + 2, m + 4, m + 5, m + 7, m + 10, m + 13\}$.

Source: Jewel Mahajan, *Multiplicative Functions Additive on Partitions of 2k Nonzero
Squares*, INTEGERS 26 (2026), Article A121, Lemma 1 (`integers-2026-A121-lem-1`), quoting
Dubouis (1911). -/
public theorem sum_nonzero_squares_iff_not_mem_exceptional (m n : ℕ) (hm : 4 ≤ m)
    (hn : 0 < n) :
    (∃ a : Fin m → ℕ, (∀ i, a i ≠ 0) ∧ ∑ i, a i ^ 2 = n) ↔
      n ∉ (if m = 4 then
            ({1, 3, 5, 9, 11, 17, 29, 41} : Set ℕ) ∪
              {n | ∃ r : ℕ, n = 2 * 4 ^ r ∨ n = 6 * 4 ^ r ∨ n = 14 * 4 ^ r}
          else if m = 5 then ({1, 2, 3, 4, 6, 7, 9, 10, 12, 15, 18, 33} : Set ℕ)
          else Set.Ico 1 m ∪
            {m + 1, m + 2, m + 4, m + 5, m + 7, m + 10, m + 13}) := by
  by_cases h4 : m = 4
  · subst h4
    rw [ite_eq_left rfl]
    constructor
    · intro hrep
      exact four_not_exceptional n hrep
    · intro hmem
      exact four_representation n hn hmem
  · by_cases h5 : m = 5
    · subst h5
      have h45 : ¬(5 : ℕ) = 4 := by decide
      rw [ite_eq_right h45, ite_eq_left rfl]
      exact five_squares n hn
    · rw [ite_eq_right h4, ite_eq_right h5]
      exact six_or_more m n (by omega) hn

end MetaMathlibExt
