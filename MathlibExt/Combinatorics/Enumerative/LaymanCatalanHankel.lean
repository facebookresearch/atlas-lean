/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt
section
private def tri : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => 2 * tri n 0 + tri n 1
  | n + 1, k + 1 => tri n k + 2 * tri n (k + 1) + tri n (k + 2)

private theorem tri_eq_zero_of_lt : ∀ (n k : ℕ), n < k → tri n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      change tri n k + 2 * tri n (k + 1) + tri n (k + 2) = 0
      have e1 : tri n k = 0 := by
        by_cases h : n < k
        · exact ih k h
        · omega
      have e2 : tri n (k + 1) = 0 := ih _ (by omega)
      have e3 : tri n (k + 2) = 0 := ih _ (by omega)
      rw [e1, e2, e3]
      ring

private theorem tri_self (n : ℕ) : tri n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change tri n n + 2 * tri n (n + 1) + tri n (n + 2) = 1
    rw [ih, tri_eq_zero_of_lt n (n+1) (by omega), tri_eq_zero_of_lt n (n+2) (by omega)]
    ring

private theorem dblPascal (m k : ℕ) :
    ((m + 2).choose (k + 2) : ℤ) =
      (m.choose k : ℤ) + 2 * (m.choose (k + 1) : ℤ) + (m.choose (k + 2) : ℤ) := by
  have h1 : ∀ (a b : ℕ), ((a + 1).choose (b + 1) : ℤ) = (a.choose b : ℤ) +
      (a.choose (b + 1) : ℤ) := by
    intro a b
    have h := Nat.choose_succ_succ a b
    have : ((a + 1).choose (b + 1) : ℤ) = ((a.choose b + a.choose (b+1) : ℕ) : ℤ) := by
      rw [h]
    rw [this, Nat.cast_add]
  have e1 := h1 (m + 1) (k + 1)
  have e2 := h1 m k
  have e3 := h1 m (k + 1)
  have hm : m + 1 + 1 = m + 2 := by omega
  have hk : k + 1 + 1 = k + 2 := by omega
  rw [hm, hk] at e1
  rw [e2, e3] at e1
  linarith

private theorem tri_closed : ∀ (n k : ℕ), k ≤ n →
    tri n k = ((2 * n + 1).choose (n - k) : ℤ) - ((2 * n + 1).choose (n + k + 2) : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    simp [tri]
  | succ n ih =>
    intro k hk
    cases k with
    | zero =>
      change 2 * tri n 0 + tri n 1 = ((2 * (n+1) + 1).choose ((n+1) - 0) : ℤ) - _
      by_cases hn : n = 0
      · subst hn
        norm_num [tri]
      · have hn1 : 1 ≤ n := by omega
        have e0 := ih 0 (by omega)
        have e1 := ih 1 hn1
        rw [e0, e1]
        have s0 : n - 0 = n := by omega
        have s1 : n + 0 + 2 = n + 2 := by omega
        have t0 : (n+1) - 0 = n + 1 := by omega
        have t1 : (n+1) + 0 + 2 = n + 3 := by omega
        rw [s0, s1] at e0 ⊢
        have hm : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
        have h1 : n + 1 = (n - 1) + 2 := by omega
        rw [t0, t1, hm, h1]
        have d1 := dblPascal (2*n+1) (n-1)
        have d2 := dblPascal (2*n+1) (n+1)
        have eA : (n - 1) + 1 = n := by omega
        have eB : (n - 1) + 2 = n + 1 := by omega
        have eC : (n + 1) + 1 = n + 2 := by omega
        have eD : (n + 1) + 2 = n + 3 := by omega
        have eE : n + 1 + 2 = n + 3 := by omega
        rw [eB] at d1
        rw [eA] at d1
        rw [eC, eD] at d2
        rw [eB, eE]
        rw [eE] at e1 ⊢
        linarith
    | succ j =>
      have hj : j ≤ n := by omega
      change tri n j + 2 * tri n (j + 1) + tri n (j + 2) =
        ((2 * (n+1) + 1).choose ((n+1) - (j+1)) : ℤ) - ((2 * (n+1) + 1).choose ((n+1)+(j+1)+2) : ℤ)
      by_cases hIn : j + 2 ≤ n
      · have e0 := ih j (by omega)
        have e1 := ih (j+1) (by omega)
        have e2 := ih (j+2) hIn
        rw [e0, e1, e2]
        have hm : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
        have hA : (n+1)-(j+1) = n-j := by omega
        have hB : (n+1)+(j+1)+2 = n+(j+2)+2 := by omega
        have g1 : (n-(j+2)) + 1 = n-(j+1) := by omega
        have g2 : (n-(j+2)) + 2 = n-j := by omega
        have g3 : (n+j+2) + 1 = n+(j+1)+2 := by omega
        have g4 : (n+j+2) + 2 = n+(j+2)+2 := by omega
        have d1 := dblPascal (2*n+1) (n-(j+2))
        have d2 := dblPascal (2*n+1) (n+j+2)
        rw [g1, g2] at d1
        rw [g3, g4] at d2
        rw [hm, hA, hB]
        linarith
      · push Not at hIn
        by_cases hMid : j + 1 ≤ n
        · have hjn : j + 1 = n := by omega
          have e0 := ih j (by omega)
          have e1 := ih (j+1) hMid
          have z2 : tri n (j+2) = 0 := tri_eq_zero_of_lt n (j+2) (by omega)
          rw [e0, e1, z2]
          have hA : (n+1)-(j+1) = 1 := by omega
          have hB : (n+1)+(j+1)+2 = 2*n+3 := by omega
          have hm : 2*(n+1)+1 = 2*n+3 := by omega
          have f0a : n - j = 1 := by omega
          have f0b : n + j + 2 = 2*n+1 := by omega
          have f1a : n - (j+1) = 0 := by omega
          have f1b : n + (j+1) + 2 = 2*n+2 := by omega
          rw [hA, hB, hm, f0a, f0b, f1a, f1b]
          have c1 : (2*n+1).choose 1 = 2*n+1 := Nat.choose_one_right _
          have c2 : (2*n+1).choose (2*n+1) = 1 := Nat.choose_self _
          have c3 : (2*n+1).choose 0 = 1 := Nat.choose_zero_right _
          have c4 : (2*n+3).choose 1 = 2*n+3 := Nat.choose_one_right _
          have c5 : (2*n+3).choose (2*n+3) = 1 := Nat.choose_self _
          have c6 : (2*n+1).choose (2*n+2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [c1, c2, c3, c4, c5, c6]
          push_cast
          ring
        · have hj_eq : j = n := by omega
          have e0 := ih j hj
          have z1 : tri n (j+1) = 0 := tri_eq_zero_of_lt n (j+1) (by omega)
          have z2 : tri n (j+2) = 0 := tri_eq_zero_of_lt n (j+2) (by omega)
          rw [e0, z1, z2]
          have hA : (n+1)-(j+1) = 0 := by omega
          have hB : (n+1)+(j+1)+2 = 2*n+4 := by omega
          have hm : 2*(n+1)+1 = 2*n+3 := by omega
          have f0a : n - j = 0 := by omega
          have f0b : n + j + 2 = 2*n+2 := by omega
          rw [hA, hB, hm, f0a, f0b]
          have c0 : (2*n+1).choose 0 = 1 := Nat.choose_zero_right _
          have c1 : (2*n+3).choose 0 = 1 := Nat.choose_zero_right _
          have cz1 : (2*n+1).choose (2*n+2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have cz2 : (2*n+3).choose (2*n+4) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [c0, c1, cz1, cz2]
          simp

private theorem tri_zero_eq_catalan (n : ℕ) : tri n 0 = ((catalan (n + 1) : ℕ) : ℤ) := by
  have hc := tri_closed n 0 (Nat.zero_le n)
  simp only [Nat.sub_zero, Nat.add_zero] at hc
  have hcat : (n + 1 + 1) * catalan (n + 1) = (2 * n + 2).choose (n + 1) := by
    have h := succ_mul_catalan_eq_centralBinom (n + 1)
    have hcb : Nat.centralBinom (n + 1) = (2 * (n + 1)).choose (n + 1) := rfl
    rw [hcb] at h
    have e2n : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [e2n] at h
    exact h
  have hpas : (2*n+2).choose (n+1) = (2*n+1).choose n + (2*n+1).choose (n+1) := by
    have h := Nat.choose_succ_succ (2*n+1) n
    have e1 : (2*n+1).succ = 2*n+2 := by omega
    have e2 : n.succ = n+1 := rfl
    rw [e1, e2] at h
    exact h
  have hsym : (2*n+1).choose (n+1) = (2*n+1).choose n := by
    apply Nat.choose_symm_of_eq_add
    omega
  have hmul : (2*n+1).choose (n+2) * (n+2) = (2*n+1).choose (n+1) * n := by
    have h := Nat.choose_succ_right_eq (2*n+1) (n+1)
    have hsub : (2*n+1)-(n+1) = n := by omega
    rw [hsub] at h
    exact h
  have hmulZ : (((2*n+1).choose (n+2) : ℤ)) * ((n : ℤ) + 2) =
      (((2*n+1).choose n : ℤ)) * (n : ℤ) := by
    have h2 := congrArg (Nat.cast : ℕ → ℤ) hmul
    simp only [Nat.cast_mul] at h2
    rw [hsym] at h2
    push_cast at h2
    nlinarith [h2]
  have hcatZ : ((n : ℤ) + 2) * (((catalan (n+1) : ℕ)) : ℤ) =
      2 * (((2*n+1).choose n : ℤ)) := by
    have h2 := congrArg (Nat.cast : ℕ → ℤ) hcat
    simp only [Nat.cast_mul] at h2
    rw [hpas, hsym] at h2
    push_cast at h2
    nlinarith [h2]
  have htriZ : ((n : ℤ) + 2) * (tri n 0) = 2 * (((2*n+1).choose n : ℤ)) := by
    rw [hc]
    nlinarith [hmulZ]
  have hne : ((n : ℤ) + 2) ≠ 0 := by
    have : (0:ℤ) < (n:ℤ) + 2 := by positivity
    omega
  exact mul_left_cancel₀ hne (by rw [htriZ, hcatZ])

private def dot (i j : ℕ) : ℤ := ∑ k ∈ Finset.range (i + j + 1), tri i k * tri j k

private theorem dot_zero (j : ℕ) : dot 0 j = tri j 0 := by
  unfold dot
  have h1 : ∀ b ∈ Finset.range (0 + j + 1), b ≠ 0 → tri 0 b * tri j b = 0 := by
    intro b hb hb0
    have : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨b', rfl⟩ := this
    simp [tri]
  have h3 : (0 : ℕ) ∉ Finset.range (0 + j + 1) → tri 0 0 * tri j 0 = 0 := by
    simp
  rw [Finset.sum_eq_single 0 h1 h3]
  simp [tri]

private theorem shiftA (i j : ℕ) :
    ∑ k ∈ Finset.range (i + j + 1), tri i (k+2) * tri j (k+1) =
    (∑ k ∈ Finset.range (i + j + 1), tri i (k+1) * tri j k) - tri i 1 * tri j 0 := by
  set N := i + j + 1 with hNdef
  have h := Finset.sum_range_succ' (fun k => tri i (k+1) * tri j k) N
  have h2 : ∑ k ∈ Finset.range N, tri i (k+1+1) * tri j (k+1) =
      ∑ k ∈ Finset.range N, tri i (k+2) * tri j (k+1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have e1 : k + 1 + 1 = k + 2 := by omega
    rw [e1]
  have h0 : tri i (0+1) * tri j 0 = tri i 1 * tri j 0 := by simp
  have key : ∑ k ∈ Finset.range (N+1), tri i (k+1) * tri j k =
      tri i 1 * tri j 0 + ∑ k ∈ Finset.range N, tri i (k+2) * tri j (k+1) := by
    rw [h, h2, h0, add_comm]
  have key2 : ∑ k ∈ Finset.range (N+1), tri i (k+1) * tri j k =
      (∑ k ∈ Finset.range N, tri i (k+1) * tri j k) + tri i (N+1) * tri j N := by
    rw [Finset.sum_range_succ]
  have vanish : tri i (N+1) * tri j N = 0 := by
    have : tri i (N+1) = 0 := tri_eq_zero_of_lt i (N+1) (by omega)
    rw [this, zero_mul]
  rw [key2, vanish, add_zero] at key
  linarith

private theorem shiftB (i j : ℕ) :
    ∑ k ∈ Finset.range (i + j + 1), tri i (k+1) * tri j (k+2) =
    (∑ k ∈ Finset.range (i + j + 1), tri i k * tri j (k+1)) - tri i 0 * tri j 1 := by
  set N := i + j + 1 with hNdef
  have h := Finset.sum_range_succ' (fun k => tri i k * tri j (k+1)) N
  have h2 : ∑ k ∈ Finset.range N, tri i (k+1) * tri j (k+1+1) =
      ∑ k ∈ Finset.range N, tri i (k+1) * tri j (k+2) := by
    apply Finset.sum_congr rfl
    intro k hk
    have e1 : k + 1 + 1 = k + 2 := by omega
    rw [e1]
  have h0 : tri i 0 * tri j (0+1) = tri i 0 * tri j 1 := by simp
  have key : ∑ k ∈ Finset.range (N+1), tri i k * tri j (k+1) =
      tri i 0 * tri j 1 + ∑ k ∈ Finset.range N, tri i (k+1) * tri j (k+2) := by
    rw [h, h2, h0, add_comm]
  have key2 : ∑ k ∈ Finset.range (N+1), tri i k * tri j (k+1) =
      (∑ k ∈ Finset.range N, tri i k * tri j (k+1)) + tri i N * tri j (N+1) := by
    rw [Finset.sum_range_succ]
  have vanish : tri i N * tri j (N+1) = 0 := by
    have hNgt : i < N ∨ j < N := by omega
    cases hNgt with
    | inl h =>
      have : tri i N = 0 := tri_eq_zero_of_lt i N h
      rw [this, zero_mul]
    | inr h =>
      have : tri j (N+1) = 0 := tri_eq_zero_of_lt j (N+1) (by omega)
      rw [this, mul_zero]
  rw [key2, vanish, add_zero] at key
  linarith

private theorem dot_succ (i j : ℕ) : dot (i + 1) j = dot i (j + 1) := by
  unfold dot
  have hN : (i + 1) + j + 1 = i + j + 2 := by omega
  have hN2 : i + (j + 1) + 1 = i + j + 2 := by omega
  rw [hN, hN2]
  set N := i + j + 1 with hNdef
  have hNp1 : i + j + 2 = N + 1 := by omega
  rw [hNp1]
  have eL : ∑ k ∈ Finset.range (N+1), tri (i+1) k * tri j k =
      tri (i+1) 0 * tri j 0 + ∑ k ∈ Finset.range N, tri (i+1) (k+1) * tri j (k+1) := by
    have h := Finset.sum_range_succ' (fun k => tri (i+1) k * tri j k) N
    rw [h, add_comm]
  have eR : ∑ k ∈ Finset.range (N+1), tri i k * tri (j+1) k =
      tri i 0 * tri (j+1) 0 + ∑ k ∈ Finset.range N, tri i (k+1) * tri (j+1) (k+1) := by
    have h := Finset.sum_range_succ' (fun k => tri i k * tri (j+1) k) N
    rw [h, add_comm]
  rw [eL, eR]
  have r0 : tri (i+1) 0 = 2 * tri i 0 + tri i 1 := rfl
  have r0' : tri (j+1) 0 = 2 * tri j 0 + tri j 1 := rfl
  rw [r0, r0']
  have expL : ∀ k : ℕ, tri (i+1) (k+1) * tri j (k+1) =
      (tri i k * tri j (k+1) + 2 * (tri i (k+1) * tri j (k+1)) + tri i (k+2) * tri j (k+1)) := by
    intro k
    change (tri i k + 2 * tri i (k+1) + tri i (k+2)) * tri j (k+1) = _
    ring
  have expR : ∀ k : ℕ, tri i (k+1) * tri (j+1) (k+1) =
      (tri i (k+1) * tri j k + 2 * (tri i (k+1) * tri j (k+1)) + tri i (k+1) * tri j (k+2)) := by
    intro k
    change tri i (k+1) * (tri j k + 2 * tri j (k+1) + tri j (k+2)) = _
    ring
  simp_rw [expL, expR]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have sA := shiftA i j
  have sB := shiftB i j
  rw [←hNdef] at sA sB
  linarith

private theorem dot_eq : ∀ (i j : ℕ), dot i j = tri (i + j) 0 := by
  intro i
  induction i with
  | zero =>
    intro j
    rw [dot_zero]
    have : 0 + j = j := by omega
    rw [this]
  | succ i ih =>
    intro j
    rw [dot_succ, ih]
    have : i + (j + 1) = (i + 1) + j := by omega
    rw [this]

private def Lmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => tri i.val j.val

private def Tmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if i.val = j.val then 3
  else if i.val + 1 = j.val then 1
  else if j.val + 1 = i.val then 1
  else 0

private theorem Lmat_lower (n : ℕ) : (Lmat n).IsLowerTriangular := by
  intro i j hij
  change tri i.val j.val = 0
  have hlt : i.val < j.val := hij
  exact tri_eq_zero_of_lt i.val j.val hlt

private theorem Lmat_diag (n : ℕ) (i : Fin n) : Lmat n i i = 1 := by
  change tri i.val i.val = 1
  exact tri_self i.val

private theorem det_Lmat (n : ℕ) : (Lmat n).det = 1 := by
  have h := Matrix.det_of_isLowerTriangular (Lmat n) (Lmat_lower n)
  rw [h]
  have h1 : ∀ i : Fin n, Lmat n i i = 1 := Lmat_diag n
  simp_rw [h1]
  simp

private theorem dot_range_n_left (n i j : ℕ) (hi : i < n) :
    (∑ k ∈ Finset.range n, tri i k * tri j k) = tri (i + j) 0 := by
  rw [← dot_eq]
  rcases le_total (i + j + 1) n with hle | hle
  · apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono hle)
    intro k _ hk
    have hkle : i + j + 1 ≤ k := by simpa [Finset.mem_range] using hk
    have : tri i k = 0 := tri_eq_zero_of_lt i k (by omega)
    rw [this, zero_mul]
  · apply Finset.sum_subset (Finset.range_mono hle)
    intro k _ hk
    have hkle : n ≤ k := by simpa [Finset.mem_range] using hk
    have : tri i k = 0 := tri_eq_zero_of_lt i k (by omega)
    rw [this, zero_mul]

private theorem dot_range_n_right (n i j : ℕ) (hj : j < n) :
    (∑ k ∈ Finset.range n, tri i k * tri j k) = tri (i + j) 0 := by
  rw [← dot_eq]
  rcases le_total (i + j + 1) n with hle | hle
  · apply Eq.symm
    apply Finset.sum_subset (Finset.range_mono hle)
    intro k _ hk
    have hkle : i + j + 1 ≤ k := by simpa [Finset.mem_range] using hk
    have : tri i k = 0 := tri_eq_zero_of_lt i k (by omega)
    rw [this, zero_mul]
  · apply Finset.sum_subset (Finset.range_mono hle)
    intro k _ hk
    have hkle : n ≤ k := by simpa [Finset.mem_range] using hk
    have : tri j k = 0 := tri_eq_zero_of_lt j k (by omega)
    rw [this, mul_zero]

private theorem Tmat_eq_sum (n : ℕ) (a b : Fin n) :
    Tmat n a b = (if a.val = b.val then (3:ℤ) else 0) + (if a.val + 1 = b.val then (1:ℤ) else 0) +
        (if b.val + 1 = a.val then (1:ℤ) else 0) := by
  simp only [Tmat]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> omega

private theorem sum_S1 (n ii b : ℕ) (hb : b < n) :
    (∑ j ∈ Finset.range n, tri ii j * (if j = b then (3:ℤ) else 0)) = tri ii b * 3 := by
  have rw1 : ∀ j : ℕ, tri ii j * (if j = b then (3:ℤ) else 0) =
      (if j = b then tri ii j * 3 else 0) := by
    intro j
    by_cases h : j = b
    · simp [h]
    · simp [h]
  simp_rw [rw1]
  rw [Finset.sum_ite_eq' _ b (fun j => tri ii j * 3)]
  simp [Finset.mem_range.2 hb]

private theorem sum_S2_zero (n ii : ℕ) :
    (∑ j ∈ Finset.range n, tri ii j * (if j + 1 = 0 then (1:ℤ) else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hne : ¬ (j + 1 = 0) := by omega
  simp only [hne, ite_false, mul_zero]

private theorem sum_S2_pos (n ii b : ℕ) (hb : b < n) (hb0 : 0 < b) :
    (∑ j ∈ Finset.range n, tri ii j * (if j + 1 = b then (1:ℤ) else 0)) = tri ii (b - 1) := by
  have rw1 : ∀ j : ℕ, tri ii j * (if j + 1 = b then (1:ℤ) else 0) =
      (if j = b - 1 then tri ii j * 1 else 0) := by
    intro j
    by_cases h : j = b - 1
    · subst h
      have hjb : b - 1 + 1 = b := by omega
      simp [hjb]
    · have h2 : ¬ (j + 1 = b) := by omega
      simp [h, h2]
  simp_rw [rw1]
  rw [Finset.sum_ite_eq' _ (b-1) (fun j => tri ii j * 1)]
  have hmem : b - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
  simp [hmem]

private theorem sum_S3 (n ii b : ℕ) (hii : ii < n) (hb : b < n) :
    (∑ j ∈ Finset.range n, tri ii j * (if b + 1 = j then (1:ℤ) else 0)) = tri ii (b + 1) := by
  by_cases hmem : b + 1 < n
  · have rw1 : ∀ j : ℕ, tri ii j * (if b + 1 = j then (1:ℤ) else 0) =
      (if b + 1 = j then tri ii j * 1 else 0) := by
      intro j
      by_cases h : b + 1 = j
      · simp [h]
      · simp [h]
    simp_rw [rw1]
    rw [Finset.sum_ite_eq _ (b+1) (fun j => tri ii j * 1)]
    have hmem2 : b + 1 ∈ Finset.range n := Finset.mem_range.2 hmem
    simp [hmem2]
  · have hsum0 : (∑ j ∈ Finset.range n, tri ii j * (if b + 1 = j then (1:ℤ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjp : j < n := Finset.mem_range.1 hj
      have hne : ¬ (b + 1 = j) := by omega
      simp [hne]
    have htri0 : tri ii (b + 1) = 0 := tri_eq_zero_of_lt ii (b+1) (by omega)
    rw [hsum0, htri0]

private theorem LT_apply (n : ℕ) (i k : Fin n) :
    (Lmat n * Tmat n) i k = tri i.val k.val + tri (i.val + 1) k.val := by
  have hi : i.val < n := i.isLt
  have hk : k.val < n := k.isLt
  rw [Matrix.mul_apply]
  have hstep : (∑ j : Fin n, Lmat n i j * Tmat n j k)
      = ∑ j ∈ Finset.range n, tri i.val j *
          ((if j = k.val then (3:ℤ) else 0) + (if j + 1 = k.val then (1:ℤ) else 0) +
              (if k.val + 1 = j then (1:ℤ) else 0)) := by
    have h1 : ∀ j : Fin n, Lmat n i j * Tmat n j k =
        tri i.val j.val * ((if j.val = k.val then (3:ℤ) else 0) +
            (if j.val + 1 = k.val then (1:ℤ) else 0) +
                (if k.val + 1 = j.val then (1:ℤ) else 0)) := by
      intro j
      simp only [Lmat]
      rw [Tmat_eq_sum]
    have h2 : (∑ j : Fin n, Lmat n i j * Tmat n j k)
        = (∑ j : Fin n, tri i.val j.val *
            ((if j.val = k.val then (3:ℤ) else 0) + (if j.val + 1 = k.val then (1:ℤ) else 0) +
                (if k.val + 1 = j.val then (1:ℤ) else 0))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact h1 j
    rw [h2]
    have h3 := Fin.sum_univ_eq_sum_range
        (fun m : ℕ => tri i.val m * ((if m = k.val then (3:ℤ) else 0) +
            (if m + 1 = k.val then (1:ℤ) else 0) + (if k.val + 1 = m then (1:ℤ) else 0))) n
    exact h3
  rw [hstep]
  have hdist : ∀ j : ℕ, tri i.val j *
      (((if j = k.val then (3:ℤ) else 0) + (if j + 1 = k.val then (1:ℤ) else 0) +
          (if k.val + 1 = j then (1:ℤ) else 0)))
      = tri i.val j * (if j = k.val then (3:ℤ) else 0) + tri i.val j *
          (if j + 1 = k.val then (1:ℤ) else 0) + tri i.val j *
              (if k.val + 1 = j then (1:ℤ) else 0) := by
    intro j
    ring
  simp_rw [hdist]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 := sum_S1 n i.val k.val hk
  have e3 := sum_S3 n i.val k.val hi hk
  by_cases hk0 : k.val = 0
  · have e2 : (∑ j ∈ Finset.range n, tri i.val j * (if j + 1 = k.val then (1:ℤ) else 0)) = 0 := by
      rw [hk0]
      exact sum_S2_zero n i.val
    rw [e1, e2, e3]
    rw [hk0]
    have htri : tri (i.val + 1) 0 = 2 * tri i.val 0 + tri i.val 1 := rfl
    linarith
  · have hbpos : 0 < k.val := by omega
    have e2 := sum_S2_pos n i.val k.val hk hbpos
    rw [e1, e2, e3]
    obtain ⟨b, hb⟩ : ∃ b, k.val = b + 1 := ⟨k.val - 1, by omega⟩
    rw [hb]
    have htri : tri (i.val + 1) (b + 1) = tri i.val b + 2 * tri i.val (b + 1) + tri i.val (b + 2) :=
        rfl
    have hb1 : b + 1 - 1 = b := by omega
    rw [hb1]
    linarith

private theorem LTLT_apply (n : ℕ) (i j : Fin n) :
    (Lmat n * Tmat n * (Lmat n).transpose) i j = tri (i.val + j.val) 0 + tri (i.val + 1 + j.val)
        0 := by
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  rw [Matrix.mul_apply]
  have h1 : ∀ k : Fin n, (Lmat n * Tmat n) i k * (Lmat n).transpose k j =
      ((tri i.val k.val + tri (i.val + 1) k.val) * tri j.val k.val) := by
    intro k
    rw [LT_apply]
    simp only [Matrix.transpose_apply, Lmat]
  have h2 : (∑ k : Fin n, (Lmat n * Tmat n) i k * (Lmat n).transpose k j)
      = (∑ k : Fin n, ((tri i.val k.val + tri (i.val + 1) k.val) * tri j.val k.val)) := by
    apply Finset.sum_congr rfl
    intro k _
    exact h1 k
  rw [h2]
  have h3 := Fin.sum_univ_eq_sum_range
      (fun m : ℕ => (tri i.val m + tri (i.val + 1) m) * tri j.val m) n
  have h4 : (∑ k : Fin n, (tri i.val k.val + tri (i.val + 1) k.val) * tri j.val k.val)
      = ∑ m ∈ Finset.range n, (tri i.val m + tri (i.val + 1) m) * tri j.val m := h3
  rw [h4]
  have hdist : ∀ m : ℕ, (tri i.val m + tri (i.val + 1) m) * tri j.val m
      = tri i.val m * tri j.val m + tri (i.val + 1) m * tri j.val m := by intro m; ring
  simp_rw [hdist]
  rw [Finset.sum_add_distrib]
  have e1 := dot_range_n_left n i.val j.val hi
  have e2 := dot_range_n_right n (i.val + 1) j.val hj
  rw [e1, e2]

private theorem H_eq (n : ℕ) :
    (fun i j : Fin n => ((catalan (i.val + j.val + 1) + catalan (i.val + j.val + 2) : ℕ) : ℤ))
    = Lmat n * Tmat n * (Lmat n).transpose := by
  funext i j
  rw [LTLT_apply]
  have e1 := tri_zero_eq_catalan (i.val + j.val)
  have e2 := tri_zero_eq_catalan (i.val + 1 + j.val)
  have h2 : i.val + 1 + j.val + 1 = i.val + j.val + 2 := by omega
  rw [h2] at e2
  rw [e1, e2]
  push_cast
  ring

private theorem succ_zero_eq_one (n : ℕ) : Fin.succ (0 : Fin (n+1)) = (1 : Fin (n+2)) := by
  ext
  simp

private theorem succAbove_one_zero (n : ℕ) : Fin.succAbove (1 : Fin (n+2)) (0 : Fin (n+1)) = 0 := by
  unfold Fin.succAbove
  simp

private theorem Tmat_row_zero_zero (n : ℕ) : Tmat (n+2) (0 : Fin (n+2)) 0 = 3 := by
  simp [Tmat]

private theorem Tmat_row_zero_one (n : ℕ) : Tmat (n+2) (0 : Fin (n+2)) (1 : Fin (n+2)) = 1 := by
  simp only [Tmat]
  simp

private theorem Tmat_row_zero_ss_aux (n : ℕ) (j : Fin (n + 2)) (hj : 2 ≤ j.val) :
    Tmat (n+2) 0 j = 0 := by
  have h1 : ¬ (0 = j.val) := by omega
  have h2 : ¬ (0 + 1 = j.val) := by omega
  simp only [Tmat, Fin.val_zero]
  simp [h1, h2]

private theorem Tmat_row_zero_ss (n : ℕ) (j : Fin n) : Tmat (n+2) 0 j.succ.succ = 0 := by
  apply Tmat_row_zero_ss_aux
  have h1 : (j.succ.succ).val = j.val + 2 := by simp [Fin.val_succ]
  omega

private theorem minor00_eq (n : ℕ) :
    (Tmat (n + 2)).submatrix (Fin.succAbove (0 : Fin (n+2))) (Fin.succAbove (0 : Fin (n+2))) = Tmat
        (n+1) := by
  funext i j
  simp only [Matrix.submatrix_apply, Fin.succAbove_zero_apply, Tmat, Fin.val_succ]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> omega

private theorem N_zero_zero_aux (n : ℕ) :
    (Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2))) (0 : Fin (n+1)) 0 = 1 := by
  simp only [Matrix.submatrix_apply, succAbove_one_zero]
  simp [Tmat]

private theorem N_succ_zero_aux (n : ℕ) (i : Fin n) :
    (Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2))) i.succ 0 = 0 := by
  simp only [Matrix.submatrix_apply, succAbove_one_zero]
  have hval : (i.succ.succ : Fin (n+2)).val = i.val + 2 := by simp [Fin.val_succ]
  have h1 : ¬ ((i.succ.succ : Fin (n+2)).val = (0 : Fin (n+2)).val) := by simp
  have h2 : ¬ ((i.succ.succ : Fin (n+2)).val + 1 = (0 : Fin (n+2)).val) := by simp
  have h3 : ¬ ((0 : Fin (n+2)).val + 1 =
      (i.succ.succ : Fin (n+2)).val) := by simp only [Fin.val_zero]; omega
  simp only [Tmat]
  simp

private theorem subminor_eq_aux (n : ℕ) :
    (((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))).submatrix
        (Fin.succAbove (0 : Fin (n+1))) Fin.succ) = Tmat n := by
  funext a b
  simp only [Matrix.submatrix_apply, Fin.succAbove_zero_apply, Fin.one_succAbove_succ]
  simp only [Tmat, Fin.val_succ]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> omega

private theorem detN_eq_aux (n : ℕ) :
    ((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))).det = (Tmat n).det := by
  have hdet : (((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))).det) =
      ∑ i : Fin (n+1), (-1 : ℤ) ^ i.val *
          ((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))) i 0 *
              (((((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))).submatrix
                  i.succAbove Fin.succ).det)) := Matrix.det_succ_column_zero _
  rw [hdet]
  rw [Fin.sum_univ_succ]
  have e0 : (-1 : ℤ) ^ (0 : Fin (n+1)).val *
      ((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))) 0 0 *
          (((((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))).submatrix
              (0 : Fin (n+1)).succAbove Fin.succ).det)) = (Tmat n).det := by
    have hpow : (-1 : ℤ) ^ (0 : Fin (n+1)).val = 1 := by simp
    rw [hpow, one_mul, N_zero_zero_aux]
    have h0 : (0 : Fin (n+1)).succAbove = Fin.succAbove (0 : Fin (n+1)) := rfl
    rw [h0, one_mul]
    rw [subminor_eq_aux]
  rw [e0]
  have hRest : (∑ i : Fin n, (-1 : ℤ) ^ (i.succ).val *
      ((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))) i.succ 0 *
          (((((Tmat (n+2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n+2)))).submatrix
              (i.succ).succAbove Fin.succ).det))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [N_succ_zero_aux n i, mul_zero, zero_mul]
  rw [hRest, add_zero]

private theorem det_Tmat_succ_succ (n : ℕ) : (Tmat (n+2)).det = 3 * (Tmat (n+1)).det -
    (Tmat n).det := by
  have hdet : (Tmat (n+2)).det =
      ∑ j : Fin (n+2), (-1 : ℤ) ^ j.val * Tmat (n+2) 0 j *
          (((Tmat (n+2)).submatrix Fin.succ j.succAbove).det) := Matrix.det_succ_row_zero _
  rw [hdet]
  have hpeel : ∀ (f : Fin (n+2) → ℤ), (∑ j : Fin (n+2), f j) = f 0 +
      (f 1 + ∑ j : Fin n, f j.succ.succ) := by
    intro f
    rw [Fin.sum_univ_succ]
    have h1 : (∑ j : Fin (n+1), f j.succ) = f (Fin.succ (0 : Fin (n+1))) + ∑ j : Fin n, f
        (Fin.succ (Fin.succ j)) := by
      rw [Fin.sum_univ_succ]
    rw [h1]
    have h01 : Fin.succ (0 : Fin (n+1)) = (1 : Fin (n+2)) := succ_zero_eq_one n
    rw [h01]
  rw [hpeel]
  have e0 : (-1 : ℤ) ^ (0 : Fin (n+2)).val * Tmat (n+2) 0 0 *
      (((Tmat (n+2)).submatrix Fin.succ (0 : Fin (n+2)).succAbove).det) = 3 * (Tmat (n+1)).det := by
    have hpow : (-1 : ℤ) ^ (0 : Fin (n+2)).val = 1 := by simp
    rw [hpow, one_mul, Tmat_row_zero_zero]
    have hmin : ((Tmat (n+2)).submatrix Fin.succ (0 : Fin (n+2)).succAbove).det =
        (Tmat (n+1)).det := by
      have h0 : (0 : Fin (n+2)).succAbove = Fin.succAbove (0 : Fin (n+2)) := rfl
      rw [h0]
      have hs : Fin.succ = Fin.succAbove (0 : Fin (n+2)) := (Fin.succAbove_zero).symm
      rw [hs]
      rw [minor00_eq]
    rw [hmin]
  have e1 : (-1 : ℤ) ^ (1 : Fin (n+2)).val * Tmat (n+2) 0 1 *
      (((Tmat (n+2)).submatrix Fin.succ (1 : Fin (n+2)).succAbove).det) = - (Tmat n).det := by
    have hpow : (-1 : ℤ) ^ (1 : Fin (n+2)).val = -1 := by simp
    rw [hpow, Tmat_row_zero_one, detN_eq_aux]
    ring
  have eRest : (∑ j : Fin n, (-1 : ℤ) ^ (j.succ.succ).val * Tmat (n+2) 0 j.succ.succ *
      (((Tmat (n+2)).submatrix Fin.succ (j.succ.succ).succAbove).det)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [Tmat_row_zero_ss n j, mul_zero, zero_mul]
  rw [e0, e1, eRest]
  ring

private theorem fib_add_four_aux (m : ℕ) : Nat.fib (m + 4) + Nat.fib m = 3 * Nat.fib (m + 2) := by
  have h1 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have h2 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two (n := m + 1)
  have h3 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two (n := m + 2)
  omega

private theorem fib_step_aux (n : ℕ) : ((Nat.fib (2 * (n + 2) + 2) : ℕ) : ℤ) = 3 *
    ((Nat.fib (2 * (n + 1) + 2) : ℕ) : ℤ) - ((Nat.fib (2 * n + 2) : ℕ) : ℤ) := by
  have h : Nat.fib (2 * n + 2 + 4) + Nat.fib (2 * n + 2) = 3 * Nat.fib (2 * n + 2 + 2) :=
      fib_add_four_aux (2 * n + 2)
  have e1 : 2 * (n + 2) + 2 = 2 * n + 2 + 4 := by omega
  have e2 : 2 * (n + 1) + 2 = 2 * n + 2 + 2 := by omega
  rw [e1, e2]
  have hZ := congrArg (Nat.cast : ℕ → ℤ) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hZ
  linarith

private theorem det_Tmat_zero_aux : (Tmat 0).det = ((Nat.fib (2 * 0 + 2) : ℕ) : ℤ) := by
  have hbase : ((Nat.fib (2 * 0 + 2) : ℕ) : ℤ) = 1 := by rfl
  rw [hbase]
  exact Matrix.det_isEmpty

private theorem det_Tmat_one_aux : (Tmat 1).det = ((Nat.fib (2 * 1 + 2) : ℕ) : ℤ) := by
  have hbase : ((Nat.fib (2 * 1 + 2) : ℕ) : ℤ) = 3 := by rfl
  rw [hbase]
  rw [Matrix.det_fin_one]
  simp [Tmat]

private theorem det_Tmat_fib (n : ℕ) : (Tmat n).det = ((Nat.fib (2 * n + 2) : ℕ) : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => exact det_Tmat_zero_aux
  | one => exact det_Tmat_one_aux
  | more n ih1 ih2 =>
    rw [det_Tmat_succ_succ, ih2, ih1, fib_step_aux]

/-- **Layman's Catalan-sum Hankel determinant, including the empty matrix.** Let $C_m$ denote the
$m$-th Catalan number and $F_m$ the $m$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For
every natural number $n$, the determinant of the $n \times n$ integer matrix whose $(i, j)$ entry
is $C_{i+j+1} + C_{i+j+2}$ for $0 \le i, j \le n-1$ equals $F_{2n+2}$. For $n = 0$ the matrix is
empty and both sides equal $1$.
-/
theorem layman_catalan_sum_hankel_det_unrestricted (n : ℕ) :
    Matrix.det (fun i j : Fin n =>
      ((catalan (i.val + j.val + 1) + catalan (i.val + j.val + 2) : ℕ) : ℤ)) =
      (Nat.fib (2 * n + 2) : ℤ) := by
  have hH : (fun i j : Fin n => ((catalan (i.val + j.val + 1) + catalan (i.val + j.val + 2) : ℕ) :
      ℤ))
      = Lmat n * Tmat n * (Lmat n).transpose := H_eq n
  rw [hH]
  rw [Matrix.det_mul, Matrix.det_mul, det_Lmat, one_mul, Matrix.det_transpose, det_Lmat, mul_one,
      det_Tmat_fib]

set_option linter.unusedVariables false in
/-- **Layman's Catalan-sum Hankel determinant.** Let $C_m$ denote the $m$-th Catalan number and
$F_m$ the $m$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For every integer $n \ge 1$, the
determinant of the $n \times n$ integer matrix whose $(i, j)$ entry is $C_{i+j+1} + C_{i+j+2}$ for
$0 \le i, j \le n-1$ equals $F_{2n+2}$.

Proves `Wanted` entry `layman_catalan_sum_hankel_det`.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL16/Bouras/bouras4.tex>, lines 109–117.
Source hash `12b867e2c1325f629838bfe224904d3bc59e21050fc9bdabc79d70f6a70f71ee`.
Concept `jis_dep_63ab37918a459a2ac2623d75`.
Corrected occurrence count: 3 mentions / 2 papers / 0 proof uses.
-/
theorem layman_catalan_sum_hankel_det (n : ℕ) (hn : 1 ≤ n) :
    Matrix.det (fun i j : Fin n =>
      ((catalan (i.val + j.val + 1) + catalan (i.val + j.val + 2) : ℕ) : ℤ)) =
      (Nat.fib (2 * n + 2) : ℤ) := by
  exact layman_catalan_sum_hankel_det_unrestricted n

end
end MetaMathlibExt
