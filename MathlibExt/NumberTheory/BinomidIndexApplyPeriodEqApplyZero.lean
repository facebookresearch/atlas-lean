/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomidIndex
import MathlibExt.NumberTheory.BinomidPartialSum
import Mathlib.Tactic.Linarith

/-!
# Periodicity of lex-minimal extensions

`IsLexMinimalExtension.apply_period_eq_apply_zero` proves that a lex-minimal extension
periodic from its second entry has the same period at its first entry.

Source: Jonathan Caalim and Yu-ichi Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 4.
-/

namespace MetaMathlibExt.IsLexMinimalExtension

private theorem partialSum_mul_le {η : ℕ → ℕ} (hη : IsBinomidIndex η) (r n : ℕ) :
    r * (∑ i ∈ Finset.range n, η i) ≤ ∑ i ∈ Finset.range (r * n), η i := by
  let s (k : ℕ) := ∑ i ∈ Finset.range k, η i
  have hadd (a b : ℕ) : s a + s b ≤ s (a + b) := by
    by_cases ha : a = 0
    · simp [ha, s]
    by_cases hb : b = 0
    · simp [hb, s]
    simpa [s] using (isBinomidIndex_iff_partialSum η).1.mp hη b (a + b)
      (by omega) (by omega)
  change r * s n ≤ s (r * n)
  induction r with
  | zero => simp [s]
  | succ r ih =>
    calc
      (r + 1) * s n = r * s n + s n := Nat.succ_mul ..
      _ ≤ s (r * n) + s n := Nat.add_le_add_right ih _
      _ ≤ s ((r + 1) * n) := by simpa [Nat.succ_mul] using hadd (r * n) n

private theorem bound_of_recurrence (s : ℕ → ℕ) (m a b : ℕ)
    (hrec : ∀ n, m < n → s n = (Finset.Ico 1 n).sup fun k => s (n - k) + s k)
    (hbase : ∀ n, n ≤ m → a * s n ≤ n * b) (n : ℕ) : a * s n ≤ n * b := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n ≤ m
    · exact hbase n hn
    by_cases hsmall : n ≤ 1
    · have hempty : Finset.Ico 1 n = ∅ := by
        ext k
        simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false, not_and]
        omega
      simp [hrec n (by omega), hempty]
    obtain ⟨k, hk, heq⟩ := (Finset.Ico 1 n).exists_mem_eq_sup
      ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩ (fun k => s (n - k) + s k)
    obtain ⟨hkpos, hklt⟩ := Finset.mem_Ico.mp hk
    rw [hrec n (by omega), heq, Nat.mul_add]
    calc
      a * s (n - k) + a * s k ≤ (n - k) * b + k * b :=
        Nat.add_le_add (ih (n - k) (by omega)) (ih k hklt)
      _ = n * b := by rw [← Nat.add_mul, Nat.sub_add_cancel hklt.le]

/-- **A lex-minimal extension periodic from its second entry is periodic.** Let
$\eta = (e_1, e_2, \dots)$ be a lex-minimal extension and let $p \ge 1$. If $e_{i+p} = e_i$
for every $i \ge 2$, then $e_{1+p} = e_1$, so the whole sequence $\eta$ is periodic with
period $p$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 4
(`integers-2024-A53-prop-4`). -/
public theorem apply_period_eq_apply_zero {η : ℕ → ℕ}
    (hη : IsLexMinimalExtension η) {p : ℕ} (hp : 0 < p)
    (hper : ∀ i, 1 ≤ i → η (i + p) = η i) : η p = η 0 := by
  obtain ⟨m, hm⟩ := hη
  have hle : η 0 ≤ η p := by simpa using hm.1 1 (p + 1) (by omega)
  by_contra hne
  let s (n : ℕ) := ∑ i ∈ Finset.range n, η i
  let d := η p - η 0
  let C := s p + d
  have hd : 0 < d := by dsimp [d]; omega
  have hs (n : ℕ) : s (n + 1) = s n + η n := Finset.sum_range_succ ..
  have hshift (n : ℕ) (hn : 1 ≤ n) : s (n + p) = s n + C := by
    induction n, hn using Nat.le_induction with
    | base =>
      have h₁ := hs p
      have h₂ := hs 0
      have h₀ : s 0 = 0 := by simp [s]
      rw [Nat.add_comm 1 p]
      simp only [Nat.zero_add] at h₂
      dsimp [C, d]
      omega
    | succ n hn ih =>
      rw [Nat.succ_add, hs, hs, ih, hper n hn]
      omega
  have hmul (n : ℕ) (hn : 1 ≤ n) : s (n * p) + d = n * C := by
    induction n, hn using Nat.le_induction with
    | base => simp [C]
    | succ n hn ih =>
      rw [Nat.add_mul, one_mul, hshift (n * p) (by nlinarith), Nat.add_mul, one_mul]
      omega
  have hstrict (n : ℕ) (hn : 1 ≤ n) : p * s n < n * C := by
    have h₁ := partialSum_mul_le hm.1 p n
    have h₂ := hmul n hn
    change p * s n ≤ s (p * n) at h₁
    rw [Nat.mul_comm p n] at h₁
    omega
  let M := m + 1
  have hC : 0 < C := by have := hstrict 1 le_rfl; omega
  have hMC : 1 ≤ M * C := by dsimp [M]; nlinarith
  have hbase (n : ℕ) (hn : n ≤ m) : (M * p) * s n ≤ n * (M * C - 1) := by
    by_cases hzero : n = 0
    · simp [hzero, s]
    have h₁ := hstrict n (by omega)
    have h₂ : n ≤ M := by dsimp [M]; omega
    have h₃ : M * C - 1 + 1 = M * C := Nat.sub_add_cancel hMC
    nlinarith
  have hbound (n : ℕ) : (M * p) * s n ≤ n * (M * C - 1) :=
    bound_of_recurrence s m (M * p) (M * C - 1)
      ((isBinomidIndex_iff_partialSum η).2 m hm) hbase n
  have h₁ := hbound ((M * d + 1) * p)
  have h₂ := hmul (M * d + 1) (by omega)
  have h₃ : M * C - 1 + 1 = M * C := Nat.sub_add_cancel hMC
  have h₄ : M * s ((M * d + 1) * p) ≤ (M * d + 1) * (M * C - 1) :=
    Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h₁) hp
  have h₅ : M * s ((M * d + 1) * p) + M * d = (M * d + 1) * (M * C) := by
    rw [← Nat.mul_add, h₂, Nat.mul_left_comm]
  have h₆ := congrArg (fun x => (M * d + 1) * x) h₃
  simp only [Nat.mul_add, Nat.mul_one] at h₆
  omega

end MetaMathlibExt.IsLexMinimalExtension
