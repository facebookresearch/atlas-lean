/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomidIndex
import MathlibExt.NumberTheory.BinomidPartialSum
import Mathlib.Data.Finset.Max
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic.Linarith

/-!
# Addition of lex-minimal extensions

Lex-minimal extensions are closed under componentwise addition.

Source: Jonathan Caalim and Yu-ichi Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 1.
-/

namespace MetaMathlibExt.IsLexMinimalExtension

private theorem sum_superadditive {η : ℕ → ℕ} (hη : IsBinomidIndex η) (a b : ℕ) :
    (∑ i ∈ Finset.range a, η i) + (∑ i ∈ Finset.range b, η i) ≤
      ∑ i ∈ Finset.range (a + b), η i := by
  rw [← Finset.sum_range_add_sum_Ico η (Nat.le_add_right a b)]
  exact Nat.add_le_add_left (by simpa using hη b (a + b) (by omega)) _

private theorem exists_period {η : ℕ → ℕ} (hη : IsLexMinimalExtension η) :
    ∃ p : ℕ, 0 < p ∧
      (∀ k, ∑ i ∈ Finset.range (k * p), η i = k * ∑ i ∈ Finset.range p, η i) ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        ∑ i ∈ Finset.range (n + p), η i =
          (∑ i ∈ Finset.range n, η i) + ∑ i ∈ Finset.range p, η i := by
  classical
  obtain ⟨m, hη⟩ := hη
  let s (n : ℕ) := ∑ i ∈ Finset.range n, η i
  have hsuper (a b : ℕ) : s a + s b ≤ s (a + b) := sum_superadditive hη.1 a b
  obtain ⟨p, hp, hmax⟩ := (Finset.Icc 1 (m + 1)).exists_max_image
    (binomidAverage η) ⟨1, by simp⟩
  have hp0 : 0 < p := by have := (Finset.mem_Icc.mp hp).1; omega
  have hpre (k : ℕ) (hk : k ≤ m + 1) : p * s k ≤ k * s p := by
    by_cases hk0 : k = 0
    · simp [hk0, s]
    · have h := hmax k (Finset.mem_Icc.mpr ⟨by omega, hk⟩)
      change (s k : ℚ) / k ≤ (s p : ℚ) / p at h
      have hkq : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
      have hpq : (0 : ℚ) < p := by exact_mod_cast hp0
      have h' := (div_le_div_iff₀ hkq hpq).mp h
      have h'' : (p : ℚ) * s k ≤ (k : ℚ) * s p := by simpa [mul_comm] using h'
      exact_mod_cast h''
  have hbound (n : ℕ) : p * s n ≤ n * s p := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n ≤ m + 1
      · exact hpre n hn
      · have hrec := (isBinomidIndex_iff_partialSum η).2 m hη n (by omega)
        obtain ⟨k, hk, heq⟩ := (Finset.Ico 1 n).exists_mem_eq_sup
          ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
          (fun k => s (n - k) + s k)
        have hk' := Finset.mem_Ico.mp hk
        have hsplit : s n = s (n - k) + s k := hrec.trans heq
        have hleft := ih (n - k) (by omega)
        have hright := ih k hk'.2
        rw [hsplit, Nat.mul_add]
        calc
          p * s (n - k) + p * s k ≤ (n - k) * s p + k * s p :=
            Nat.add_le_add hleft hright
          _ = n * s p := by rw [← Nat.add_mul, Nat.sub_add_cancel hk'.2.le]
  have hmul (k : ℕ) : s (k * p) = k * s p := by
    induction k with
    | zero => simp [s]
    | succ k ih =>
      have hlow := hsuper (k * p) p
      have hupp := hbound ((k + 1) * p)
      rw [Nat.add_mul, Nat.one_mul] at hupp ⊢
      rw [ih] at hlow
      nlinarith
  let d (n : ℕ) := n * s p - p * s n
  have hd (n : ℕ) : d n + p * s n = n * s p := Nat.sub_add_cancel (hbound n)
  have hstep (n : ℕ) : d (n + p) ≤ d n := by
    have h := Nat.mul_le_mul_left p (hsuper n p)
    have hn := hd n
    have hnp := hd (n + p)
    nlinarith
  have hstab (r : Fin p) : ∃ N, ∀ k, N ≤ k →
      d (r.val + N * p) = d (r.val + k * p) := by
    apply WellFoundedLT.antitone_chain_condition
    apply antitone_nat_of_succ_le
    intro k
    simpa [Nat.add_mul, Nat.add_assoc] using hstep (r.val + k * p)
  choose q hq using hstab
  let Q := Finset.univ.sup q
  refine ⟨p, hp0, hmul, Q * p, fun n hn => ?_⟩
  let r : Fin p := ⟨n % p, Nat.mod_lt n hp0⟩
  have hQ : Q ≤ n / p := (Nat.le_div_iff_mul_le hp0).mpr hn
  have hqle : q r ≤ n / p := (Finset.le_sup (f := q) (Finset.mem_univ r)).trans hQ
  have hrep : r.val + n / p * p = n := by
    simpa [r, Nat.mul_comm] using Nat.mod_add_div n p
  have hnext : r.val + (n / p + 1) * p = n + p := by
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, hrep]
  have heq : d n = d (n + p) := by
    simpa only [hrep, hnext] using (hq r (n / p) hqle).symm.trans
      (hq r (n / p + 1) (by omega))
  have hn' := hd n
  have hnp := hd (n + p)
  change s (n + p) = s n + s p
  nlinarith

private theorem of_sum_period {η : ℕ → ℕ} (hη : IsBinomidIndex η) {p N : ℕ}
    (hp : 0 < p) (hperiod : ∀ n, N ≤ n →
      ∑ i ∈ Finset.range (n + p), η i =
        (∑ i ∈ Finset.range n, η i) + ∑ i ∈ Finset.range p, η i) :
    IsLexMinimalExtension η := by
  classical
  refine ⟨N + p, hη, fun γ hγ hagree => ?_⟩
  by_cases heq : η = γ
  · exact Or.inl heq
  · have hdiff : ∃ j, η j ≠ γ j := by
      by_contra h
      apply heq
      funext j
      simpa using not_exists.mp h j
    let j := Nat.find hdiff
    have hj : η j ≠ γ j := Nat.find_spec hdiff
    have hbefore (i : ℕ) (hi : i < j) : η i = γ i := by
      simpa using Nat.find_min hdiff hi
    have hjpre : N + p ≤ j := by
      by_contra h
      exact hj (hagree j (by omega)).symm
    have hsums (t : ℕ) (ht : t ≤ j) :
        ∑ i ∈ Finset.range t, γ i = ∑ i ∈ Finset.range t, η i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hbefore i (lt_of_lt_of_le (Finset.mem_range.mp hi) ht)).symm
    have hsplit := sum_superadditive hγ (j + 1 - p) p
    rw [hsums _ (by omega), hsums _ (by omega), Nat.sub_add_cancel (by omega),
      Finset.sum_range_succ, hsums j le_rfl] at hsplit
    have hper := hperiod (j + 1 - p) (by omega)
    rw [Nat.sub_add_cancel (by omega), Finset.sum_range_succ] at hper
    exact Or.inr ⟨j, hbefore, by omega⟩

private theorem sum_period_mul {η : ℕ → ℕ} {p N : ℕ}
    (hperiod : ∀ n, N ≤ n →
      ∑ i ∈ Finset.range (n + p), η i =
        (∑ i ∈ Finset.range n, η i) + ∑ i ∈ Finset.range p, η i)
    (k n : ℕ) (hn : N ≤ n) :
    ∑ i ∈ Finset.range (n + k * p), η i =
      (∑ i ∈ Finset.range n, η i) + k * ∑ i ∈ Finset.range p, η i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, hperiod _ (by omega), ih]
    simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- **Lex-minimal extensions are closed under addition.** If $\eta_1$ and $\eta_2$ are
lex-minimal extensions, then their componentwise sum $\eta_1 + \eta_2$ is a lex-minimal
extension.

Since the zero sequence is also a lex-minimal extension, the set $L$ of lex-minimal extensions
is a monoid under componentwise addition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Corollary 1
(`integers-2024-A53-cor-1`). -/
public theorem add {η₁ η₂ : ℕ → ℕ}
    (h₁ : IsLexMinimalExtension η₁) (h₂ : IsLexMinimalExtension η₂) :
    IsLexMinimalExtension (η₁ + η₂) := by
  obtain ⟨p₁, hp₁, hmul₁, N₁, hper₁⟩ := exists_period h₁
  obtain ⟨p₂, hp₂, hmul₂, N₂, hper₂⟩ := exists_period h₂
  have hb₁ : IsBinomidIndex η₁ := h₁.choose_spec.1
  have hb₂ : IsBinomidIndex η₂ := h₂.choose_spec.1
  have hb : IsBinomidIndex (η₁ + η₂) := by
    intro k n hkn
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using
      Nat.add_le_add (hb₁ k n hkn) (hb₂ k n hkn)
  apply of_sum_period hb (p := p₁ * p₂) (N := max N₁ N₂) (Nat.mul_pos hp₁ hp₂)
  intro n hn
  have hper₁' := sum_period_mul hper₁ p₂ n ((le_max_left N₁ N₂).trans hn)
  have hper₂' := sum_period_mul hper₂ p₁ n ((le_max_right N₁ N₂).trans hn)
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [Nat.mul_comm p₁ p₂, hper₁', Nat.mul_comm p₂ p₁, hper₂',
    hmul₂ p₁, Nat.mul_comm p₁ p₂, hmul₁ p₂]
  omega

end MetaMathlibExt.IsLexMinimalExtension
