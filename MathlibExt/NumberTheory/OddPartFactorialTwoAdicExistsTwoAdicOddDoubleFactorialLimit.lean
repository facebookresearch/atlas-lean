/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import MathlibExt.NumberTheory.OddPartFactorialTwoAdic
import Mathlib.Algebra.Order.CauSeq.Completion

/-!
# A 2-adic limit of normalized odd double factorials

This module proves the existence of a 2-adic integer `w` with `w ≡ ((2^e - 1)!! - 1) / 2^e`
modulo `2^(e-1)` for every `e ≥ 3`.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition after Corollary 10.
-/

namespace MetaMathlibExt

@[expose] public section

private def normQuot (e : ℕ) : ℤ := ((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e

private theorem normQuot_compat (e₁ e₂ : ℕ) (h1 : 3 ≤ e₁) (hle : e₁ ≤ e₂) :
    (2 : ℤ) ^ (e₁ - 1) ∣ normQuot e₁ - normQuot e₂ := by
  induction e₂, hle using Nat.le_induction with
  | base => simp [normQuot]
  | succ k hle ih =>
    have hk3 : 3 ≤ k := le_trans h1 hle
    have hstep : (2 : ℤ) ^ (k - 1) ∣ normQuot k - normQuot (k + 1) :=
      (oddDoubleFactorial_normalized_congr k hk3).2.2
    have hpow : (2 : ℤ) ^ (e₁ - 1) ∣ (2 : ℤ) ^ (k - 1) := pow_dvd_pow _ (by omega)
    have hstep' : (2 : ℤ) ^ (e₁ - 1) ∣ normQuot k - normQuot (k + 1) :=
      dvd_trans hpow hstep
    have hadd : (2 : ℤ) ^ (e₁ - 1) ∣
        (normQuot e₁ - normQuot k) + (normQuot k - normQuot (k + 1)) :=
      dvd_add ih hstep'
    have heq : (normQuot e₁ - normQuot k) + (normQuot k - normQuot (k + 1))
        = normQuot e₁ - normQuot (k + 1) := by ring
    rwa [heq] at hadd

private noncomputable def seqPadic : ℕ → ℤ_[2] := fun n => ((normQuot (n + 3) : ℤ) : ℤ_[2])

private theorem seqPadic_cau : IsCauSeq Norm.norm seqPadic := by
  intro ε hε
  obtain ⟨K, hK⟩ := PadicInt.exists_pow_neg_lt 2 hε
  have hK' : (2 : ℝ) ^ (-(K : ℤ)) < ε := by simpa [Nat.cast_ofNat] using hK
  refine ⟨K, fun m hm => ?_⟩
  have hle : K + 3 ≤ m + 3 := by omega
  have hdiv : (2 : ℤ) ^ ((K + 3) - 1) ∣ normQuot (K + 3) - normQuot (m + 3) :=
    normQuot_compat _ _ (by omega) hle
  have hdiv' : (2 : ℤ) ^ ((K + 3) - 1) ∣ normQuot (m + 3) - normQuot (K + 3) := by
    have h := dvd_neg.mpr hdiv
    simpa [neg_sub] using h
  have hcast : (seqPadic m - seqPadic K : ℤ_[2])
      = ((normQuot (m + 3) - normQuot (K + 3) : ℤ) : ℤ_[2]) := by
    simp [seqPadic, Int.cast_sub]
  have hnorm : ‖(seqPadic m - seqPadic K : ℤ_[2])‖
      ≤ (2 : ℝ) ^ (-(((K + 3) - 1 : ℕ) : ℤ)) := by
    rw [hcast]
    have hiff := PadicInt.norm_int_le_pow_iff_dvd (p := 2)
      (k := normQuot (m + 3) - normQuot (K + 3)) (n := (K + 3) - 1)
    simp only [Nat.cast_ofNat] at hiff
    exact hiff.mpr hdiv'
  have hmono : (2 : ℝ) ^ (-(((K + 3) - 1 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-(K : ℤ)) := by
    apply zpow_le_zpow_right₀ (by norm_num)
    have : (K : ℤ) ≤ (((K + 3) - 1 : ℕ) : ℤ) := by
      have : K ≤ (K + 3) - 1 := by omega
      exact_mod_cast this
    omega
  exact lt_of_le_of_lt (le_trans hnorm hmono) hK'

/--
**A 2-adic limit of normalized odd double factorials.** Write $(2^e - 1)!!$ for the product of
the odd natural numbers from $1$ to $2^e - 1$. There is a 2-adic integer $w$ such that for every
natural number $e \ge 3$, $2^{e-1}$ divides $w - \lfloor ((2^e - 1)!! - 1) / 2^e \rfloor$ in
$\mathbb{Z}_2$.

For $e \ge 3$ the division is exact. The paper writes $e \ge 2$, but at $e = 2$ the quotient
$(3 - 1)/4$ is not an integer.

Source: Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer
Sequences 29 (2026), Article 26.3.1, Definition after Corollary 10.
-/
public theorem exists_twoAdic_oddDoubleFactorial_limit :
    ∃ w : ℤ_[2], ∀ e : ℕ, 3 ≤ e →
      (2 : ℤ_[2]) ^ (e - 1) ∣ w -
        (↑(((oddDoubleFactorial e : ℤ) - 1) / (2 : ℤ) ^ e) : ℤ_[2])
    := by
  let f : CauSeq ℤ_[2] Norm.norm := ⟨seqPadic, seqPadic_cau⟩
  refine ⟨CauSeq.lim f, fun e he => ?_⟩
  set N := e - 3 with hN
  have hNe : N + 3 = e := by omega
  have hseq : seqPadic N = ((normQuot e : ℤ) : ℤ_[2]) := by simp [seqPadic, hNe]
  have hsuff : ‖(CauSeq.lim f - seqPadic N : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-((e - 1 : ℕ) : ℤ)) →
      (2 : ℤ_[2]) ^ (e - 1) ∣ CauSeq.lim f - ((normQuot e : ℤ) : ℤ_[2]) := by
    intro h
    rw [← hseq]
    have hiff := PadicInt.norm_le_pow_iff_mem_span_pow (p := 2)
      (CauSeq.lim f - seqPadic N) (e - 1)
    rw [Ideal.mem_span_singleton] at hiff
    simp only [Nat.cast_ofNat] at hiff
    exact hiff.mp h
  apply hsuff
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((e - 1 : ℕ) : ℤ)) :=
    zpow_pos (by norm_num) _
  have hequiv : f ≈ CauSeq.const Norm.norm (CauSeq.lim f) := CauSeq.equiv_lim f
  obtain ⟨i, hi⟩ := CauSeq.equiv_def₃ hequiv hpos
  set j := max i N with hj
  have hji : j ≥ i := le_max_left _ _
  have hjN : j ≥ N := le_max_right _ _
  have happ := hi j hji j le_rfl
  simp only [CauSeq.const_apply] at happ
  have hle : e ≤ j + 3 := by omega
  have hdiv : (2 : ℤ) ^ (e - 1) ∣ normQuot e - normQuot (j + 3) :=
    normQuot_compat _ _ he hle
  have hdiv' : (2 : ℤ) ^ (e - 1) ∣ normQuot (j + 3) - normQuot e := by
    have h := dvd_neg.mpr hdiv
    simpa [neg_sub] using h
  have hcast2 : (seqPadic j - seqPadic N : ℤ_[2])
      = ((normQuot (j + 3) - normQuot e : ℤ) : ℤ_[2]) := by
    simp [seqPadic, hNe, Int.cast_sub]
  have h2 : ‖(seqPadic j - seqPadic N : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-((e - 1 : ℕ) : ℤ)) := by
    rw [hcast2]
    have hiff := PadicInt.norm_int_le_pow_iff_dvd (p := 2)
      (k := normQuot (j + 3) - normQuot e) (n := e - 1)
    simp only [Nat.cast_ofNat] at hiff
    exact hiff.mpr hdiv'
  have h1 : ‖(CauSeq.lim f - seqPadic j : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-((e - 1 : ℕ) : ℤ)) := by
    have heq : (CauSeq.lim f - seqPadic j : ℤ_[2]) = -(seqPadic j - CauSeq.lim f) := by ring
    rw [heq, norm_neg]
    exact le_of_lt happ
  have hultr := PadicInt.nonarchimedean (CauSeq.lim f - seqPadic j) (seqPadic j - seqPadic N)
  have heq2 : (CauSeq.lim f - seqPadic j : ℤ_[2]) + (seqPadic j - seqPadic N)
      = CauSeq.lim f - seqPadic N := by ring
  rw [heq2] at hultr
  exact le_trans hultr (max_le_iff.mpr ⟨h1, h2⟩)

end

end MetaMathlibExt
