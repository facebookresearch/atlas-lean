/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.LiminfLimsup
public import MathlibExt.Combinatorics.Enumerative.TotienomialCoefficient
public import MathlibExt.NumberTheory.BinomidAverage
public import MathlibExt.NumberTheory.BinomidPartialSum
public import MathlibExt.NumberTheory.GeneralizedFibocatalanNumber
public import MathlibExt.NumberTheory.PrimeDvdChoose

import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Intersection of shifts of lex-minimal extensions

Distinct shifts of lex-minimal extensions have only the zero sequence in common.
The proof uses a maximum initial average and superadditivity of partial sums.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 6
(`integers-2024-A53-prop-6`).
-/

namespace MetaMathlibExt

private theorem sum_binomidShift (d : ℕ) (γ : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range n, binomidShift d γ i = ∑ i ∈ Finset.range (n - d), γ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : n < d
    · have h₀ : n - d = 0 := by omega
      have h₁ : n + 1 - d = 0 := by omega
      simp [binomidShift, hn, h₀, h₁]
    · have h₁ : n + 1 - d = (n - d) + 1 := by omega
      simp [binomidShift, hn, h₁, Finset.sum_range_succ]

private theorem exists_average_bound {η : ℕ → ℕ} (hη : IsLexMinimalExtension η) :
    ∃ j, (∀ n, ((∑ i ∈ Finset.range n, η i : ℕ) : ℚ) ≤ binomidAverage η j * n) ∧
      ((∑ i ∈ Finset.range j, η i : ℕ) : ℚ) = binomidAverage η j * j := by
  classical
  obtain ⟨m, hη⟩ := hη
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image (Finset.range (m + 1))
    (binomidAverage η) (by simp)
  have hb : 0 ≤ binomidAverage η j := by
    unfold binomidAverage
    positivity
  have hbound (n : ℕ) :
      ((∑ i ∈ Finset.range n, η i : ℕ) : ℚ) ≤ binomidAverage η j * n := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n ≤ m
      · cases n with
        | zero => simp
        | succ n =>
          exact (div_le_iff₀ (by positivity : 0 < ((n + 1 : ℕ) : ℚ))).mp
            (hmax (n + 1) (by
              simp only [Finset.mem_range]
              omega))
      · rw [(isBinomidIndex_iff_partialSum η).2 m hη n (by omega)]
        refine Finset.sup_induction
          (p := fun a : ℕ => (a : ℚ) ≤ binomidAverage η j * n) ?_ ?_ ?_
        · change (0 : ℚ) ≤ binomidAverage η j * n
          positivity
        · intro a ha b hb
          change ((max a b : ℕ) : ℚ) ≤ binomidAverage η j * n
          rw [Nat.cast_max]
          exact max_le ha hb
        · intro k hk
          obtain ⟨hk₁, hkn⟩ := Finset.mem_Ico.mp hk
          have ha := ih (n - k) (by omega)
          have hc := ih k hkn
          rw [Nat.cast_add]
          rw [Nat.cast_sub hkn.le] at ha
          nlinarith
  refine ⟨j, hbound, ?_⟩
  cases j with
  | zero => simp [binomidAverage]
  | succ j =>
    unfold binomidAverage
    exact (div_mul_cancel₀ _ (by positivity)).symm

private theorem lex_shift_eq_zero {d : ℕ} (hd : 0 < d) {γ : ℕ → ℕ}
    (hγ : IsBinomidIndex γ) (hlex : IsLexMinimalExtension (binomidShift d γ)) :
    binomidShift d γ = fun _ => 0 := by
  obtain ⟨j, hbound, hj⟩ := exists_average_bound hlex
  have hb : binomidAverage (binomidShift d γ) j ≤ 0 := by
    by_contra hn
    have hbpos : 0 < binomidAverage (binomidShift d γ) j := by linarith
    have hdj : d < j := by
      by_contra hn
      have hzero : j - d = 0 := by omega
      have hz : binomidAverage (binomidShift d γ) j = 0 := by
        simp [binomidAverage, sum_binomidShift, hzero]
      linarith
    have hdouble := (isBinomidIndex_iff_partialSum γ).1.mp hγ
      (j - d) (2 * (j - d)) (by omega) (by omega)
    have hsub : 2 * (j - d) - (j - d) = j - d := by omega
    rw [hsub] at hdouble
    have hdouble' :
        ((∑ i ∈ Finset.range (j - d), γ i : ℕ) : ℚ) +
          ((∑ i ∈ Finset.range (j - d), γ i : ℕ) : ℚ) ≤
            ((∑ i ∈ Finset.range (2 * (j - d)), γ i : ℕ) : ℚ) := by
      exact_mod_cast hdouble
    have h₂ := hbound (2 * (j - d) + d)
    rw [sum_binomidShift, Nat.add_sub_cancel] at h₂
    rw [sum_binomidShift] at hj
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hdj.le] at h₂
    norm_num only [Nat.cast_ofNat] at h₂
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    nlinarith
  funext i
  have h := hbound (i + 1)
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg hb (Nat.cast_nonneg (i + 1) : (0 : ℚ) ≤ _)
  have hsum := h.trans hnonpos
  rw [Finset.sum_range_succ, Nat.cast_add] at hsum
  have hi : ((binomidShift d γ i : ℕ) : ℚ) = 0 := by
    have hs : (0 : ℚ) ≤ (∑ k ∈ Finset.range i, binomidShift d γ k : ℕ) := by positivity
    have he : (0 : ℚ) ≤ (binomidShift d γ i : ℕ) := by positivity
    linarith
  exact_mod_cast hi

private theorem eq_shift_of_shift_eq {l m : ℕ} (hlm : l ≤ m) {η γ : ℕ → ℕ}
    (h : binomidShift l η = binomidShift m γ) : η = binomidShift (m - l) γ := by
  funext i
  have hleft : ¬l + i < l := by omega
  by_cases hi : i < m - l
  · have hli : l + i < m := by omega
    simpa [binomidShift, hleft, hi, hli] using congrFun h (l + i)
  · have hli : ¬l + i < m := by omega
    have hsub : l + i - m = i - (m - l) := by omega
    simpa [binomidShift, hleft, hi, hli, hsub] using congrFun h (l + i)

@[expose] public section

/-- **Distinct shifts of lex-minimal extensions meet only in zero.** Let $L$ be the set of
lex-minimal extensions, and for a natural number $l$ let $\sigma^l$ be the right shift that
prepends $l$ zeros to a sequence. For natural numbers $l \neq m$,
$\sigma^l(L) \cap \sigma^m(L) = \{(0, 0, 0, \dots)\}$: the only sequence in both images is
the zero sequence.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 6
(`integers-2024-A53-prop-6`). -/
public theorem binomidShift_image_inter_eq_zero {l m : ℕ} (hlm : l ≠ m) :
    binomidShift l '' {η | IsLexMinimalExtension η}
        ∩ binomidShift m '' {η | IsLexMinimalExtension η}
      = {fun _ => 0} := by
  have hzero (d : ℕ) : binomidShift d (fun _ => 0) = fun _ => 0 := by
    funext i
    simp [binomidShift]
  ext ξ
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨η, hη, hηξ⟩, ⟨γ, hγ, hγξ⟩⟩
    have h : binomidShift l η = binomidShift m γ := hηξ.trans hγξ.symm
    rcases Nat.lt_or_gt_of_ne hlm with hlt | hgt
    · have hrel := eq_shift_of_shift_eq hlt.le h
      have hz : η = fun _ => 0 := hrel.trans
        (lex_shift_eq_zero (by omega) hγ.choose_spec.1 (hrel ▸ hη))
      rw [← hηξ, hz, hzero]
    · have hrel := eq_shift_of_shift_eq hgt.le h.symm
      have hz : γ = fun _ => 0 := hrel.trans
        (lex_shift_eq_zero (by omega) hη.choose_spec.1 (hrel ▸ hγ))
      rw [← hγξ, hz, hzero]
  · intro hξ
    subst ξ
    exact ⟨⟨fun _ => 0, ⟨0, isLexMinimalExtensionOf_zero 0⟩, hzero l⟩,
      ⟨fun _ => 0, ⟨0, isLexMinimalExtensionOf_zero 0⟩, hzero m⟩⟩

end

end MetaMathlibExt
