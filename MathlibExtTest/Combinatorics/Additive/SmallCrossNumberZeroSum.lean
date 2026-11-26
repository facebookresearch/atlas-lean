/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import all MathlibExt.Combinatorics.Additive.SmallCrossNumberZeroSum

open MetaMathlibExt

-- A sequence of length zero has no nonempty witness.
example : goodSequenceProb (ZMod 35) 0 = 0 := by
  have h : {g : Fin 0 → ZMod 35 | IsGoodSequence g} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, ⟨i, -⟩, -⟩
    exact i.elim0
  simp [goodSequenceProb, h]

-- Two copies of the nonzero element of order two attain cross number exactly one.
example : IsGoodSequence (fun _ : Fin 2 => (1 : ZMod 2)) := by
  refine ⟨Finset.univ, Finset.univ_nonempty, ?_, ?_⟩
  · decide
  · norm_num [ZMod.addOrderOf_one]

-- At length one in `ZMod 2 ^ 1`, only the zero sequence is good.
example : goodSequenceProb (Fin 1 → ZMod 2) 1 = 1 / 2 := by
  have h : {g : Fin 1 → Fin 1 → ZMod 2 | IsGoodSequence g} = {0} := by
    ext g
    change IsGoodSequence g ↔ g = 0
    constructor
    · rintro ⟨s, ⟨i, hi⟩, hz, -⟩
      have hs : s = {i} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun j _ => Subsingleton.elim j i⟩
      rw [hs, Finset.sum_singleton] at hz
      funext j
      rw [Subsingleton.elim j i]
      exact hz
    · rintro rfl
      exact ⟨{0}, Finset.singleton_nonempty _, by simp, by simp⟩
  simp [goodSequenceProb, h]

-- The threshold bound for good sequences in `ZMod 2 ^ d`.
example (ε : ℝ) (hε : 0 < ε) (t : ℕ → ℝ)
    (ht : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s) t) :
    t =O[Filter.atTop]
      fun d : ℕ => (2 : ℝ) ^ d / Real.logb 2 (Real.logb 2 ((2 : ℝ) ^ d)) ^ (1 - ε) :=
  zmod_two_pi_good_threshold_isBigO ε hε t ht

-- At length one in the group of order 35, only the zero sequence is good.
example : goodSequenceProb (ZMod 35) 1 = 1 / 35 := by
  have h : {g : Fin 1 → ZMod 35 | IsGoodSequence g} = {0} := by
    ext g
    change IsGoodSequence g ↔ g = 0
    constructor
    · rintro ⟨s, ⟨i, hi⟩, hz, -⟩
      have hs : s = {i} := Finset.ext fun j => by simp [Subsingleton.elim j i, hi]
      rw [hs, Finset.sum_singleton] at hz
      funext j
      simpa [Subsingleton.elim j i] using hz
    · rintro rfl
      exact ⟨{0}, Finset.singleton_nonempty _, by simp, by simp⟩
  simp [goodSequenceProb, h]

/-! ### The birthday threshold satisfies the hypothesis of the bound

A sequence in `ZMod 2 ^ d` is good exactly when it contains zero or repeats an entry. Counting
those sequences gives the birthday bounds, so the square root of `2 ^ d` is a threshold function. -/

namespace MathlibExtTest.Combinatorics.Additive.SmallCrossNumberZeroSum

open Filter Asymptotics MetaMathlibExt.zmod_two_pi_good_threshold_isBigO

open Classical in
private theorem prob_eq (d s : ℕ) :
    goodSequenceProb (Fin d → ZMod 2) s =
      1 - ((Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => ¬ IsGoodSequence g).card : ℝ) /
        ((2 : ℝ) ^ d) ^ s := by
  have hprob : goodSequenceProb (Fin d → ZMod 2) s =
      ((Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => IsGoodSequence g).card : ℝ) /
        ((2 ^ d : ℕ) : ℝ) ^ s := by
    simp [goodSequenceProb, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  have hsum : (Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => IsGoodSequence g).card +
      (Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => ¬ IsGoodSequence g).card =
      (2 ^ d) ^ s := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ d) ^ s := by positivity
  push_cast at hprob
  rw [hprob, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  exact_mod_cast hsum

-- Sequences of distinct nonzero vectors are not good.
open Classical in
private theorem descFactorial_le_card_bad (d s : ℕ) :
    (2 ^ d - 1).descFactorial s ≤
      (Finset.univ.filter fun g : Fin s → Fin d → ZMod 2 => ¬ IsGoodSequence g).card := by
  have hcard : Fintype.card (Fin s ↪ {x : Fin d → ZMod 2 // x ≠ 0}) =
      (2 ^ d - 1).descFactorial s := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    simp
  let toBad (e : Fin s ↪ {x : Fin d → ZMod 2 // x ≠ 0}) :
      {g : Fin s → Fin d → ZMod 2 // ¬ IsGoodSequence g} :=
    ⟨fun i => (e i).1, by
      rw [good_iff]
      rintro (⟨i, hi⟩ | ⟨i, j, hij, h⟩)
      · exact (e i).2 hi
      · exact hij (e.injective (Subtype.ext h))⟩
  have hinj : Function.Injective toBad := by
    intro e e' h
    exact Function.Embedding.ext fun i => Subtype.ext (congrFun (congrArg Subtype.val h) i)
  rw [← hcard, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective toBad hinj

-- `(n)_s / n ^ s ≤ exp (-s (s - 1) / (2 n))`.
private theorem descFactorial_div_le_exp (n s : ℕ) (hn : 0 < n) :
    (n.descFactorial s : ℝ) / (n : ℝ) ^ s ≤ Real.exp (-((s : ℝ) * (s - 1) / (2 * n))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
    rcases lt_or_ge s n with hs | hs
    · have hsR : (s : ℝ) < n := by exact_mod_cast hs
      have h1 : 0 ≤ ((n : ℝ) - s) / n := div_nonneg (by linarith) hnR.le
      have h2 : ((n : ℝ) - s) / n ≤ Real.exp (-(s / n)) := by
        have h := Real.one_sub_le_exp_neg ((s : ℝ) / n)
        rwa [one_sub_div hnR.ne'] at h
      calc ((n - s : ℕ) : ℝ) * n.descFactorial s / ((n : ℝ) ^ s * n)
          = (((n : ℝ) - s) / n) * (n.descFactorial s / (n : ℝ) ^ s) := by
            rw [Nat.cast_sub hs.le]
            field_simp
        _ ≤ Real.exp (-(s / n)) * Real.exp (-((s : ℝ) * (s - 1) / (2 * n))) :=
          mul_le_mul h2 ih (by positivity) (Real.exp_pos _).le
        _ = Real.exp (-(((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) - 1) / (2 * n))) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          field_simp
          ring
    · rw [Nat.sub_eq_zero_of_le hs]
      simp only [Nat.cast_zero, zero_mul, zero_div]
      exact (Real.exp_pos _).le

-- `1 - s (s + 1) / (2 n) ≤ (n - 1)_s / n ^ s`.
private theorem one_sub_le_descFactorial_div (n s : ℕ) (hn : 0 < n) :
    1 - (s : ℝ) * (s + 1) / (2 * n) ≤ ((n - 1).descFactorial s : ℝ) / (n : ℝ) ^ s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
    rcases lt_or_ge s (n - 1) with hs | hs
    · have hsR : (s : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : s + 1 ≤ n)
      have hcast : ((n - 1 - s : ℕ) : ℝ) = n - 1 - s := by
        rw [Nat.cast_sub hs.le, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have ha : 0 ≤ ((n : ℝ) - 1 - s) / n := div_nonneg (by linarith) hnR.le
      have hab : 0 ≤ ((s : ℝ) + 1) / n * ((s : ℝ) * (s + 1) / (2 * n)) := by positivity
      have hsplit : ((n : ℝ) - 1 - s) / n = 1 - ((s : ℝ) + 1) / n := by
        field_simp
        ring
      calc 1 - ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) + 1) / (2 * n)
          = 1 - ((s : ℝ) + 1) / n - (s : ℝ) * (s + 1) / (2 * n) := by
            push_cast
            field_simp
            ring
        _ ≤ (((n : ℝ) - 1 - s) / n) * (1 - (s : ℝ) * (s + 1) / (2 * n)) := by
          rw [hsplit]
          nlinarith [hab]
        _ ≤ (((n : ℝ) - 1 - s) / n) * ((n - 1).descFactorial s / (n : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_left ih ha
        _ = _ := by
          rw [hcast]
          field_simp
    · rw [Nat.sub_eq_zero_of_le hs]
      have hn1 : (n : ℝ) ≤ s + 1 := by exact_mod_cast (by omega : n ≤ s + 1)
      simp only [Nat.cast_zero, zero_mul, zero_div, sub_nonpos]
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith

-- The square root of `2 ^ d` is a threshold function for good sequences in `ZMod 2 ^ d`, so the
-- hypothesis of `zmod_two_pi_good_threshold_isBigO` can hold.
open Classical in
example : IsThresholdFunction (fun d s => goodSequenceProb (Fin d → ZMod 2) s)
    (fun d => Real.sqrt ((2 : ℝ) ^ d)) := by
  refine ⟨Eventually.of_forall fun d => Real.sqrt_pos.mpr (by positivity),
    fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · -- Once `f` dominates the square root, repeated entries become almost certain.
    have hx : Tendsto (fun d => (f d : ℝ) * ((f d : ℝ) - 1) / (2 * (2 : ℝ) ^ d)) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      have hc : (0 : ℝ) < 1 / (2 * (|b| + 1)) := by positivity
      filter_upwards [hf.def hc] with d hd
      have hN : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      have hsq : Real.sqrt ((2 : ℝ) ^ d) ^ 2 = (2 : ℝ) ^ d := Real.sq_sqrt hN.le
      have h1 : 1 ≤ Real.sqrt ((2 : ℝ) ^ d) :=
        Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num))
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] at hd
      have hf2 : 2 * (|b| + 1) * Real.sqrt ((2 : ℝ) ^ d) ≤ f d := by
        have hpos : (0 : ℝ) < 2 * (|b| + 1) := by positivity
        calc 2 * (|b| + 1) * Real.sqrt ((2 : ℝ) ^ d)
            ≤ 2 * (|b| + 1) * (1 / (2 * (|b| + 1)) * f d) :=
              mul_le_mul_of_nonneg_left hd hpos.le
          _ = f d := by field_simp
      -- With `B = |b| + 1`: `f ≥ 2 B √N ≥ 2`, so `f (f - 1) ≥ f ^ 2 / 2 ≥ 2 B ^ 2 N ≥ 2 b N`.
      have hB : 1 ≤ |b| + 1 := by linarith [abs_nonneg b]
      have hfge : (2 : ℝ) ≤ f d := by nlinarith
      have hfsq : 4 * (|b| + 1) ^ 2 * (2 : ℝ) ^ d ≤ (f d : ℝ) ^ 2 := by
        have h := pow_le_pow_left₀ (by positivity) hf2 2
        rw [mul_pow, mul_pow, hsq] at h
        linarith
      have hhalf : (f d : ℝ) ^ 2 / 2 ≤ f d * (f d - 1) := by nlinarith
      have hbB : b ≤ (|b| + 1) ^ 2 := by nlinarith [le_abs_self b, abs_nonneg b]
      have hbN : b * (2 * (2 : ℝ) ^ d) ≤ 2 * (|b| + 1) ^ 2 * (2 : ℝ) ^ d := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hlow (d : ℕ) : 1 - Real.exp (-((f d : ℝ) * ((f d : ℝ) - 1) / (2 * (2 : ℝ) ^ d))) ≤
        goodSequenceProb (Fin d → ZMod 2) (f d) := by
      have h := descFactorial_div_le_exp (2 ^ d) (f d) (by positivity)
      push_cast at h
      rw [prob_eq]
      have hbad := card_bad_le (d := d) (s := f d)
      have hbad' : ((Finset.univ.filter fun g : Fin (f d) → Fin d → ZMod 2 =>
          ¬ IsGoodSequence g).card : ℝ) ≤ ((2 ^ d).descFactorial (f d) : ℕ) := by
        exact_mod_cast hbad
      have hdiv := div_le_div_of_nonneg_right hbad' (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ d) ^ f d)
      linarith
    have hup (d : ℕ) : goodSequenceProb (Fin d → ZMod 2) (f d) ≤ 1 := by
      rw [prob_eq]
      have : (0 : ℝ) ≤ ((Finset.univ.filter fun g : Fin (f d) → Fin d → ZMod 2 =>
          ¬ IsGoodSequence g).card : ℝ) / ((2 : ℝ) ^ d) ^ f d := by positivity
      linarith
    have hexp : Tendsto (fun d => 1 - Real.exp (-((f d : ℝ) * ((f d : ℝ) - 1) /
        (2 * (2 : ℝ) ^ d)))) atTop (nhds 1) := by
      have h := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)).const_sub 1
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hexp tendsto_const_nhds hlow hup
  · -- Below the square root, zeros and repeated entries become rare.
    have hy : Tendsto (fun d => (f d : ℝ) * ((f d : ℝ) + 1) / (2 * (2 : ℝ) ^ d)) atTop
        (nhds 0) := by
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun d =>
        lt_of_lt_of_le ha (by positivity), fun a ha => ?_⟩
      have hc : (0 : ℝ) < min 1 (a / 2) := by positivity
      filter_upwards [hf.def hc] with d hd
      have hN : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      have hsq : Real.sqrt ((2 : ℝ) ^ d) ^ 2 = (2 : ℝ) ^ d := Real.sq_sqrt hN.le
      have h1 : 1 ≤ Real.sqrt ((2 : ℝ) ^ d) :=
        Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num))
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_natCast] at hd
      have hc1 : min 1 (a / 2) ≤ 1 := min_le_left _ _
      have hca : min 1 (a / 2) ≤ a / 2 := min_le_right _ _
      have hf0 : (0 : ℝ) ≤ f d := Nat.cast_nonneg _
      -- With `c = min 1 (a / 2)`: `f ^ 2 ≤ c ^ 2 N ≤ c N` and `f ≤ c √N ≤ c N`.
      have hsN : Real.sqrt ((2 : ℝ) ^ d) ≤ (2 : ℝ) ^ d := by nlinarith
      have hfN : (f d : ℝ) ≤ min 1 (a / 2) * (2 : ℝ) ^ d :=
        hd.trans (mul_le_mul_of_nonneg_left hsN hc.le)
      have hff : (f d : ℝ) * f d ≤ min 1 (a / 2) * (2 : ℝ) ^ d := by
        have h2 : (f d : ℝ) * f d ≤ (min 1 (a / 2) * Real.sqrt ((2 : ℝ) ^ d)) *
            (min 1 (a / 2) * Real.sqrt ((2 : ℝ) ^ d)) := mul_self_le_mul_self hf0 hd
        have h3 : (min 1 (a / 2) * Real.sqrt ((2 : ℝ) ^ d)) *
            (min 1 (a / 2) * Real.sqrt ((2 : ℝ) ^ d)) =
              min 1 (a / 2) * min 1 (a / 2) * (2 : ℝ) ^ d := by
          calc _ = min 1 (a / 2) * min 1 (a / 2) * Real.sqrt ((2 : ℝ) ^ d) ^ 2 := by ring
            _ = _ := by rw [hsq]
        have h4 : min 1 (a / 2) * min 1 (a / 2) * (2 : ℝ) ^ d ≤ min 1 (a / 2) * (2 : ℝ) ^ d := by
          have := mul_le_mul_of_nonneg_right hc1 (mul_nonneg hc.le hN.le)
          nlinarith
        linarith
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hup (d : ℕ) : goodSequenceProb (Fin d → ZMod 2) (f d) ≤
        (f d : ℝ) * ((f d : ℝ) + 1) / (2 * (2 : ℝ) ^ d) := by
      have h := one_sub_le_descFactorial_div (2 ^ d) (f d) (by positivity)
      push_cast at h
      rw [prob_eq]
      have hbad := descFactorial_le_card_bad d (f d)
      have hbad' : (((2 ^ d - 1).descFactorial (f d) : ℕ) : ℝ) ≤
          ((Finset.univ.filter fun g : Fin (f d) → Fin d → ZMod 2 =>
            ¬ IsGoodSequence g).card : ℝ) := by
        exact_mod_cast hbad
      have hdiv := div_le_div_of_nonneg_right hbad' (by positivity : (0 : ℝ) ≤ ((2 : ℝ) ^ d) ^ f d)
      linarith
    have hlow (d : ℕ) : 0 ≤ goodSequenceProb (Fin d → ZMod 2) (f d) := by
      unfold goodSequenceProb
      positivity
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hy hlow hup

end MathlibExtTest.Combinatorics.Additive.SmallCrossNumberZeroSum
