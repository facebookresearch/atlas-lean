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
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.IsBounded

/-!
# Lex-minimal extensions satisfy the Average Condition

`IsLexMinimalExtension.binomidAverageCondition` shows every lex-minimal extension satisfies
the Average Condition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3
(`integers-2024-A53-lem-3`).
-/

namespace MetaMathlibExt

private theorem binomidAverage_nonneg {η : ℕ → ℕ} {i : ℕ} (_hi : 1 ≤ i) :
    0 ≤ binomidAverage η i := by
  unfold binomidAverage
  apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem binomidAverage_zero (η : ℕ → ℕ) : binomidAverage η 0 = 0 := by
  simp [binomidAverage]

private theorem average_le_max_of_sum {η : ℕ → ℕ} {n a b : ℕ}
    (hn : 1 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = n)
    (hsum : ∑ i ∈ Finset.range n, η i
      = ∑ i ∈ Finset.range a, η i + ∑ i ∈ Finset.range b, η i) :
    binomidAverage η n ≤ max (binomidAverage η a) (binomidAverage η b) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha' : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb' : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hab' : (a : ℚ) + b = n := by exact_mod_cast hab
  set M : ℚ := max (binomidAverage η a) (binomidAverage η b) with hM
  have haM : binomidAverage η a ≤ M := le_max_left _ _
  have hbM : binomidAverage η b ≤ M := le_max_right _ _
  have h1 : ((∑ i ∈ Finset.range a, η i : ℕ) : ℚ) ≤ M * a := by
    have := (div_le_iff₀ ha').mp haM
    simpa [binomidAverage, mul_comm] using this
  have h2 : ((∑ i ∈ Finset.range b, η i : ℕ) : ℚ) ≤ M * b := by
    have := (div_le_iff₀ hb').mp hbM
    simpa [binomidAverage, mul_comm] using this
  have h3 : ((∑ i ∈ Finset.range n, η i : ℕ) : ℚ) ≤ M * n := by
    have hsum' : ((∑ i ∈ Finset.range n, η i : ℕ) : ℚ)
        = ((∑ i ∈ Finset.range a, η i : ℕ) : ℚ)
          + ((∑ i ∈ Finset.range b, η i : ℕ) : ℚ) := by
      exact_mod_cast hsum
    rw [hsum']
    calc ((∑ i ∈ Finset.range a, η i : ℕ) : ℚ)
          + ((∑ i ∈ Finset.range b, η i : ℕ) : ℚ)
        ≤ M * a + M * b := add_le_add h1 h2
      _ = M * n := by rw [← mul_add, ← hab']
  have := (div_le_iff₀ hn').mpr (by simpa [mul_comm] using h3)
  simpa [binomidAverage] using this

private theorem average_le_max_prefix {η : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hη : IsLexMinimalExtensionOf η m) {i₀ : ℕ}
    (hi₀max : ∀ x ∈ Finset.Icc 1 m, binomidAverage η x ≤ binomidAverage η i₀)
    (n : ℕ) (hn : 1 ≤ n) : binomidAverage η n ≤ binomidAverage η i₀ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hle : n ≤ m
    · exact hi₀max n (Finset.mem_Icc.mpr ⟨hn, hle⟩)
    · push Not at hle
      have hmn : m < n := hle
      have hrec := (isBinomidIndex_iff_partialSum η).2 m hη n hmn
      have hne : (Finset.Ico 1 n).Nonempty := ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
      obtain ⟨k, hk_mem, hk_eq⟩ :=
        Finset.exists_mem_eq_sup (Finset.Ico 1 n) hne
          (fun k => ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i)
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk_mem).1
      have hkn : k < n := (Finset.mem_Ico.mp hk_mem).2
      have hkn_le : k ≤ n := hkn.le
      have hnk_pos : 1 ≤ n - k := by omega
      have hnk_lt : n - k < n := by omega
      have hsum : ∑ i ∈ Finset.range n, η i
          = ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i := by
        rw [hrec, hk_eq]
      have hab : (n - k) + k = n := Nat.sub_add_cancel hkn_le
      have hbound : binomidAverage η n
          ≤ max (binomidAverage η (n - k)) (binomidAverage η k) :=
        average_le_max_of_sum hn hnk_pos hk1 hab hsum
      have ih1 : binomidAverage η (n - k) ≤ binomidAverage η i₀ :=
        ih (n - k) hnk_lt hnk_pos
      have ih2 : binomidAverage η k ≤ binomidAverage η i₀ := ih k hkn hk1
      calc binomidAverage η n
          ≤ max (binomidAverage η (n - k)) (binomidAverage η k) := hbound
        _ ≤ binomidAverage η i₀ := max_le ih1 ih2

@[expose] public section

/-- **Lex-minimal extensions satisfy the Average Condition.** Every lex-minimal extension
satisfies the Average Condition.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 3
(`integers-2024-A53-lem-3`). -/
public theorem IsLexMinimalExtension.binomidAverageCondition {η : ℕ → ℕ}
    (hη : IsLexMinimalExtension η) : BinomidAverageCondition η := by
  obtain ⟨m, hηm⟩ := hη
  by_cases hm0 : m = 0
  · subst hm0
    have hzero : IsBinomidIndex (fun _ => 0) := isBinomidIndex_const 0
    have hagree : ∀ i < 0, (fun _ => 0) i = η i := fun i hi => by omega
    rcases hηm.2 (fun _ => 0) hzero hagree with heq | ⟨j, _, hlt⟩
    · rw [heq]
      exact binomidAverageCondition_const 0
    · have hlt0 : η j < 0 := hlt
      omega
  · have hm : 1 ≤ m := by omega
    have hne : (Finset.Icc 1 m).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩⟩
    obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
      Finset.exists_max_image (Finset.Icc 1 m) (binomidAverage η) hne
    have hi₀1 : 1 ≤ i₀ := (Finset.mem_Icc.mp hi₀mem).1
    have hub : ∀ n, 1 ≤ n → binomidAverage η n ≤ binomidAverage η i₀ :=
      fun n hn => average_le_max_prefix hm hηm hi₀max n hn
    have hnonneg : 0 ≤ binomidAverage η i₀ := binomidAverage_nonneg hi₀1
    have hub0 : ∀ i, binomidAverage η i ≤ binomidAverage η i₀ := by
      intro i
      by_cases hi : 1 ≤ i
      · exact hub i hi
      · have hi0 : i = 0 := by omega
        rw [hi0, binomidAverage_zero]
        exact hnonneg
    have hubER : ∀ i, ((binomidAverage η i : ℝ) : EReal)
        ≤ ((binomidAverage η i₀ : ℝ) : EReal) := by
      intro i
      exact EReal.coe_le_coe (Rat.cast_le.mpr (hub0 i))
    have hev : ∀ᶠ i in Filter.atTop, ((binomidAverage η i : ℝ) : EReal)
        ≤ ((binomidAverage η i₀ : ℝ) : EReal) :=
      Filter.Eventually.of_forall hubER
    have hcob : Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop
        (fun i => ((binomidAverage η i : ℝ) : EReal)) :=
      Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop
        (Filter.Eventually.of_forall fun i => bot_le)
    have hlim_le : binomidUpperAverage η ≤ ((binomidAverage η i₀ : ℝ) : EReal) := by
      unfold binomidUpperAverage
      exact Filter.limsup_le_of_le hcob hev
    have hbin : IsBinomidIndex η := hηm.1
    have hfreq : ∃ᶠ i in Filter.atTop, ((binomidAverage η i₀ : ℝ) : EReal)
        ≤ ((binomidAverage η i : ℝ) : EReal) := by
      rw [Filter.frequently_atTop]
      intro N
      refine ⟨(N + 1) * i₀, ?_, ?_⟩
      · have hle : N + 1 ≤ (N + 1) * i₀ := Nat.le_mul_of_pos_right _ (by omega)
        omega
      · have hk1 : 1 ≤ N + 1 := by omega
        have hmult := (hbin.binomidAverage_props hi₀1 hi₀1).2.1 (N + 1) hk1
        have hNpos : 1 ≤ (N + 1) * i₀ := by
          have : 0 < (N + 1) * i₀ := Nat.mul_pos (by omega) (by omega)
          omega
        have hle2 := hub _ hNpos
        have heq : binomidAverage η ((N + 1) * i₀) = binomidAverage η i₀ :=
          le_antisymm hle2 hmult
        rw [heq]
    have hbdd : Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop
        (fun i => ((binomidAverage η i : ℝ) : EReal)) :=
      Filter.isBoundedUnder_of ⟨_, hubER⟩
    have hlim_ge : ((binomidAverage η i₀ : ℝ) : EReal) ≤ binomidUpperAverage η := by
      unfold binomidUpperAverage
      exact Filter.le_limsup_of_frequently_le hfreq hbdd
    exact ⟨i₀, hi₀1, le_antisymm hlim_le hlim_ge⟩

end

end MetaMathlibExt
