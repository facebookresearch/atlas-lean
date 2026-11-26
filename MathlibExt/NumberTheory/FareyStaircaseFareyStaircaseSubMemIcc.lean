/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.FareyStaircase
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounds on the increment of the Farey staircase

The theorem `fareyStaircase_sub_mem_Icc` bounds the increment `D_n(x) = A_n(x) - A_{n-1}(x)`
of the Farey staircase: it is nonnegative and at most `(log n) / (n * (n - 1))` for `n ≥ 2`.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (b) (`integers-2024-A37-lem-8`) (primary text: arXiv:2303.02935).
-/

namespace MetaMathlibExt

@[expose] public section

open scoped Classical in
/-- A nonempty finset of naturals has a first index maximizing a real function. -/
private theorem exists_first_max (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) :
    ∃ d ∈ s, (∀ k ∈ s, f k ≤ f d) ∧ ∀ k ∈ s, f k = f d → d ≤ k := by
  have himg : (s.image f).Nonempty := hs.image f
  set M := (s.image f).max' himg with hM
  have hmax_mem : M ∈ s.image f := Finset.max'_mem _ _
  obtain ⟨d₀, hd₀s, hd₀M⟩ := Finset.mem_image.mp hmax_mem
  have hsub : s.filter (fun k => f k = M) ⊆ s := Finset.filter_subset _ _
  have hne : (s.filter (fun k => f k = M)).Nonempty :=
    ⟨d₀, Finset.mem_filter.mpr ⟨hd₀s, hd₀M⟩⟩
  set d := (s.filter (fun k => f k = M)).min' hne with hd
  have hdmem : d ∈ s.filter (fun k => f k = M) := Finset.min'_mem _ _
  have hdeq : f d = M := (Finset.mem_filter.mp hdmem).2
  refine ⟨d, hsub hdmem, ?_, ?_⟩
  · intro k hks
    have hle : f k ≤ M := Finset.le_max' _ _ (Finset.mem_image_of_mem f hks)
    simpa [hdeq] using hle
  · intro k hks hkeq
    have hkM : f k = M := by rw [hkeq, hdeq]
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hks, hkM⟩)

/-- Lower bound: the sum of the lower rational approximations does not exceed `⌊nx⌋`. -/
private theorem floor_sum_le_floor (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k ≤ ⌊(n : ℝ) * x⌋ := by
  refine Nat.strong_induction_on n (fun n ih => ?_)
  rcases n with _ | n
  · simp
  · have hn1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 (n + 1) := Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩
    obtain ⟨d, hds, hdmax, -⟩ := exists_first_max _ ⟨1, hmem⟩
      (fun k : ℕ => (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ))
    rw [Finset.mem_Icc] at hds
    obtain ⟨hd1, hdn⟩ := hds
    have hsub : n + 1 - d < n + 1 := by omega
    have ih0 := ih (n + 1 - d) hsub
    have hcast : ((n + 1 - d : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) - (d : ℝ) := Nat.cast_sub hdn
    have hsplit : ((n + 1 : ℕ) : ℝ) * x = ((n + 1 - d : ℕ) : ℝ) * x + (d : ℝ) * x := by
      rw [hcast]; ring
    have hfloor : ⌊((n + 1 - d : ℕ) : ℝ) * x⌋ + ⌊(d : ℝ) * x⌋ ≤ ⌊((n + 1 : ℕ) : ℝ) * x⌋ := by
      rw [hsplit]; exact Int.le_floor_add _ _
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hcard : (Finset.Icc (n + 1 - d + 1) (n + 1)).card = d := by
      rw [Nat.card_Icc]; omega
    have hblock : (⌊(d : ℝ) * x⌋ : ℝ)
        = ∑ k ∈ Finset.Icc (n + 1 - d + 1) (n + 1), (⌊(d : ℝ) * x⌋ : ℝ) / d := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      field_simp
    have hterm : ∀ k ∈ Finset.Icc (n + 1 - d + 1) (n + 1),
        (⌊(k : ℝ) * x⌋ : ℝ) / k ≤ (⌊(d : ℝ) * x⌋ : ℝ) / d := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      apply hdmax k
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hblock_le : ∑ k ∈ Finset.Icc (n + 1 - d + 1) (n + 1), (⌊(k : ℝ) * x⌋ : ℝ) / k
        ≤ ⌊(d : ℝ) * x⌋ := by
      rw [hblock]
      exact Finset.sum_le_sum hterm
    have hsplit_sum := Finset.sum_Ico_consecutive
      (fun k : ℕ => (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ))
      (show 1 ≤ n + 1 - d + 1 by omega) (show n + 1 - d + 1 ≤ n + 1 + 1 by omega)
    simp only [Finset.Ico_add_one_right_eq_Icc] at hsplit_sum
    rw [← hsplit_sum]
    have hcast_le : (⌊((n + 1 - d : ℕ) : ℝ) * x⌋ : ℝ) + (⌊(d : ℝ) * x⌋ : ℝ) ≤ (⌊((n + 1 : ℕ) : ℝ) * x⌋ : ℝ) := by
      exact_mod_cast hfloor
    linarith [ih0, hblock_le, hcast_le]

/-- Rearrangement: weighting a permutation of `{0, ..., n-1}` by `1/k` is maximized when the
values decrease with `k`. -/
private theorem sum_perm_div_le (n : ℕ) : ∀ (a : ℕ → ℕ),
    (∀ k ∈ Finset.Icc 1 n, a k < n) →
    (∀ j ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Icc 1 n, a j = a l → j = l) →
    ∑ k ∈ Finset.Icc 1 n, (a k : ℝ) / k ≤ ∑ k ∈ Finset.Icc 1 n, ((n : ℝ) - k) / k := by
  induction n with
  | zero => intro a _ _; simp
  | succ n ih =>
    intro a hmem hinj
    set t := a (n + 1) with ht
    set b : ℕ → ℕ := fun k => if t < a k then a k - 1 else a k with hb
    have htop : n + 1 ∈ Finset.Icc 1 (n + 1) :=
      Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 n, le_rfl⟩
    have httop : t < n + 1 := hmem _ htop
    have hsub : ∀ k ∈ Finset.Icc 1 n, k ∈ Finset.Icc 1 (n + 1) := by
      intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    have hne_top : ∀ k ∈ Finset.Icc 1 n, a k ≠ t := by
      intro k hk hcon
      have hkk : k ∈ Finset.Icc 1 (n + 1) := hsub k hk
      have heq := hinj k hkk (n + 1) htop hcon
      rw [Finset.mem_Icc] at hk
      omega
    have hbmem : ∀ k ∈ Finset.Icc 1 n, b k < n := by
      intro k hk
      have hak : a k < n + 1 := hmem k (hsub k hk)
      have hne : a k ≠ t := hne_top k hk
      simp only [hb]
      split_ifs with h <;> omega
    have hbinj : ∀ j ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Icc 1 n, b j = b l → j = l := by
      intro j hj l hl hbjl
      simp only [hb] at hbjl
      by_cases hj' : t < a j <;> by_cases hl' : t < a l <;>
        simp only [hj', hl', ite_true, ite_false] at hbjl
      · have heq : a j = a l := by omega
        exact hinj j (hsub j hj) l (hsub l hl) heq
      · have halt : a l = t := by omega
        have heq := hinj l (hsub l hl) (n + 1) htop halt
        rw [Finset.mem_Icc] at hl
        omega
      · have halt : a j = t := by omega
        have heq := hinj j (hsub j hj) (n + 1) htop halt
        rw [Finset.mem_Icc] at hj
        omega
      · exact hinj j (hsub j hj) l (hsub l hl) hbjl
    have ih' := ih b hbmem hbinj
    have hsum : ∑ k ∈ Finset.Icc 1 n, (a k : ℝ) / k
        = ∑ k ∈ Finset.Icc 1 n, (b k : ℝ) / k
          + ∑ k ∈ (Finset.Icc 1 n).filter (fun k => t < a k), (1 / (k : ℝ)) := by
      have hterm : ∀ k ∈ Finset.Icc 1 n, (a k : ℝ) / k
          = (b k : ℝ) / k + (if t < a k then (1 / (k : ℝ)) else 0) := by
        intro k hk
        simp only [hb]
        split_ifs with h
        · have h1 : 1 ≤ a k := by omega
          have hcast : ((a k - 1 : ℕ) : ℝ) = (a k : ℝ) - 1 := by
            rw [Nat.cast_sub h1, Nat.cast_one]
          rw [hcast, sub_div, sub_add_cancel]
        · simp
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hterm
    have hsurj : ∀ v < n + 1, ∃ k ∈ Finset.Icc 1 (n + 1), a k = v := by
      intro v hv
      have hsubimg : (Finset.Icc 1 (n + 1)).image a ⊆ Finset.range (n + 1) := by
        intro w hw
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_range.mpr (hmem k hk)
      have hcardimg : ((Finset.Icc 1 (n + 1)).image a).card
          = (Finset.range (n + 1)).card := by
        rw [Finset.card_image_of_injOn (fun j hj l hl h =>
          hinj j (Finset.mem_coe.mp hj) l (Finset.mem_coe.mp hl) h),
          Nat.card_Icc, Finset.card_range]
        omega
      have heq := Finset.eq_of_subset_of_card_le hsubimg (le_of_eq hcardimg.symm)
      have hmemv : v ∈ (Finset.Icc 1 (n + 1)).image a := by
        rw [heq]; exact Finset.mem_range.mpr hv
      obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hmemv
      exact ⟨k, hk, hkv⟩
    have himg_eq : ((Finset.Icc 1 n).filter (fun k => a k ≤ t)).image a
        = Finset.range t := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · rintro ⟨k, ⟨⟨hk1, hkn⟩, hkle⟩, rfl⟩
        have hkk : k ∈ Finset.Icc 1 (n + 1) := Finset.mem_Icc.mpr ⟨hk1, by omega⟩
        have hne : a k ≠ t := by
          intro hcon
          have heq := hinj k hkk (n + 1) htop hcon
          omega
        omega
      · intro hv
        obtain ⟨k, hk, hkv⟩ := hsurj v (by omega : v < n + 1)
        have hkk := Finset.mem_Icc.mp hk
        have hkne : k ≠ n + 1 := by
          intro hcon
          rw [hcon, ← ht] at hkv
          omega
        exact ⟨k, ⟨⟨hkk.1, by omega⟩, by omega⟩, hkv⟩
    have hcard_filter : ((Finset.Icc 1 n).filter (fun k => a k ≤ t)).card = t := by
      have hinjOn : Set.InjOn a ↑((Finset.Icc 1 n).filter (fun k => a k ≤ t)) := by
        intro j hj l hl h
        apply hinj j _ l _ h
        · exact hsub j ((Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1)
        · exact hsub l ((Finset.mem_filter.mp (Finset.mem_coe.mp hl)).1)
      have h1 := Finset.card_image_of_injOn hinjOn
      rw [himg_eq, Finset.card_range] at h1
      exact h1.symm
    have htle : (t : ℝ) / (((n + 1 : ℕ)) : ℝ)
        ≤ ∑ k ∈ (Finset.Icc 1 n).filter (fun k => a k ≤ t), (1 / (k : ℝ)) := by
      have hcast1 : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast1]
      have hval : (((Finset.Icc 1 n).filter (fun k => a k ≤ t)).card : ℝ) / ((n : ℝ) + 1)
          = ∑ _k ∈ (Finset.Icc 1 n).filter (fun k => a k ≤ t), (1 / ((n : ℝ) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_one_div]
      conv_lhs => rw [← hcard_filter]
      rw [hval]
      apply Finset.sum_le_sum
      intro k hk
      have hkk := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hkle : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : k ≤ n + 1)
      exact one_div_le_one_div_of_le hkpos hkle
    have hcover := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun k => t < a k)
      (fun k => (1 / (k : ℝ)))
    simp only [not_lt] at hcover
    have hRHS : ∑ k ∈ Finset.Icc 1 n, ((((n + 1 : ℕ)) : ℝ) - k) / k
        = ∑ k ∈ Finset.Icc 1 n, ((n : ℝ) - k) / k + ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      ring
    have hsplitL : ∑ k ∈ Finset.Icc 1 (n + 1), (a k : ℝ) / (k : ℝ)
        = ∑ k ∈ Finset.Icc 1 n, (a k : ℝ) / (k : ℝ)
          + (a (n + 1) : ℝ) / (((n + 1 : ℕ)) : ℝ) :=
      Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ n + 1 by omega) _
    have hsplitR : ∑ k ∈ Finset.Icc 1 (n + 1), ((((n + 1 : ℕ)) : ℝ) - k) / (k : ℝ)
        = ∑ k ∈ Finset.Icc 1 n, ((((n + 1 : ℕ)) : ℝ) - k) / (k : ℝ) + 0 := by
      have h := Finset.sum_Icc_succ_top (a := 1) (b := n) (show (1 : ℕ) ≤ n + 1 by omega)
        (fun k : ℕ => ((((n + 1 : ℕ)) : ℝ) - k) / (k : ℝ))
      rw [h]
      simp
    simp only [hsplitL, hsplitR, ← ht]
    linarith [hsum, ih', htle, hcover, hRHS]

/-- No index below the first maximum can make the maximal value integral. -/
private theorem not_integer_of_first_max (n : ℕ) (x y : ℝ)
    (hxmax : ∀ k ∈ Finset.Icc 1 n, ⌊(k : ℝ) * y⌋ = ⌊(k : ℝ) * x⌋)
    (hfirst_lt : ∀ k ∈ Finset.Icc 1 n, k < n → (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) < y)
    (e : ℕ) (he1 : 1 ≤ e) (hen : e < n) (t : ℤ) (hey : (e : ℝ) * y = (t : ℝ)) : False := by
  have he_mem : e ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨he1, by omega⟩
  have hlt_e := hfirst_lt e he_mem hen
  have hxmax_e := hxmax e he_mem
  have he_pos : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
  have hlt2 : (⌊(e : ℝ) * x⌋ : ℝ) < (e : ℝ) * y := by
    have h := hlt_e
    rw [div_lt_iff₀ he_pos] at h
    linarith
  have hfloor_eq : ⌊(e : ℝ) * y⌋ = t := by
    have h1 : ⌊((t : ℤ) : ℝ)⌋ = t := Int.floor_intCast t
    rwa [hey]
  rw [hxmax_e] at hfloor_eq
  have heq : (e : ℝ) * y = (⌊(e : ℝ) * x⌋ : ℝ) := by rw [hey, hfloor_eq]
  linarith

/-- Upper bound: the gap between `⌊nx⌋` and the sum of lower rational approximations is at most
the harmonic tail. -/
private theorem floor_gap_le_harmonic (n : ℕ) : ∀ (x : ℝ),
    (⌊(n : ℝ) * x⌋ : ℝ) - ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k
      ≤ ∑ k ∈ Finset.Icc 2 n, (1 / k : ℝ) := by
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro x
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hnmem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hn1, le_rfl⟩
    have hmem1 : (1 : ℕ) ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩
    obtain ⟨d, hds, hdmax0, hdfirst0⟩ := exists_first_max _ ⟨1, hmem1⟩
      (fun k : ℕ => (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ))
    have hdmax : ∀ k ∈ Finset.Icc 1 n,
        (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) ≤ (⌊(d : ℝ) * x⌋ : ℝ) / (d : ℝ) := hdmax0
    have hdfirst : ∀ k ∈ Finset.Icc 1 n,
        (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) = (⌊(d : ℝ) * x⌋ : ℝ) / (d : ℝ) → d ≤ k :=
      hdfirst0
    rw [Finset.mem_Icc] at hds
    obtain ⟨hd1, hdn⟩ := hds
    set y : ℝ := (⌊(d : ℝ) * x⌋ : ℝ) / (d : ℝ) with hy
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    have hy_le : y ≤ x := by
      have h : (⌊(d : ℝ) * x⌋ : ℝ) ≤ (d : ℝ) * x := Int.floor_le _
      rw [hy, div_le_iff₀ hdpos, mul_comm x]
      exact h
    have hxmax : ∀ k ∈ Finset.Icc 1 n, ⌊(k : ℝ) * y⌋ = ⌊(k : ℝ) * x⌋ := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) ≤ k := by exact_mod_cast (by omega : 0 ≤ k)
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      apply le_antisymm
      · exact Int.floor_le_floor (by gcongr)
      · rw [Int.le_floor]
        have h := hdmax k hk
        have h2 := mul_le_mul_of_nonneg_left h hkpos
        have h3 : (k : ℝ) * ((⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ)) = (⌊(k : ℝ) * x⌋ : ℝ) := by
          have hc := div_mul_cancel₀ ((⌊(k : ℝ) * x⌋ : ℝ)) hk0
          rw [mul_comm ((k : ℝ)) (((⌊(k : ℝ) * x⌋ : ℝ)) / (k : ℝ))]
          exact hc
        rwa [h3] at h2
    have hgap : (⌊(n : ℝ) * x⌋ : ℝ) - ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k
        = (⌊(n : ℝ) * y⌋ : ℝ) - ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * y⌋ : ℝ) / k := by
      have hsum : ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k
          = ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * y⌋ : ℝ) / k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hxmax k hk]
      rw [hxmax n hnmem, hsum]
    rw [hgap]
    have hdy : (d : ℝ) * y = (⌊(d : ℝ) * x⌋ : ℝ) := by
      have h := div_mul_cancel₀ ((⌊(d : ℝ) * x⌋ : ℝ)) hd0
      rw [hy, mul_comm ((d : ℝ)) (((⌊(d : ℝ) * x⌋ : ℝ)) / (d : ℝ))]
      exact h
    rcases lt_or_eq_of_le hdn with hdn_lt | hdn_eq
    · have ihd := ih d hdn_lt y
      have hxmax_d : ⌊(d : ℝ) * y⌋ = ⌊(d : ℝ) * x⌋ :=
        hxmax d (Finset.mem_Icc.mpr ⟨hd1, hdn⟩)
      have hsplit_sum := Finset.sum_Ico_consecutive
        (fun k : ℕ => (⌊(k : ℝ) * y⌋ : ℝ) / (k : ℝ))
        (show 1 ≤ d + 1 by omega) (show d + 1 ≤ n + 1 by omega)
      simp only [Finset.Ico_add_one_right_eq_Icc] at hsplit_sum
      have hny : (n : ℝ) * y = ((n - d : ℕ) : ℝ) * y + (⌊(d : ℝ) * x⌋ : ℝ) := by
        have hcast : ((n - d : ℕ) : ℝ) = (n : ℝ) - (d : ℝ) := Nat.cast_sub hdn
        rw [hcast, ← hdy]
        ring
      have hfloor_split : ⌊(n : ℝ) * y⌋ = ⌊((n - d : ℕ) : ℝ) * y⌋ + ⌊(d : ℝ) * x⌋ := by
        rw [hny, Int.floor_add_intCast]
      have hcard2 : (Finset.Icc (d + 1) n).card = n - d := by
        rw [Nat.card_Icc]; omega
      have hblock2 : ((n - d : ℕ) : ℝ) * y = ∑ k ∈ Finset.Icc (d + 1) n, y := by
        rw [Finset.sum_const, hcard2, nsmul_eq_mul]
      have hterm_lt : ∀ k ∈ Finset.Icc (d + 1) n,
          y - (⌊(k : ℝ) * y⌋ : ℝ) / k < 1 / (k : ℝ) := by
        intro k hk
        have hkk := Finset.mem_Icc.mp hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
        have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
        have h1 : (k : ℝ) * y - (⌊(k : ℝ) * y⌋ : ℝ) < 1 := by
          have h := Int.lt_floor_add_one ((k : ℝ) * y)
          linarith
        have heq : y - (⌊(k : ℝ) * y⌋ : ℝ) / k
            = ((k : ℝ) * y - (⌊(k : ℝ) * y⌋ : ℝ)) / k := by
          rw [eq_div_iff hk0, sub_mul, div_mul_cancel₀ _ hk0]
          ring
        rw [heq]
        gcongr
      have hmemd : d + 1 ∈ Finset.Icc (d + 1) n :=
        Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      have hsum_lt : ∑ k ∈ Finset.Icc (d + 1) n, (y - (⌊(k : ℝ) * y⌋ : ℝ) / k)
          < ∑ k ∈ Finset.Icc (d + 1) n, (1 / (k : ℝ)) :=
        Finset.sum_lt_sum (fun k hk => le_of_lt (hterm_lt k hk))
          ⟨d + 1, hmemd, hterm_lt _ hmemd⟩
      have hsplit_harm := Finset.sum_Ico_consecutive (fun k : ℕ => (1 / (k : ℝ)))
        (show 2 ≤ d + 1 by omega) (show d + 1 ≤ n + 1 by omega)
      simp only [Finset.Ico_add_one_right_eq_Icc] at hsplit_harm
      have hfloor_le : (⌊((n - d : ℕ) : ℝ) * y⌋ : ℝ) ≤ ((n - d : ℕ) : ℝ) * y :=
        Int.floor_le _
      have hsub_distrib : ∑ k ∈ Finset.Icc (d + 1) n, (y - (⌊(k : ℝ) * y⌋ : ℝ) / k)
          = ∑ k ∈ Finset.Icc (d + 1) n, y
            - ∑ k ∈ Finset.Icc (d + 1) n, (⌊(k : ℝ) * y⌋ : ℝ) / k :=
        Finset.sum_sub_distrib _ _
      have hcast_split : (⌊(n : ℝ) * y⌋ : ℝ)
          = (⌊((n - d : ℕ) : ℝ) * y⌋ : ℝ) + (⌊(d : ℝ) * x⌋ : ℝ) := by
        exact_mod_cast hfloor_split
      have hcast_d : (⌊(d : ℝ) * y⌋ : ℝ) = (⌊(d : ℝ) * x⌋ : ℝ) := by
        exact_mod_cast hxmax_d
      rw [hcast_split, ← hsplit_sum, ← hsplit_harm]
      linarith [ihd, hfloor_le, hblock2, hsum_lt, hsub_distrib, hcast_d]
    · set m : ℤ := ⌊(n : ℝ) * x⌋ with hm
      have hnym : (n : ℝ) * y = (m : ℝ) := by
        rw [hm, ← hdn_eq]
        exact hdy
      have hfirst_lt : ∀ k ∈ Finset.Icc 1 n,
          k < n → (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) < y := by
        intro k hk hkn
        have hle := hdmax k hk
        have hne : (⌊(k : ℝ) * x⌋ : ℝ) / (k : ℝ) ≠ y := by
          intro hcon
          have hle' := hdfirst k hk hcon
          omega
        exact lt_of_le_of_ne hle hne
      have hcard1 : (Finset.Icc 1 n).card = n := by
        rw [Nat.card_Icc]; omega
      set a : ℕ → ℕ := fun k => (((k : ℤ) * m - (n : ℤ) * ⌊(k : ℝ) * y⌋).toNat) with ha
      have hz_real : ∀ k : ℕ, ((((k : ℤ) * m - (n : ℤ) * ⌊(k : ℝ) * y⌋) : ℤ) : ℝ)
          = (n : ℝ) * ((k : ℝ) * y - (⌊(k : ℝ) * y⌋ : ℝ)) := by
        intro k
        push_cast
        rw [← hnym]
        ring
      have ha_nonneg : ∀ k : ℕ, (0:ℤ) ≤ (k : ℤ) * m - (n : ℤ) * ⌊(k : ℝ) * y⌋ := by
        intro k
        have hreal : (0:ℝ) ≤ ((((k : ℤ) * m - (n : ℤ) * ⌊(k : ℝ) * y⌋) : ℤ) : ℝ) := by
          rw [hz_real k]
          exact mul_nonneg (Nat.cast_nonneg n)
            (sub_nonneg.mpr (Int.floor_le ((k : ℝ) * y)))
        by_contra hcon
        have hcon' : (k : ℤ) * m - (n : ℤ) * ⌊(k : ℝ) * y⌋ < 0 := not_le.mp hcon
        have h' : ((((k : ℤ) * m - (n : ℤ) * ⌊(k : ℝ) * y⌋) : ℤ) : ℝ) < 0 := by
          exact_mod_cast hcon'
        linarith
      have ha_val : ∀ k : ℕ, ((a k : ℕ) : ℝ)
          = (n : ℝ) * ((k : ℝ) * y - (⌊(k : ℝ) * y⌋ : ℝ)) := by
        intro k
        have h1 : ((a k : ℕ) : ℤ) = (k : ℤ) * m - (n : ℤ) * ⌊(k : ℝ) * y⌋ :=
          Int.toNat_of_nonneg (ha_nonneg k)
        rw [← hz_real k]
        exact_mod_cast h1
      have ha_lt : ∀ k ∈ Finset.Icc 1 n, a k < n := by
        intro k hk
        have h1 : (k : ℝ) * y - (⌊(k : ℝ) * y⌋ : ℝ) < 1 := by
          have h := Int.lt_floor_add_one ((k : ℝ) * y)
          linarith
        have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have h2 : ((a k : ℕ) : ℝ) < (n : ℝ) := by
          rw [ha_val k]
          have hlt : (n:ℝ)*((k:ℝ)*y - ⌊(k:ℝ)*y⌋) < (n:ℝ)*1 := by gcongr
          simpa using hlt
        exact_mod_cast h2
      have ha_inj : ∀ j ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Icc 1 n, a j = a l → j = l := by
        intro j hj l hl hjal
        have hjj := Finset.mem_Icc.mp hj
        have hll := Finset.mem_Icc.mp hl
        have haj : ((a j : ℕ) : ℤ) = (j : ℤ) * m - (n : ℤ) * ⌊(j : ℝ) * y⌋ :=
          Int.toNat_of_nonneg (ha_nonneg j)
        have hal : ((a l : ℕ) : ℤ) = (l : ℤ) * m - (n : ℤ) * ⌊(l : ℝ) * y⌋ :=
          Int.toNat_of_nonneg (ha_nonneg l)
        have hcon : (j : ℤ) * m - (n : ℤ) * ⌊(j : ℝ) * y⌋
            = (l : ℤ) * m - (n : ℤ) * ⌊(l : ℝ) * y⌋ := by
          rw [← haj, ← hal]
          exact_mod_cast hjal
        have hint : ((j : ℤ) - l) * m = (n : ℤ) * (⌊(j:ℝ)*y⌋ - ⌊(l:ℝ)*y⌋) := by
          linear_combination hcon
        have hreal : ((j : ℝ) - l) * y
            = (⌊(j:ℝ)*y⌋:ℝ) - (⌊(l:ℝ)*y⌋:ℝ) := by
          have hc := congrArg (fun z : ℤ => (z : ℝ)) hint
          push_cast at hc
          rw [← hnym] at hc
          have h2 : (n:ℝ)*(((j:ℝ)-l)*y) = (n:ℝ)*((⌊(j:ℝ)*y⌋:ℝ)-(⌊(l:ℝ)*y⌋:ℝ)) := by
            linear_combination hc
          exact mul_left_cancel₀ hn0' h2
        rcases lt_trichotomy j l with hlt | heq | hgt
        · exfalso
          have hcast : ((l - j : ℕ) : ℝ) = (l : ℝ) - j := Nat.cast_sub (le_of_lt hlt)
          have he : ((l - j : ℕ) : ℝ) * y
              = (⌊(l:ℝ)*y⌋:ℝ) - (⌊(j:ℝ)*y⌋:ℝ) := by
            rw [hcast]; linarith [hreal]
          have hey : ((l - j : ℕ) : ℝ) * y
              = (((⌊(l:ℝ)*y⌋ - ⌊(j:ℝ)*y⌋ : ℤ)) : ℝ) := by
            rw [he, Int.cast_sub]
          exact not_integer_of_first_max n x y hxmax hfirst_lt (l - j) (by omega) (by omega)
            _ hey
        · exact heq
        · exfalso
          have hcast : ((j - l : ℕ) : ℝ) = (j : ℝ) - l := Nat.cast_sub (le_of_lt hgt)
          have he : ((j - l : ℕ) : ℝ) * y
              = (⌊(j:ℝ)*y⌋:ℝ) - (⌊(l:ℝ)*y⌋:ℝ) := by
            rw [hcast]; exact hreal
          have hey : ((j - l : ℕ) : ℝ) * y
              = (((⌊(j:ℝ)*y⌋ - ⌊(l:ℝ)*y⌋ : ℤ)) : ℝ) := by
            rw [he, Int.cast_sub]
          exact not_integer_of_first_max n x y hxmax hfirst_lt (j - l) (by omega) (by omega)
            _ hey
      have hrearr := sum_perm_div_le n a ha_lt ha_inj
      have hconv : ∑ k ∈ Finset.Icc 1 n, (((k : ℝ) * y - (⌊(k : ℝ) * y⌋ : ℝ)) / k)
          = (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, (a k : ℝ) / k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hk0 : (k : ℝ) ≠ 0 := by
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          exact_mod_cast (by omega : k ≠ 0)
        rw [ha_val k, mul_div_assoc, ← mul_assoc, one_div_mul_cancel hn0', one_mul]
      have hRHS_id : (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, ((n : ℝ) - k) / k
          = ∑ k ∈ Finset.Icc 2 n, (1 / k : ℝ) := by
        have hterm : ∀ k ∈ Finset.Icc 1 n, (1 / (n : ℝ)) * (((n : ℝ) - k) / k)
            = (1 / (k : ℝ)) - 1 / (n : ℝ) := by
          intro k hk
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
          field_simp
        have h2 : ∑ k ∈ Finset.Icc 1 n, (1 / (n:ℝ)) * (((n:ℝ)-k)/k)
            = ∑ k ∈ Finset.Icc 1 n, ((1/(k:ℝ)) - 1/(n:ℝ)) :=
          Finset.sum_congr rfl hterm
        rw [Finset.mul_sum, h2, Finset.sum_sub_distrib]
        have h3 : ∑ _k ∈ Finset.Icc 1 n, (1 / (n : ℝ)) = 1 := by
          rw [Finset.sum_const, hcard1, nsmul_eq_mul, mul_one_div_cancel hn0']
        have h4 : ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ))
            = 1 + ∑ k ∈ Finset.Icc 2 n, (1 / (k : ℝ)) := by
          have hset : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnotmem : (1:ℕ) ∉ Finset.Icc 2 n := by
            intro h
            have h' := Finset.mem_Icc.mp h
            omega
          rw [hset, Finset.sum_insert hnotmem, Nat.cast_one, div_one]
        linarith [h4, h3]
      have hfloor_ny : (⌊(n : ℝ) * y⌋ : ℝ) ≤ (n : ℝ) * y := Int.floor_le _
      have hsum_y : (n : ℝ) * y = ∑ k ∈ Finset.Icc 1 n, y := by
        rw [Finset.sum_const, hcard1, nsmul_eq_mul]
      have hsub2 : ∑ k ∈ Finset.Icc 1 n, (y - (⌊(k : ℝ) * y⌋ : ℝ) / k)
          = ∑ k ∈ Finset.Icc 1 n, y - ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * y⌋ : ℝ) / k :=
        Finset.sum_sub_distrib _ _
      have hdecomp2 : ∑ k ∈ Finset.Icc 1 n, (y - (⌊(k : ℝ) * y⌋ : ℝ) / k)
          = ∑ k ∈ Finset.Icc 1 n, (((k : ℝ) * y - (⌊(k : ℝ) * y⌋ : ℝ)) / k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk0 : (k : ℝ) ≠ 0 := by
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          exact_mod_cast (by omega : k ≠ 0)
        rw [eq_div_iff hk0, sub_mul, div_mul_cancel₀ _ hk0]
        ring
      have hnn : (0:ℝ) ≤ 1 / (n : ℝ) :=
        one_div_nonneg.mpr (by exact_mod_cast (by omega : 0 ≤ n))
      have hrearr' : (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, (a k : ℝ) / k
          ≤ (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, ((n : ℝ) - k) / k :=
        mul_le_mul_of_nonneg_left hrearr hnn
      linarith [hfloor_ny, hsum_y, hsub2, hdecomp2, hconv, hrearr', hRHS_id]

/-- The harmonic tail from `2` to `n` is at most `log n`. -/
private theorem harmonic_Icc_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 2 n, (1 / k : ℝ) ≤ Real.log n := by
  induction n, hn using Nat.le_induction
  case base =>
    rw [Finset.Icc_eq_empty (by decide : ¬ (2:ℕ) ≤ 1), Finset.sum_empty, Nat.cast_one,
      Real.log_one]
  case succ n hn ih =>
    have hsplit : ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (k:ℝ))
        = ∑ k ∈ Finset.Icc 2 n, (1 / (k:ℝ)) + 1 / (((n + 1 : ℕ)) : ℝ) :=
      Finset.sum_Icc_succ_top (show 2 ≤ n + 1 by omega) _
    rw [hsplit]
    have hstep : (1 / (((n + 1 : ℕ)) : ℝ)) ≤ Real.log ((n + 1 : ℕ)) - Real.log n := by
      have hn_pos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn1_pos : (0:ℝ) < (n : ℝ) + 1 := by
        have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      have hfrac_pos : (0:ℝ) < (n : ℝ) / ((n : ℝ) + 1) := div_pos hn_pos hn1_pos
      have hlog := Real.log_le_sub_one_of_pos hfrac_pos
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      have hn1_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1_pos
      have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have hlog_eq : Real.log ((n : ℝ) / ((n : ℝ) + 1))
          = Real.log n - Real.log ((n + 1 : ℕ)) := by
        rw [Real.log_div hn_ne hn1_ne, ← hcast]
      have halg : (1:ℝ) - (n : ℝ) / ((n : ℝ) + 1) = 1 / (((n + 1 : ℕ)) : ℝ) := by
        rw [hcast, sub_eq_iff_eq_add, ← add_div, add_comm (1:ℝ) (n:ℝ), div_self hn1_ne]
      linarith [hlog, hlog_eq, halg]
    linarith [ih, hstep]

/-- **Bounds on the increment of the Farey staircase.** Let $n \ge 2$ be a natural number and $x$
a real number, and write $A_m$ for the Farey staircase of order $m$. Then
$0 \le A_n(x) - A_{n-1}(x) \le \frac{\log n}{n(n-1)}$, where $\log$ is the natural logarithm.

Source: David Harry Richman, *Lower Rational Approximations and Farey Staircases*, INTEGERS 24
(2024), Article A37, Lemma 8 (b) (`integers-2024-A37-lem-8`). -/
public theorem fareyStaircase_sub_mem_Icc {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    0 ≤ fareyStaircase n x - fareyStaircase (n - 1) x ∧
      fareyStaircase n x - fareyStaircase (n - 1) x ≤ Real.log n / (n * (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnm_pos : (0:ℝ) < (n : ℝ) - 1 := by
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlower : fareyStaircase n x ≤ (⌊(n : ℝ) * x⌋ : ℝ) / n := by
    have h := floor_sum_le_floor n x
    have hnn : (0:ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hn_pos)
    have hmul := mul_le_mul_of_nonneg_left h hnn
    have heq : (n : ℝ)⁻¹ * (⌊(n : ℝ) * x⌋ : ℝ) = (⌊(n : ℝ) * x⌋ : ℝ) / n := by ring
    rw [heq] at hmul
    simpa [fareyStaircase] using hmul
  have hupper : (⌊(n : ℝ) * x⌋ : ℝ) / n ≤ fareyStaircase n x + Real.log n / n := by
    have hgap := floor_gap_le_harmonic n x
    have hharm := harmonic_Icc_le_log n hn1
    have hle : (⌊(n : ℝ) * x⌋ : ℝ) - ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k
        ≤ Real.log n := le_trans hgap hharm
    have hdiv : ((⌊(n : ℝ) * x⌋ : ℝ) - ∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k) / n
        ≤ Real.log n / n :=
      div_le_div_of_nonneg_right hle (le_of_lt hn_pos)
    have hA : fareyStaircase n x
        = (∑ k ∈ Finset.Icc 1 n, (⌊(k : ℝ) * x⌋ : ℝ) / k) / n := by
      simp only [fareyStaircase]
      ring
    rw [sub_div] at hdiv
    rw [hA]
    linarith [hdiv]
  have hsub := (fareyStaircase_sub_eq hn x).2
  rw [hsub]
  constructor
  · apply mul_nonneg (inv_nonneg.mpr (le_of_lt hnm_pos))
    linarith [hlower]
  · have hG : (⌊(n : ℝ) * x⌋ : ℝ) / n - fareyStaircase n x ≤ Real.log n / n := by
      linarith [hupper]
    have hmul := mul_le_mul_of_nonneg_left hG (inv_nonneg.mpr (le_of_lt hnm_pos))
    have heq : ((n : ℝ) - 1)⁻¹ * (Real.log n / n) = Real.log n / (n * (n - 1)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    rw [heq] at hmul
    exact hmul

end

end MetaMathlibExt
