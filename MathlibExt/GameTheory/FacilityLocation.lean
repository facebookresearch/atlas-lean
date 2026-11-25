/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.List.Sort
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Strategyproof facility location on the line

Model (C1): agents `ι` report points `x : ι → ℝ` on the real line; a
deterministic mechanism `f : Mechanism ι` outputs a facility location `y : ℝ`;
agent `i`'s cost is `|y - x i|`. Social cost sums individual costs; maximum
cost takes the largest individual cost.

Main results:
- C1 (model): `Mechanism`, `cost`, `socialCost`, `maxCost` with `le_maxCost`
  and `maxCost_le`; `IsStrategyproof`, `IsGroupStrategyproof`, and
  `isStrategyproof_of_isGroupStrategyproof`.
- C2 (median): `median` (lower median), `median_minimizes_socialCost`,
  `median_isGroupStrategyproof`, `median_isStrategyproof`.
- C3 (leftmost): `leftmost` with `leftmost_le` and `leftmost_exists`;
  `IsApproxMaxCost`, `leftmost_isStrategyproof`,
  `leftmost_isApproxMaxCost_two`.
- C4 (lower bound): `two_le_of_isStrategyproof_isApproxMaxCost`.

Non-goals: randomized mechanisms; multiple facilities; networks.

References:
- A. D. Procaccia and M. Tennenholtz, "Approximate mechanism design without
  money", ACM Transactions on Economics and Computation 1(4), 2013 (EC 2009).
- H. Moulin, "On strategy-proofness and single peakedness",
  Public Choice 35, 1980.
-/

namespace MathlibExt.GameTheory.FacilityLocation

variable {ι : Type*}

/-- (C1 model) A deterministic facility-location mechanism maps reported
profiles to a facility location. -/
public abbrev Mechanism (ι : Type*) : Type _ := (ι → ℝ) → ℝ

/-- (C1 model) Cost to agent `i` when the profile is `x` and the facility
is at `y`: the distance `|y - x i|`. -/
public def cost (x : ι → ℝ) (y : ℝ) (i : ι) : ℝ := |y - x i|

/-- (C1 model) Social cost: the sum of individual costs. -/
public def socialCost [Fintype ι] (x : ι → ℝ) (y : ℝ) : ℝ := ∑ i, |y - x i|

/-- (C1 model) Maximum cost: the largest individual cost. -/
public noncomputable def maxCost [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (y : ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty fun i => |y - x i|

/-- (C1 model) Each agent's cost is at most the maximum cost. -/
public theorem le_maxCost [Fintype ι] [Nonempty ι] (x : ι → ℝ) (y : ℝ)
    (i : ι) : |y - x i| ≤ maxCost x y :=
  Finset.le_sup' (fun j => |y - x j|) (Finset.mem_univ i)

/-- (C1 model) The maximum cost is at most `z` if every agent's cost is. -/
public theorem maxCost_le [Fintype ι] [Nonempty ι] (x : ι → ℝ) (y : ℝ)
    (z : ℝ) (h : ∀ i, |y - x i| ≤ z) : maxCost x y ≤ z :=
  Finset.sup'_le _ _ fun i _ => h i

/-- (C1 model) Strategyproofness: no agent can strictly lower its own cost
by unilaterally misreporting. -/
public def IsStrategyproof [DecidableEq ι] (f : Mechanism ι) : Prop :=
  ∀ (x : ι → ℝ) (i : ι) (r : ℝ),
    |f x - x i| ≤ |f (Function.update x i r) - x i|

/-- (C1 model) Group strategyproofness: no nonempty coalition can jointly
misreport so that every member's cost strictly drops. -/
public def IsGroupStrategyproof (f : Mechanism ι) : Prop :=
  ∀ (x x' : ι → ℝ) (S : Finset ι), (∀ i, i ∉ S → x' i = x i) →
    ¬ (S.Nonempty ∧ ∀ i ∈ S, |f x' - x i| < |f x - x i|)

/-- (C1 model) Group strategyproofness implies strategyproofness, via
singleton coalitions. -/
public theorem isStrategyproof_of_isGroupStrategyproof [DecidableEq ι]
    {f : Mechanism ι} (h : IsGroupStrategyproof f) : IsStrategyproof f := by
  intro x i r
  have hmem : ∀ j, j ∉ ({i} : Finset ι) → Function.update x i r j = x j := by
    intro j hj
    exact Function.update_of_ne (by simpa [Finset.mem_singleton] using hj) r x
  have hneg := h x (Function.update x i r) {i} hmem
  have hne : ({i} : Finset ι).Nonempty := ⟨i, Finset.mem_singleton_self i⟩
  by_contra hcon
  push Not at hcon
  exact hneg ⟨hne, fun j hj => by rw [Finset.mem_singleton.mp hj]; exact hcon⟩

/-- (C2 median) The lower median: the `((n-1)/2)`-th order statistic
(0-indexed) of the profile, via the sorted list of reports. -/
public noncomputable def median {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ℝ :=
  (List.insertionSort (· ≤ ·) (List.ofFn x)).get ⟨(n - 1) / 2, by
    rw [List.length_insertionSort, List.length_ofFn]
    have hn : n ≠ 0 := NeZero.ne n
    omega⟩

/-- Helper bridging `Finset` filter cards and `List.countP` on `ofFn`. -/
private theorem card_filter_eq_countP_ofFn {n : ℕ} (f : Fin n → ℝ)
    (p : ℝ → Prop) [DecidablePred p]
    [DecidablePred fun i => p (f i)] :
    (Finset.univ.filter fun i => p (f i)).card =
      (List.ofFn f).countP fun v => decide (p v) := by
  have h1 : (Finset.univ.filter fun i => p (f i)).card =
      ((List.finRange n).toFinset.filter fun i => p (f i)).card := by
    rw [← List.toFinset_finRange]
  rw [h1, (List.nodup_finRange n).card_eq_countP, List.ofFn_eq_map,
    List.countP_map]
  apply List.countP_congr
  intro b _
  simp

/-- Helper transferring counts from profiles to sorted lists. -/
private theorem card_filter_eq_countP_sorted {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) (p : ℝ → Prop) [DecidablePred p]
    [DecidablePred fun i => p (x i)] :
    (Finset.univ.filter fun i => p (x i)).card =
      (List.insertionSort (· ≤ ·) (List.ofFn x)).countP
        fun v => decide (p v) := by
  rw [card_filter_eq_countP_ofFn]
  exact (List.Perm.countP_eq _
    (List.perm_insertionSort _ _)).symm

/-- Helper: sorted list length equals profile size. -/
private theorem sorted_length {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    (List.insertionSort (· ≤ ·) (List.ofFn x)).length = n := by
  rw [List.length_insertionSort, List.length_ofFn]

/-- Helper: sorted list get is monotone. -/
private theorem sorted_mono {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    Monotone (List.insertionSort (· ≤ ·) (List.ofFn x)).get :=
  List.sortedLE_insertionSort.monotone_get

/-- Helper: at least `k+1` reports are at most the median. -/
private theorem median_card_le {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    (n - 1) / 2 + 1 ≤
      (Finset.univ.filter fun i => x i ≤ median x).card := by
  classical
  set s := List.insertionSort (· ≤ ·) (List.ofFn x) with hs
  set k := (n - 1) / 2 with hk
  set m := median x with hm
  have hlen : s.length = n := by
    rw [hs, List.length_insertionSort, List.length_ofFn]
  have hn : n ≠ 0 := NeZero.ne n
  have hk_lt : k < n := by omega
  have hk_len : k < s.length := by omega
  set K : Fin s.length := ⟨k, hk_len⟩ with hK
  have hm_eq : s.get K = m := by simp [hs, hm, hK, median, hk]
  have hmono : Monotone s.get := by
    rw [hs]
    exact sorted_mono x
  rw [card_filter_eq_countP_sorted x (fun v => v ≤ m)]
  have hbridge : (Finset.univ.filter
      fun i : Fin s.length => s.get i ≤ m).card =
      s.countP fun v => decide (v ≤ m) := by
    have h := card_filter_eq_countP_ofFn s.get (fun v => v ≤ m)
    rw [List.ofFn_get] at h
    exact h
  rw [← hbridge]
  have hsub : Finset.Iic K ⊆
      Finset.univ.filter (fun i : Fin s.length => s.get i ≤ m) := by
    intro i hi
    rw [Finset.mem_Iic] at hi
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ i
    · calc s.get i ≤ s.get K := hmono hi
        _ = m := hm_eq
  have hle := Finset.card_le_card hsub
  have hcard : (Finset.Iic K).card = k + 1 := by
    rw [Fin.card_Iic]
  omega

/-- Helper: at most `k` reports are below the median. -/
private theorem median_card_lt {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    (Finset.univ.filter fun i => x i < median x).card ≤ (n - 1) / 2 := by
  classical
  set s := List.insertionSort (· ≤ ·) (List.ofFn x) with hs
  set k := (n - 1) / 2 with hk
  set m := median x with hm
  have hlen : s.length = n := by
    rw [hs, List.length_insertionSort, List.length_ofFn]
  have hn : n ≠ 0 := NeZero.ne n
  have hk_lt : k < n := by omega
  have hk_len : k < s.length := by omega
  set K : Fin s.length := ⟨k, hk_len⟩ with hK
  have hm_eq : s.get K = m := by simp [hs, hm, hK, median, hk]
  have hmono : Monotone s.get := by
    rw [hs]
    exact sorted_mono x
  rw [card_filter_eq_countP_sorted x (fun v => v < m)]
  have hbridge : (Finset.univ.filter
      fun i : Fin s.length => s.get i < m).card =
      s.countP fun v => decide (v < m) := by
    have h := card_filter_eq_countP_ofFn s.get (fun v => v < m)
    rw [List.ofFn_get] at h
    exact h
  rw [← hbridge]
  have hsub : Finset.univ.filter
      (fun i : Fin s.length => s.get i < m) ⊆ Finset.Iio K := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_Iio]
    by_contra hcon
    push Not at hcon
    have h1 : s.get K ≤ s.get i := hmono hcon
    rw [hm_eq] at h1
    linarith [hi.2]
  have hle := Finset.card_le_card hsub
  have hcard : (Finset.Iio K).card = k := by
    rw [Fin.card_Iio]
  omega

/-- Helper: at least `n-k` reports are at least the median. -/
private theorem median_card_ge {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    n - (n - 1) / 2 ≤
      (Finset.univ.filter fun i => median x ≤ x i).card := by
  classical
  set s := List.insertionSort (· ≤ ·) (List.ofFn x) with hs
  set k := (n - 1) / 2 with hk
  set m := median x with hm
  have hlen : s.length = n := by
    rw [hs, List.length_insertionSort, List.length_ofFn]
  have hn : n ≠ 0 := NeZero.ne n
  have hk_lt : k < n := by omega
  have hk_len : k < s.length := by omega
  set K : Fin s.length := ⟨k, hk_len⟩ with hK
  have hm_eq : s.get K = m := by simp [hs, hm, hK, median, hk]
  have hmono : Monotone s.get := by
    rw [hs]
    exact sorted_mono x
  rw [card_filter_eq_countP_sorted x (fun v => m ≤ v)]
  have hbridge : (Finset.univ.filter
      fun i : Fin s.length => m ≤ s.get i).card =
      s.countP fun v => decide (m ≤ v) := by
    have h := card_filter_eq_countP_ofFn s.get (fun v => m ≤ v)
    rw [List.ofFn_get] at h
    exact h
  rw [← hbridge]
  have hsub : Finset.Ici K ⊆
      Finset.univ.filter (fun i : Fin s.length => m ≤ s.get i) := by
    intro i hi
    rw [Finset.mem_Ici] at hi
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_univ i
    · calc m = s.get K := hm_eq.symm
        _ ≤ s.get i := hmono hi
  have hle := Finset.card_le_card hsub
  have hcard : (Finset.Ici K).card = s.length - k := by
    rw [Fin.card_Ici]
  omega

/-- Helper: at most `n-k-1` reports are above the median. -/
private theorem median_card_gt {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    (Finset.univ.filter fun i => median x < x i).card ≤
      n - (n - 1) / 2 - 1 := by
  classical
  set s := List.insertionSort (· ≤ ·) (List.ofFn x) with hs
  set k := (n - 1) / 2 with hk
  set m := median x with hm
  have hlen : s.length = n := by
    rw [hs, List.length_insertionSort, List.length_ofFn]
  have hn : n ≠ 0 := NeZero.ne n
  have hk_lt : k < n := by omega
  have hk_len : k < s.length := by omega
  set K : Fin s.length := ⟨k, hk_len⟩ with hK
  have hm_eq : s.get K = m := by simp [hs, hm, hK, median, hk]
  have hmono : Monotone s.get := by
    rw [hs]
    exact sorted_mono x
  rw [card_filter_eq_countP_sorted x (fun v => m < v)]
  have hbridge : (Finset.univ.filter
      fun i : Fin s.length => m < s.get i).card =
      s.countP fun v => decide (m < v) := by
    have h := card_filter_eq_countP_ofFn s.get (fun v => m < v)
    rw [List.ofFn_get] at h
    exact h
  rw [← hbridge]
  have hsub : Finset.univ.filter
      (fun i : Fin s.length => m < s.get i) ⊆ Finset.Ioi K := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_Ioi]
    by_contra hcon
    push Not at hcon
    have h1 : s.get i ≤ s.get K := hmono hcon
    rw [hm_eq] at h1
    linarith [hi.2]
  have hle := Finset.card_le_card hsub
  have hcard : (Finset.Ioi K).card = s.length - 1 - k := by
    rw [Fin.card_Ioi]
  omega

/-- (C2 median) The median minimizes social cost. -/
public theorem median_minimizes_socialCost {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) (y : ℝ) : socialCost x (median x) ≤ socialCost x y := by
  classical
  set m := median x with hm
  set k := (n - 1) / 2 with hk
  have hn : n ≠ 0 := NeZero.ne n
  have h2k : 2 * k ≤ n - 1 := by omega
  have hn2 : n ≤ 2 * k + 2 := by omega
  have hle0 := median_card_le x
  have hlt0 := median_card_lt x
  have hge0 := median_card_ge x
  have hgt0 := median_card_gt x
  rw [← hm] at hle0 hlt0 hge0 hgt0
  rw [← hk] at hle0 hlt0 hge0 hgt0
  have hdiff : socialCost x y - socialCost x m =
      ∑ i, (|y - x i| - |m - x i|) := by
    simp only [socialCost, ← Finset.sum_sub_distrib]
  suffices h : 0 ≤ ∑ i, (|y - x i| - |m - x i|) by
    have h2 : 0 ≤ socialCost x y - socialCost x m := by
      rw [hdiff]
      exact h
    exact sub_nonneg.mp h2
  rcases le_total m y with hmy | hym
  · set p : Fin n → Prop := fun i => x i ≤ m with hp
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ p
      (fun i => |y - x i| - |m - x i|)
    have heq : ∀ i ∈ Finset.univ.filter p,
        |y - x i| - |m - x i| = y - m := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have hxi : x i ≤ m := hi.2
      have h1 : |y - x i| = y - x i := abs_of_nonneg (by linarith)
      have h2 : |m - x i| = m - x i := abs_of_nonneg (by linarith)
      rw [h1, h2]
      ring
    have hlow : ∀ i, -(y - m) ≤ |y - x i| - |m - x i| := by
      intro i
      have htri : |m - x i| ≤ |m - y| + |y - x i| := by
        have h := abs_add_le (m - y) (y - x i)
        have heq2 : (m - y) + (y - x i) = m - x i := by ring
        rwa [heq2] at h
      have habs : |m - y| = y - m := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      linarith
    have hsum1 : ∑ i ∈ Finset.univ.filter p,
        (|y - x i| - |m - x i|) =
        (Finset.univ.filter p).card • (y - m) := by
      calc ∑ i ∈ Finset.univ.filter p, (|y - x i| - |m - x i|)
          = ∑ _ ∈ Finset.univ.filter p, (y - m) :=
            Finset.sum_congr rfl (fun i hi => heq i hi)
        _ = (Finset.univ.filter p).card • (y - m) :=
            Finset.sum_const _
    have hsum2 : (Finset.univ.filter fun i => ¬p i).card • (-(y - m)) ≤
        ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
          (|y - x i| - |m - x i|) := by
      calc (Finset.univ.filter fun i => ¬p i).card • (-(y - m))
          = ∑ _ ∈ Finset.univ.filter (fun i => ¬p i), (-(y - m)) :=
            (Finset.sum_const _).symm
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
            (|y - x i| - |m - x i|) :=
            Finset.sum_le_sum (fun i _ => hlow i)
    have htotal : (Finset.univ.filter p).card • (y - m) +
        (Finset.univ.filter fun i => ¬p i).card • (-(y - m)) ≤
        ∑ i, (|y - x i| - |m - x i|) := by
      calc (Finset.univ.filter p).card • (y - m) +
            (Finset.univ.filter fun i => ¬p i).card • (-(y - m))
          ≤ ∑ i ∈ Finset.univ.filter p, (|y - x i| - |m - x i|) +
            ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
              (|y - x i| - |m - x i|) := by
            rw [hsum1]
            exact add_le_add le_rfl hsum2
        _ = ∑ i, (|y - x i| - |m - x i|) := hsplit
    have hcard1 : k + 1 ≤ (Finset.univ.filter p).card := by
      simpa [hp] using hle0
    have hcard2 : (Finset.univ.filter fun i => ¬p i).card ≤
        n - k - 1 := by
      have heq2 : Finset.univ.filter (fun i => ¬p i) =
          Finset.univ.filter (fun i => m < x i) := by
        apply Finset.filter_congr
        intro i _
        simp [hp, not_le]
      rw [heq2]
      exact hgt0
    have hcard : (Finset.univ.filter fun i => ¬p i).card ≤
        (Finset.univ.filter p).card := by
      omega
    have hnonneg : 0 ≤ (Finset.univ.filter p).card • (y - m) +
        (Finset.univ.filter fun i => ¬p i).card • (-(y - m)) := by
      rw [nsmul_eq_mul, nsmul_eq_mul]
      have hle_nm : ((Finset.univ.filter fun i => ¬p i).card : ℝ) ≤
          (Finset.univ.filter p).card := Nat.cast_le.mpr hcard
      have hpos : (0 : ℝ) ≤ y - m := by linarith
      have heq3 : ((Finset.univ.filter p).card : ℝ) * (y - m) +
          ((Finset.univ.filter fun i => ¬p i).card : ℝ) * (-(y - m)) =
          (((Finset.univ.filter p).card : ℝ) -
            (Finset.univ.filter fun i => ¬p i).card) * (y - m) := by
        ring
      rw [heq3]
      apply mul_nonneg _ hpos
      linarith
    linarith
  · set p : Fin n → Prop := fun i => m ≤ x i with hp
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ p
      (fun i => |y - x i| - |m - x i|)
    have heq : ∀ i ∈ Finset.univ.filter p,
        |y - x i| - |m - x i| = m - y := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have hxi : m ≤ x i := hi.2
      have h1 : |y - x i| = x i - y := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      have h2 : |m - x i| = x i - m := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      rw [h1, h2]
      ring
    have hlow : ∀ i, -(m - y) ≤ |y - x i| - |m - x i| := by
      intro i
      have htri : |m - x i| ≤ |m - y| + |y - x i| := by
        have h := abs_add_le (m - y) (y - x i)
        have heq2 : (m - y) + (y - x i) = m - x i := by ring
        rwa [heq2] at h
      have habs : |m - y| = m - y :=
        abs_of_nonneg (by linarith)
      linarith
    have hsum1 : ∑ i ∈ Finset.univ.filter p,
        (|y - x i| - |m - x i|) =
        (Finset.univ.filter p).card • (m - y) := by
      calc ∑ i ∈ Finset.univ.filter p, (|y - x i| - |m - x i|)
          = ∑ _ ∈ Finset.univ.filter p, (m - y) :=
            Finset.sum_congr rfl (fun i hi => heq i hi)
        _ = (Finset.univ.filter p).card • (m - y) :=
            Finset.sum_const _
    have hsum2 : (Finset.univ.filter fun i => ¬p i).card • (-(m - y)) ≤
        ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
          (|y - x i| - |m - x i|) := by
      calc (Finset.univ.filter fun i => ¬p i).card • (-(m - y))
          = ∑ _ ∈ Finset.univ.filter (fun i => ¬p i), (-(m - y)) :=
            (Finset.sum_const _).symm
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
            (|y - x i| - |m - x i|) :=
            Finset.sum_le_sum (fun i _ => hlow i)
    have htotal : (Finset.univ.filter p).card • (m - y) +
        (Finset.univ.filter fun i => ¬p i).card • (-(m - y)) ≤
        ∑ i, (|y - x i| - |m - x i|) := by
      calc (Finset.univ.filter p).card • (m - y) +
            (Finset.univ.filter fun i => ¬p i).card • (-(m - y))
          ≤ ∑ i ∈ Finset.univ.filter p, (|y - x i| - |m - x i|) +
            ∑ i ∈ Finset.univ.filter (fun i => ¬p i),
              (|y - x i| - |m - x i|) := by
            rw [hsum1]
            exact add_le_add le_rfl hsum2
        _ = ∑ i, (|y - x i| - |m - x i|) := hsplit
    have hcard1 : n - k ≤ (Finset.univ.filter p).card := by
      simpa [hp] using hge0
    have hcard2 : (Finset.univ.filter fun i => ¬p i).card ≤ k := by
      have heq2 : Finset.univ.filter (fun i => ¬p i) =
          Finset.univ.filter (fun i => x i < m) := by
        apply Finset.filter_congr
        intro i _
        simp [hp, not_le]
      rw [heq2]
      exact hlt0
    have hcard : (Finset.univ.filter fun i => ¬p i).card ≤
        (Finset.univ.filter p).card := by
      omega
    have hnonneg : 0 ≤ (Finset.univ.filter p).card • (m - y) +
        (Finset.univ.filter fun i => ¬p i).card • (-(m - y)) := by
      rw [nsmul_eq_mul, nsmul_eq_mul]
      have hle_nm : ((Finset.univ.filter fun i => ¬p i).card : ℝ) ≤
          (Finset.univ.filter p).card := Nat.cast_le.mpr hcard
      have hpos : (0 : ℝ) ≤ m - y := by linarith
      have heq3 : ((Finset.univ.filter p).card : ℝ) * (m - y) +
          ((Finset.univ.filter fun i => ¬p i).card : ℝ) * (-(m - y)) =
          (((Finset.univ.filter p).card : ℝ) -
            (Finset.univ.filter fun i => ¬p i).card) * (m - y) := by
        ring
      rw [heq3]
      apply mul_nonneg _ hpos
      linarith
    linarith

/-- (C2 median) The median mechanism is group strategyproof. -/
public theorem median_isGroupStrategyproof {n : ℕ} [NeZero n] :
    IsGroupStrategyproof (median : Mechanism (Fin n)) := by
  classical
  intro x x' S hagree hcon
  obtain ⟨hne, hgains⟩ := hcon
  set m := median x with hm
  set m' := median x' with hm'
  set k := (n - 1) / 2 with hk
  have hn : n ≠ 0 := NeZero.ne n
  have hk_lt : k < n := by omega
  have hle'0 := median_card_le x'
  have hlt0 := median_card_lt x
  have hge'0 := median_card_ge x'
  have hgt0 := median_card_gt x
  rw [← hm'] at hle'0 hge'0
  rw [← hm] at hlt0 hgt0
  rw [← hk] at hle'0 hlt0 hge'0 hgt0
  rcases lt_trichotomy m' m with hlt | heq | hgt
  · have hall : ∀ i ∈ S, x i < m := by
      intro i hi
      by_contra hcon2
      push Not at hcon2
      have hxi : m ≤ x i := hcon2
      have hg := hgains i hi
      have h1 : |m' - x i| = x i - m' := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      have h2 : |m - x i| = x i - m := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (by linarith)
      linarith
    have hsub : Finset.univ.filter (fun i => x' i ≤ m') ⊆
        Finset.univ.filter (fun i => x i < m) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      constructor
      · exact Finset.mem_univ i
      · by_cases his : i ∈ S
        · exact hall i his
        · have heq2 : x' i = x i := hagree i his
          calc x i = x' i := heq2.symm
            _ ≤ m' := hi.2
            _ < m := hlt
    have hle := Finset.card_le_card hsub
    omega
  · obtain ⟨i, hi⟩ := hne
    have hg := hgains i hi
    rw [heq] at hg
    linarith
  · have hall : ∀ i ∈ S, m < x i := by
      intro i hi
      by_contra hcon2
      push Not at hcon2
      have hxi : x i ≤ m := hcon2
      have hg := hgains i hi
      have h1 : |m' - x i| = m' - x i :=
        abs_of_nonneg (by linarith)
      have h2 : |m - x i| = m - x i :=
        abs_of_nonneg (by linarith)
      linarith
    have hsub : Finset.univ.filter (fun i => m' ≤ x' i) ⊆
        Finset.univ.filter (fun i => m < x i) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      constructor
      · exact Finset.mem_univ i
      · by_cases his : i ∈ S
        · exact hall i his
        · have heq2 : x' i = x i := hagree i his
          calc m < m' := hgt
            _ ≤ x' i := hi.2
            _ = x i := heq2
    have hle := Finset.card_le_card hsub
    omega

/-- (C2 median) The median mechanism is strategyproof. -/
public theorem median_isStrategyproof {n : ℕ} [NeZero n] :
    IsStrategyproof (median : Mechanism (Fin n)) :=
  isStrategyproof_of_isGroupStrategyproof median_isGroupStrategyproof

/-- (C3 leftmost) The leftmost mechanism outputs the minimum report. -/
public noncomputable def leftmost {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty x

/-- (C3 leftmost) The leftmost output is at most every report. -/
public theorem leftmost_le {n : ℕ} [NeZero n] (x : Fin n → ℝ) (i : Fin n) :
    leftmost x ≤ x i :=
  Finset.inf'_le x (Finset.mem_univ i)

/-- (C3 leftmost) The leftmost output equals some report. -/
public theorem leftmost_exists {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    ∃ i, leftmost x = x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty x
  exact ⟨i, hi⟩

/-- (C3 leftmost) Approximation guarantee for maximum cost: the mechanism's
maximum cost is at most `c` times the optimum. -/
public def IsApproxMaxCost [Fintype ι] [Nonempty ι] (f : Mechanism ι)
    (c : ℝ) : Prop :=
  ∀ (x : ι → ℝ) (y : ℝ), maxCost x (f x) ≤ c * maxCost x y

/-- (C3 leftmost) The leftmost mechanism is strategyproof. -/
public theorem leftmost_isStrategyproof {n : ℕ} [NeZero n] :
    IsStrategyproof (leftmost : Mechanism (Fin n)) := by
  intro x i r
  by_cases h : x i = leftmost x
  · rw [← h, sub_self, abs_zero]
    exact abs_nonneg _
  · obtain ⟨j, hj⟩ := leftmost_exists x
    have hji : j ≠ i := by
      intro heq
      apply h
      rw [heq] at hj
      exact hj.symm
    have hle1 : leftmost (Function.update x i r) ≤ leftmost x := by
      calc leftmost (Function.update x i r)
          ≤ Function.update x i r j := leftmost_le _ j
        _ = x j := Function.update_of_ne hji r x
        _ = leftmost x := hj.symm
    have hle2 : leftmost x ≤ x i := leftmost_le x i
    have hle3 : leftmost (Function.update x i r) ≤ x i :=
      le_trans hle1 hle2
    rw [abs_sub_comm (leftmost x) (x i),
      abs_sub_comm (leftmost (Function.update x i r)) (x i),
      abs_of_nonneg (sub_nonneg.mpr hle2),
      abs_of_nonneg (sub_nonneg.mpr hle3)]
    exact sub_le_sub_left hle1 (x i)

/-- (C3 leftmost) The leftmost mechanism is 2-approximate for maximum cost. -/
public theorem leftmost_isApproxMaxCost_two {n : ℕ} [NeZero n] :
    IsApproxMaxCost (leftmost : Mechanism (Fin n)) 2 := by
  intro x y
  refine maxCost_le x (leftmost x) _ fun i => ?_
  obtain ⟨j, hj⟩ := leftmost_exists x
  rw [hj]
  calc |x j - x i| ≤ |x j - y| + |y - x i| := abs_sub_le _ _ _
    _ ≤ maxCost x y + maxCost x y := by
        apply add_le_add
        · rw [abs_sub_comm]
          exact le_maxCost x y j
        · exact le_maxCost x y i
    _ = 2 * maxCost x y := by ring

/-- Helper computing `maxCost` on `Fin 2` profiles. -/
private theorem maxCost_fin2 (a b y : ℝ) :
    maxCost ![a, b] y = max |y - a| |y - b| := by
  apply le_antisymm
  · refine maxCost_le _ _ _ fun i => ?_
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · rw [max_le_iff]
    constructor
    · calc |y - a| = |y - ![a, b] 0| := by
            rw [Matrix.cons_val_zero]
        _ ≤ maxCost ![a, b] y := le_maxCost _ _ 0
    · calc |y - b| = |y - ![a, b] 1| := by
            rw [Matrix.cons_val_one, Matrix.cons_val_zero]
        _ ≤ maxCost ![a, b] y := le_maxCost _ _ 1

/-- (C4 lower bound) No deterministic strategyproof mechanism beats ratio 2
for maximum cost, already with two agents. -/
public theorem two_le_of_isStrategyproof_isApproxMaxCost
    (f : Mechanism (Fin 2)) (hSP : IsStrategyproof f) (c : ℝ)
    (hc : IsApproxMaxCost f c) : 2 ≤ c := by
  by_contra hlt
  push Not at hlt
  set y0 : ℝ := f ![0, 1] with hy0
  have hhalf : maxCost ![0, 1] (1 / 2) = 1 / 2 := by
    rw [maxCost_fin2]
    norm_num
  have hc1 := hc ![0, 1] (1 / 2)
  rw [hhalf] at hc1
  have hmax_eq : maxCost ![0, 1] y0 = max |y0| |y0 - 1| := by
    rw [maxCost_fin2, sub_zero]
  rw [hmax_eq] at hc1
  have habs0 : |y0| ≤ c * (1 / 2) :=
    le_trans (le_max_left _ _) hc1
  have habs1 : |y0 - 1| ≤ c * (1 / 2) :=
    le_trans (le_max_right _ _) hc1
  have hlt0 : |y0| < 1 := by linarith
  have hlt1 : |y0 - 1| < 1 := by linarith
  rw [abs_lt] at hlt0 hlt1
  have hy0_lo : 0 < y0 := by linarith
  have hy0_hi : y0 < 1 := by linarith
  set x' : Fin 2 → ℝ := ![y0, 1] with hx'
  have hupd1 : x' = Function.update ![0, 1] 0 y0 := by
    funext i
    fin_cases i
    · simp [hx', Function.update_self]
    · simp [hx']
  have hupd2 : ![0, 1] = Function.update x' 0 0 := by
    funext i
    fin_cases i
    · simp [hx', Function.update_self]
    · simp [hx']
  have hx'_0 : x' 0 = y0 := by simp [hx']
  have hx'_1 : x' 1 = 1 := by simp [hx']
  have hsp := hSP x' 0 0
  rw [← hupd2] at hsp
  rw [hx'_0, hy0, sub_self, abs_zero] at hsp
  have hfx' : f x' = y0 := by
    have h0 : |f x' - y0| = 0 := le_antisymm hsp (abs_nonneg _)
    have h1 : f x' - y0 = 0 := abs_eq_zero.mp h0
    exact sub_eq_zero.mp h1
  have hc2 := hc x' ((1 + y0) / 2)
  rw [hfx'] at hc2
  have hlhs : 1 - y0 ≤ maxCost x' y0 := by
    have h1 : |y0 - 1| ≤ maxCost x' y0 := by
      calc |y0 - 1| = |y0 - x' 1| := by rw [hx'_1]
        _ ≤ maxCost x' y0 := le_maxCost _ _ 1
    have h2 : |y0 - 1| = 1 - y0 := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (by linarith)
    linarith
  have hrhs : maxCost x' ((1 + y0) / 2) = (1 - y0) / 2 := by
    rw [hx', maxCost_fin2]
    have e1 : |(1 + y0) / 2 - y0| = (1 - y0) / 2 := by
      have h : (1 + y0) / 2 - y0 = (1 - y0) / 2 := by ring
      rw [h]
      exact abs_of_nonneg (by linarith)
    have e2 : |(1 + y0) / 2 - 1| = (1 - y0) / 2 := by
      have h : (1 + y0) / 2 - 1 = -((1 - y0) / 2) := by ring
      rw [h, abs_neg]
      exact abs_of_nonneg (by linarith)
    rw [e1, e2, max_self]
  rw [hrhs] at hc2
  have hpos : 0 < 1 - y0 := by linarith
  have hlt2 : c * ((1 - y0) / 2) < 1 - y0 := by
    have h1 : c / 2 < 1 := by linarith
    have h2 := mul_lt_mul_of_pos_right h1 hpos
    have h3 : c * ((1 - y0) / 2) = c / 2 * (1 - y0) := by ring
    have h4 : (1 : ℝ) * (1 - y0) = 1 - y0 := one_mul _
    linarith
  linarith

end MathlibExt.GameTheory.FacilityLocation
