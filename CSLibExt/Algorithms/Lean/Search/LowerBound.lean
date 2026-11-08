/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Data.Array.Pairwise
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Log

import Lean.Elab.Tactic.Omega

/-!
# Binary lower-bound search

This module implements lower-bound search on a sorted array. It follows the contract in the C++
working draft N4950, sections `[alg.binary.search.general]` and `[lower.bound]`: the result is the
end of the initial segment whose values are below the key. For a sorted array, this is the first
index whose value is at least the key, or the array size if no such index exists.

The draft gives a logarithmic comparison bound. The explicit model here charges one `TimeM Nat`
tick for the element comparison in each iteration. Interval arithmetic, indexing, branches, and
recursive calls are free. Under that model, an array of length `n` uses at most
`Nat.clog 2 (n + 1)` comparisons. The exact-membership wrapper performs one additional equality
comparison when the lower-bound index is valid.

Source: ISO C++ working draft N4950, `[alg.binary.search.general]` and `[lower.bound]`, pinned at
`cplusplus/draft@4e4de1df8ee941255b653b61d0a62050b34cf8c9`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [LinearOrder α]

/--
Returns the first index containing a value at least `key`, charging one tick for each element
comparison. If every value is below `key`, it returns `xs.size`.

Precondition: `xs` must be sorted (or at least partitioned at `key`: every element below the
returned index is `< key` and every element from that index on is `≥ key`). On an unsorted array
the result is unspecified: for example, `lowerBound #[2, 1] 2` returns `2`, not the first
qualifying index `0`.
-/
def lowerBound (xs : Array α) (key : α) : TimeM Nat Nat :=
  let rec loop (lo hi : Nat) (hlohi : lo ≤ hi) (hhi : hi ≤ xs.size) : TimeM Nat Nat :=
    if h : lo < hi then
      let mid := lo + (hi - lo) / 2
      have hmidhi : mid < hi := by
        dsimp [mid]
        omega
      have hmid : mid < xs.size := hmidhi.trans_le hhi
      do
        ✓
        if xs[mid] < key then
          loop (mid + 1) hi (by omega) hhi
        else
          loop lo mid (by omega) (hmidhi.le.trans hhi)
    else
      pure lo
  termination_by hi - lo
  loop 0 xs.size (Nat.zero_le _) le_rfl

private theorem pairwise_getElem_le (xs : Array α)
    (hs : xs.Pairwise (fun x y => x ≤ y))
    (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) (hij : i ≤ j) :
    xs[i] ≤ xs[j] := by
  obtain rfl | hij := Nat.eq_or_lt_of_le hij
  · exact le_rfl
  · exact Array.pairwise_iff_getElem.mp hs i j hi hj hij

private theorem lowerBound_loop_spec (xs : Array α) (key : α)
    (hs : xs.Pairwise (fun x y => x ≤ y))
    (lo hi : Nat) (hlohi : lo ≤ hi) (hhi : hi ≤ xs.size)
    (hlow : ∀ j (_hj : j < lo) (_hjs : j < xs.size), xs[j] < key)
    (hhigh : ∀ j (_hj : hi ≤ j) (_hjs : j < xs.size), key ≤ xs[j]) :
    let result := lowerBound.loop xs key lo hi hlohi hhi
    lo ≤ result.ret ∧ result.ret ≤ hi ∧
      (∀ j (_hj : j < result.ret) (_hjs : j < xs.size), xs[j] < key) ∧
      (∀ j (_hj : result.ret ≤ j) (_hjs : j < xs.size), key ≤ xs[j]) := by
  induction hmeasure : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | h d ih =>
      rw [lowerBound.loop.eq_def]
      split
      next hlt =>
        simp only [TimeM.ret_bind]
        split
        next hcmp =>
          have hrec := ih (hi - (lo + (hi - lo) / 2 + 1)) (by omega)
            (lo + (hi - lo) / 2 + 1) hi (by omega) hhi
            (by
              intro j hj hjs
              by_cases hjlo : j < lo
              · exact hlow j hjlo hjs
              · exact (pairwise_getElem_le xs hs j (lo + (hi - lo) / 2) hjs (by omega)
                  (by omega)).trans_lt hcmp)
            hhigh rfl
          rcases hrec with ⟨hl, hu, hbelow, habove⟩
          exact ⟨by omega, hu, hbelow, habove⟩
        next hcmp =>
          have hrec := ih (lo + (hi - lo) / 2 - lo) (by omega)
            lo (lo + (hi - lo) / 2) (by omega) (by omega) hlow
            (by
              intro j hj hjs
              exact (le_of_not_gt hcmp).trans
                (pairwise_getElem_le xs hs (lo + (hi - lo) / 2) j (by omega) hjs hj))
            rfl
          rcases hrec with ⟨hl, hu, hbelow, habove⟩
          exact ⟨hl, by omega, hbelow, habove⟩
      next hlt =>
        simp only [TimeM.ret_pure]
        constructor
        · omega
        constructor
        · omega
        exact ⟨hlow, fun j hj hjs => hhigh j (by omega) hjs⟩

/--
On a sorted array, the returned index separates values below `key` from values at least `key`.
-/
theorem lowerBound_spec (xs : Array α) (key : α)
    (hs : xs.Pairwise (fun x y => x ≤ y)) :
    (lowerBound xs key).ret ≤ xs.size ∧
      (∀ j (_hj : j < (lowerBound xs key).ret) (_hjs : j < xs.size), xs[j] < key) ∧
      (∀ j (_hj : (lowerBound xs key).ret ≤ j) (_hjs : j < xs.size), key ≤ xs[j]) := by
  simpa only [lowerBound] using
    (lowerBound_loop_spec xs key hs 0 xs.size (Nat.zero_le _) le_rfl
      (by omega) (by omega)).2

private theorem clog_two_half (n : Nat) (hn : 0 < n) :
    Nat.clog 2 (n / 2 + 1) + 1 = Nat.clog 2 (n + 1) := by
  conv_rhs =>
    rw [Nat.clog_of_one_lt (b := 2) (n := n + 1) (by omega) (by omega)]
  congr 2
  omega

private theorem lowerBound_loop_time_le (xs : Array α) (key : α) (lo hi : Nat)
    (hlohi : lo ≤ hi) (hhi : hi ≤ xs.size) :
    (lowerBound.loop xs key lo hi hlohi hhi).time ≤ Nat.clog 2 (hi - lo + 1) := by
  induction hmeasure : hi - lo using Nat.strong_induction_on generalizing lo hi with
  | h d ih =>
      rw [lowerBound.loop.eq_def]
      split
      next hlt =>
        simp only [TimeM.time_bind, TimeM.time_tick]
        split
        next hcmp =>
          have hrec := ih (hi - (lo + (hi - lo) / 2 + 1)) (by omega)
            (lo + (hi - lo) / 2 + 1) hi (by omega) hhi rfl
          calc
            1 + (lowerBound.loop xs key (lo + (hi - lo) / 2 + 1) hi _ hhi).time ≤
                1 + Nat.clog 2 (hi - (lo + (hi - lo) / 2 + 1) + 1) :=
              Nat.add_le_add_left hrec 1
            _ ≤ 1 + Nat.clog 2 ((hi - lo) / 2 + 1) :=
              Nat.add_le_add_left (Nat.clog_mono_right 2 (by omega)) 1
            _ = Nat.clog 2 (d + 1) := by
              rw [← hmeasure, Nat.add_comm 1, clog_two_half (hi - lo) (by omega)]
        next hcmp =>
          have hrec := ih (lo + (hi - lo) / 2 - lo) (by omega)
            lo (lo + (hi - lo) / 2) (by omega) (by omega) rfl
          calc
            1 + (lowerBound.loop xs key lo (lo + (hi - lo) / 2) _ _).time ≤
                1 + Nat.clog 2 (lo + (hi - lo) / 2 - lo + 1) :=
              Nat.add_le_add_left hrec 1
            _ = 1 + Nat.clog 2 ((hi - lo) / 2 + 1) := by
              congr 3
              omega
            _ = Nat.clog 2 (d + 1) := by
              rw [← hmeasure, Nat.add_comm 1, clog_two_half (hi - lo) (by omega)]
      next hlt =>
        simp only [TimeM.time_pure]
        exact Nat.zero_le _

/-- Lower-bound search uses at most `clog₂(n + 1)` element comparisons. -/
theorem lowerBound_time_le (xs : Array α) (key : α) :
    (lowerBound xs key).time ≤ Nat.clog 2 (xs.size + 1) := by
  simpa only [lowerBound, Nat.sub_zero] using
    lowerBound_loop_time_le xs key 0 xs.size (Nat.zero_le _) le_rfl

/--
Returns the first index containing `key`, or `none` when `key` is absent. A valid lower-bound index
costs one additional equality comparison.

Precondition: as for `lowerBound`, `xs` must be sorted (or partitioned at `key`); on an unsorted
array a present key can be missed and the result can be `none`.
-/
def binarySearchFirst? (xs : Array α) (key : α) : TimeM Nat (Option Nat) := do
  let i ← lowerBound xs key
  if h : i < xs.size then
    ✓
    if xs[i] = key then
      return some i
    else
      return none
  else
    return none

private theorem lowerBound_eq_of_first (xs : Array α) (key : α)
    (hs : xs.Pairwise (fun x y => x ≤ y)) (i : Nat) (hi : i < xs.size)
    (hkey : xs[i] = key)
    (hfirst : ∀ j (_hj : j < i) (_hjs : j < xs.size), xs[j] < key) :
    (lowerBound xs key).ret = i := by
  have hspec := lowerBound_spec xs key hs
  apply Nat.le_antisymm
  · by_contra hle
    have hir : i < (lowerBound xs key).ret := Nat.lt_of_not_ge hle
    have hlt := hspec.2.1 i hir hi
    rw [hkey] at hlt
    exact lt_irrefl key hlt
  · apply Nat.le_of_not_gt
    intro hri
    have hrsize : (lowerBound xs key).ret < xs.size := hri.trans hi
    exact (not_lt_of_ge (hspec.2.2 _ le_rfl hrsize)) (hfirst _ hri hrsize)

/-- The membership wrapper returns exactly the first occurrence of `key`. -/
theorem binarySearchFirst?_eq_some_iff (xs : Array α) (key : α)
    (hs : xs.Pairwise (fun x y => x ≤ y)) (i : Nat) :
    (binarySearchFirst? xs key).ret = some i ↔
      ∃ hi : i < xs.size,
        xs[i] = key ∧
          ∀ j (_hj : j < i) (_hjs : j < xs.size), xs[j] < key := by
  constructor
  · intro h
    simp only [binarySearchFirst?, TimeM.ret_bind] at h
    split at h
    next hr =>
      split at h
      next hkey =>
        have hir : (lowerBound xs key).ret = i := by simpa using h
        subst i
        exact ⟨hr, hkey, (lowerBound_spec xs key hs).2.1⟩
      next hkey => simp at h
    next hr => simp at h
  · rintro ⟨hi, hkey, hfirst⟩
    have hr := lowerBound_eq_of_first xs key hs i hi hkey hfirst
    simp [binarySearchFirst?, hr, hi, hkey]

/-- The membership wrapper returns `none` exactly when `key` is absent. -/
theorem binarySearchFirst?_eq_none_iff (xs : Array α) (key : α)
    (hs : xs.Pairwise (fun x y => x ≤ y)) :
    (binarySearchFirst? xs key).ret = none ↔
      ∀ i (hi : i < xs.size), xs[i] ≠ key := by
  constructor
  · intro hnone i hi hkey
    have hspec := lowerBound_spec xs key hs
    have hri : (lowerBound xs key).ret ≤ i := by
      apply Nat.le_of_not_gt
      intro hir
      have hlt := hspec.2.1 i hir hi
      rw [hkey] at hlt
      exact lt_irrefl key hlt
    have hrsize : (lowerBound xs key).ret < xs.size := hri.trans_lt hi
    have hrkey : xs[(lowerBound xs key).ret] = key := by
      apply le_antisymm
      · exact (pairwise_getElem_le xs hs _ i hrsize hi hri).trans_eq hkey
      · exact hspec.2.2 _ le_rfl hrsize
    have hsome : (binarySearchFirst? xs key).ret = some (lowerBound xs key).ret := by
      simp [binarySearchFirst?, hrsize, hrkey]
    simp [hnone] at hsome
  · intro habsent
    cases hresult : (binarySearchFirst? xs key).ret with
    | none => rfl
    | some i =>
        obtain ⟨hi, hkey, -⟩ := (binarySearchFirst?_eq_some_iff xs key hs i).mp hresult
        exact (habsent i hi hkey).elim

/-- The wrapper adds one comparison exactly when the lower-bound index is valid. -/
theorem binarySearchFirst?_time (xs : Array α) (key : α) :
    (binarySearchFirst? xs key).time =
      (lowerBound xs key).time + if (lowerBound xs key).ret < xs.size then 1 else 0 := by
  simp only [binarySearchFirst?, TimeM.time_bind]
  split
  · simp only [TimeM.time_bind, TimeM.time_tick]
    split <;> rfl
  · rfl

/-- The membership wrapper uses at most one comparison beyond lower-bound search. -/
theorem binarySearchFirst?_time_le (xs : Array α) (key : α) :
    (binarySearchFirst? xs key).time ≤ Nat.clog 2 (xs.size + 1) + 1 := by
  rw [binarySearchFirst?_time]
  exact Nat.add_le_add (lowerBound_time_le xs key) (by split <;> simp)

end Cslib.Algorithms.Lean.TimeM
