/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ProgramVerification/PermuteToUnimodal.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `permute_to_unimodal`, revision 1.
Copyright 2026 Lean FRO, LLC.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Julia M. Himmel (submitter)

The algorithm, the definitions of unimodality and Hamming distance, and the correctness
statement are adapted from the benchmark. ATLAS supplies the proof. lean-eval ships no
`NOTICE` file.
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Order.Prod.Lex.Basic
import Batteries.Data.List.Perm
import Mathlib.Data.List.Sort

/-!
# Optimal unimodal rearrangement

`minRearrange_correct` proves that `minRearrange` computes the minimum Hamming distance
from a permutation to a unimodal permutation. Placing successive values at either end
traces a lattice path. The original positions it preserves form a chain of edge midpoints,
whose maximum length the algorithm computes by patience sorting.
-/

@[expose] public section

namespace MathlibExt.TheoryOfComputation.PermuteToUnimodalWanted
namespace ProgramVerification

/--
**Unimodal rearrangement algorithm.**
Given an array `arr` which is a permutation of the numbers from `1` to `arr.size`,
`minRearrange` computes the size of the smallest subset of indices within the array
that may be permuted such that the array becomes first increasing and then decreasing.
For example, `minRearrange #[1, 6, 4, 3, 2, 5] = 2` since we can swap the first and
the last element to achieve the desired property.

A candidate for a preserved position is the midpoint of an edge that places the original
value there. After sorting these points lexicographically, the algorithm subtracts the length
of a longest nondecreasing subsequence of their second coordinates from the array length.
The implementation runs in `O(n log n)`.

* `minRearrange #[] = 0`
* `minRearrange #[1, 6, 4, 3, 2, 5] = 2`
* `minRearrange #[4, 3, 2, 1, 5] = 4`
* `minRearrange #[1, 2, 4, 3] = 0`
* `minRearrange #[1, 2, 7, 4, 5, 6, 3, 8, 9, 10] = 2`
-/
def minRearrange (arr : Array Nat) : Nat :=
  let n := arr.size
  let v :=
    (arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map
      (fun (a, i) => (2 * i + 1, 2 * (a - i - 1))) ++
    (arr.zipIdx.filter (fun (a, i) => n ≤ a + i)).map
      (fun (a, i) => (2 * (a + i - n), 2 * (n - i) - 1))
  let vv :=
    (v.toList.mergeSort (le := fun a b => a = b ∨ Prod.Lex (· < ·) (· < ·) a b)).toArray
  n - lis (vv.map (·.2))
where
  lis (arr : Array Nat) : Nat :=
    if h : arr = #[] then
      0
    else
      let dp := Array.replicate arr.size (arr.max h + 1)
      loop arr 0 0 dp (by grind)
  loop (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) : Nat :=
    if hi' : i = arr.size then
      ans
    else
      let pos := upperBound arr[i] dp
      loop arr (max ans (pos + 1)) (i + 1) (dp.set! pos (arr[i])) (by grind)
  upperBound (needle : Nat) (arr : Array Nat) : Nat :=
    go needle arr 0 arr.size
  go (needle : Nat) (arr : Array Nat) (lo hi : Nat) (hhi : hi ≤ arr.size := by omega) : Nat :=
    if h : lo < hi then
      let mid := lo + (hi - lo) / 2
      if arr[mid] ≤ needle then
        go needle arr (mid + 1) hi
      else
        go needle arr lo mid
    else lo

/--
**Unimodal arrays.** An array $a$ of natural numbers is unimodal if it is the concatenation of a
strictly increasing array $b$ followed by a strictly decreasing array $b'$, where either part may
be empty.
-/
def Unimodal (arr : Array Nat) : Prop :=
  ∃ b b', arr = b ++ b' ∧ b.toList.Pairwise (· < ·) ∧ b'.toList.Pairwise (· > ·)

/--
**Number of differing positions.** For two vectors $a, b \in \mathbb{N}^n$, this is the number of
indices $i < n$ with $a_i \neq b_i$, that is, the Hamming distance between $a$ and $b$.
-/
def differences {n : Nat} (a b : Vector Nat n) : Nat :=
  (List.finRange n).filter (fun i => a[i] ≠ b[i]) |>.length

namespace minRearrange_correct

open scoped List

/-! ### The upper-bound search and the nondecreasing subsequence computation -/

/-- Some length-`k` nondecreasing subsequence of the prefix `p` has all entries at most `c`. -/
private def Fits (p : List Nat) (k c : Nat) : Prop :=
  ∃ s, s <+ p ∧ s.Pairwise (· ≤ ·) ∧ s.length = k ∧ ∀ y ∈ s, y ≤ c

private theorem fits_zero (p : List Nat) (c : Nat) : Fits p 0 c :=
  ⟨[], List.nil_sublist _, .nil, rfl, by simp⟩

private theorem Fits.shorten {p : List Nat} {k j c : Nat} (h : Fits p k c) (hj : j ≤ k) :
    Fits p j c := by
  obtain ⟨s, hs, hp, hl, hb⟩ := h
  have ht := List.take_sublist j s
  exact ⟨s.take j, ht.trans hs, hp.sublist ht, by simp [hl, hj], fun y hy => hb y (ht.subset hy)⟩

private theorem fits_snoc {p : List Nat} {j c x : Nat} :
    Fits (p ++ [x]) (j + 1) c ↔ Fits p (j + 1) c ∨ x ≤ c ∧ Fits p j x := by
  constructor
  · rintro ⟨s, hs, hp, hl, hb⟩
    obtain ⟨a, b, rfl, ha, hb'⟩ := List.sublist_append_iff.mp hs
    rcases List.sublist_singleton.mp hb' with rfl | rfl
    · left
      exact ⟨a, ha, by simpa using hp, by simpa using hl, by simpa using hb⟩
    · exact Or.inr ⟨hb x (by simp), a, ha, (List.pairwise_append.mp hp).1,
        by simpa using hl, fun y hy => (List.pairwise_append.mp hp).2.2 y hy x (by simp)⟩
  · rintro (⟨s, hs, hp, hl, hb⟩ | ⟨hx, s, hs, hp, hl, hb⟩)
    · exact ⟨s, hs.trans (List.sublist_append_left ..), hp, hl, hb⟩
    · refine ⟨s ++ [x], hs.append (.refl _), List.pairwise_append.mpr ?_, by simp [hl], ?_⟩
      · exact ⟨hp, by simp, by simpa using hb⟩
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact (hb y hy).trans hx
        · simpa [List.mem_singleton.mp hy] using hx

private theorem go_cut (a : Array Nat) (x lo hi : Nat) (hh : hi ≤ a.size) (hl : lo ≤ hi)
    (mono : ∀ i j : Nat, i ≤ j → j < a.size → a[j]! ≤ x → a[i]! ≤ x)
    (left : ∀ j < lo, a[j]! ≤ x)
    (right : ∀ j, hi ≤ j → j < a.size → x < a[j]!) :
    let pos := minRearrange.go x a lo hi hh
    pos ≤ a.size ∧ (∀ j < pos, a[j]! ≤ x) ∧ (∀ j, pos ≤ j → j < a.size → x < a[j]!) := by
  rw [minRearrange.go]
  split
  · rename_i h
    dsimp only
    split
    · rename_i hle
      apply go_cut a x _ _ hh (by omega) mono _ right
      intro j hj
      apply mono j (lo + (hi - lo) / 2) (by omega) (by omega)
      simpa [getElem!_pos, show lo + (hi - lo) / 2 < a.size by omega] using hle
    · rename_i hgt
      apply go_cut a x _ _ (by omega) (by omega) mono left
      intro j hj hja
      by_contra! hle
      exact hgt (by simpa [getElem!_pos, show lo + (hi - lo) / 2 < a.size by omega] using
        (mono _ j hj hja hle))
  · have : lo = hi := by omega
    subst lo
    exact ⟨hh, left, right⟩
termination_by hi - lo
decreasing_by all_goals omega

private theorem fits_le {p : List Nat} {k c : Nat} (h : Fits p k c) : k ≤ p.length := by
  obtain ⟨s, hs, _, rfl, _⟩ := h
  exact hs.length_le

private def Best (p : List Nat) (k : Nat) : Prop :=
  (∃ s, s <+ p ∧ s.Pairwise (· ≤ ·) ∧ s.length = k) ∧
    ∀ s, s <+ p → s.Pairwise (· ≤ ·) → s.length ≤ k

/-- The threshold `c` admits a subsequence of length `j + 1` exactly when `dp[j] ≤ c`.
At the largest input value `M` this also characterizes the active entries `j < ans`. -/
private theorem loop_best (a dp : Array Nat) (ans i M : Nat) (hi : i ≤ a.size)
    (hm : ∀ y ∈ a, y ≤ M) (hd : dp.size = a.size) (ha : ans ≤ i)
    (inv : ∀ j < a.size, ∀ c ≤ M, Fits (a.toList.take i) (j + 1) c ↔ dp[j]! ≤ c)
    (active : ∀ j < a.size, j < ans ↔ dp[j]! ≤ M) :
    Best a.toList (minRearrange.loop a ans i dp hi) := by
  rw [minRearrange.loop]
  split
  · subst i
    simp only [List.take_of_length_le, Array.length_toList, le_refl] at inv
    constructor
    · cases ans with
      | zero => exact ⟨[], List.nil_sublist _, .nil, rfl⟩
      | succ k =>
        obtain ⟨s, hs, hp, hl, _⟩ := (inv k (by omega) M le_rfl).mpr
          ((active k (by omega)).mp (by omega))
        exact ⟨s, hs, hp, hl⟩
    · intro s hs hp
      cases hlen : s.length with
      | zero => omega
      | succ j =>
        have hj := hs.length_le
        simp only [Array.length_toList] at hj
        have hf : Fits a.toList (j + 1) M :=
          ⟨s, hs, hp, hlen, fun y hy => hm y (by simpa using hs.subset hy)⟩
        have := (active j (by omega)).mpr ((inv j (by omega) M le_rfl).mp hf)
        omega
  · rename_i hne
    have hi' : i < a.size := by omega
    let x := a[i]
    let pos := minRearrange.upperBound x dp
    have hx : x ≤ M := hm x (Array.getElem_mem hi')
    have mono (j k : Nat) (hle : j ≤ k) (hk : k < dp.size) (hb : dp[k]! ≤ x) :
        dp[j]! ≤ x :=
      (inv j (by omega) x hx).mp (((inv k (by omega) x hx).mpr hb).shorten (by omega))
    obtain ⟨_, left, right⟩ := go_cut dp x 0 dp.size le_rfl (by omega) mono
      (by simp) (by omega)
    change ∀ j < pos, _ at left
    change ∀ j, pos ≤ j → _ at right
    have hpos : pos ≤ i := by
      by_contra! hh
      have h := fits_le ((inv i hi' x hx).mpr (left i hh))
      simp only [List.length_take, Array.length_toList] at h
      omega
    have hp : pos < dp.size := by omega
    have htake : a.toList.take (i + 1) = a.toList.take i ++ [x] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hi')]
      rfl
    have hset (j : Nat) (hj : j < a.size) :
        (dp.set! pos x)[j]! = if pos = j then x else dp[j]! := by
      simp [Array.set!, Array.setIfInBounds, hp, getElem!_pos, show j < dp.size by omega,
        Array.getElem_set]
    apply loop_best a (dp.set! pos x) (max ans (pos + 1)) (i + 1) M _ hm
    · simpa using hd
    · omega
    · intro j hj c hc
      rw [htake, fits_snoc, inv j hj c hc, hset j hj]
      have prev : Fits (a.toList.take i) j x ↔ j ≤ pos := by
        cases j with
        | zero => simp [fits_zero]
        | succ k =>
          rw [inv k (by omega) x hx]
          constructor
          · intro hk
            by_contra! hh
            have := right k (by omega) (by omega)
            omega
          · intro hk
            exact left k (by omega)
      rw [prev]
      split <;> rename_i heq
      · subst j
        have := right pos le_rfl hp
        omega
      · by_cases hh : j < pos
        · have := left j hh
          omega
        · omega
    · intro j hj
      rw [hset j hj]
      split <;> rename_i heq
      · subst j
        omega
      · have := active j hj
        by_cases hh : j < pos
        · have := left j hh
          omega
        · omega
termination_by a.size - i

private theorem lis_best (a : Array Nat) : Best a.toList (minRearrange.lis a) := by
  rw [minRearrange.lis]
  split
  · subst a
    exact ⟨⟨[], .refl _, .nil, rfl⟩, fun _ hs _ => hs.length_le⟩
  · rename_i h
    apply loop_best a _ _ _ (a.max h)
    · exact fun y hy => Array.le_max_of_mem hy
    · simp
    · omega
    · intro j hj c hc
      simp [getElem!_pos, hj, Fits]
      omega
    · intro j hj
      simp [getElem!_pos, hj]

/-! ### Chains of preserved positions

After filling `l` positions on the left and `r` on the right, the next value is `l + r + 1`.
A left placement moves from `(2*l, 2*r)` two units to the right. A right placement moves
two units up. An edge is eligible when its midpoint represents a position that keeps its value.
-/

private abbrev Point := Nat × Nat

private def Eligible (f : Nat → Nat) (n : Nat) (p : Point) : Prop :=
  ∃ u v, u + v < n ∧
    (p = (2 * u + 1, 2 * v) ∧ f u = u + v + 1 ∨ p = (2 * u, 2 * v + 1) ∧ f (n - v - 1) = u + v + 1)

private def Follows (p q : Point) : Prop := p.1 ≤ q.1 ∧ p.2 ≤ q.2 ∧ p ≠ q

private def hits (f : Nat → Nat) (n l r : Nat) : List Bool → List Point
  | [] => []
  | true :: s =>
    let tail := hits f n (l + 1) r s
    if f l = l + r + 1 then (2 * l + 1, 2 * r) :: tail else tail
  | false :: s =>
    let tail := hits f n l (r + 1) s
    if f (n - r - 1) = l + r + 1 then (2 * l, 2 * r + 1) :: tail else tail

private theorem hits_left (f : Nat → Nat) (n l r : Nat) (s : List Bool) :
    (hits f n l r (true :: s)).length =
      (hits f n (l + 1) r s).length + if f l = l + r + 1 then 1 else 0 := by
  simp only [hits]
  split <;> simp

private theorem hits_right (f : Nat → Nat) (n l r : Nat) (s : List Bool) :
    (hits f n l r (false :: s)).length =
      (hits f n l (r + 1) s).length + if f (n - r - 1) = l + r + 1 then 1 else 0 := by
  simp only [hits]
  split <;> simp

private theorem hits_chain (f : Nat → Nat) (n l r : Nat) (s : List Bool)
    (hlen : l + r + s.length = n) :
    (hits f n l r s).Pairwise Follows ∧
    ∀ p ∈ hits f n l r s, Eligible f n p ∧ 2 * l ≤ p.1 ∧ 2 * r ≤ p.2 := by
  induction s generalizing l r with
  | nil => simp [hits]
  | cons side s ih =>
    simp only [List.length_cons] at hlen
    cases side
    · obtain ⟨hp, hb⟩ := ih l (r + 1) (by omega)
      simp only [hits]
      split
      · rename_i heq
        refine ⟨List.pairwise_cons.mpr ⟨?_, hp⟩, ?_⟩
        · intro q hq
          obtain ⟨_, h₁, h₂⟩ := hb q hq
          exact ⟨h₁, by omega, fun e => by rw [← e] at h₂; dsimp at h₂; omega⟩
        · intro p h
          rcases List.mem_cons.mp h with rfl | ht
          · exact ⟨⟨l, r, by omega, Or.inr ⟨rfl, heq⟩⟩, by simp⟩
          · obtain ⟨he, h₁, h₂⟩ := hb p ht
            exact ⟨he, h₁, by omega⟩
      · exact ⟨hp, fun p h => ⟨(hb p h).1, (hb p h).2.1, by have := (hb p h).2.2; omega⟩⟩
    · obtain ⟨hp, hb⟩ := ih (l + 1) r (by omega)
      simp only [hits]
      split
      · rename_i heq
        refine ⟨List.pairwise_cons.mpr ⟨?_, hp⟩, ?_⟩
        · intro q hq
          obtain ⟨_, h₁, h₂⟩ := hb q hq
          exact ⟨by omega, h₂, fun e => by rw [← e] at h₁; dsimp at h₁; omega⟩
        · intro p h
          rcases List.mem_cons.mp h with rfl | ht
          · exact ⟨⟨l, r, by omega, Or.inl ⟨rfl, heq⟩⟩, by simp⟩
          · obtain ⟨he, h₁, h₂⟩ := hb p ht
            exact ⟨he, by omega, h₂⟩
      · exact ⟨hp, fun p h => ⟨(hb p h).1, by have := (hb p h).2.1; omega, (hb p h).2.2⟩⟩

-- At a matched left edge the input value at this left index fixes the other coordinate.
-- Hence no later, distinct eligible edge can have the same odd first coordinate.
private theorem pass_left {f : Nat → Nat} {n l r : Nat} {q : Point}
    (hit : f l = l + r + 1) (hq : Eligible f n q) (hf : Follows (2 * l + 1, 2 * r) q) :
    2 * (l + 1) ≤ q.1 ∧ 2 * r ≤ q.2 := by
  obtain ⟨u, v, _, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ := hq <;>
    simp [Follows, Prod.ext_iff] at hf ⊢
  all_goals by_cases e : l = u <;> simp_all
  all_goals omega

private theorem pass_right {f : Nat → Nat} {n l r : Nat} {q : Point}
    (hit : f (n - r - 1) = l + r + 1) (hq : Eligible f n q)
    (hf : Follows (2 * l, 2 * r + 1) q) :
    2 * l ≤ q.1 ∧ 2 * (r + 1) ≤ q.2 := by
  obtain ⟨u, v, _, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ := hq <;>
    simp [Follows, Prod.ext_iff] at hf ⊢
  all_goals by_cases e : r = v <;> simp_all
  all_goals omega

/-- Walk toward the first requested midpoint, cross its edge, then cover the remaining chain. -/
private theorem cover_chain (f : Nat → Nat) (n m l r : Nat) (hn : l + r + m = n)
    (pts : List Point) (hc : pts.Pairwise Follows) (he : ∀ p ∈ pts, Eligible f n p)
    (hb : ∀ p ∈ pts, 2 * l ≤ p.1 ∧ 2 * r ≤ p.2) :
    ∃ s : List Bool, s.length = m ∧ pts.length ≤ (hits f n l r s).length := by
  cases pts with
  | nil => exact ⟨List.replicate m true, by simp, Nat.zero_le _⟩
  | cons p ps =>
    have hp := he p (.head _)
    have hbp := hb p (.head _)
    obtain ⟨u, v, hu, huv⟩ := hp
    have hf := (List.pairwise_cons.mp hc).1
    have htail := (List.pairwise_cons.mp hc).2
    have het (q) (hq : q ∈ ps) := he q (List.mem_cons_of_mem _ hq)
    have hm : 0 < m := by
      rcases huv with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp at hbp <;> omega
    by_cases hl : 2 * (l + 1) ≤ p.1
    · obtain ⟨s, hs, hlen⟩ := cover_chain f n (m - 1) (l + 1) r (by omega) (p :: ps) hc he (by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | ht
        · exact ⟨hl, hbp.2⟩
        · exact ⟨hl.trans (hf q ht).1, (hb q (.tail _ ht)).2⟩)
      exact ⟨true :: s, by simp; omega, by rw [hits_left]; omega⟩
    by_cases hr : 2 * (r + 1) ≤ p.2
    · obtain ⟨s, hs, hlen⟩ := cover_chain f n (m - 1) l (r + 1) (by omega) (p :: ps) hc he (by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | ht
        · exact ⟨hbp.1, hr⟩
        · exact ⟨(hb q (.tail _ ht)).1, hr.trans (hf q ht).2.1⟩)
      exact ⟨false :: s, by simp; omega, by rw [hits_right]; omega⟩
    rcases huv with ⟨rfl, hit⟩ | ⟨rfl, hit⟩ <;> simp only at hl hr hbp
    · have eu : u = l := by omega
      subst u
      have ev : v = r := by omega
      subst v
      obtain ⟨s, hs, hlen⟩ := cover_chain f n (m - 1) (l + 1) r (by omega) ps htail het
        (fun q hq => pass_left hit (het q hq) (hf q hq))
      exact ⟨true :: s, by simp; omega, by simp [hits_left, hit]; omega⟩
    · have eu : u = l := by omega
      subst u
      have ev : v = r := by omega
      subst v
      obtain ⟨s, hs, hlen⟩ := cover_chain f n (m - 1) l (r + 1) (by omega) ps htail het
        (fun q hq => pass_right hit (het q hq) (hf q hq))
      exact ⟨false :: s, by simp; omega, by simp [hits_right, hit]; omega⟩
termination_by m

/-! ### Encoding unimodal permutations by choices of ends -/

private def row (k : Nat) : List Bool → List Nat
  | [] => []
  | true :: s => k :: row (k + 1) s
  | false :: s => row (k + 1) s ++ [k]

private theorem row_perm (k : Nat) (s : List Bool) :
    (row k s).Perm (List.range' k s.length) := by
  induction s generalizing k with
  | nil => rfl
  | cons side s ih =>
    cases side <;> simp only [row, List.length_cons, List.range'_succ]
    · exact (List.perm_append_singleton ..).trans ((ih _).cons k)
    · exact (ih _).cons k

private theorem row_length (k : Nat) (s : List Bool) : (row k s).length = s.length := by
  simpa using (row_perm k s).length_eq

private def Peak (xs : List Nat) : Prop :=
  ∃ b d : List Nat, xs = b ++ d.reverse ∧ b.Pairwise (· < ·) ∧ d.Pairwise (· < ·)

private theorem peak_iff (a : Array Nat) : Peak a.toList ↔ Unimodal a := by
  constructor
  · rintro ⟨b, d, h, hb, hd⟩
    exact ⟨b.toArray, d.reverse.toArray, by simpa using congrArg List.toArray h,
      by simpa using hb, by simpa [List.pairwise_reverse] using hd⟩
  · rintro ⟨b, d, rfl, hb, hd⟩
    exact ⟨b.toList, d.toList.reverse, by simp, hb, by simpa [List.pairwise_reverse] using hd⟩

private theorem row_peak (k : Nat) (s : List Bool) : Peak (row k s) := by
  induction s generalizing k with
  | nil => exact ⟨[], [], rfl, .nil, .nil⟩
  | cons side s ih =>
    obtain ⟨b, d, h, hb, hd⟩ := ih (k + 1)
    have hlt (y) (hy : y ∈ b ++ d.reverse) : k < y := by
      rw [← h] at hy
      have := (row_perm (k + 1) s).mem_iff.mp hy
      simp at this
      omega
    cases side
    · refine ⟨b, k :: d, by simp [row, h], hb, List.pairwise_cons.mpr ⟨?_, hd⟩⟩
      exact fun y hy => hlt y (by simp [hy])
    · refine ⟨k :: b, d, by simp [row, h], List.pairwise_cons.mpr ⟨?_, hb⟩, hd⟩
      exact fun y hy => hlt y (by simp [hy])

private theorem head_of_least {k : Nat} {b : List Nat}
    (hb : b.Pairwise (· < ·)) (hm : k ∈ b) (hl : ∀ y ∈ b, k ≤ y) :
    ∃ t, b = k :: t := by
  cases b with
  | nil => simp at hm
  | cons a b =>
    rcases List.mem_cons.mp hm with rfl | ht
    · exact ⟨_, rfl⟩
    · have := (List.pairwise_cons.mp hb).1 k ht
      have := hl a (.head _)
      omega

/-- The least unused value is either the first element of the increasing part or the
last element of the decreasing part. Removing it gives the next choice of end. -/
private theorem encode (k m : Nat) (xs : List Nat) (hp : Peak xs)
    (hperm : xs.Perm (List.range' k m)) : ∃ s, s.length = m ∧ row k s = xs := by
  induction m generalizing k xs with
  | zero =>
    have hx : xs = [] := List.perm_nil.mp hperm
    exact ⟨[], rfl, hx.symm⟩
  | succ m ih =>
    obtain ⟨b, d, rfl, hb, hd⟩ := hp
    rw [List.range'_succ] at hperm
    have hleast (y) (h : y ∈ b ++ d.reverse) : k ≤ y := by
      have := hperm.mem_iff.mp h
      simp at this
      omega
    have hk := hperm.mem_iff.mpr (List.mem_cons_self (a := k))
    rcases List.mem_append.mp hk with hm | hm
    · obtain ⟨t, rfl⟩ := head_of_least hb hm (fun y hy => hleast y (by simp [hy]))
      obtain ⟨s, hs, hr⟩ := ih (k + 1) (t ++ d.reverse)
        ⟨t, d, rfl, (List.pairwise_cons.mp hb).2, hd⟩ hperm.cons_inv
      exact ⟨true :: s, by simp [hs], by simp [row, hr]⟩
    · obtain ⟨t, rfl⟩ := head_of_least hd (List.mem_reverse.mp hm)
        (fun y hy => hleast y (by simp [hy]))
      have hp' : (k :: (b ++ t.reverse)).Perm (k :: List.range' (k + 1) m) :=
        (List.perm_append_singleton ..).symm.trans (by simpa [List.append_assoc] using hperm)
      obtain ⟨s, hs, hr⟩ := ih (k + 1) (b ++ t.reverse)
        ⟨b, t, rfl, hb, (List.pairwise_cons.mp hd).2⟩ hp'.cons_inv
      exact ⟨false :: s, by simp [hs], by simp [row, hr, List.append_assoc]⟩

private def misses (f : Nat → Nat) (l : Nat) : List Nat → Nat
  | [] => 0
  | a :: xs => misses f (l + 1) xs + if f l = a then 0 else 1

private theorem misses_snoc (f : Nat → Nat) (l : Nat) (xs : List Nat) (a : Nat) :
    misses f l (xs ++ [a]) = misses f l xs + if f (l + xs.length) = a then 0 else 1 := by
  induction xs generalizing l with
  | nil => simp [misses]
  | cons x xs ih =>
    simp only [List.cons_append, misses, ih, List.length_cons]
    rw [show l + 1 + xs.length = l + (xs.length + 1) by omega]
    omega

private theorem hits_add_misses (f : Nat → Nat) (n l r : Nat) (s : List Bool)
    (h : l + r + s.length = n) :
    (hits f n l r s).length + misses f l (row (l + r + 1) s) = s.length := by
  induction s generalizing l r with
  | nil => simp [row, hits, misses]
  | cons side s ih =>
    simp only [List.length_cons] at h ⊢
    cases side
    · have hh := ih l (r + 1) (by omega)
      rw [hits_right, row, misses_snoc, row_length]
      rw [show l + s.length = n - r - 1 by omega, show l + r + 1 + 1 = l + (r + 1) + 1 by omega]
      split <;> simp_all <;> omega
    · have hh := ih (l + 1) r (by omega)
      rw [hits_left, row, misses, show l + r + 1 + 1 = l + 1 + r + 1 by omega]
      split <;> simp_all <;> omega

private theorem misses_finRange (f : Nat → Nat) (l : Nat) (xs : List Nat) :
    misses f l xs =
      ((List.finRange xs.length).filter fun (i : Fin xs.length) => xs[i] ≠ f (l + i)).length := by
  induction xs generalizing l with
  | nil => simp [misses]
  | cons x xs ih =>
    simp only [misses, List.length_cons, List.finRange_succ, List.filter_cons, List.filter_map]
    rw [ih]
    by_cases he : f l = x <;>
      simp [he, Ne.symm, Function.comp_def, Nat.add_left_comm, Nat.add_comm]

/-! ### Relating the program's sorted candidate list to the lattice paths -/

private def leftPoint (z : Nat × Nat) : Point := (2 * z.2 + 1, 2 * (z.1 - z.2 - 1))
private def rightPoint (n : Nat) (z : Nat × Nat) : Point := (2 * (z.1 + z.2 - n), 2 * (n - z.2) - 1)

private def candidates (a : Array Nat) : List Point :=
  let z := a.toList.zipIdx
  ((z.filter fun x => x.2 + 1 ≤ x.1).map leftPoint) ++
    ((z.filter fun x => a.size ≤ x.1 + x.2).map (rightPoint a.size))

private def cmp (p q : Point) : Bool := p = q ∨ Prod.Lex (· < ·) (· < ·) p q

private theorem cmp_iff (p q : Point) : cmp p q ↔ toLex p ≤ toLex q := by
  simp only [cmp, decide_eq_true_eq, Prod.lex_iff, Prod.Lex.toLex_le_toLex, Prod.ext_iff]
  omega

private theorem candidates_nodup (a : Array Nat) : (candidates a).Nodup := by
  have hidx : (a.toList.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  have hd := List.pairwise_map.mp hidx
  unfold candidates
  rw [List.nodup_append]
  refine ⟨List.pairwise_map.mpr ?_, List.pairwise_map.mpr ?_, ?_⟩
  · apply (hd.sublist List.filter_sublist).imp
    intro z w hn he
    have := congrArg Prod.fst he
    dsimp [leftPoint] at this
    omega
  · apply (hd.sublist List.filter_sublist).imp_of_mem
    intro z w hz hw hn he
    have hz' := List.snd_lt_of_mem_zipIdx (List.mem_filter.mp hz).1
    have hw' := List.snd_lt_of_mem_zipIdx (List.mem_filter.mp hw).1
    simp only [Array.length_toList] at hz' hw'
    have := congrArg Prod.snd he
    dsimp [rightPoint] at this
    omega
  · intro p hp q hq heq
    subst q
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨w, _, he⟩ := List.mem_map.mp hq
    have := congrArg Prod.fst he
    dsimp [leftPoint, rightPoint] at this
    omega

private theorem candidates_mem (a : Array Nat) (hmax : ∀ i < a.size, a[i]! ≤ a.size)
    (p : Point) : p ∈ candidates a ↔ Eligible (fun i => a[i]!) a.size p := by
  simp only [candidates, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨⟨y, i⟩, ⟨hi, hy⟩, rfl⟩ | ⟨⟨y, i⟩, ⟨hi, hy⟩, rfl⟩) <;>
      obtain ⟨hi', hyval⟩ := List.mem_zipIdx' hi <;>
      simp only [Array.length_toList] at hi' <;>
      change y = a[i] at hyval <;> subst y <;> dsimp at hy <;>
      have hm := hmax i hi' <;> simp [getElem!_pos, hi'] at hm
    · refine ⟨i, a[i] - i - 1, by omega, Or.inl ⟨rfl, ?_⟩⟩
      simp [getElem!_pos, hi']
      omega
    · refine ⟨a[i] + i - a.size, a.size - i - 1, by omega, Or.inr ⟨?_, ?_⟩⟩
      · dsimp [rightPoint]
        congr 1
        omega
      · rw [show a.size - (a.size - i - 1) - 1 = i by omega]
        simp [getElem!_pos, hi']
        omega
  · rintro ⟨u, v, huv, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · have hu : u < a.size := by omega
      simp [getElem!_pos, hu] at h
      left
      refine ⟨(a[u], u), ⟨?_, by dsimp; omega⟩, ?_⟩
      · simp [List.mem_zipIdx_iff_getElem?, hu]
      · dsimp [leftPoint]
        congr 1
        omega
    · let i := a.size - v - 1
      have hi : i < a.size := by dsimp [i]; omega
      change a[i]! = _ at h
      simp [getElem!_pos, hi] at h
      right
      refine ⟨(a[i], i), ⟨?_, ?_⟩, ?_⟩
      · simp [List.mem_zipIdx_iff_getElem?, hi]
      · dsimp [i] at *
        omega
      · dsimp [rightPoint, i] at *
        congr 1 <;> omega

private def ordered (a : Array Nat) := (candidates a).mergeSort cmp

private theorem ordered_sorted (a : Array Nat) :
    (ordered a).Pairwise (fun p q => toLex p ≤ toLex q) := by
  apply List.Pairwise.imp (fun {p q} (h : cmp p q) => (cmp_iff p q).mp h)
  apply List.pairwise_mergeSort
  · intro p q r hp hq
    exact (cmp_iff ..).mpr (((cmp_iff ..).mp hp).trans ((cmp_iff ..).mp hq))
  · intro p q
    simpa [cmp_iff] using le_total (toLex p) (toLex q)

private theorem follows_sublist (a : Array Nat) (ps : List Point) (hp : ps.Pairwise Follows)
    (hs : ps ⊆ ordered a) : ps <+ ordered a := by
  let rel (p q : Point) := toLex p ≤ toLex q
  let _ : Std.Antisymm rel := ⟨fun p q h₁ h₂ => toLex.injective (le_antisymm h₁ h₂)⟩
  exact List.sublist_of_subperm_of_pairwise (r := rel)
    (List.subperm_of_subset (hp.imp fun h => h.2.2) hs)
    (hp.imp fun h => Prod.Lex.toLex_le_toLex'.mpr ⟨h.1, fun _ => h.2.1⟩) (ordered_sorted _)

private theorem one_range (n : Nat) : (1...=n).toArray.toList = List.range' 1 n := by
  rw [Nat.toList_toArray_rcc, Nat.toList_rcc_eq_toList_rco, List.range'_eq_toList_rco,
    Nat.add_comm 1 n]

private theorem diff_eq_misses {n : Nat} (x a : Vector Nat n) :
    differences x a = misses (fun i => a.toArray[i]!) 0 x.toArray.toList := by
  obtain ⟨x, rfl⟩ := x
  rw [differences, misses_finRange]
  congr 1
  apply List.filter_congr
  intro i _
  by_cases h : x[(i : Nat)] = a[(i : Nat)] <;> simp [getElem!_pos, h]

private theorem program_eq (a : Array Nat) :
    minRearrange a = a.size - minRearrange.lis ((ordered a).map Prod.snd).toArray := by
  simp only [minRearrange, ordered, candidates, List.map_toArray, Array.toList_append,
    Array.toList_map, Array.toList_filter, Array.toList_zipIdx]
  rfl

/-- For any choice of ends, the matched positions give a subsequence of the algorithm's
second coordinates. Conversely, a longest such subsequence can be visited by a choice of ends. -/
private theorem optimal_hits (a : Array Nat) (hm : ∀ i < a.size, a[i]! ≤ a.size) :
    let k := minRearrange.lis ((ordered a).map Prod.snd).toArray
    let score := fun s => (hits (fun i => a[i]!) a.size 0 0 s).length
    (∃ s, s.length = a.size ∧ k ≤ score s) ∧ ∀ s, s.length = a.size → score s ≤ k := by
  let ps := ordered a
  let k := minRearrange.lis (ps.map Prod.snd).toArray
  have hbest : Best (ps.map Prod.snd) k := by simpa [k] using lis_best (ps.map Prod.snd).toArray
  have hperm : ps.Perm (candidates a) := List.mergeSort_perm ..
  have helig (p) : p ∈ ps ↔ Eligible (fun i => a[i]!) a.size p :=
    hperm.mem_iff.trans (candidates_mem a hm p)
  have hsort := ordered_sorted a
  constructor
  · obtain ⟨ys, hys, hp, hlen⟩ := hbest.1
    obtain ⟨qs, hs, rfl⟩ := List.sublist_map_iff.mp hys
    have hfirst := (hsort.sublist hs).imp (fun h => (Prod.Lex.toLex_le_toLex'.mp h).1)
    have hnd := (hperm.nodup_iff.mpr (candidates_nodup a)).sublist hs
    have hchain : qs.Pairwise Follows :=
      List.pairwise_and_iff.mpr ⟨hfirst, List.pairwise_and_iff.mpr ⟨List.pairwise_map.mp hp, hnd⟩⟩
    obtain ⟨s, hn, h⟩ := cover_chain _ a.size a.size 0 0 (by simp) qs hchain
      (fun p h => (helig p).mp (hs.subset h)) (by simp)
    simp only [List.length_map] at hlen
    rw [hlen] at h
    exact ⟨s, hn, h⟩
  · intro s hn
    obtain ⟨hp, he⟩ := hits_chain (fun i => a[i]!) a.size 0 0 s (by simpa using hn)
    have hs := follows_sublist a _ hp (fun p h => (helig p).mpr (he p h).1)
    simpa using hbest.2 _ (hs.map Prod.snd) (List.pairwise_map.mpr (hp.imp fun h => h.2.1))

end minRearrange_correct
open minRearrange_correct

-- Keep the vector size proofs inline, as in the wanted statement.
set_option backward.proofsInPublic true in
/--
**Correctness of the unimodal rearrangement algorithm.** Let $a$ be an array of length $n$ that
is a permutation of $1, \dots, n$, and let $m(a)$ be the value that the program
$\mathrm{minRearrange}$ computes on $a$. Then some unimodal permutation $x$ of
$1, \dots, n$ differs from $a$ in exactly $m(a)$ positions, and every unimodal permutation of
$1, \dots, n$ differs from $a$ in at least $m(a)$ positions. So $m(a)$ is the minimum number of
positions in which $a$ differs from a unimodal permutation of $1, \dots, n$.

Source: NWERC 2025 Problem G, see https://2025.nwerc.eu/problem-set.pdf
Via leanprover/lean-eval@38361be, problem `permute_to_unimodal`.
-/
theorem minRearrange_correct {arr : Array Nat} :
    arr.Perm (1...=arr.size).toArray →
      (∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
        Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector =
          minRearrange arr) ∧
      (∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
        Unimodal x → minRearrange arr ≤
          differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector) := by
  intro hperm
  have hmax (i) (hi : i < arr.size) : arr[i]! ≤ arr.size := by
    have h := hperm.toList.mem_iff.mp (Array.getElem_mem_toList hi)
    rw [one_range] at h
    simp [getElem!_pos, hi]
    simp at h
    omega
  let k := minRearrange.lis ((ordered arr).map Prod.snd).toArray
  have heq : minRearrange arr = arr.size - k := program_eq arr
  obtain ⟨⟨s, hs, hs'⟩, hbound⟩ := optimal_hits arr hmax
  have dist (s : List Bool) (hlen : s.length = arr.size) :
      (hits (fun i => arr[i]!) arr.size 0 0 s).length +
      misses (fun i => arr[i]!) 0 (row 1 s) = arr.size := by
    simpa [hlen] using hits_add_misses (fun i => arr[i]!) arr.size 0 0 s (by simpa using hlen)
  constructor
  · let x := (row 1 s).toArray
    have hx : x.Perm (1...=arr.size).toArray :=
      ⟨by rw [one_range, ← hs]; exact row_perm 1 s⟩
    refine ⟨x, hx, (peak_iff x).mp (by simpa [x] using row_peak 1 s), ?_⟩
    rw [diff_eq_misses, heq]
    change misses (fun i => arr[i]!) 0 (row 1 s) = arr.size - k
    have hu := hbound s hs
    change (hits (fun i => arr[i]!) arr.size 0 0 s).length ≤ k at hu
    change k ≤ (hits (fun i => arr[i]!) arr.size 0 0 s).length at hs'
    have := dist s hs
    omega
  · intro x hx huni
    obtain ⟨t, ht, hr⟩ := encode 1 arr.size x.toList ((peak_iff x).mpr huni)
      (by rw [← one_range]; exact hx.toList)
    rw [diff_eq_misses, heq]
    change arr.size - k ≤ misses (fun i => arr[i]!) 0 x.toList
    rw [← hr]
    have hu := hbound t ht
    change (hits (fun i => arr[i]!) arr.size 0 0 t).length ≤ k at hu
    have := dist t ht
    omega

end ProgramVerification

end MathlibExt.TheoryOfComputation.PermuteToUnimodalWanted
