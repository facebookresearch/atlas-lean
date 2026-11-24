/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Find

/-!
# Sorting by reversals: breakpoints and the `b ≤ 2d` bound

Unsigned and signed permutations of `1..n` (as lists over `Int`), reversal
distance, and the classical breakpoint lower bound, following the genome
rearrangement chapter of Shamir–Peer, *Algorithms for Molecular Biology*,
Lecture 11 (§11.2 unsigned, signed setting thereafter).

A *breakpoint* is an adjacent pair in the framed list (sentinels `0` and
`n + 1`) that is not consecutive: absolute difference different from `1` in
the unsigned model (`ubreaks`), directed successor test `next - prev ≠ 1`
in the signed model (`sbreaks`). A signed reversal reverses a block and
negates its entries, so singleton reversals flip one sign. The doubling map
sends `+x` to `(2x - 1, 2x)` and `-x` to `(2x, 2x - 1)`; for valid signed
permutations the directed count equals the unsigned count of the doubled
permutation (`sbreaks_eq_ubreaks_dbl_of_valid`; the unrestricted form is
false, see `sbreaks_eq_ubreaks_dbl_counterex`).

## Main results

* `ubreaks_revBlock_le`, `ubreaks_le_revBlock`: one unsigned reversal changes
  the breakpoint count by at most two, in either direction.
* `sortable`, `ssortable`: every valid permutation sorts by reversals, so the
  distances `udist` and `sdist` are genuine minima.
* `ub_le_two_mul_udist`, `sb_le_two_mul_sdist`: `b(π) ≤ 2 * d(π)`
  (Lecture 11, Theorem 11.2 and its signed analogue).
* `ubreaks_eq_zero_iff`, `sbreaks_eq_zero_iff` (derived): the identity is the
  unique valid permutation with breakpoint count zero.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Rearrangement.SortingByReversals

/-- Reverse the 0-based inclusive block `i..j` of a list. Meaningful for `i <= j < pi.length`.
Outside that range the truncated subtraction `j + 1 - i` is `0` when `j < i`, and the result is
`pi.take i ++ pi.drop (j + 1)`: `pi` itself when `i = j + 1`, with repeated entries when
`j + 1 < min i pi.length`. For `i ≤ j` and `pi.length ≤ j` the suffix from `i` is reversed. -/
def revBlock (pi : List Int) (i j : Nat) : List Int :=
  pi.take i ++ (pi.drop i |>.take (j + 1 - i)).reverse ++ pi.drop (j + 1)

/-- Count the adjacent pairs of a list whose absolute difference is not `1` (`0` for at most one
entry); `ubreaks` applies it to the list framed by `0` and `n + 1`. -/
def gapCount : List Int -> Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if (b - a).natAbs = 1 then 0 else 1) + gapCount (b :: t)

/-- Framed breakpoint count with sentinels `0` and `n + 1`. -/
def ubreaks (n : Nat) (pi : List Int) : Nat :=
  gapCount (0 :: pi ++ [Int.ofNat (n + 1)])

/-- Adjacent-gap indicator: `0` when consecutive values differ by exactly `1`, else `1`. -/
def isGap (a b : Int) : Nat :=
  if (b - a).natAbs = 1 then 0 else 1

theorem isGap_le_one (a b : Int) : isGap a b ≤ 1 := by
  unfold isGap
  split <;> omega

theorem isGap_symm (a b : Int) : isGap a b = isGap b a := by
  simp only [isGap]
  have h : a - b = -(b - a) := by omega
  rw [h, Int.natAbs_neg]

theorem gapCount_cons_of_ne (x : Int) (l : List Int) (h : l ≠ []) :
    gapCount (x :: l) = isGap x (l.head h) + gapCount l := by
  cases l with
  | nil => exact absurd rfl h
  | cons y t => rfl

theorem gapCount_append (l₁ l₂ : List Int) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    gapCount (l₁ ++ l₂)
      = gapCount l₁ + gapCount l₂ + isGap (l₁.getLast h₁) (l₂.head h₂) := by
  revert h₁
  induction l₁ with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro h₁
    cases t with
    | nil =>
      rw [List.getLast_singleton]
      have h1 : ([a] : List Int) ++ l₂ = a :: l₂ := rfl
      rw [h1, gapCount_cons_of_ne _ _ h₂]
      have h0 : gapCount [a] = 0 := rfl
      omega
    | cons b t' =>
      have hbt' : b :: t' ≠ [] := by simp
      have happ : (a :: b :: t') ++ l₂ = a :: ((b :: t') ++ l₂) := rfl
      have hbt : (b :: t') ++ l₂ ≠ [] := List.append_ne_nil_of_left_ne_nil hbt' l₂
      rw [happ, gapCount_cons_of_ne _ _ hbt, gapCount_cons_of_ne _ _ hbt',
        List.head_append_left hbt', List.head_cons, ih hbt', List.getLast_cons hbt']
      omega

theorem gapCount_reverse (l : List Int) : gapCount l.reverse = gapCount l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.reverse_cons]
    cases t with
    | nil => rfl
    | cons b t' =>
      have hne : (b :: t') ≠ [] := by simp
      have hrev : (b :: t').reverse ≠ [] := by
        intro hcon
        exact hne (List.reverse_eq_nil_iff.mp hcon)
      have hsingle : ([a] : List Int) ≠ [] := by simp
      have h1 := gapCount_append (b :: t').reverse [a] hrev hsingle
      rw [h1, ih]
      have hgl : (b :: t').reverse.getLast hrev = b := by
        rw [List.getLast_reverse hrev, List.head_cons]
      have hgap : gapCount (a :: b :: t') = isGap a b + gapCount (b :: t') := rfl
      rw [hgl, List.head_singleton, isGap_symm b a]
      have h0 : gapCount [a] = 0 := rfl
      omega

theorem pi_split (pi : List Int) (i j : Nat) (hij : i ≤ j) (_hj : j < pi.length) :
    pi.take i ++ (pi.drop i).take (j + 1 - i) ++ pi.drop (j + 1) = pi := by
  have h3 : (pi.drop i).drop (j + 1 - i) = pi.drop (j + 1) := by
    rw [List.drop_drop]
    congr 1
    omega
  have h2 : (pi.drop i).take (j + 1 - i) ++ (pi.drop i).drop (j + 1 - i) = pi.drop i :=
    List.take_append_drop _ _
  rw [← h3, List.append_assoc, h2]
  exact List.take_append_drop i pi

theorem mid_nonempty (pi : List Int) (i j : Nat) (hij : i ≤ j) (hj : j < pi.length) :
    (pi.drop i).take (j + 1 - i) ≠ [] := by
  have hlen : ((pi.drop i).take (j + 1 - i)).length = j + 1 - i := by
    rw [List.length_take, List.length_drop]
    omega
  intro hcon
  rw [hcon] at hlen
  simp at hlen
  omega

theorem revBlock_eq (pi : List Int) (i j : Nat) :
    revBlock pi i j
      = pi.take i ++ ((pi.drop i).take (j + 1 - i)).reverse ++ pi.drop (j + 1) := rfl

theorem gapCount_concat_eq (L S R : List Int) (hL : L ≠ []) (hS : S ≠ []) (hR : R ≠ []) :
    gapCount ((L ++ S) ++ R)
      = gapCount L + gapCount S + gapCount R
        + (isGap (L.getLast hL) (S.head hS) + isGap (S.getLast hS) (R.head hR)) := by
  have hLS : L ++ S ≠ [] := List.append_ne_nil_of_left_ne_nil hL S
  have e1 := gapCount_append (L ++ S) R hLS hR
  have e1a := gapCount_append L S hL hS
  have g1 : (L ++ S).getLast hLS = S.getLast hS := List.getLast_append_right hS
  rw [e1, e1a, g1]
  omega

theorem frame_eq (n : Nat) (pi : List Int) (i j : Nat) (hij : i ≤ j) (hj : j < pi.length) :
    (0 :: pi ++ [Int.ofNat (n + 1)])
      = (([0] ++ pi.take i) ++ (pi.drop i).take (j + 1 - i))
        ++ (pi.drop (j + 1) ++ [Int.ofNat (n + 1)]) := by
  have hpi := pi_split pi i j hij hj
  conv => lhs; rw [← hpi]
  have h0 : ∀ X : List Int, (0 :: X) = [0] ++ X := fun X => rfl
  conv => lhs; rw [h0]
  simp only [List.append_assoc]

theorem frameR_eq (n : Nat) (pi : List Int) (i j : Nat) :
    (0 :: revBlock pi i j ++ [Int.ofNat (n + 1)])
      = (([0] ++ pi.take i) ++ ((pi.drop i).take (j + 1 - i)).reverse)
        ++ (pi.drop (j + 1) ++ [Int.ofNat (n + 1)]) := by
  have hrw := revBlock_eq pi i j
  conv => lhs; rw [hrw]
  have h0 : ∀ X : List Int, (0 :: X) = [0] ++ X := fun X => rfl
  conv => lhs; rw [h0]
  simp only [List.append_assoc]

theorem ubreaks_revBlock_le (n : Nat) (pi : List Int) (i j : Nat)
    (hij : i <= j) (hj : j < pi.length) :
    ubreaks n (revBlock pi i j) <= ubreaks n pi + 2 := by
  have hSne : (pi.drop i).take (j + 1 - i) ≠ [] := mid_nonempty pi i j hij hj
  have hSrne : ((pi.drop i).take (j + 1 - i)).reverse ≠ [] := by
    intro hcon
    exact hSne (List.reverse_eq_nil_iff.mp hcon)
  have hLne : ([0] : List Int) ++ pi.take i ≠ [] :=
    List.append_ne_nil_of_left_ne_nil (by simp) _
  have hRne : pi.drop (j + 1) ++ [Int.ofNat (n + 1)] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ (by simp)
  have eS := gapCount_concat_eq ([0] ++ pi.take i) ((pi.drop i).take (j + 1 - i))
    (pi.drop (j + 1) ++ [Int.ofNat (n + 1)]) hLne hSne hRne
  have eR := gapCount_concat_eq ([0] ++ pi.take i) (((pi.drop i).take (j + 1 - i)).reverse)
    (pi.drop (j + 1) ++ [Int.ofNat (n + 1)]) hLne hSrne hRne
  have hr1 : (((pi.drop i).take (j + 1 - i)).reverse).head hSrne
      = ((pi.drop i).take (j + 1 - i)).getLast hSne := List.head_reverse hSrne
  have hr2 : (((pi.drop i).take (j + 1 - i)).reverse).getLast hSrne
      = ((pi.drop i).take (j + 1 - i)).head hSne := List.getLast_reverse hSrne
  have hrev := gapCount_reverse ((pi.drop i).take (j + 1 - i))
  rw [hr1, hr2, hrev] at eR
  have hfS := frame_eq n pi i j hij hj
  have hfR := frameR_eq n pi i j
  have q1 := isGap_le_one (([0] ++ pi.take i).getLast hLne)
    (((pi.drop i).take (j + 1 - i)).head hSne)
  have q2 := isGap_le_one (((pi.drop i).take (j + 1 - i)).getLast hSne)
    ((pi.drop (j + 1) ++ [Int.ofNat (n + 1)]).head hRne)
  have q3 := isGap_le_one (([0] ++ pi.take i).getLast hLne)
    (((pi.drop i).take (j + 1 - i)).getLast hSne)
  have q4 := isGap_le_one (((pi.drop i).take (j + 1 - i)).head hSne)
    ((pi.drop (j + 1) ++ [Int.ofNat (n + 1)]).head hRne)
  simp only [ubreaks]
  rw [hfR, hfS, eR, eS]
  omega

theorem ubreaks_le_revBlock (n : Nat) (pi : List Int) (i j : Nat)
    (hij : i <= j) (hj : j < pi.length) :
    ubreaks n pi <= ubreaks n (revBlock pi i j) + 2 := by
  have hSne : (pi.drop i).take (j + 1 - i) ≠ [] := mid_nonempty pi i j hij hj
  have hSrne : ((pi.drop i).take (j + 1 - i)).reverse ≠ [] := by
    intro hcon
    exact hSne (List.reverse_eq_nil_iff.mp hcon)
  have hLne : ([0] : List Int) ++ pi.take i ≠ [] :=
    List.append_ne_nil_of_left_ne_nil (by simp) _
  have hRne : pi.drop (j + 1) ++ [Int.ofNat (n + 1)] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ (by simp)
  have eS := gapCount_concat_eq ([0] ++ pi.take i) ((pi.drop i).take (j + 1 - i))
    (pi.drop (j + 1) ++ [Int.ofNat (n + 1)]) hLne hSne hRne
  have eR := gapCount_concat_eq ([0] ++ pi.take i) (((pi.drop i).take (j + 1 - i)).reverse)
    (pi.drop (j + 1) ++ [Int.ofNat (n + 1)]) hLne hSrne hRne
  have hr1 : (((pi.drop i).take (j + 1 - i)).reverse).head hSrne
      = ((pi.drop i).take (j + 1 - i)).getLast hSne := List.head_reverse hSrne
  have hr2 : (((pi.drop i).take (j + 1 - i)).reverse).getLast hSrne
      = ((pi.drop i).take (j + 1 - i)).head hSne := List.getLast_reverse hSrne
  have hrev := gapCount_reverse ((pi.drop i).take (j + 1 - i))
  rw [hr1, hr2, hrev] at eR
  have hfS := frame_eq n pi i j hij hj
  have hfR := frameR_eq n pi i j
  have q1 := isGap_le_one (([0] ++ pi.take i).getLast hLne)
    (((pi.drop i).take (j + 1 - i)).head hSne)
  have q2 := isGap_le_one (((pi.drop i).take (j + 1 - i)).getLast hSne)
    ((pi.drop (j + 1) ++ [Int.ofNat (n + 1)]).head hRne)
  have q3 := isGap_le_one (([0] ++ pi.take i).getLast hLne)
    (((pi.drop i).take (j + 1 - i)).getLast hSne)
  have q4 := isGap_le_one (((pi.drop i).take (j + 1 - i)).head hSne)
    ((pi.drop (j + 1) ++ [Int.ofNat (n + 1)]).head hRne)
  simp only [ubreaks]
  rw [hfS, hfR, eS, eR]
  omega

open scoped List

/-- Inclusive interval list `[m, m + 1, …, n]` (`[]` when `n < m`).
The identity target `(List.Icc 1 n).map Int.ofNat` is the sorted unsigned
permutation; see Shamir-Peer Lecture 11 §11.2 for the unsigned setting. -/
def _root_.List.Icc (m n : Nat) : List Nat := List.range' m (n + 1 - m)

/-- Peeling the top element off the identity interval. -/
theorem Icc_one_succ (n : Nat) : List.Icc 1 (n + 1) = List.Icc 1 n ++ [n + 1] := by
  unfold List.Icc
  have e1 : n + 1 + 1 - 1 = n + 1 := by omega
  have e2 : n + 1 - 1 = n := by omega
  rw [e1, e2, List.range'_concat, show 1 + 1 * n = n + 1 from by omega]

/-- The identity target grows by appending the new top element. -/
theorem target_succ (n : Nat) :
    (List.Icc 1 (n + 1)).map Int.ofNat
      = (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)] := by
  rw [Icc_one_succ, List.map_append, List.map_cons, List.map_nil]

/-- Length of the identity target. -/
theorem target_length (n : Nat) : ((List.Icc 1 n).map Int.ofNat).length = n := by
  rw [List.length_map]
  unfold List.Icc
  rw [List.length_range']
  omega

/-- The top element belongs to the identity target. -/
theorem mem_target_succ (n : Nat) :
    Int.ofNat (n + 1) ∈ (List.Icc 1 (n + 1)).map Int.ofNat := by
  rw [target_succ]
  simp

/-- Unsigned validity: `pi` is a permutation of the identity `[1, …, n]`.
Cf. the unsigned permutations of Shamir-Peer Lecture 11 §11.2. -/
def UValid (n : Nat) (pi : List Int) : Prop := pi ~ (List.Icc 1 n).map Int.ofNat

/-- Sortability by reversals in exactly `k` steps: `done` is the identity in
`0` steps, `step` peels off one reversal. Cf. Shamir-Peer Lecture 11 §11.2. -/
inductive USortableIn : Nat → Nat → List Int → Prop where
  | done (n : Nat) : USortableIn 0 n ((List.Icc 1 n).map Int.ofNat)
  | step (k n : Nat) (pi : List Int) (i j : Nat) (hij : i ≤ j) (hlt : j < pi.length)
    (h : USortableIn k n (revBlock pi i j)) : USortableIn (k + 1) n pi

/-- Reversals preserve length (for meaningful `i ≤ j < pi.length`).
Cf. Shamir-Peer Lecture 11 §11.2. -/
theorem revBlock_length (pi : List Int) (i j : Nat) (hij : i ≤ j) (hj : j < pi.length) :
    (revBlock pi i j).length = pi.length := by
  rw [revBlock_eq, List.length_append, List.length_append, List.length_reverse,
    List.length_take, List.length_take, List.length_drop, List.length_drop]
  omega

/-- A meaningful reversal permutes the list. -/
theorem revBlock_perm (pi : List Int) (i j : Nat) (hij : i ≤ j) (hj : j < pi.length) :
    revBlock pi i j ~ pi := by
  have hpi : pi.take i ++ ((pi.drop i).take (j + 1 - i) ++ pi.drop (j + 1)) = pi := by
    rw [← List.append_assoc]
    exact pi_split pi i j hij hj
  have hmid : ((pi.drop i).take (j + 1 - i)).reverse ++ pi.drop (j + 1)
      ~ (pi.drop i).take (j + 1 - i) ++ pi.drop (j + 1) :=
    List.Perm.append (List.reverse_perm _) List.Perm.rfl
  rw [revBlock_eq, List.append_assoc]
  exact (List.Perm.append_left _ hmid).trans (List.Perm.of_eq hpi)

/-- Reversals preserve unsigned validity (for meaningful `i ≤ j < pi.length`).
Cf. Shamir-Peer Lecture 11 §11.2. -/
theorem revBlock_valid (n : Nat) (pi : List Int) (i j : Nat) (h : UValid n pi)
    (hij : i ≤ j) (hj : j < pi.length) : UValid n (revBlock pi i j) :=
  List.Perm.trans (revBlock_perm pi i j hij hj) h

/-- Reversals inside the prefix of `X ++ [c]` act on the prefix alone: for `i ≤ j < X.length`,
`revBlock (X ++ [c]) i j = revBlock X i j ++ [c]` (any `c`). -/
theorem revBlock_append_singleton (X : List Int) (c : Int) (i j : Nat)
    (hij : i ≤ j) (hj : j < X.length) :
    revBlock (X ++ [c]) i j = revBlock X i j ++ [c] := by
  have hiX : i ≤ X.length := by omega
  have hjX : j + 1 ≤ X.length := by omega
  have hmid : j + 1 - i ≤ (X.drop i).length := by
    rw [List.length_drop]
    omega
  rw [revBlock_eq, revBlock_eq, List.take_append_of_le_length hiX,
    List.drop_append_of_le_length hiX, List.take_append_of_le_length hmid,
    List.drop_append_of_le_length hjX]
  simp only [List.append_assoc]

/-- Lifting sortability across a fixed top element (pancake suffix invariant).
Cf. Shamir-Peer Lecture 11 §11.2. -/
theorem USortableIn_succ_append (k n : Nat) (X : List Int) (hX : USortableIn k n X) :
    USortableIn k (n + 1) (X ++ [Int.ofNat (n + 1)]) := by
  induction hX with
  | done n0 =>
    rw [← target_succ]
    exact USortableIn.done _
  | step k0 n0 X0 i0 j0 hij0 hlt0 _ ih0 =>
    have hlen1 : ([Int.ofNat (n0 + 1)]).length = 1 := rfl
    have hlt' : j0 < (X0 ++ [Int.ofNat (n0 + 1)]).length := by
      rw [List.length_append, hlen1]
      omega
    have heq : revBlock (X0 ++ [Int.ofNat (n0 + 1)]) i0 j0
        = revBlock X0 i0 j0 ++ [Int.ofNat (n0 + 1)] :=
      revBlock_append_singleton X0 _ i0 j0 hij0 hlt0
    refine USortableIn.step _ _ _ _ _ hij0 hlt' ?_
    rw [heq]
    exact ih0

/-- Every unsigned permutation sorts by reversals (pancake argument).
Cf. Shamir-Peer Lecture 11 §11.2. -/
theorem sortable (n : Nat) (pi : List Int) (h : UValid n pi) :
    ∃ k, USortableIn k n pi := by
  induction n generalizing pi with
  | zero =>
    have hT0 : (List.Icc 1 0).map Int.ofNat = [] := rfl
    unfold UValid at h
    rw [hT0] at h
    have hnil : pi = [] := List.Perm.eq_nil h
    subst hnil
    refine ⟨0, ?_⟩
    rw [← hT0]
    exact USortableIn.done _
  | succ n ih =>
    unfold UValid at h
    have hlen : pi.length = n + 1 :=
      (List.Perm.length_eq h).trans (target_length (n + 1))
    have hc_mem : Int.ofNat (n + 1) ∈ pi :=
      (List.Perm.mem_iff h).mpr (mem_target_succ n)
    obtain ⟨p, hp_lt, hp_get⟩ :
        ∃ p, ∃ (hp : p < pi.length), pi[p]'hp = Int.ofNat (n + 1) :=
      ⟨_, List.idxOf_lt_length_of_mem hc_mem,
        List.getElem_idxOf (List.idxOf_lt_length_of_mem hc_mem)⟩
    have htake : pi.take (p + 1) = pi.take p ++ [Int.ofNat (n + 1)] := by
      have ht := List.take_succ_eq_append_getElem hp_lt
      rw [hp_get] at ht
      exact ht
    have hrev1 : revBlock pi 0 p
        = [Int.ofNat (n + 1)] ++
          ((pi.take p).reverse ++ pi.drop (p + 1)) := by
      rw [revBlock_eq]
      simp only [List.take_zero, List.drop_zero, Nat.sub_zero, List.nil_append]
      rw [htake, List.reverse_append, List.reverse_singleton, List.append_assoc]
    have hlen1 : (revBlock pi 0 p).length = n + 1 :=
      (revBlock_length pi 0 p (Nat.zero_le p) hp_lt).trans hlen
    have hn_lt : n < (revBlock pi 0 p).length := by
      rw [hlen1]
      exact Nat.lt_succ_self n
    have hle : (revBlock pi 0 p).length ≤ n + 1 := by omega
    have htake2 : (revBlock pi 0 p).take (n + 1) = revBlock pi 0 p :=
      List.take_of_length_le hle
    have hdrop2 : (revBlock pi 0 p).drop (n + 1) = [] :=
      List.drop_of_length_le hle
    have hrev2 : revBlock (revBlock pi 0 p) 0 n
        = ((pi.take p).reverse ++ pi.drop (p + 1)).reverse
          ++ [Int.ofNat (n + 1)] := by
      rw [revBlock_eq]
      simp only [List.take_zero, List.drop_zero, Nat.sub_zero, List.nil_append]
      rw [htake2, hdrop2, List.append_nil, hrev1, List.reverse_append,
        List.reverse_singleton]
    have hperm2 : ((pi.take p).reverse ++ pi.drop (p + 1)).reverse
          ++ [Int.ofNat (n + 1)]
        ~ (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)] := by
      have g := (revBlock_perm _ 0 n (Nat.zero_le n) hn_lt).trans
        ((revBlock_perm _ 0 p (Nat.zero_le p) hp_lt).trans h)
      rw [hrev2, target_succ] at g
      exact g
    have hX : ((pi.take p).reverse ++ pi.drop (p + 1)).reverse
        ~ (List.Icc 1 n).map Int.ofNat :=
      (List.perm_append_right_iff _).mp hperm2
    obtain ⟨k, hk⟩ := ih _ hX
    have hlift : USortableIn k (n + 1)
        (((pi.take p).reverse ++ pi.drop (p + 1)).reverse
          ++ [Int.ofNat (n + 1)]) :=
      USortableIn_succ_append k n _ hk
    have hlift' : USortableIn k (n + 1) (revBlock (revBlock pi 0 p) 0 n) := by
      rw [hrev2]
      exact hlift
    have s1 : USortableIn (k + 1) (n + 1) (revBlock pi 0 p) :=
      USortableIn.step k (n + 1) _ 0 n (Nat.zero_le n) hn_lt hlift'
    exact ⟨k + 1 + 1, USortableIn.step (k + 1) (n + 1) _ 0 p (Nat.zero_le p) hp_lt s1⟩

/-- Decidability of sortability for `Nat.find` (classical). -/
noncomputable instance decSortableIn (n : Nat) (pi : List Int) :
    DecidablePred (fun k => USortableIn k n pi) :=
  Classical.decPred _

/-- Unsigned reversal distance as a genuine minimum (Shamir-Peer sec. 11.2). -/
noncomputable def udist (n : Nat) (pi : List Int) (h : UValid n pi) : Nat := Nat.find (sortable n pi h)

/-- The consecutive integers `n + 1` and `n + 2` have no gap. -/
theorem isGap_consec (n : Nat) : isGap (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) = 0 := by
  have hd : (Int.ofNat (n + 2) - Int.ofNat (n + 1)).natAbs = 1 := by
    have h1 : Int.ofNat (n + 2) = Int.ofNat n + 2 := by simp
    have h2 : Int.ofNat (n + 1) = Int.ofNat n + 1 := by simp
    rw [h1, h2]
    have h3 : (Int.ofNat n + 2 - (Int.ofNat n + 1) : Int) = 1 := by omega
    rw [h3]
    rfl
  unfold isGap
  rw [hd]
  rfl

/-- Framed identity extends by one on the right. -/
theorem framed_succ (n : Nat) :
    (0 :: (List.Icc 1 (n + 1)).map Int.ofNat ++ [Int.ofNat (n + 1 + 1)])
      = (0 :: (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)])
        ++ [Int.ofNat (n + 1 + 1)] := by
  rw [target_succ]
  have h0 : ∀ X : List Int, (0 :: X) = [0] ++ X := fun X => rfl
  conv => lhs; rw [h0]
  conv => rhs; rw [h0]
  simp only [List.append_assoc]

/-- Last element of the framed identity. -/
theorem framed_getLast (n : Nat) (h : (0 :: (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)]) ≠ []) :
    (0 :: (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)]).getLast h
      = Int.ofNat (n + 1) := by
  have hsingle : ([Int.ofNat (n + 1)] : List Int) ≠ [] := by simp
  have e1 : ((0 :: (List.Icc 1 n).map Int.ofNat) ++ [Int.ofNat (n + 1)]).getLast h
      = ([Int.ofNat (n + 1)] : List Int).getLast hsingle :=
    List.getLast_append_right hsingle
  have e2 : ([Int.ofNat (n + 1)] : List Int).getLast hsingle = Int.ofNat (n + 1) :=
    List.getLast_singleton hsingle
  exact e1.trans e2

/-- The identity has no breakpoints. Cf. Shamir-Peer Lecture 11 §11.2. -/
theorem ubreaks_target (n : Nat) : ubreaks n ((List.Icc 1 n).map Int.ofNat) = 0 := by
  induction n with
  | zero =>
    have hT0 : (List.Icc 1 0).map Int.ofNat = [] := rfl
    rw [hT0]
    rfl
  | succ n ih =>
    have hfr := framed_succ n
    have hne : (0 :: (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)]) ≠ [] := by simp
    have hsingle : ([Int.ofNat (n + 1 + 1)] : List Int) ≠ [] := by simp
    have happ := gapCount_append
      (0 :: (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)])
      [Int.ofNat (n + 1 + 1)] hne hsingle
    have hlast := framed_getLast n hne
    have hhead : ([Int.ofNat (n + 1 + 1)] : List Int).head hsingle = Int.ofNat (n + 1 + 1) :=
      List.head_singleton
    have hgap0 : gapCount [Int.ofNat (n + 1 + 1)] = 0 := rfl
    have hconsec := isGap_consec n
    simp only [ubreaks] at ih ⊢
    rw [hfr, happ, hlast, hhead, hgap0, hconsec, ih]

/-- Breakpoint lower bound by sortability (Shamir-Peer Lecture 11 sec. 11.2 Theorem 11.2). -/
theorem ubreaks_le_two_mul_of_sortableIn {k n : Nat} {pi : List Int} (h : USortableIn k n pi) : ubreaks n pi <= 2 * k := by
  induction h with
  | done n =>
    rw [ubreaks_target]
  | step k n pi i j hij hlt _ ih =>
    have hle := ubreaks_le_revBlock n pi i j hij hlt
    omega

/-- Breakpoint lower bound by distance (Shamir-Peer Lecture 11 sec. 11.2 Theorem 11.2). -/
theorem ub_le_two_mul_udist {n : Nat} {pi : List Int} (h : UValid n pi) : ubreaks n pi <= 2 * udist n pi h := by
  have hsort : USortableIn (udist n pi h) n pi := Nat.find_spec (sortable n pi h)
  exact ubreaks_le_two_mul_of_sortableIn hsort

/-- Unique zero distance is the identity (derived unique-zero; cf. Shamir-Peer Lecture 11 sec. 11.2). -/
theorem udist_eq_zero_iff {n : Nat} {pi : List Int} (h : UValid n pi) :
    udist n pi h = 0 <-> pi = (List.Icc 1 n).map Int.ofNat := by
  constructor
  · intro hz
    have hsort : USortableIn (udist n pi h) n pi := Nat.find_spec (sortable n pi h)
    rw [hz] at hsort
    cases hsort
    rfl
  · intro hpi
    have h0 : USortableIn 0 n pi := by
      rw [hpi]
      exact USortableIn.done n
    have hle : udist n pi h ≤ 0 := Nat.find_min' (sortable n pi h) h0
    omega

/-- Gap indicator vanishes exactly on adjacent values. -/
theorem isGap_eq_zero_iff (a b : Int) : isGap a b = 0 ↔ (b - a).natAbs = 1 := by
  unfold isGap
  by_cases hc : (b - a).natAbs = 1
  · simp [hc]
  · simp [hc]

/-- Absolute value one means plus or minus one. -/
theorem natAbs_eq_one_iff (x : Int) : x.natAbs = 1 ↔ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    cases x with
    | ofNat n =>
      simp at h
      subst h
      left
      rfl
    | negSucc n =>
      simp at h
      have hn : n = 0 := by omega
      subst hn
      right
      rfl
  · intro h
    cases h with
    | inl h1 => rw [h1]; rfl
    | inr h2 => rw [h2]; rfl

/-- A vanishing gap into a successor forces the predecessor or its successor. -/
theorem isGap_up_cases (k : Nat) (x : Int) (h : isGap x (Int.ofNat (k + 1)) = 0) :
    x = Int.ofNat k ∨ x = Int.ofNat (k + 2) := by
  have hnat : (Int.ofNat (k + 1) - x).natAbs = 1 := (isGap_eq_zero_iff _ _).mp h
  have hdisj : Int.ofNat (k + 1) - x = 1 ∨ Int.ofNat (k + 1) - x = -1 :=
    (natAbs_eq_one_iff _).mp hnat
  have h1 : Int.ofNat (k + 1) = Int.ofNat k + 1 := by simp
  have h2 : Int.ofNat (k + 2) = Int.ofNat k + 2 := by simp
  cases hdisj with
  | inl hpos =>
    left
    rw [h1] at hpos
    omega
  | inr hneg =>
    right
    rw [h1] at hneg
    rw [h2]
    omega

/-- A vanishing append count forces vanishing pieces and junction. -/
theorem gapCount_append_eq_zero (l₁ l₂ : List Int) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (h0 : gapCount (l₁ ++ l₂) = 0) :
    gapCount l₁ = 0 ∧ gapCount l₂ = 0 ∧ isGap (l₁.getLast h₁) (l₂.head h₂) = 0 := by
  have e := gapCount_append l₁ l₂ h₁ h₂
  omega

/-- A nonempty list splits off its last element. -/
theorem exists_init_last (l : List Int) (h : l ≠ []) :
    ∃ init x, l = init ++ [x] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    cases t with
    | nil => exact ⟨[], a, rfl⟩
    | cons b t' =>
      have ht : b :: t' ≠ [] := by simp
      obtain ⟨init', x, heq⟩ := exists_init_last (b :: t') ht
      exact ⟨a :: init', x, by rw [heq]; rfl⟩

/-- Membership in the identity target is bounded above. -/
theorem mem_target_upper (n : Nat) (x : Int) (h : x ∈ (List.Icc 1 n).map Int.ofNat) :
    ∃ m, m ≤ n ∧ x = Int.ofNat m := by
  induction n generalizing x with
  | zero =>
    have hT0 : (List.Icc 1 0).map Int.ofNat = [] := rfl
    rw [hT0] at h
    exact absurd h List.not_mem_nil
  | succ n ih =>
    rw [target_succ, List.mem_append] at h
    cases h with
    | inl hmem =>
      obtain ⟨m, hmle, heq⟩ := ih x hmem
      exact ⟨m, by omega, heq⟩
    | inr hsing =>
      have heq : x = Int.ofNat (n + 1) := List.mem_singleton.mp hsing
      exact ⟨n + 1, by omega, heq⟩

/-- Last element of a framed prefix. -/
theorem framed_init_getLast (init : List Int) (x : Int)
    (h : (0 :: init ++ [x]) ≠ []) :
    (0 :: init ++ [x]).getLast h = x := by
  have hsingle : ([x] : List Int) ≠ [] := by simp
  have e1 : ((0 :: init) ++ [x]).getLast h
      = ([x] : List Int).getLast hsingle :=
    List.getLast_append_right hsingle
  have e2 : ([x] : List Int).getLast hsingle = x :=
    List.getLast_singleton hsingle
  exact e1.trans e2

/-- Unique zero breakpoints is the identity (derived unique-zero; cf. Shamir-Peer Lecture 11 sec. 11.2). -/
theorem ubreaks_eq_zero_iff {n : Nat} {pi : List Int} (h : UValid n pi) :
    ubreaks n pi = 0 <-> pi = (List.Icc 1 n).map Int.ofNat := by
  constructor
  · intro hb
    induction n generalizing pi with
    | zero =>
      have hT0 : (List.Icc 1 0).map Int.ofNat = [] := rfl
      unfold UValid at h
      rw [hT0] at h
      have hnil : pi = [] := List.Perm.eq_nil h
      rw [hnil]
      exact hT0.symm
    | succ n ih =>
      have hlen : pi.length = n + 1 :=
        (List.Perm.length_eq h).trans (target_length (n + 1))
      have hne : pi ≠ [] := by
        intro hcon
        rw [hcon] at hlen
        simp at hlen
      obtain ⟨init, x, rfl⟩ := exists_init_last pi hne
      have hne1 : (0 :: init ++ [x]) ≠ [] := by simp
      have hsingle2 : ([Int.ofNat (n + 1 + 1)] : List Int) ≠ [] := by simp
      have hb' : gapCount ((0 :: init ++ [x]) ++ [Int.ofNat (n + 1 + 1)]) = 0 := hb
      obtain ⟨hgap1, _, hgapJ⟩ :=
        gapCount_append_eq_zero (0 :: init ++ [x]) [Int.ofNat (n + 1 + 1)] hne1 hsingle2 hb'
      have hlast : (0 :: init ++ [x]).getLast hne1 = x := framed_init_getLast init x hne1
      have hhead : ([Int.ofNat (n + 1 + 1)] : List Int).head hsingle2 = Int.ofNat (n + 1 + 1) :=
        List.head_singleton
      rw [hlast, hhead] at hgapJ
      have hx_eq : x = Int.ofNat (n + 1) := by
        have hx_cases := isGap_up_cases (n + 1) x hgapJ
        cases hx_cases with
        | inl hx1 => exact hx1
        | inr hx3 =>
          have hxmem : x ∈ init ++ [x] := by simp
          have hxtarg : x ∈ (List.Icc 1 (n + 1)).map Int.ofNat :=
            (List.Perm.mem_iff h).mp hxmem
          obtain ⟨m, hmle, heq⟩ := mem_target_upper (n + 1) x hxtarg
          have heq2 : Int.ofNat m = Int.ofNat (n + 1 + 2) := heq.symm.trans hx3
          have hm_eq : m = n + 1 + 2 := Int.ofNat_inj.mp heq2
          have hfalse : False := by omega
          exact False.elim hfalse
      subst hx_eq
      have hub0 : ubreaks n init = 0 := hgap1
      have htarget : (List.Icc 1 (n + 1)).map Int.ofNat
          = (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)] := target_succ n
      unfold UValid at h
      rw [htarget] at h
      have hinit : UValid n init := (List.perm_append_right_iff _).mp h
      have hinit_eq : init = (List.Icc 1 n).map Int.ofNat := ih hinit hub0
      rw [hinit_eq, target_succ]
  · intro hpi
    rw [hpi, ubreaks_target]

/-- Signed validity: absolute values of `pi` permute `1..n`.
Cf. the signed permutations of Shamir-Peer Lecture 11 signed setting. -/
def SValid (n : Nat) (pi : List Int) : Prop :=
  pi.map Int.natAbs ~ List.Icc 1 n

/-- Doubling one signed element: `+x -> [2x-1, 2x]`, `-x -> [2x, 2x-1]` (`x = |entry|`).
Meant for the nonzero entries of a signed permutation; the entry `0` falls in the first case,
`dblOne 0 = [-1, 0]`.
Cf. the doubled unsigned permutation of Shamir-Peer Lecture 11 signed setting. -/
def dblOne (x : Int) : List Int :=
  if 0 ≤ x then [2 * (x.natAbs : Int) - 1, 2 * (x.natAbs : Int)]
  else [2 * (x.natAbs : Int), 2 * (x.natAbs : Int) - 1]

/-- Doubling of a list: the concatenation of the doubled pairs `dblOne` of its entries. For a
valid signed permutation of `1..n` it is an unsigned permutation of `1..2n` (`dbl_valid`). -/
def dbl (pi : List Int) : List Int := pi.flatMap dblOne

/-- Directed gap count: adjacent pairs with `b - a != 1`.
Cf. the signed directed breakpoints of Shamir-Peer Lecture 11 signed setting. -/
def dirGapCount : List Int -> Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if b - a = 1 then 0 else 1) + dirGapCount (b :: t)

/-- Signed breakpoint count with sentinels `0` and `n + 1`.
Cf. the signed breakpoint count of Shamir-Peer Lecture 11 signed setting. -/
def sbreaks (n : Nat) (pi : List Int) : Nat := dirGapCount (0 :: pi ++ [Int.ofNat (n + 1)])

/-- Directed-gap indicator: `0` when `b - a = 1`, else `1`.
Cf. the signed directed breakpoints of Shamir-Peer Lecture 11 signed setting. -/
def isDirGap (a b : Int) : Nat :=
  if b - a = 1 then 0 else 1

/-- First element of the doubled pair. Meant for nonzero `x`; `dblFirst 0 = -1`.
Cf. the doubled unsigned permutation of Shamir-Peer Lecture 11 signed setting. -/
def dblFirst (x : Int) : Int :=
  if 0 ≤ x then 2 * (x.natAbs : Int) - 1 else 2 * (x.natAbs : Int)

/-- Last element of the doubled pair. Meant for nonzero `x`; `dblLast 0 = 0`.
Cf. the doubled unsigned permutation of Shamir-Peer Lecture 11 signed setting. -/
def dblLast (x : Int) : Int :=
  if 0 ≤ x then 2 * (x.natAbs : Int) else 2 * (x.natAbs : Int) - 1

theorem dblOne_eq_first_last (x : Int) : dblOne x = [dblFirst x, dblLast x] := by
  unfold dblOne dblFirst dblLast
  split <;> rfl

theorem dblOne_of_nonneg (x : Int) (h : 0 ≤ x) :
    dblOne x = [2 * (x.natAbs : Int) - 1, 2 * (x.natAbs : Int)] := by
  unfold dblOne
  simp [h]

theorem dblOne_of_neg (x : Int) (h : x < 0) :
    dblOne x = [2 * (x.natAbs : Int), 2 * (x.natAbs : Int) - 1] := by
  have hn : ¬ 0 ≤ x := by omega
  unfold dblOne
  simp [hn]

theorem dblFirst_of_nonneg (x : Int) (h : 0 ≤ x) :
    dblFirst x = 2 * (x.natAbs : Int) - 1 := by
  unfold dblFirst
  simp [h]

theorem dblFirst_of_neg (x : Int) (h : x < 0) :
    dblFirst x = 2 * (x.natAbs : Int) := by
  have hn : ¬ 0 ≤ x := by omega
  unfold dblFirst
  simp [hn]

theorem dblLast_of_nonneg (x : Int) (h : 0 ≤ x) :
    dblLast x = 2 * (x.natAbs : Int) := by
  unfold dblLast
  simp [h]

theorem dblLast_of_neg (x : Int) (h : x < 0) :
    dblLast x = 2 * (x.natAbs : Int) - 1 := by
  have hn : ¬ 0 ≤ x := by omega
  unfold dblLast
  simp [hn]

theorem isDirGap_le_one (a b : Int) : isDirGap a b ≤ 1 := by
  unfold isDirGap
  split <;> omega

theorem isDirGap_eq_zero_iff (a b : Int) : isDirGap a b = 0 ↔ b - a = 1 := by
  unfold isDirGap
  by_cases hc : b - a = 1
  · simp [hc]
  · simp [hc]

theorem dirGapCount_cons_of_ne (x : Int) (l : List Int) (h : l ≠ []) :
    dirGapCount (x :: l) = isDirGap x (l.head h) + dirGapCount l := by
  cases l with
  | nil => exact absurd rfl h
  | cons y t => rfl

theorem dirGapCount_append (l₁ l₂ : List Int) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    dirGapCount (l₁ ++ l₂)
      = dirGapCount l₁ + dirGapCount l₂ + isDirGap (l₁.getLast h₁) (l₂.head h₂) := by
  revert h₁
  induction l₁ with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro h₁
    cases t with
    | nil =>
      rw [List.getLast_singleton]
      have h1 : ([a] : List Int) ++ l₂ = a :: l₂ := rfl
      rw [h1, dirGapCount_cons_of_ne _ _ h₂]
      have h0 : dirGapCount [a] = 0 := rfl
      omega
    | cons b t' =>
      have hbt' : b :: t' ≠ [] := by simp
      have happ : (a :: b :: t') ++ l₂ = a :: ((b :: t') ++ l₂) := rfl
      have hbt : (b :: t') ++ l₂ ≠ [] := List.append_ne_nil_of_left_ne_nil hbt' l₂
      rw [happ, dirGapCount_cons_of_ne _ _ hbt, dirGapCount_cons_of_ne _ _ hbt',
        List.head_append_left hbt', List.head_cons, ih hbt', List.getLast_cons hbt']
      omega

/-- Inside each doubled pair the absolute gap is `1` (never a breakpoint).
Cf. the doubled unsigned permutation of Shamir-Peer Lecture 11 signed setting. -/
theorem inside_gap (x : Int) : isGap (dblFirst x) (dblLast x) = 0 := by
  by_cases h : 0 ≤ x
  · rw [dblFirst_of_nonneg x h, dblLast_of_nonneg x h]
    have hd : 2 * (x.natAbs : Int) - (2 * (x.natAbs : Int) - 1) = 1 := by omega
    unfold isGap
    rw [hd]
    rfl
  · have hlt : x < 0 := by omega
    rw [dblFirst_of_neg x hlt, dblLast_of_neg x hlt]
    have hd : (2 * (x.natAbs : Int) - 1) - 2 * (x.natAbs : Int) = -1 := by omega
    unfold isGap
    rw [hd]
    rfl

/-- A member can be pulled to the front up to permutation. -/
theorem exists_perm_cons_of_mem (x : Int) (l : List Int) (h : x ∈ l) :
    ∃ xs, l ~ x :: xs := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp at h
    cases h with
    | inl heq =>
      subst heq
      exact ⟨ys, List.Perm.rfl⟩
    | inr hmem =>
      obtain ⟨xs, hperm⟩ := ih hmem
      have h1 : (y :: ys) ~ (y :: x :: xs) := List.Perm.cons y hperm
      have h2 : (y :: x :: xs) ~ (x :: y :: xs) := List.Perm.swap x y xs
      exact ⟨y :: xs, h1.trans h2⟩

/-- The top element belongs to its own interval. -/
theorem mem_Icc_self_succ (n : Nat) : (n + 1) ∈ List.Icc 1 (n + 1) := by
  rw [Icc_one_succ]
  simp

/-- The doubled identity target extends by two on the right. -/
theorem target_double_succ (n : Nat) :
    (List.Icc 1 (2 * (n + 1))).map Int.ofNat
      = (List.Icc 1 (2 * n)).map Int.ofNat
        ++ [Int.ofNat (2 * n + 1), Int.ofNat (2 * n + 2)] := by
  have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  rw [h2, target_succ]
  have h3 : 2 * n + 1 = (2 * n) + 1 := by omega
  rw [h3, target_succ]
  have heq : (2 * n + 1) + 1 = 2 * n + 2 := by omega
  rw [heq]
  simp [List.append_assoc]

/-- Doubling an element of absolute value `n + 1` permutes the top pair. -/
theorem dblOne_perm_target_ext (x : Int) (n : Nat) (habs : x.natAbs = n + 1) :
    dblOne x ~ [Int.ofNat (2 * n + 1), Int.ofNat (2 * n + 2)] := by
  by_cases h : 0 ≤ x
  · rw [dblOne_of_nonneg x h, habs]
    have e1 : 2 * (((n + 1 : Nat)) : Int) - 1 = Int.ofNat (2 * n + 1) := by
      simp
      omega
    have e2 : 2 * (((n + 1 : Nat)) : Int) = Int.ofNat (2 * n + 2) := by
      simp
      omega
    rw [e1, e2]
  · have hlt : x < 0 := by omega
    rw [dblOne_of_neg x hlt, habs]
    have e1 : 2 * (((n + 1 : Nat)) : Int) - 1 = Int.ofNat (2 * n + 1) := by
      simp
      omega
    have e2 : 2 * (((n + 1 : Nat)) : Int) = Int.ofNat (2 * n + 2) := by
      simp
      omega
    rw [e1, e2]
    exact List.Perm.swap _ _ []

theorem dbl_valid {n : Nat} {pi : List Int} (h : SValid n pi) : UValid (2 * n) (dbl pi) := by
  induction n generalizing pi with
  | zero =>
    unfold SValid at h
    unfold UValid
    have hT0 : List.Icc 1 0 = [] := rfl
    rw [hT0] at h
    have hnil_map : pi.map Int.natAbs = [] := List.Perm.eq_nil h
    have hnil : pi = [] := by
      cases pi with
      | nil => rfl
      | cons x xs =>
        simp at hnil_map
    subst hnil
    have h0 : 2 * 0 = 0 := by omega
    rw [h0, hT0]
    unfold dbl
    simp [List.flatMap_nil, List.map_nil]
  | succ n ih =>
    unfold SValid at h
    unfold UValid
    have hmem : (n + 1) ∈ List.Icc 1 (n + 1) := mem_Icc_self_succ n
    have hmem_map : (n + 1) ∈ pi.map Int.natAbs := (List.Perm.mem_iff h).mpr hmem
    obtain ⟨x, hxmem, hxabs⟩ := List.mem_map.mp hmem_map
    obtain ⟨xs, hperm_pi⟩ := exists_perm_cons_of_mem x pi hxmem
    have hperm_map := List.Perm.map Int.natAbs hperm_pi
    simp at hperm_map
    rw [hxabs] at hperm_map
    have hIcc : List.Icc 1 (n + 1) = List.Icc 1 n ++ [n + 1] := Icc_one_succ n
    rw [hIcc] at h
    have hmid : ((n + 1) :: xs.map Int.natAbs) ~ (List.Icc 1 n ++ [n + 1]) :=
      hperm_map.symm.trans h
    have ha : (List.Icc 1 n ++ [n + 1]) ~ ([n + 1] ++ List.Icc 1 n) :=
      List.perm_append_comm
    have heq : ([n + 1] ++ List.Icc 1 n) = ((n + 1) :: List.Icc 1 n) := rfl
    rw [heq] at ha
    have hcons : ((n + 1) :: xs.map Int.natAbs) ~ ((n + 1) :: List.Icc 1 n) :=
      hmid.trans ha
    have htail : xs.map Int.natAbs ~ List.Icc 1 n := List.Perm.cons_inv hcons
    have ih_perm : UValid (2 * n) (dbl xs) := ih htail
    unfold UValid at ih_perm
    have hperm_dbl := List.Perm.flatMap_right dblOne hperm_pi
    unfold dbl at hperm_dbl ⊢
    rw [List.flatMap_cons] at hperm_dbl
    have hOne := dblOne_perm_target_ext x n hxabs
    have happend := List.Perm.append hOne ih_perm
    have htarget := target_double_succ n
    have hcomm2 : ([Int.ofNat (2 * n + 1), Int.ofNat (2 * n + 2)]
        ++ (List.Icc 1 (2 * n)).map Int.ofNat)
        ~ ((List.Icc 1 (2 * n)).map Int.ofNat
          ++ [Int.ofNat (2 * n + 1), Int.ofNat (2 * n + 2)]) :=
      List.perm_append_comm
    have hchain := hperm_dbl.trans (happend.trans hcomm2)
    rw [htarget]
    exact hchain

/-- Cast of `natAbs` recovers a nonnegative integer. -/
theorem natAbs_cast_of_nonneg (x : Int) (h : 0 ≤ x) : ((x.natAbs : Nat) : Int) = x :=
  Int.ofNat_natAbs_of_nonneg h

/-- Cast of `natAbs` negates a negative integer. -/
theorem natAbs_cast_of_neg (x : Int) (h : x < 0) : ((x.natAbs : Nat) : Int) = -x := by
  have hpos : 0 ≤ -x := by omega
  have e1 : (((-x).natAbs : Nat) : Int) = -x := Int.ofNat_natAbs_of_nonneg hpos
  have e2 : (-x).natAbs = x.natAbs := Int.natAbs_neg x
  rw [e2] at e1
  exact e1

/-- Between consecutive doubled pairs the absolute gap matches the directed gap, for entries with
`1 ≤ p.natAbs`, `1 ≤ q.natAbs` and `p.natAbs ≠ q.natAbs`: `|dblFirst q - dblLast p| = 1` iff
`q - p = 1`.
Cf. the signed directed correspondence of Shamir-Peer Lecture 11 signed setting. -/
theorem between_gap (p q : Int) (hp : 1 ≤ p.natAbs) (hq : 1 ≤ q.natAbs)
    (hne : p.natAbs ≠ q.natAbs) :
    isGap (dblLast p) (dblFirst q) = isDirGap p q := by
  by_cases hp0 : 0 ≤ p <;> by_cases hq0 : 0 ≤ q
  · rw [dblLast_of_nonneg p hp0, dblFirst_of_nonneg q hq0]
    have hp_eq : ((p.natAbs : Nat) : Int) = p := natAbs_cast_of_nonneg p hp0
    have hq_eq : ((q.natAbs : Nat) : Int) = q := natAbs_cast_of_nonneg q hq0
    have ha := isGap_le_one (2 * ((p.natAbs : Nat) : Int)) (2 * ((q.natAbs : Nat) : Int) - 1)
    have hb := isDirGap_le_one p q
    have hiff : isGap (2 * ((p.natAbs : Nat) : Int)) (2 * ((q.natAbs : Nat) : Int) - 1) = 0
        ↔ isDirGap p q = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        left
        omega
    omega
  · have hqlt : q < 0 := by omega
    rw [dblLast_of_nonneg p hp0, dblFirst_of_neg q hqlt]
    have hp_eq : ((p.natAbs : Nat) : Int) = p := natAbs_cast_of_nonneg p hp0
    have hq_eq : ((q.natAbs : Nat) : Int) = -q := natAbs_cast_of_neg q hqlt
    have ha := isGap_le_one (2 * ((p.natAbs : Nat) : Int)) (2 * ((q.natAbs : Nat) : Int))
    have hb := isDirGap_le_one p q
    have hiff : isGap (2 * ((p.natAbs : Nat) : Int)) (2 * ((q.natAbs : Nat) : Int)) = 0
        ↔ isDirGap p q = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        left
        omega
    omega
  · have hplt : p < 0 := by omega
    rw [dblLast_of_neg p hplt, dblFirst_of_nonneg q hq0]
    have hp_eq : ((p.natAbs : Nat) : Int) = -p := natAbs_cast_of_neg p hplt
    have hq_eq : ((q.natAbs : Nat) : Int) = q := natAbs_cast_of_nonneg q hq0
    have ha := isGap_le_one (2 * ((p.natAbs : Nat) : Int) - 1) (2 * ((q.natAbs : Nat) : Int) - 1)
    have hb := isDirGap_le_one p q
    have hiff : isGap (2 * ((p.natAbs : Nat) : Int) - 1) (2 * ((q.natAbs : Nat) : Int) - 1) = 0
        ↔ isDirGap p q = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        left
        omega
    omega
  · have hplt : p < 0 := by omega
    have hqlt : q < 0 := by omega
    rw [dblLast_of_neg p hplt, dblFirst_of_neg q hqlt]
    have hp_eq : ((p.natAbs : Nat) : Int) = -p := natAbs_cast_of_neg p hplt
    have hq_eq : ((q.natAbs : Nat) : Int) = -q := natAbs_cast_of_neg q hqlt
    have ha := isGap_le_one (2 * ((p.natAbs : Nat) : Int) - 1) (2 * ((q.natAbs : Nat) : Int))
    have hb := isDirGap_le_one p q
    have hiff : isGap (2 * ((p.natAbs : Nat) : Int) - 1) (2 * ((q.natAbs : Nat) : Int)) = 0
        ↔ isDirGap p q = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        right
        omega
    omega

/-- At the left sentinel the absolute gap matches the directed gap, for a nonzero entry `x`.
Cf. the signed directed correspondence of Shamir-Peer Lecture 11 signed setting. -/
theorem left_gap (x : Int) (hx : 1 ≤ x.natAbs) :
    isGap 0 (dblFirst x) = isDirGap 0 x := by
  by_cases h0 : 0 ≤ x
  · rw [dblFirst_of_nonneg x h0]
    have hp_eq : ((x.natAbs : Nat) : Int) = x := natAbs_cast_of_nonneg x h0
    have ha := isGap_le_one 0 (2 * ((x.natAbs : Nat) : Int) - 1)
    have hb := isDirGap_le_one 0 x
    have hiff : isGap 0 (2 * ((x.natAbs : Nat) : Int) - 1) = 0 ↔ isDirGap 0 x = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        left
        omega
    omega
  · have hlt : x < 0 := by omega
    rw [dblFirst_of_neg x hlt]
    have hp_eq : ((x.natAbs : Nat) : Int) = -x := natAbs_cast_of_neg x hlt
    have ha := isGap_le_one 0 (2 * ((x.natAbs : Nat) : Int))
    have hb := isDirGap_le_one 0 x
    have hiff : isGap 0 (2 * ((x.natAbs : Nat) : Int)) = 0 ↔ isDirGap 0 x = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        left
        omega
    omega

/-- At the right sentinel the absolute gap matches the directed gap, for an entry with
`x.natAbs ≤ n`.
Cf. the signed directed correspondence of Shamir-Peer Lecture 11 signed setting. -/
theorem right_gap (x : Int) (n : Nat) (hxle : x.natAbs ≤ n) :
    isGap (dblLast x) (Int.ofNat (2 * n + 1)) = isDirGap x (Int.ofNat (n + 1)) := by
  have e1 : Int.ofNat (2 * n + 1) = 2 * (((n : Nat)) : Int) + 1 := by simp
  have e2 : Int.ofNat (n + 1) = (((n : Nat)) : Int) + 1 := by simp
  by_cases h0 : 0 ≤ x
  · rw [dblLast_of_nonneg x h0, e1, e2]
    have hp_eq : ((x.natAbs : Nat) : Int) = x := natAbs_cast_of_nonneg x h0
    have ha := isGap_le_one (2 * ((x.natAbs : Nat) : Int)) (2 * (((n : Nat)) : Int) + 1)
    have hb := isDirGap_le_one x ((((n : Nat)) : Int) + 1)
    have hiff : isGap (2 * ((x.natAbs : Nat) : Int)) (2 * (((n : Nat)) : Int) + 1) = 0
        ↔ isDirGap x ((((n : Nat)) : Int) + 1) = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        left
        omega
    omega
  · have hlt : x < 0 := by omega
    rw [dblLast_of_neg x hlt, e1, e2]
    have hp_eq : ((x.natAbs : Nat) : Int) = -x := natAbs_cast_of_neg x hlt
    have ha := isGap_le_one (2 * ((x.natAbs : Nat) : Int) - 1) (2 * (((n : Nat)) : Int) + 1)
    have hb := isDirGap_le_one x ((((n : Nat)) : Int) + 1)
    have hiff : isGap (2 * ((x.natAbs : Nat) : Int) - 1) (2 * (((n : Nat)) : Int) + 1) = 0
        ↔ isDirGap x ((((n : Nat)) : Int) + 1) = 0 := by
      rw [isGap_eq_zero_iff, isDirGap_eq_zero_iff, natAbs_eq_one_iff]
      constructor
      · intro hdisj
        cases hdisj with
        | inl h1 => omega
        | inr h2 => omega
      · intro hq1
        left
        omega
    omega

/-- Empty signed and doubled framings agree. -/
theorem empty_gap (n : Nat) :
    isDirGap 0 (Int.ofNat (n + 1)) = isGap 0 (Int.ofNat (2 * n + 1)) := by
  have e1 : Int.ofNat (n + 1) = (((n : Nat)) : Int) + 1 := by simp
  have e2 : Int.ofNat (2 * n + 1) = 2 * (((n : Nat)) : Int) + 1 := by simp
  rw [e1, e2]
  have ha := isDirGap_le_one 0 ((((n : Nat)) : Int) + 1)
  have hb := isGap_le_one 0 (2 * (((n : Nat)) : Int) + 1)
  have hiff : isDirGap 0 ((((n : Nat)) : Int) + 1) = 0
      ↔ isGap 0 (2 * (((n : Nat)) : Int) + 1) = 0 := by
    rw [isDirGap_eq_zero_iff, isGap_eq_zero_iff, natAbs_eq_one_iff]
    constructor
    · intro hq1
      left
      omega
    · intro hdisj
      cases hdisj with
      | inl h1 => omega
      | inr h2 => omega
  omega

/-- Membership in the identity interval is bounded. -/
theorem mem_Icc_bounds (n k : Nat) (h : k ∈ List.Icc 1 n) : 1 ≤ k ∧ k ≤ n := by
  induction n generalizing k with
  | zero =>
    have hT0 : List.Icc 1 0 = [] := rfl
    rw [hT0] at h
    simp at h
  | succ n ih =>
    rw [Icc_one_succ, List.mem_append] at h
    cases h with
    | inl hmem =>
      obtain ⟨h1, hle⟩ := ih k hmem
      exact ⟨h1, by omega⟩
    | inr hsing =>
      have heq : k = n + 1 := List.mem_singleton.mp hsing
      subst heq
      constructor <;> omega

/-- The identity interval has no duplicates. -/
theorem Icc_nodup (n : Nat) : (List.Icc 1 n).Nodup := by
  unfold List.Icc
  exact List.nodup_range' 1 (by omega)

/-- All absolute values lie in `1..n`. -/
def MemRange (n : Nat) (pi : List Int) : Prop :=
  ∀ x ∈ pi, 1 ≤ x.natAbs ∧ x.natAbs ≤ n

/-- Validity implies the range condition. -/
theorem SValid_imp_memRange (n : Nat) (pi : List Int) (h : SValid n pi) :
    MemRange n pi := by
  unfold SValid at h
  intro x hx
  have hmap : x.natAbs ∈ pi.map Int.natAbs := List.mem_map_of_mem hx
  have hIcc : x.natAbs ∈ List.Icc 1 n := (List.Perm.mem_iff h).mp hmap
  exact mem_Icc_bounds n _ hIcc

/-- Validity implies distinct absolute values. -/
theorem SValid_imp_nodup (n : Nat) (pi : List Int) (h : SValid n pi) :
    (pi.map Int.natAbs).Nodup := by
  unfold SValid at h
  have hIcc := Icc_nodup n
  have hiff := List.Perm.nodup_iff h
  exact hiff.mpr hIcc

/-- Tail correspondence from a signed head to a doubled head: if the entries of `x :: xs` have
pairwise distinct absolute values in `1..n`, the directed gap count of `x :: xs ++ [n + 1]`
equals the gap count of `dblLast x :: dbl xs ++ [2 * n + 1]`.
Cf. the signed directed correspondence of Shamir-Peer Lecture 11 signed setting. -/
theorem aux_correspondence (n : Nat) (x : Int) (xs : List Int)
    (hmem : MemRange n (x :: xs)) (hnodup : ((x :: xs).map Int.natAbs).Nodup) :
    dirGapCount (x :: xs ++ [Int.ofNat (n + 1)])
      = gapCount (dblLast x :: dbl xs ++ [Int.ofNat (2 * n + 1)]) := by
  induction xs generalizing x with
  | nil =>
    have hxmem : x ∈ x :: ([] : List Int) := by simp
    obtain ⟨hx1, hxle⟩ := hmem x hxmem
    have hr := right_gap x n hxle
    have eL : dirGapCount [x, Int.ofNat (n + 1)] = isDirGap x (Int.ofNat (n + 1)) := rfl
    have eR : gapCount [dblLast x, Int.ofNat (2 * n + 1)]
        = isGap (dblLast x) (Int.ofNat (2 * n + 1)) := rfl
    show dirGapCount [x, Int.ofNat (n + 1)]
      = gapCount [dblLast x, Int.ofNat (2 * n + 1)]
    rw [eL, eR]
    exact hr.symm
  | cons y ys ih =>
    have hmap2 : ((x :: y :: ys).map Int.natAbs)
        = x.natAbs :: ((y :: ys).map Int.natAbs) := rfl
    rw [hmap2, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hnodup_tail⟩ := hnodup
    have hmem_tail : MemRange n (y :: ys) := by
      intro z hz
      apply hmem
      exact List.mem_cons_of_mem x hz
    have hxmem : x ∈ x :: y :: ys := by simp
    have hymem_list : y ∈ x :: y :: ys := by simp
    obtain ⟨hx1, hxle⟩ := hmem x hxmem
    obtain ⟨hy1, hyle⟩ := hmem y hymem_list
    have hymem : y.natAbs ∈ ((y :: ys).map Int.natAbs) :=
      List.mem_map_of_mem (by simp)
    have hne : x.natAbs ≠ y.natAbs := by
      intro heq
      apply hnotin
      rw [heq]
      exact hymem
    have hbet := between_gap x y hx1 hy1 hne
    have hins := inside_gap y
    have hIH := ih y hmem_tail hnodup_tail
    have eL : dirGapCount (x :: y :: ys ++ [Int.ofNat (n + 1)])
        = isDirGap x y + dirGapCount (y :: ys ++ [Int.ofNat (n + 1)]) := rfl
    have hdbl : dbl (y :: ys) = [dblFirst y, dblLast y] ++ dbl ys := by
      unfold dbl
      rw [List.flatMap_cons, dblOne_eq_first_last]
    have hrw : (([dblFirst y, dblLast y] ++ dbl ys) ++ [Int.ofNat (2 * n + 1)])
        = dblFirst y :: dblLast y :: (dbl ys ++ [Int.ofNat (2 * n + 1)]) := by
      rw [List.append_assoc]
      rfl
    rw [hdbl] at ⊢
    have hcons : ((dblLast x :: ([dblFirst y, dblLast y] ++ dbl ys)) ++ [Int.ofNat (2 * n + 1)])
        = dblLast x :: ((([dblFirst y, dblLast y] ++ dbl ys) ++ [Int.ofNat (2 * n + 1)])) := rfl
    rw [hcons, hrw] at ⊢
    have eR1 : gapCount (dblLast x :: dblFirst y :: dblLast y :: (dbl ys ++ [Int.ofNat (2 * n + 1)]))
        = isGap (dblLast x) (dblFirst y)
          + gapCount (dblFirst y :: dblLast y :: (dbl ys ++ [Int.ofNat (2 * n + 1)])) := rfl
    have eR2 : gapCount (dblFirst y :: dblLast y :: (dbl ys ++ [Int.ofNat (2 * n + 1)]))
        = isGap (dblFirst y) (dblLast y)
          + gapCount ((dblLast y :: dbl ys) ++ [Int.ofNat (2 * n + 1)]) := rfl
    rw [eL, eR1, eR2, hbet, hins, hIH]
    omega

/-- Signed directed count equals unsigned absolute-gap count of the doubling,
for valid signed permutations.
Cf. the signed directed correspondence of Shamir-Peer Lecture 11 signed setting. -/
theorem sbreaks_eq_ubreaks_dbl_of_valid (n : Nat) (pi : List Int) (h : SValid n pi) :
    sbreaks n pi = ubreaks (2 * n) (dbl pi) := by
  cases pi with
  | nil =>
    have eL : dirGapCount [0, Int.ofNat (n + 1)] = isDirGap 0 (Int.ofNat (n + 1)) := rfl
    have eR : gapCount [0, Int.ofNat (2 * n + 1)] = isGap 0 (Int.ofNat (2 * n + 1)) := rfl
    have hempty := empty_gap n
    show dirGapCount [0, Int.ofNat (n + 1)] = gapCount [0, Int.ofNat (2 * n + 1)]
    rw [eL, eR]
    exact hempty
  | cons x xs =>
    have hmem : MemRange n (x :: xs) := SValid_imp_memRange n (x :: xs) h
    have hnodup : ((x :: xs).map Int.natAbs).Nodup := SValid_imp_nodup n (x :: xs) h
    have hxmem : x ∈ x :: xs := by simp
    obtain ⟨hx1, hxle⟩ := hmem x hxmem
    have hleft := left_gap x hx1
    have hins := inside_gap x
    have haux := aux_correspondence n x xs hmem hnodup
    have eL : dirGapCount (0 :: x :: xs ++ [Int.ofNat (n + 1)])
        = isDirGap 0 x + dirGapCount (x :: xs ++ [Int.ofNat (n + 1)]) := rfl
    have hdbl : dbl (x :: xs) = [dblFirst x, dblLast x] ++ dbl xs := by
      unfold dbl
      rw [List.flatMap_cons, dblOne_eq_first_last]
    have hrw : (([dblFirst x, dblLast x] ++ dbl xs) ++ [Int.ofNat (2 * n + 1)])
        = dblFirst x :: dblLast x :: (dbl xs ++ [Int.ofNat (2 * n + 1)]) := by
      rw [List.append_assoc]
      rfl
    have eR1 : gapCount (0 :: dblFirst x :: dblLast x :: (dbl xs ++ [Int.ofNat (2 * n + 1)]))
        = isGap 0 (dblFirst x)
          + gapCount (dblFirst x :: dblLast x :: (dbl xs ++ [Int.ofNat (2 * n + 1)])) := rfl
    have eR2 : gapCount (dblFirst x :: dblLast x :: (dbl xs ++ [Int.ofNat (2 * n + 1)]))
        = isGap (dblFirst x) (dblLast x)
          + gapCount ((dblLast x :: dbl xs) ++ [Int.ofNat (2 * n + 1)]) := rfl
    show dirGapCount (0 :: x :: xs ++ [Int.ofNat (n + 1)])
      = gapCount (0 :: dbl (x :: xs) ++ [Int.ofNat (2 * n + 1)])
    rw [hdbl] at ⊢
    have hcons : ((0 :: ([dblFirst x, dblLast x] ++ dbl xs)) ++ [Int.ofNat (2 * n + 1)])
        = 0 :: ((([dblFirst x, dblLast x] ++ dbl xs) ++ [Int.ofNat (2 * n + 1)])) := rfl
    rw [hcons, hrw] at ⊢
    rw [eL, eR1, eR2, hleft, hins, haux]
    omega

/-- The unrestricted correspondence is false: a repeated entry gives a
directed breakpoint but no absolute gap between its two doubled copies.
For `n = 1`, `pi = [1, 1]`: `sbreaks` counts the `1 -> 1` step while the
doubled `... 2, 1 ...` junction has absolute gap `1`.
Cf. the signed directed correspondence of Shamir-Peer Lecture 11 signed setting. -/
theorem sbreaks_eq_ubreaks_dbl_counterex :
    ∃ n pi, sbreaks n pi ≠ ubreaks (2 * n) (dbl pi) := by
  exact ⟨1, [1, 1], by decide⟩

/-- Signed reversal: reverse the 0-based inclusive block `i..j` and negate its elements.
Meaningful for `i ≤ j < pi.length`. Outside that range `j + 1 - i` truncates to `0` when
`j < i`, giving `pi.take i ++ pi.drop (j + 1)` with nothing negated (`pi` itself when
`i = j + 1`, repeated entries when `j + 1 < min i pi.length`); for `i ≤ j` and
`pi.length ≤ j` the suffix from `i` is reversed and negated. -/
def srevBlock (pi : List Int) (i j : Nat) : List Int :=
  pi.take i ++ ((pi.drop i).take (j + 1 - i)).reverse.map (fun x => -x) ++ pi.drop (j + 1)

theorem dblOne_length (x : Int) : (dblOne x).length = 2 := by
  unfold dblOne
  split <;> rfl

theorem dbl_cons (x : Int) (xs : List Int) : dbl (x :: xs) = dblOne x ++ dbl xs := by
  simp [dbl]

theorem dbl_append (l₁ l₂ : List Int) : dbl (l₁ ++ l₂) = dbl l₁ ++ dbl l₂ := by
  simp [dbl]

/-- Doubling doubles the length; cf. Lecture 11 signed setting. -/
theorem dbl_length (pi : List Int) : (dbl pi).length = 2 * pi.length := by
  induction pi with
  | nil => rfl
  | cons x xs ih =>
    rw [dbl_cons, List.length_append, dblOne_length, ih]
    show 2 + 2 * xs.length = 2 * (xs.length + 1)
    omega

theorem dbl_nil : dbl [] = [] := by rfl

theorem dbl_singleton (x : Int) : dbl [x] = dblOne x := by
  simp [dbl]

theorem dbl_take (pi : List Int) (i : Nat) : dbl (pi.take i) = (dbl pi).take (2 * i) := by
  induction pi generalizing i with
  | nil =>
    simp [dbl]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ n =>
      have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
      simp only [List.take_succ_cons, dbl_cons, h2]
      rw [List.take_append, dblOne_length]
      have htake : List.take (2 * n + 2) (dblOne x) = dblOne x := by
        apply List.take_of_length_le
        rw [dblOne_length]
        omega
      rw [htake]
      have hsub : 2 * n + 2 - 2 = 2 * n := by omega
      rw [hsub, ih]

theorem dbl_drop (pi : List Int) (i : Nat) : dbl (pi.drop i) = (dbl pi).drop (2 * i) := by
  induction pi generalizing i with
  | nil =>
    simp [dbl]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ n =>
      have h2 : 2 * (n + 1) = 2 * n + 2 := by omega
      simp only [List.drop_succ_cons, dbl_cons, h2]
      rw [List.drop_append, dblOne_length]
      have hdrop : List.drop (2 * n + 2) (dblOne x) = [] := by
        apply List.drop_eq_nil_of_le
        rw [dblOne_length]
        omega
      rw [hdrop]
      have hsub : 2 * n + 2 - 2 = 2 * n := by omega
      simp [hsub, ih]

theorem dblOne_neg_of_ne_zero (x : Int) (hne : x ≠ 0) :
    dblOne (-x) = (dblOne x).reverse := by
  by_cases h : 0 ≤ x
  · have hneg : ¬ (0 ≤ -x) := by omega
    unfold dblOne
    rw [ite_eq_right hneg, ite_eq_left h, Int.natAbs_neg]
    rfl
  · have hpos : 0 ≤ -x := by omega
    unfold dblOne
    rw [ite_eq_left hpos, ite_eq_right h, Int.natAbs_neg]
    rfl

theorem dbl_reverse_neg (l : List Int) (h : ∀ x ∈ l, x ≠ 0) :
    dbl (l.reverse.map (fun x => -x)) = (dbl l).reverse := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ 0 := h x (by simp)
    have hxs : ∀ y ∈ xs, y ≠ 0 := by
      intro y hy
      exact h y (by simp [hy])
    have ih' := ih hxs
    have hneg := dblOne_neg_of_ne_zero x hx
    rw [List.reverse_cons, List.map_append, List.map_singleton, dbl_append, dbl_singleton,
      dbl_cons, List.reverse_append, ih', hneg]

/-- Signed reversal corresponds to unsigned reversal of doubling: for a valid signed permutation
(nonzero entries) and `i ≤ j < pi.length`, doubling the signed reversal of `i..j` gives the
reversal of the block `2 * i` to `2 * j + 1` of the doubled list; cf. Lecture 11 signed setting. -/
theorem dbl_srevBlock (n : Nat) (pi : List Int) (i j : Nat) (h : SValid n pi)
    (hij : i ≤ j) (_hj : j < pi.length) :
    dbl (srevBlock pi i j) = revBlock (dbl pi) (2 * i) (2 * j + 1) := by
  have hmem := SValid_imp_memRange n pi h
  have hne_mid : ∀ x ∈ (pi.drop i).take (j + 1 - i), x ≠ 0 := by
    intro x hx
    have hdrop : x ∈ pi.drop i := List.mem_of_mem_take hx
    have hpi : x ∈ pi := List.mem_of_mem_drop hdrop
    have hrange := hmem x hpi
    have h1 : 1 ≤ x.natAbs := hrange.1
    intro hzero
    have h2 : x.natAbs = 0 := by
      rw [hzero]
      rfl
    omega
  have hmid_rev := dbl_reverse_neg ((pi.drop i).take (j + 1 - i)) hne_mid
  have hmid_eq : dbl ((pi.drop i).take (j + 1 - i)) =
      ((dbl pi).drop (2 * i)).take (2 * j + 1 + 1 - 2 * i) := by
    have h1 := dbl_take (pi.drop i) (j + 1 - i)
    have h2 := dbl_drop pi i
    rw [h2] at h1
    have harith : 2 * (j + 1 - i) = 2 * j + 1 + 1 - 2 * i := by omega
    rw [harith] at h1
    exact h1
  have hsuf_eq : dbl (pi.drop (j + 1)) = (dbl pi).drop (2 * j + 1 + 1) := by
    have h1 := dbl_drop pi (j + 1)
    have harith : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    rw [harith] at h1
    exact h1
  unfold srevBlock
  rw [dbl_append, dbl_append, dbl_take, hmid_rev, hmid_eq, hsuf_eq, revBlock_eq]

theorem map_natAbs_neg (l : List Int) :
    List.map Int.natAbs (List.map (fun x => -x) l) = List.map Int.natAbs l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [Int.natAbs_neg, ih]

theorem srevBlock_length (pi : List Int) (i j : Nat) (hij : i ≤ j)
    (hj : j < pi.length) : (srevBlock pi i j).length = pi.length := by
  unfold srevBlock
  simp only [List.length_append, List.length_map, List.length_reverse, List.length_take,
    List.length_drop]
  have hi : i ≤ pi.length := by omega
  have hmid_le : j + 1 - i ≤ pi.length - i := by omega
  rw [Nat.min_eq_left hi, Nat.min_eq_left hmid_le]
  omega

/-- Signed reversals with `i ≤ j < pi.length` preserve validity; cf. Lecture 11 signed setting. -/
theorem srevBlock_valid (n : Nat) (pi : List Int) (i j : Nat) (h : SValid n pi)
    (hij : i ≤ j) (hj : j < pi.length) : SValid n (srevBlock pi i j) := by
  unfold SValid at h ⊢
  have hsplit := pi_split pi i j hij hj
  have hmid_map : List.map Int.natAbs
        (((pi.drop i).take (j + 1 - i)).reverse.map (fun x => -x)) =
        (List.map Int.natAbs ((pi.drop i).take (j + 1 - i))).reverse := by
    rw [List.map_reverse, List.map_reverse, map_natAbs_neg]
  have hperm_mid : List.map Int.natAbs
        (((pi.drop i).take (j + 1 - i)).reverse.map (fun x => -x)) ~
        List.map Int.natAbs ((pi.drop i).take (j + 1 - i)) := by
    rw [hmid_map]
    exact List.reverse_perm _
  have hmap_srev : List.map Int.natAbs (srevBlock pi i j) =
      List.map Int.natAbs (pi.take i) ++
        List.map Int.natAbs
          (((pi.drop i).take (j + 1 - i)).reverse.map (fun x => -x)) ++
        List.map Int.natAbs (pi.drop (j + 1)) := by
    unfold srevBlock
    rw [List.map_append, List.map_append]
  have hmap_pi : List.map Int.natAbs pi =
      List.map Int.natAbs (pi.take i) ++
        List.map Int.natAbs ((pi.drop i).take (j + 1 - i)) ++
        List.map Int.natAbs (pi.drop (j + 1)) := by
    have hcongr := congrArg (List.map Int.natAbs) hsplit
    rw [List.map_append, List.map_append] at hcongr
    exact hcongr.symm
  have hperm : List.map Int.natAbs (srevBlock pi i j) ~
      List.map Int.natAbs pi := by
    rw [hmap_srev, hmap_pi]
    exact List.Perm.append (List.Perm.append (List.Perm.refl _) hperm_mid)
      (List.Perm.refl _)
  exact hperm.trans h

/-- For a valid signed permutation and `i ≤ j < pi.length`, a signed reversal increases the
breakpoint count by at most two; cf. Lecture 11 signed setting. -/
theorem sbreaks_srevBlock_le (n : Nat) (pi : List Int) (i j : Nat) (h : SValid n pi)
    (hij : i ≤ j) (hj : j < pi.length) :
    sbreaks n (srevBlock pi i j) ≤ sbreaks n pi + 2 := by
  have hvalid := srevBlock_valid n pi i j h hij hj
  have hcorr := sbreaks_eq_ubreaks_dbl_of_valid n pi h
  have hcorr2 := sbreaks_eq_ubreaks_dbl_of_valid n (srevBlock pi i j) hvalid
  have hdbl := dbl_srevBlock n pi i j h hij hj
  have hlen := dbl_length pi
  have hij2 : 2 * i ≤ 2 * j + 1 := by omega
  have hj2 : 2 * j + 1 < (dbl pi).length := by
    rw [hlen]
    omega
  have hub := ubreaks_revBlock_le (2 * n) (dbl pi) (2 * i) (2 * j + 1) hij2 hj2
  rw [←hdbl] at hub
  rw [←hcorr2, ←hcorr] at hub
  exact hub

/-- For a valid signed permutation and `i ≤ j < pi.length`, a signed reversal decreases the
breakpoint count by at most two; cf. Lecture 11 signed setting. -/
theorem sbreaks_le_srevBlock (n : Nat) (pi : List Int) (i j : Nat) (h : SValid n pi)
    (hij : i ≤ j) (hj : j < pi.length) :
    sbreaks n pi ≤ sbreaks n (srevBlock pi i j) + 2 := by
  have hvalid := srevBlock_valid n pi i j h hij hj
  have hcorr := sbreaks_eq_ubreaks_dbl_of_valid n pi h
  have hcorr2 := sbreaks_eq_ubreaks_dbl_of_valid n (srevBlock pi i j) hvalid
  have hdbl := dbl_srevBlock n pi i j h hij hj
  have hlen := dbl_length pi
  have hij2 : 2 * i ≤ 2 * j + 1 := by omega
  have hj2 : 2 * j + 1 < (dbl pi).length := by
    rw [hlen]
    omega
  have hub := ubreaks_le_revBlock (2 * n) (dbl pi) (2 * i) (2 * j + 1) hij2 hj2
  rw [←hdbl] at hub
  rw [←hcorr2, ←hcorr] at hub
  exact hub

/-- Sortability by signed reversals in exactly `k` steps.
Cf. Shamir-Peer Lecture 11 signed setting. -/
inductive SSortableIn : Nat → Nat → List Int → Prop where
  | done (n : Nat) : SSortableIn 0 n ((List.Icc 1 n).map Int.ofNat)
  | step (k n : Nat) (pi : List Int) (i j : Nat) (hij : i ≤ j) (hlt : j < pi.length)
    (h : SSortableIn k n (srevBlock pi i j)) : SSortableIn (k + 1) n pi

theorem srevBlock_append_singleton (X : List Int) (c : Int) (i j : Nat)
    (hij : i ≤ j) (hj : j < X.length) :
    srevBlock (X ++ [c]) i j = srevBlock X i j ++ [c] := by
  have hi_le : i ≤ X.length := by omega
  have hj_le : j + 1 ≤ X.length := by omega
  have htake : List.take i (X ++ [c]) = List.take i X :=
    List.take_append_of_le_length hi_le
  have hdrop : List.drop i (X ++ [c]) = List.drop i X ++ [c] :=
    List.drop_append_of_le_length hi_le
  have hlen_drop : (List.drop i X).length = X.length - i := List.length_drop
  have hmid_le : j + 1 - i ≤ (List.drop i X).length := by
    rw [hlen_drop]
    omega
  have hmid_take : List.take (j + 1 - i) (List.drop i (X ++ [c])) =
      List.take (j + 1 - i) (List.drop i X) := by
    rw [hdrop]
    exact List.take_append_of_le_length hmid_le
  have hdrop2 : List.drop (j + 1) (X ++ [c]) = List.drop (j + 1) X ++ [c] :=
    List.drop_append_of_le_length hj_le
  unfold srevBlock
  rw [htake, hmid_take, hdrop2]
  simp only [List.append_assoc]

theorem SSortableIn_succ_append (k n : Nat) (X : List Int) (hX : SSortableIn k n X) :
    SSortableIn k (n + 1) (X ++ [Int.ofNat (n + 1)]) := by
  induction hX with
  | done n =>
    rw [←target_succ n]
    exact SSortableIn.done (n + 1)
  | step k n pi i j hij hlt h ih =>
    have happ := srevBlock_append_singleton pi (Int.ofNat (n + 1)) i j hij hlt
    have hlen : j < (pi ++ [Int.ofNat (n + 1)]).length := by
      rw [List.length_append]
      show j < pi.length + 1
      omega
    have hmem : SSortableIn k (n + 1) (srevBlock (pi ++ [Int.ofNat (n + 1)]) i j) := by
      rw [happ]
      exact ih
    exact SSortableIn.step k (n + 1) (pi ++ [Int.ofNat (n + 1)]) i j hij hlen hmem

def sabs (pi : List Int) : List Int :=
  pi.map (Int.ofNat ∘ Int.natAbs)

theorem sabs_length (pi : List Int) : (sabs pi).length = pi.length := by
  simp [sabs]

theorem sabs_valid (n : Nat) (pi : List Int) (h : SValid n pi) : UValid n (sabs pi) := by
  unfold SValid at h
  unfold UValid
  have hmap : sabs pi = List.map Int.ofNat (List.map Int.natAbs pi) := by
    simp [sabs, List.map_map]
  rw [hmap]
  exact List.Perm.map Int.ofNat h

theorem sabs_neg_map (l : List Int) :
    List.map (Int.ofNat ∘ Int.natAbs) (List.map (fun x => -x) l) =
      List.map (Int.ofNat ∘ Int.natAbs) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [Int.natAbs_neg, ih]

theorem sabs_srevBlock (pi : List Int) (i j : Nat) :
    sabs (srevBlock pi i j) = revBlock (sabs pi) i j := by
  unfold sabs srevBlock revBlock
  rw [List.map_append, List.map_append, List.map_take, List.map_drop, List.map_reverse,
    List.map_reverse, sabs_neg_map, List.map_take, List.map_drop]

theorem sabs_append (l₁ l₂ : List Int) : sabs (l₁ ++ l₂) = sabs l₁ ++ sabs l₂ := by
  simp [sabs]

theorem srevBlock_last (Y : List Int) (x : Int) :
    srevBlock (Y ++ [x]) Y.length Y.length = Y ++ [-x] := by
  have htake : List.take Y.length (Y ++ [x]) = Y := by
    rw [List.take_append_of_le_length (le_refl _), List.take_length]
  have hdrop : List.drop Y.length (Y ++ [x]) = [x] := by
    rw [List.drop_append_of_le_length (le_refl _), List.drop_length]
    rfl
  have hmid_len : Y.length + 1 - Y.length = 1 := by omega
  have htake1 : List.take 1 [x] = [x] := rfl
  have hlen_single : ([x].length = 1) := rfl
  have hlen_app : (Y ++ [x]).length = Y.length + 1 := by
    rw [List.length_append, hlen_single]
  have hdrop2 : List.drop (Y.length + 1) (Y ++ [x]) = [] := by
    apply List.drop_eq_nil_of_le
    rw [hlen_app]
  unfold srevBlock
  rw [htake, hdrop, hmid_len, htake1, hdrop2, List.reverse_singleton,
    List.map_singleton, List.append_nil]

theorem sabs_sortable (n : Nat) (pi : List Int)
    (h : sabs pi = (List.Icc 1 n).map Int.ofNat) : ∃ k, SSortableIn k n pi := by
  induction n generalizing pi with
  | zero =>
    have hnil : sabs pi = [] := by
      rw [h]
      rfl
    simp only [sabs] at hnil
    have hpi : pi = [] := List.map_eq_nil_iff.mp hnil
    rw [hpi]
    exact ⟨0, SSortableIn.done 0⟩
  | succ n ih =>
    have hlen_sabs := sabs_length pi
    have hlen_target := target_length (n + 1)
    have hlen : pi.length = n + 1 := by
      have hcongr := congrArg List.length h
      rw [hlen_sabs, hlen_target] at hcongr
      exact hcongr
    have hpos : 0 < pi.length := by
      rw [hlen]
      omega
    have hne := List.ne_nil_of_length_pos hpos
    obtain ⟨Y, x, hpi_eq⟩ := exists_init_last pi hne
    have hlen_app : (Y ++ [x]).length = Y.length + 1 := by
      rw [List.length_append, List.length_singleton]
    have hlenY : Y.length = n := by
      have hcongr : (Y ++ [x]).length = n + 1 := by
        rw [←hpi_eq, hlen]
      rw [hlen_app] at hcongr
      omega
    have hsabs_eq : sabs Y ++ sabs [x] = (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)] := by
      have h1 : sabs (Y ++ [x]) = (List.Icc 1 (n + 1)).map Int.ofNat := by
        rw [←hpi_eq, h]
      rw [sabs_append, target_succ] at h1
      exact h1
    have hsingle : sabs [x] = [(Int.ofNat ∘ Int.natAbs) x] := rfl
    rw [hsingle] at hsabs_eq
    have hlen_sabsY : (sabs Y).length = n := by
      rw [sabs_length, hlenY]
    have hlen_idn : ((List.Icc 1 n).map Int.ofNat).length = n := target_length n
    have hlen_eq : (sabs Y).length = ((List.Icc 1 n).map Int.ofNat).length := by
      rw [hlen_sabsY, hlen_idn]
    obtain ⟨heqY, heqX⟩ := List.append_inj hsabs_eq hlen_eq
    have ihY := ih Y heqY
    obtain ⟨k, hk⟩ := ihY
    have hlift := SSortableIn_succ_append k n Y hk
    have hg : (Int.ofNat ∘ Int.natAbs) x = Int.ofNat (n + 1) := by
      simpa using heqX
    simp only [Function.comp_apply] at hg
    have habs : x.natAbs = n + 1 := Int.ofNat_inj.mp hg
    by_cases hx : 0 ≤ x
    · have hcast := natAbs_cast_of_nonneg x hx
      rw [habs] at hcast
      have hx_eq : x = Int.ofNat (n + 1) := hcast.symm
      rw [hpi_eq, hx_eq]
      exact ⟨k, hlift⟩
    · have hneg : x < 0 := by omega
      have hcast := natAbs_cast_of_neg x hneg
      rw [habs] at hcast
      have hx_eq : x = -Int.ofNat (n + 1) := by
        show x = -↑(n + 1)
        omega
      have hflip : srevBlock (Y ++ [x]) Y.length Y.length = Y ++ [Int.ofNat (n + 1)] := by
        rw [srevBlock_last, hx_eq]
        simp
      have hmem : SSortableIn k (n + 1) (srevBlock (Y ++ [x]) Y.length Y.length) := by
        rw [hflip]
        exact hlift
      have hlen_pi : Y.length < (Y ++ [x]).length := by
        rw [hlen_app]
        omega
      have hstep := SSortableIn.step k (n + 1) (Y ++ [x]) Y.length Y.length (le_refl _) hlen_pi hmem
      rw [hpi_eq]
      exact ⟨k + 1, hstep⟩

theorem ssortable_lift (n m : Nat) (q pi : List Int) (h : USortableIn m n q)
    (heq : sabs pi = q) (hv : SValid n pi) : ∃ k, SSortableIn k n pi := by
  induction h generalizing pi with
  | done n =>
    exact sabs_sortable n pi heq
  | step k n q i j hij hlt h ih =>
    have hlen_eq : pi.length = q.length := by
      have hcongr := congrArg List.length heq
      rw [sabs_length] at hcongr
      exact hcongr
    have hj : j < pi.length := by
      rw [hlen_eq]
      exact hlt
    have hvalid := srevBlock_valid n pi i j hv hij hj
    have hsabs : sabs (srevBlock pi i j) = revBlock q i j := by
      rw [sabs_srevBlock, heq]
    obtain ⟨kk, hk⟩ := ih (srevBlock pi i j) hsabs hvalid
    exact ⟨kk + 1, SSortableIn.step kk n pi i j hij hj hk⟩

/-- Every signed permutation sorts by signed reversals.
Cf. Shamir-Peer Lecture 11 signed setting. -/
theorem ssortable (n : Nat) (pi : List Int) (h : SValid n pi) :
    ∃ k, SSortableIn k n pi := by
  have huv := sabs_valid n pi h
  obtain ⟨m, hm⟩ := sortable n (sabs pi) huv
  exact ssortable_lift n m (sabs pi) pi hm rfl h

noncomputable instance decSSortableIn (n : Nat) (pi : List Int) :
    DecidablePred (fun k => SSortableIn k n pi) :=
  Classical.decPred _

/-- Signed reversal distance as a genuine minimum; cf. Lecture 11 signed setting. -/
noncomputable def sdist (n : Nat) (pi : List Int) (h : SValid n pi) : Nat :=
  Nat.find (ssortable n pi h)

theorem isDirGap_consec (n : Nat) :
    isDirGap (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) = 0 := by
  have h : (↑(n + 2) : Int) - (↑(n + 1) : Int) = 1 := by omega
  have h2 : Int.ofNat (n + 2) - Int.ofNat (n + 1) = 1 := h
  unfold isDirGap
  rw [ite_eq_left h2]

theorem sbreaks_target (n : Nat) : sbreaks n ((List.Icc 1 n).map Int.ofNat) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sbreaks
    rw [framed_succ n]
    have h1 : (0 :: (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)]) ≠ [] := by simp
    have h2 : ([Int.ofNat (n + 1 + 1)] : List Int) ≠ [] := by simp
    rw [dirGapCount_append _ _ h1 h2]
    have hlast := framed_getLast n h1
    have hhead : ([Int.ofNat (n + 1 + 1)] : List Int).head h2 = Int.ofNat (n + 1 + 1) := rfl
    rw [hlast, hhead]
    have hconsec : isDirGap (Int.ofNat (n + 1)) (Int.ofNat (n + 1 + 1)) = 0 := by
      have heq : n + 1 + 1 = n + 2 := by omega
      rw [heq]
      exact isDirGap_consec n
    rw [hconsec]
    have h0 : dirGapCount (0 :: (List.Icc 1 n).map Int.ofNat ++ [Int.ofNat (n + 1)]) = 0 := ih
    have hsingle : dirGapCount ([Int.ofNat (n + 1 + 1)] : List Int) = 0 := rfl
    rw [h0, hsingle]

/-- Breakpoint lower bound by sortability, for a valid signed permutation;
cf. Lecture 11 signed setting. -/
theorem sbreaks_le_two_mul_of_ssortableIn (k n : Nat) (pi : List Int)
    (h : SSortableIn k n pi) (hv : SValid n pi) : sbreaks n pi ≤ 2 * k := by
  revert hv
  induction h with
  | done n =>
    intro hv
    rw [sbreaks_target]
  | step k n pi i j hij hlt h ih =>
    intro hv
    have hvalid := srevBlock_valid n pi i j hv hij hlt
    have ihBound := ih hvalid
    have hstep := sbreaks_le_srevBlock n pi i j hv hij hlt
    omega

/-- Breakpoint lower bound by distance; cf. Lecture 11 signed setting. -/
theorem sb_le_two_mul_sdist (n : Nat) (pi : List Int) (h : SValid n pi) :
    sbreaks n pi ≤ 2 * sdist n pi h := by
  have hsort : SSortableIn (sdist n pi h) n pi := Nat.find_spec (ssortable n pi h)
  exact sbreaks_le_two_mul_of_ssortableIn (sdist n pi h) n pi hsort h

theorem SValid_length (n : Nat) (pi : List Int) (h : SValid n pi) : pi.length = n := by
  unfold SValid at h
  have hlen_perm := List.Perm.length_eq h
  have hlen_map : (List.map Int.natAbs pi).length = pi.length := by simp
  have hlen_icc : (List.Icc 1 n).length = n := by
    have htarget := target_length n
    have hmap_len : ((List.Icc 1 n).map Int.ofNat).length = (List.Icc 1 n).length := by simp
    rw [hmap_len] at htarget
    exact htarget
  rw [hlen_map, hlen_icc] at hlen_perm
  exact hlen_perm

theorem perm_append_singleton_cancel (l₁ l₂ : List Nat) (a : Nat)
    (h : l₁ ++ [a] ~ l₂ ++ [a]) : l₁ ~ l₂ := by
  have h1 : (l₁ ++ [a]).reverse = a :: l₁.reverse := by
    rw [List.reverse_append, List.reverse_singleton]
    rfl
  have h2 : (l₂ ++ [a]).reverse = a :: l₂.reverse := by
    rw [List.reverse_append, List.reverse_singleton]
    rfl
  have hperm_rev : (a :: l₁.reverse) ~ (a :: l₂.reverse) := by
    rw [←h1, ←h2]
    exact (List.reverse_perm _).trans (h.trans (List.Perm.symm (List.reverse_perm _)))
  have hrev_perm := List.Perm.cons_inv hperm_rev
  exact (List.Perm.symm (List.reverse_perm _)).trans (hrev_perm.trans (List.reverse_perm _))

theorem eq_identity_of_dbl_eq (n : Nat) (pi : List Int) (h : SValid n pi)
    (hdbl : dbl pi = (List.Icc 1 (2 * n)).map Int.ofNat) :
    pi = (List.Icc 1 n).map Int.ofNat := by
  induction n generalizing pi with
  | zero =>
    have hlen := SValid_length 0 pi h
    have hpi : pi = [] := List.eq_nil_of_length_eq_zero hlen
    rw [hpi]
    rfl
  | succ n ih =>
    have hlen := SValid_length (n + 1) pi h
    have hpos : 0 < pi.length := by
      rw [hlen]
      omega
    have hne := List.ne_nil_of_length_pos hpos
    obtain ⟨Y, x, hpi_eq⟩ := exists_init_last pi hne
    have hlen_app : (Y ++ [x]).length = Y.length + 1 := by
      rw [List.length_append, List.length_singleton]
    have hlenY : Y.length = n := by
      have hcongr : (Y ++ [x]).length = n + 1 := by
        rw [←hpi_eq, hlen]
      rw [hlen_app] at hcongr
      omega
    have hdbl_eq : dbl Y ++ dblOne x =
        (List.Icc 1 (2 * n)).map Int.ofNat ++ [Int.ofNat (2 * n + 1), Int.ofNat (2 * n + 2)] := by
      have h1 : dbl (Y ++ [x]) = (List.Icc 1 (2 * (n + 1))).map Int.ofNat := by
        rw [←hpi_eq, hdbl]
      rw [dbl_append, dbl_singleton, target_double_succ] at h1
      exact h1
    have hlen_dblY : (dbl Y).length = 2 * n := by
      rw [dbl_length, hlenY]
    have hlen_idn : ((List.Icc 1 (2 * n)).map Int.ofNat).length = 2 * n := target_length (2 * n)
    have hlen_eq : (dbl Y).length = ((List.Icc 1 (2 * n)).map Int.ofNat).length := by
      rw [hlen_dblY, hlen_idn]
    obtain ⟨heqY, heqX⟩ := List.append_inj hdbl_eq hlen_eq
    have hx_eq : x = Int.ofNat (n + 1) := by
      by_cases hx : 0 ≤ x
      · have hone := dblOne_of_nonneg x hx
        rw [hone] at heqX
        have hpair : 2 * (x.natAbs : Int) - 1 = Int.ofNat (2 * n + 1) ∧
            2 * (x.natAbs : Int) = Int.ofNat (2 * n + 2) := by
          simpa using heqX
        have hcomp : 2 * (x.natAbs : Int) = Int.ofNat (2 * n + 2) := hpair.right
        have habs : x.natAbs = n + 1 := by
          have hcast : (2 : Int) * (x.natAbs : Int) = ((2 * n + 2 : Nat) : Int) := hcomp
          omega
        have hcast2 := natAbs_cast_of_nonneg x hx
        rw [habs] at hcast2
        exact hcast2.symm
      · have hneg : x < 0 := by omega
        have hone := dblOne_of_neg x hneg
        rw [hone] at heqX
        have hpair : 2 * (x.natAbs : Int) = Int.ofNat (2 * n + 1) ∧
            2 * (x.natAbs : Int) - 1 = Int.ofNat (2 * n + 2) := by
          simpa using heqX
        have hcomp : 2 * (x.natAbs : Int) = Int.ofNat (2 * n + 1) := hpair.left
        have hfalse : False := by
          have hcast : (2 : Int) * (x.natAbs : Int) = ((2 * n + 1 : Nat) : Int) := hcomp
          omega
        exact False.elim hfalse
    have habsX : x.natAbs = n + 1 := by
      rw [hx_eq]
      rfl
    have hvalidY : SValid n Y := by
      unfold SValid at h ⊢
      have hmap_pi : List.map Int.natAbs pi = List.map Int.natAbs Y ++ [n + 1] := by
        rw [hpi_eq, List.map_append]
        simp [habsX]
      have hIcc : List.Icc 1 (n + 1) = List.Icc 1 n ++ [n + 1] := Icc_one_succ n
      rw [hmap_pi, hIcc] at h
      exact perm_append_singleton_cancel _ _ _ h
    have heqY_id : dbl Y = (List.Icc 1 (2 * n)).map Int.ofNat := heqY
    have hY_eq := ih Y hvalidY heqY_id
    rw [hpi_eq, hY_eq, hx_eq, target_succ]

/-- Unique zero breakpoints is the identity (derived unique-zero);
cf. Shamir-Peer Lecture 11 signed setting. -/
theorem sbreaks_eq_zero_iff (n : Nat) (pi : List Int) (h : SValid n pi) :
    sbreaks n pi = 0 ↔ pi = (List.Icc 1 n).map Int.ofNat := by
  constructor
  · intro h0
    have hcorr := sbreaks_eq_ubreaks_dbl_of_valid n pi h
    rw [h0] at hcorr
    have hub0 : ubreaks (2 * n) (dbl pi) = 0 := hcorr.symm
    have hvalid_dbl := dbl_valid h
    have hiff := ubreaks_eq_zero_iff hvalid_dbl
    have hdbl_eq := hiff.mp hub0
    exact eq_identity_of_dbl_eq n pi h hdbl_eq
  · intro heq
    rw [heq]
    exact sbreaks_target n

/-- Unique zero distance is the identity (derived unique-zero);
cf. Shamir-Peer Lecture 11 signed setting. -/
theorem sdist_eq_zero_iff (n : Nat) (pi : List Int) (h : SValid n pi) :
    sdist n pi h = 0 ↔ pi = (List.Icc 1 n).map Int.ofNat := by
  constructor
  · intro h0
    have hsort : SSortableIn (sdist n pi h) n pi := Nat.find_spec (ssortable n pi h)
    rw [h0] at hsort
    cases hsort
    rfl
  · intro heq
    have h0 : SSortableIn 0 n pi := by
      rw [heq]
      exact SSortableIn.done n
    have hle := Nat.find_min' (ssortable n pi h) h0
    show sdist n pi h = 0
    have hle2 : sdist n pi h ≤ 0 := hle
    omega

end Cslib.Bioinformatics.Rearrangement.SortingByReversals
