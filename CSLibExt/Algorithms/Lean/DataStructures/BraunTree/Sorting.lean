/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree
public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree.Complete
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sorting with Braun-tree priority queues

Two sorting algorithms via Braun-tree priority queues, following the
AFP entry `Sorting_Braun` and *Functional Data Structures and
Algorithms*, Chapter 16.

Algorithm A: build a heap by repeated `insert` (`heapOfA`), extract
by merging the children (`listOfA` via `merge`). Algorithm B: build a
heap bottom-up with `heapify` (`heapOfB`), extract by `delMin`
(`listOfB'`). Both produce the input as a sorted list
(`List.Pairwise (· ≤ ·)`) with the same multiset. `t_sortA` and
`t_sortB` are the machine-checked `O(n log n)` bounds, via the
`nlog2` (`Nat.clog 2`) log bounds and the `Complete` machinery
(`height_acomplete`, `acomplete_if_braun`).

## Differences from Isabelle, forced by totality / Lean's statement style

* Sorting's `merge` (Phase 2, Algorithm A) is a *different* function
  from `ReplaceMin.merge` (which is `delMin2`'s helper); here it is
  `BraunTree.Sorting.merge`, fully qualified
  `Cslib.Algorithms.Lean.BraunTree.Sorting.merge`.
* `heapify` is totalised with `heapify (n+1) [] = (Leaf, [])`, and
  `listOfB` / `tListOfB` are defined by fuel (the fuel is `size t`);
  both totalisations are unreachable on the inputs the lemmas use
  (`n ≤ length xs` / `Braun t`, which give
  `size (delMin t) = size t - 1`).
* `t_insert` is `BraunTree.T_insert`: its equations are Sorting's
  `t_insert` equations up to `+1` commutation.
* `t_sift_down` and `t_del_left` / `t_del_min` are *not*
  `BraunTree.T_siftDown` / `T_delLeft` / `T_delMin`: Sorting counts
  `t_sift_down (Node Leaf x Leaf) a Leaf = 2` (vs `T_siftDown = 1`)
  and `t_del_left` counts 2 per level (vs `T_delLeft` 1). They are
  defined here as `tSiftDown`, `tDelLeft`, `tDelMin`.
  `tSiftDown`'s two remaining uncovered inputs
  (`Node Leaf x₁ r₁, a, Leaf` with `r₁` a `Node`, and the
  `Node (Node …) …, a, Leaf` gap) are totalised to `1`; both are
  Braun-impossible (the first unless `r₁ = Leaf`, where the
  `= 2` equation takes precedence), and `tSiftDown_height` proves
  those cases by contradiction from `Braun`.
* `set_listOfA` / `set_listOfB` are stated as `Iff`s over `List.Mem`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTree.Sorting

open BraunTree
open BraunTree.Complete




variable {α : Type u} [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α]

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- `size t = (msetTree t).card`. Used to get `size_heapOfA` from
    `mset_heapOfA`. -/
theorem size_eq_card_msetTree (t : BraunTree α) :
    size t = (msetTree t).card := by
  induction t with
  | Leaf => rfl
  | Node l a r ihl ihr =>
      simp [size, msetTree, ihl, ihr]

/-! ### Phase 1, Algorithm A: list to tree by repeated `insert` -/

/-- Isabelle's `heap_of_A`: build a heap by repeated `insert`. -/
def heapOfA : List α → BraunTree α
  | [] => BraunTree.Leaf
  | a :: as => insert a (heapOfA as)

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `heap_heap_of_A`. -/
theorem heap_heapOfA (xs : List α) : Heap (heapOfA xs) := by
  induction xs with
  | nil => exact trivial
  | cons a as ih => exact heap_insert a ih

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `braun_heap_of_A`. -/
theorem braun_heapOfA (xs : List α) : Braun (heapOfA xs) := by
  induction xs with
  | nil => exact trivial
  | cons a as ih => exact braun_insert a ih

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `mset_tree_heap_of_A`. -/
theorem mset_heapOfA (xs : List α) :
    msetTree (heapOfA xs) = (xs : Multiset α) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      change msetTree (insert a (heapOfA as)) = ((a :: as : List α) : Multiset α)
      rw [mset_insert, ih]
      rfl

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `size_heap_of_A`. -/
theorem size_heapOfA (xs : List α) : size (heapOfA xs) = xs.length := by
  rw [size_eq_card_msetTree, mset_heapOfA]
  simp

omit [DecidableLE α] [DecidableEq α] in
/-- `insert` never decreases `height`. AFP lemma `height_insert_ge`. -/
theorem height_insert_ge {t : BraunTree α} (x : α) :
    height t ≤ height (insert x t) := by
  induction t generalizing x with
  | Leaf => simp [insert, height]
  | Node l y r ihl ihr =>
      simp only [insert]
      split_ifs with h
      · -- insert x (Node l y r) = Node (insert y r) x l
        -- height = max (height (insert y r)) (height l) + 1 ≥ height l + 1 ≥ ...
        have h1 : height r ≤ height (insert y r) := ihr y
        simp only [height]
        omega
      · have h1 : height r ≤ height (insert x r) := ihr x
        simp only [height]
        omega

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `t_insert_height`: Sorting's `t_insert` is `T_insert`
    (see the header), so this is `T_insert_le`. -/
theorem t_insert_height (x : α) (t : BraunTree α) : T_insert x t ≤ height t + 1 :=
  T_insert_le x t

/-- Time of building a heap by repeated `insert`, summed over the list.
    Isabelle's `t_heap_of_A`, with `t_insert = T_insert`. -/
def T_heapOfA : List α → ℕ
  | [] => 0
  | a :: as => T_insert a (heapOfA as) + T_heapOfA as

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `t_heap_of_A_bound`. -/
theorem T_heapOfA_bound (xs : List α) :
    T_heapOfA xs ≤ xs.length * (height (heapOfA xs) + 1) := by
  induction xs with
  | nil => simp [T_heapOfA]
  | cons x xs ih =>
      have h1 : T_insert x (heapOfA xs) ≤ height (heapOfA xs) + 1 :=
        T_insert_le x (heapOfA xs)
      have h2 : height (heapOfA xs) ≤ height (heapOfA (x :: xs)) :=
        height_insert_ge x
      simp only [T_heapOfA, List.length_cons]
      have hmul : (xs.length + 1) * (height (heapOfA xs) + 1) =
          xs.length * (height (heapOfA xs) + 1) + (height (heapOfA xs) + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have h3 : (xs.length + 1) * (height (heapOfA xs) + 1) ≤
          (xs.length + 1) * (height (heapOfA (x :: xs)) + 1) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right h2 1)
      omega


/-! ### Phase 1, Algorithm B: `heapify` -/

/-- Isabelle's `heapify`: build a Braun heap of the first `n` elements
    of `xs`, returning the leftover list. Totalised on `[]` for `n+1`. -/
def heapify : ℕ → List α → BraunTree α × List α
  | 0, xs => (BraunTree.Leaf, xs)
  | (_ + 1), [] => (BraunTree.Leaf, [])
  | (n + 1), (x :: xs) =>
      let (l, ys) := heapify ((n + 1) / 2) xs
      let (r, zs) := heapify (n / 2) ys
      (siftDown l x r, zs)
termination_by n _ => n
decreasing_by all_goals omega

omit [DecidableLT α] [DecidableEq α] in
/-- One-step equation for `heapify` on a non-empty list. -/
theorem heapify_succ_cons (n : ℕ) (x : α) (xs : List α) :
    heapify (n + 1) (x :: xs) =
      let (l, ys) := heapify ((n + 1) / 2) xs
      let (r, zs) := heapify (n / 2) ys
      (siftDown l x r, zs) := by
  simp [heapify]

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `heapify_snd`: the leftover list is `drop n xs`. Proved by
    strong induction on `length xs`. -/
theorem heapify_snd : ∀ (n : ℕ) (xs : List α), n ≤ xs.length →
    (heapify n xs).2 = xs.drop n := by
  suffices H : ∀ (m : ℕ) (n : ℕ) (xs : List α), xs.length = m → n ≤ xs.length →
      (heapify n xs).2 = xs.drop n by
    intro n xs hn
    exact H xs.length n xs rfl hn
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro n xs hlen hn
      cases n with
      | zero => simp [heapify]
      | succ n' =>
          cases xs with
          | nil => simp at hn
          | cons x xs' =>
              have hlencons : (x :: xs').length = xs'.length + 1 := rfl
              have hlen' : xs'.length + 1 = m := hlen
              have hn' : n' ≤ xs'.length := by omega
              have h1le : (n' + 1) / 2 ≤ xs'.length := by omega
              have h1 : (heapify ((n' + 1) / 2) xs').2 = xs'.drop ((n' + 1) / 2) := by
                apply ih xs'.length (by omega) ((n' + 1) / 2) xs' rfl h1le
              cases h1eq : heapify ((n' + 1) / 2) xs' with
              | mk l ys =>
                  have hys : ys = xs'.drop ((n' + 1) / 2) := by
                    have := h1
                    rw [h1eq] at this
                    exact this
                  have hyslen : ys.length = xs'.length - (n' + 1) / 2 := by
                    rw [hys, List.length_drop]
                  have h2le : n' / 2 ≤ ys.length := by omega
                  have h2 : (heapify (n' / 2) ys).2 = ys.drop (n' / 2) := by
                    apply ih ys.length (by omega) (n' / 2) ys rfl h2le
                  rw [heapify_succ_cons, h1eq]
                  dsimp only
                  rw [h2]
                  simp only [List.drop_succ_cons]
                  rw [hys, List.drop_drop]
                  have hdiv : (n' + 1) / 2 + n' / 2 = n' := by omega
                  rw [hdiv]

omit [DecidableLT α] [DecidableEq α] in
/-- `heapify` returns the pair from `heapify_snd`: helper form. -/
theorem heapify_snd_tup {n : ℕ} {xs : List α} {t : BraunTree α} {ys : List α}
    (h : heapify n xs = (t, ys)) (hn : n ≤ xs.length) : ys = xs.drop n := by
  have h2 := heapify_snd n xs hn
  rw [h] at h2
  exact h2

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `heapify_correct`, by strong induction on `n`. -/
theorem heapify_correct : ∀ (n : ℕ) (xs : List α),
    n ≤ xs.length → ∀ (t : BraunTree α) (ys : List α),
    heapify n xs = (t, ys) →
    size t = n ∧ Heap t ∧ Braun t ∧ msetTree t = (xs.take n : Multiset α) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro xs hn t ys hheap
      cases n with
      | zero =>
          have : heapify 0 xs = (BraunTree.Leaf, xs) := by simp [heapify]
          rw [this] at hheap
          simp only [Prod.mk.injEq] at hheap
          obtain ⟨rfl, rfl⟩ := hheap
          refine ⟨rfl, trivial, trivial, ?_⟩
          simp [msetTree]
      | succ n' =>
          cases xs with
          | nil => simp at hn
          | cons x xs' =>
              have hlencons : (x :: xs').length = xs'.length + 1 := rfl
              have hn' : n' ≤ xs'.length := by omega
              have h1le : (n' + 1) / 2 ≤ xs'.length := by omega
              cases h1eq : heapify ((n' + 1) / 2) xs' with
              | mk t1 ys1 =>
                  have hys : ys1 = xs'.drop ((n' + 1) / 2) :=
                    heapify_snd_tup h1eq h1le
                  have hyslen : ys1.length = xs'.length - (n' + 1) / 2 := by
                    rw [hys, List.length_drop]
                  have h2le : n' / 2 ≤ ys1.length := by omega
                  cases h2eq : heapify (n' / 2) ys1 with
                  | mk t2 ys2 =>
                      have hheap' : heapify (n' + 1) (x :: xs') =
                          (siftDown t1 x t2, ys2) := by
                        rw [heapify_succ_cons, h1eq]
                        dsimp only
                        rw [h2eq]
                      rw [hheap'] at hheap
                      simp only [Prod.mk.injEq] at hheap
                      obtain ⟨rfl, rfl⟩ := hheap
                      have ih1 := ih ((n' + 1) / 2) (by omega) xs' h1le t1 ys1 h1eq
                      have ih2 := ih (n' / 2) (by omega) ys1 h2le t2 ys2 h2eq
                      obtain ⟨hsz1, hhp1, hbr1, hms1⟩ := ih1
                      obtain ⟨hsz2, hhp2, hbr2, hms2⟩ := ih2
                      have hbraunNode : Braun (BraunTree.Node t1 x t2) := by
                        rw [braun_node]
                        refine ⟨?_, hbr1, hbr2⟩
                        omega
                      have htake : (xs'.take ((n' + 1) / 2) : Multiset α) +
                          (ys1.take (n' / 2) : Multiset α) =
                          (xs'.take n' : Multiset α) := by
                        have hdiv : (n' + 1) / 2 + n' / 2 = n' := by omega
                        have htake' : xs'.take n' =
                            xs'.take ((n' + 1) / 2) ++ ys1.take (n' / 2) := by
                          conv_lhs => rw [← hdiv]
                          rw [List.take_add, ← hys]
                        rw [htake']
                        simp
                      refine ⟨?_, heap_siftDown hbraunNode hhp1 hhp2,
                        braun_siftDown hbraunNode, ?_⟩
                      · rw [size_siftDown hbraunNode]
                        omega
                      · rw [mset_siftDown hbraunNode, hms1, hms2]
                        have hrhs : (((x :: xs').take (n' + 1) : List α) : Multiset α) =
                            {x} + ((xs'.take n') : Multiset α) := by simp
                        rw [hrhs, ← htake]

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `braun_heapify`. -/
theorem braun_heapify {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    Braun (heapify n xs).1 := by
  cases h : heapify n xs with
  | mk t ys =>
      have hc := heapify_correct n xs hn t ys h
      exact hc.2.2.1

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `heap_heapify`. -/
theorem heap_heapify {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    Heap (heapify n xs).1 := by
  cases h : heapify n xs with
  | mk t ys =>
      have hc := heapify_correct n xs hn t ys h
      exact hc.2.1

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `mset_heapify`. -/
theorem mset_heapify {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    msetTree (heapify n xs).1 = (xs.take n : Multiset α) := by
  cases h : heapify n xs with
  | mk t ys =>
      have hc := heapify_correct n xs hn t ys h
      exact hc.2.2.2

/-! ### Phase 1, Algorithm B: running time of `heapify` -/

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- `Braun (Node l a r)` does not mention the root `a`. -/
theorem braun_node_root {l r : BraunTree α} {a b : α} :
    Braun (BraunTree.Node l a r) ↔ Braun (BraunTree.Node l b r) :=
  Iff.rfl

/-- Isabelle's `t_sift_down` (Sorting version; see header). The extra
    fourth equation (`Node Leaf x₁ r₁, a, Leaf -> 1`) totalises the
    input Isabelle leaves unspecified; it is Braun-impossible unless
    `r₁ = Leaf`, where the second equation (`= 2`) takes precedence. -/
def tSiftDown : BraunTree α → α → BraunTree α → ℕ
  | .Leaf, _, _ => 1
  | .Node .Leaf _ .Leaf, _, .Leaf => 2
  | .Node l₁ x₁ r₁, a, .Node l₂ x₂ r₂ =>
      if a ≤ x₁ ∧ a ≤ x₂ then 1
      else if x₁ ≤ x₂ then 1 + tSiftDown l₁ a r₁
      else 1 + tSiftDown l₂ a r₂
  | .Node .Leaf _x₁ _r₁, _a, .Leaf => 1
  | .Node (.Node _l₁ _x₁ _r₁) _x₂ _r₂, _a, .Leaf => 1
termination_by l _ r => size l + size r
decreasing_by all_goals simp only [size]; omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_sift_down_height`. -/
theorem tSiftDown_height {l : BraunTree α} {x : α} {r : BraunTree α}
    (hb : Braun (BraunTree.Node l x r)) : tSiftDown l x r ≤ height (BraunTree.Node l x r) := by
  induction l, x, r using tSiftDown.induct with
  | case1 x_elem r => simp [tSiftDown, height]
  | case2 a_elem x_elem => simp [tSiftDown, height]
  | case3 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle => simp [tSiftDown, height, hle]
  | case4 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle h12 ih =>
      have hbraun1 : Braun (BraunTree.Node l₁ a_elem r₁) := by
        obtain ⟨_, hbl, _⟩ := hb
        exact braun_node_root.mp hbl
      have h1 := ih hbraun1
      simp only [tSiftDown, hle, h12, ite_false, ite_true]
      simp only [height] at h1 ⊢
      omega
  | case5 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle h12 ih =>
      have hbraun2 : Braun (BraunTree.Node l₂ a_elem r₂) := by
        obtain ⟨_, _, hbr⟩ := hb
        exact braun_node_root.mp hbr
      have h1 := ih hbraun2
      simp only [tSiftDown, hle, h12, ite_false]
      simp only [height] at h1 ⊢
      omega
  | case6 x₁ r₁ a_elem =>
      cases r₁ with
      | Leaf => simp [tSiftDown, height]
      | Node l₁' x₁' r₁' =>
          exfalso
          rw [braun_node] at hb
          simp only [size] at hb
          omega
  | case7 l₁ x₁ r₁ x₂ r₂ a_elem =>
      exfalso
      rw [braun_node] at hb
      simp only [size] at hb
      omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `sift_down_height`. -/
theorem siftDown_height {l : BraunTree α} {x : α} {r : BraunTree α}
    (hb : Braun (BraunTree.Node l x r)) :
    height (siftDown l x r) ≤ height (BraunTree.Node l x r) := by
  induction l, x, r using siftDown.induct with
  | case1 x_elem r => simp [siftDown, height]
  | case2 x₀ a_sub x_elem hle =>
      simp only [siftDown]
      split_ifs
      simp [height]
  | case3 x₀ a_sub x_elem hle =>
      simp only [siftDown]
      split_ifs
      simp [height]
  | case4 l₁ x₁ r₁ x₂ r₂ a_elem hle =>
      exfalso
      rw [braun_node] at hb
      simp only [size] at hb
      omega
  | case5 l₁ x₁ r₁ x₂ r₂ a_elem hle ih =>
      exfalso
      rw [braun_node] at hb
      simp only [size] at hb
      omega
  | case6 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle => simp [siftDown, height, hle]
  | case7 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle h12 ih =>
      have hbraun1 : Braun (BraunTree.Node l₁ a_elem r₁) := by
        obtain ⟨_, hbl, _⟩ := hb
        rw [braun_node] at hbl
        exact ⟨hbl.1, hbl.2.1, hbl.2.2⟩
      have h1 := ih hbraun1
      simp only [siftDown, hle, h12, ite_false, ite_true]
      simp only [height] at h1 ⊢
      omega
  | case8 l₁ x₁ r₁ a_elem l₂ x₂ r₂ hle h12 ih =>
      have hbraun2 : Braun (BraunTree.Node l₂ a_elem r₂) := by
        obtain ⟨_, _, hbr⟩ := hb
        rw [braun_node] at hbr
        exact ⟨hbr.1, hbr.2.1, hbr.2.2⟩
      have h1 := ih hbraun2
      simp only [siftDown, hle, h12, ite_false]
      simp only [height] at h1 ⊢
      omega

omit [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `t_heap_of_A_log_bound`: `height (heapOfA xs)` is
    `nlog2 (xs.length + 1)`, via `height_acomplete` + `acomplete_if_braun`
    + `size_heapOfA`. -/
theorem T_heapOfA_log_bound (xs : List α) :
    T_heapOfA xs ≤ xs.length * (nlog2 (xs.length + 1) + 1) := by
  have hbound := T_heapOfA_bound xs
  have hheight : height (heapOfA xs) = nlog2 (xs.length + 1) := by
    have hac : acomplete (heapOfA xs) := acomplete_if_braun (braun_heapOfA xs)
    have h := height_acomplete hac
    rw [size1_size, size_heapOfA] at h
    exact h
  rw [hheight] at hbound
  exact hbound
/-- Time of `heapify`: Isabelle's `t_heapify`. -/
def tHeapify : ℕ → List α → ℕ
  | 0, _ => 1
  | (_ + 1), [] => 1
  | (n + 1), (x :: xs) =>
      let (l, ys) := heapify ((n + 1) / 2) xs
      let (r, zs) := heapify (n / 2) ys
      1 + tHeapify ((n + 1) / 2) xs + tHeapify (n / 2) ys + tSiftDown l x r
termination_by n _ => n
decreasing_by all_goals omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_heapify_induct`, by strong induction on `n`. -/
theorem t_heapify_induct : ∀ (n : ℕ) (xs : List α), n ≤ xs.length →
    tHeapify n xs + height (heapify n xs).1 ≤ 5 * n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro xs hn
      cases n with
      | zero =>
          simp [tHeapify, heapify, height]
      | succ n' =>
          cases xs with
          | nil => simp at hn
          | cons x xs' =>
              have hlencons : (x :: xs').length = xs'.length + 1 := rfl
              have hn' : n' ≤ xs'.length := by omega
              have h1le : (n' + 1) / 2 ≤ xs'.length := by omega
              cases h1eq : heapify ((n' + 1) / 2) xs' with
              | mk l ys =>
                  have hys : ys = xs'.drop ((n' + 1) / 2) :=
                    heapify_snd_tup h1eq h1le
                  have hyslen : ys.length = xs'.length - (n' + 1) / 2 := by
                    rw [hys, List.length_drop]
                  have h2le : n' / 2 ≤ ys.length := by omega
                  cases h2eq : heapify (n' / 2) ys with
                  | mk r zs =>
                      have hbraun : Braun (BraunTree.Node l x r) := by
                        have hc1 := heapify_correct ((n' + 1) / 2) xs' h1le l ys h1eq
                        have hc2 := heapify_correct (n' / 2) ys h2le r zs h2eq
                        rw [braun_node]
                        refine ⟨?_, hc1.2.2.1, hc2.2.2.1⟩
                        omega
                      have ih1 := ih ((n' + 1) / 2) (by omega) xs' h1le
                      have ih2 := ih (n' / 2) (by omega) ys h2le
                      rw [h1eq] at ih1
                      rw [h2eq] at ih2
                      dsimp only at ih1 ih2
                      have hts : tSiftDown l x r ≤ height l + 1 := by
                        have h1 := tSiftDown_height hbraun
                        rw [braun_height_node_eq hbraun] at h1
                        omega
                      have hsh : height (siftDown l x r) ≤ height r + 2 := by
                        have h1 := siftDown_height hbraun
                        have h2 := braun_height_node_eq hbraun
                        have h3 := braun_height_l_le hbraun
                        omega
                      have ht : tHeapify (n' + 1) (x :: xs') =
                          1 + tHeapify ((n' + 1) / 2) xs' + tHeapify (n' / 2) ys +
                            tSiftDown l x r := by
                        simp [tHeapify, h1eq, h2eq]
                      have hhep : (heapify (n' + 1) (x :: xs')).1 = siftDown l x r := by
                        rw [heapify_succ_cons, h1eq]
                        dsimp only
                        rw [h2eq]
                      rw [ht, hhep]
                      omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_heapify_bound`. -/
theorem t_heapify_bound {n : ℕ} {xs : List α} (hn : n ≤ xs.length) :
    tHeapify n xs ≤ 5 * n + 1 := by
  have h := t_heapify_induct n xs hn
  omega

/-! ### Phase 2, Algorithm A: `merge` and `list_of_A` -/

/-- Isabelle's `merge` (Sorting version, Algorithm A). -/
def merge : BraunTree α → BraunTree α → BraunTree α
  | .Leaf, r => r
  | l, .Leaf => l
  | .Node l₁ a₁ r₁, .Node l₂ a₂ r₂ =>
      if a₁ ≤ a₂ then BraunTree.Node (merge l₁ r₁) a₁ (BraunTree.Node l₂ a₂ r₂)
      else BraunTree.Node (BraunTree.Node l₁ a₁ r₁) a₂ (merge l₂ r₂)
termination_by l r => size l + size r
decreasing_by all_goals simp only [size]; omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `merge_size`. -/
theorem merge_size (l r : BraunTree α) :
    size (merge l r) = size l + size r := by
  induction l, r using merge.induct with
  | case1 r => simp [merge, size]
  | case2 l => simp [merge, size]
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_true]
      simp only [size]
      omega
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_false]
      simp only [size]
      omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `set_tree_merge`. -/
theorem set_merge (l r : BraunTree α) :
    setTree (merge l r) = setTree l ∪ setTree r := by
  induction l, r using merge.induct with
  | case1 r => simp [merge, setTree]
  | case2 l => simp [merge, setTree]
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_true]
      ext y
      simp [setTree, ih]
      tauto
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_false]
      ext y
      simp [setTree, ih]
      tauto

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `mset_tree_merge`. -/
theorem mset_merge_sort (l r : BraunTree α) :
    msetTree (merge l r) = msetTree l + msetTree r := by
  induction l, r using merge.induct with
  | case1 r => simp [merge, msetTree]
  | case2 l => simp [merge, msetTree]
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_true]
      have m1 : msetTree (BraunTree.Node (merge l₁ r₁) a₁ (BraunTree.Node l₂ a₂ r₂))
          = {a₁} + msetTree (merge l₁ r₁) + msetTree (BraunTree.Node l₂ a₂ r₂) := rfl
      rw [m1, ih]
      have m2 : msetTree (BraunTree.Node l₁ a₁ r₁) = {a₁} + msetTree l₁ + msetTree r₁ := rfl
      have m3 : msetTree (BraunTree.Node l₂ a₂ r₂) = {a₂} + msetTree l₂ + msetTree r₂ := rfl
      rw [m2, m3]
      ac_rfl
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_false]
      have m1 : msetTree (BraunTree.Node (BraunTree.Node l₁ a₁ r₁) a₂ (merge l₂ r₂))
          = {a₂} + msetTree (BraunTree.Node l₁ a₁ r₁) + msetTree (merge l₂ r₂) := rfl
      rw [m1, ih]
      have m2 : msetTree (BraunTree.Node l₁ a₁ r₁) = {a₁} + msetTree l₁ + msetTree r₁ := rfl
      have m3 : msetTree (BraunTree.Node l₂ a₂ r₂) = {a₂} + msetTree l₂ + msetTree r₂ := rfl
      rw [m2, m3]
      ac_rfl

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `merge_heap`. -/
theorem merge_heap {l r : BraunTree α} (hl : Heap l) (hr : Heap r) :
    Heap (merge l r) := by
  induction l, r using merge.induct with
  | case1 r => simpa [merge] using hr
  | case2 l => simpa [merge] using hl
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      have hhl : Heap (BraunTree.Node l₁ a₁ r₁) := hl
      rw [heap_node] at hhl
      obtain ⟨_, _, hhl1, hhr1⟩ := hhl
      have hih : Heap (merge l₁ r₁) := ih hhl1 hhr1
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (merge l₁ r₁) a₁ (BraunTree.Node l₂ a₂ r₂) := by
        simp [merge, hle]
      rw [hmerge, heap_node]
      refine ⟨?_, ?_, hih, hr⟩
      · intro y hy
        have hy' : y ∈ msetTree (merge l₁ r₁) := hy
        rw [mset_merge_sort] at hy'
        simp only [Multiset.mem_add] at hy'
        rcases hy' with hy1 | hy1
        · exact heap_root_le hl y (by
            rw [show msetTree (BraunTree.Node l₁ a₁ r₁) = {a₁} + msetTree l₁ + msetTree r₁ from rfl]
            exact (Multiset.mem_add).mpr (Or.inl ((Multiset.mem_add).mpr (Or.inr hy1))))
        · exact heap_root_le hl y (by
            rw [show msetTree (BraunTree.Node l₁ a₁ r₁) = {a₁} + msetTree l₁ + msetTree r₁ from rfl]
            exact (Multiset.mem_add).mpr (Or.inr hy1))
      · intro y hy
        exact le_trans hle (heap_root_le hr y hy)
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      have hhl : Heap (BraunTree.Node l₁ a₁ r₁) := hl
      rw [heap_node] at hhl
      obtain ⟨_, _, hhl1, hhr1⟩ := hhl
      have hhr : Heap (BraunTree.Node l₂ a₂ r₂) := hr
      rw [heap_node] at hhr
      obtain ⟨_, _, hhr1, hhr2⟩ := hhr
      have hih : Heap (merge l₂ r₂) := ih hhr1 hhr2
      have hmerge : merge (BraunTree.Node l₁ a₁ r₁) (BraunTree.Node l₂ a₂ r₂)
          = BraunTree.Node (BraunTree.Node l₁ a₁ r₁) a₂ (merge l₂ r₂) := by
        simp [merge, hle]
      rw [hmerge, heap_node]
      refine ⟨?_, ?_, hl, hih⟩
      · intro y hy
        exact le_trans (le_of_lt (lt_of_not_ge hle)) (heap_root_le hl y hy)
      · intro y hy
        have hy' : y ∈ msetTree (merge l₂ r₂) := hy
        rw [mset_merge_sort] at hy'
        simp only [Multiset.mem_add] at hy'
        rcases hy' with hy1 | hy1
        · exact heap_root_le hr y (by
            rw [show msetTree (BraunTree.Node l₂ a₂ r₂) = {a₂} + msetTree l₂ + msetTree r₂ from rfl]
            exact (Multiset.mem_add).mpr (Or.inl ((Multiset.mem_add).mpr (Or.inr hy1))))
        · exact heap_root_le hr y (by
            rw [show msetTree (BraunTree.Node l₂ a₂ r₂) = {a₂} + msetTree l₂ + msetTree r₂ from rfl]
            exact (Multiset.mem_add).mpr (Or.inr hy1))

/-- Isabelle's `list_of_A`: extract by repeatedly merging children.
    Well-founded on `size t`, since `size (merge l r) = size l + size r`. -/
def listOfA : BraunTree α → List α
  | .Leaf => []
  | .Node l a r => a :: listOfA (merge l r)
termination_by t => size t
decreasing_by simp only [merge_size, size]; omega

omit [DecidableLT α] [DecidableEq α] in
/-- One-step equation for `listOfA` on a node. -/
theorem listOfA_node (l : BraunTree α) (a : α) (r : BraunTree α) :
    listOfA (BraunTree.Node l a r) = a :: listOfA (merge l r) := by
  simp [listOfA]

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `set_list_of_A`, by strong induction on `size t`.
    Stated as an `Iff` over `List.Mem` (the List→Set coercion is not
    in scope with this file's narrow imports). -/
theorem set_listOfA : ∀ (t : BraunTree α) (y : α),
    y ∈ listOfA t ↔ y ∈ setTree t := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf =>
          intro y
          simp [listOfA, setTree]
      | Node l a r =>
          intro y
          have hlt : size (merge l r) < m := by
            have hms := merge_size l r
            have : size (BraunTree.Node l a r) = m := h
            simp only [size] at this ⊢
            omega
          have h1 := ih (size (merge l r)) hlt (merge l r) rfl
          rw [listOfA_node]
          simp only [List.mem_cons]
          rw [h1 y, set_merge]
          simp only [setTree, Set.mem_union, Set.mem_singleton_iff]
          tauto

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `mset_list_of_A`, by strong induction on `size t`. -/
theorem mset_listOfA : ∀ (t : BraunTree α), ((listOfA t : List α) : Multiset α) = msetTree t := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf => simp [listOfA, msetTree]
      | Node l a r =>
          have hlt : size (merge l r) < m := by
            have : size (BraunTree.Node l a r) = m := h
            have hms := merge_size l r
            simp only [size] at this ⊢
            omega
          have h1 := ih (size (merge l r)) hlt (merge l r) rfl
          rw [mset_merge_sort] at h1
          have m1 : msetTree (BraunTree.Node l a r) = {a} + msetTree l + msetTree r := rfl
          rw [listOfA_node, m1]
          have hcoe : ((a :: listOfA (merge l r) : List α) : Multiset α) =
              {a} + ((listOfA (merge l r) : List α) : Multiset α) := by simp
          rw [hcoe, h1]
          ac_rfl

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `sorted_list_of_A`, by strong induction on `size t`. -/
theorem sorted_listOfA : ∀ (t : BraunTree α), Heap t → List.Pairwise (· ≤ ·) (listOfA t) := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf => intro _; simp [listOfA]
      | Node l a r =>
          intro ht
          have htNode : Heap (BraunTree.Node l a r) := ht
          rw [heap_node] at ht
          obtain ⟨_, _, htl, htr⟩ := ht
          rw [listOfA_node]
          refine List.pairwise_cons.mpr ⟨?_, ?_⟩
          · intro b hb
            have hb' : b ∈ setTree (merge l r) := by
              have hs := set_listOfA (merge l r) b
              exact hs.mp hb
            rw [set_merge] at hb'
            simp only [Set.mem_union] at hb'
            rcases hb' with hb1 | hb1
            · exact heap_root_le htNode b (mem_setTree.mp (by simp [setTree, hb1]))
            · exact heap_root_le htNode b (mem_setTree.mp (by simp [setTree, hb1]))
          · have hlt : size (merge l r) < m := by
              have hms := merge_size l r
              have : size (BraunTree.Node l a r) = m := h
              simp only [size] at this ⊢
              omega
            exact ih (size (merge l r)) hlt (merge l r) rfl (merge_heap htl htr)

omit [DecidableEq α] in
/-- AFP lemma `sortedA`. -/
theorem sortedA (xs : List α) :
    List.Pairwise (· ≤ ·) (listOfA (heapOfA xs)) :=
  sorted_listOfA (heapOfA xs) (heap_heapOfA xs)

omit [DecidableEq α] in
/-- AFP lemma `msetA`. -/
theorem msetA (xs : List α) :
    ((listOfA (heapOfA xs) : List α) : Multiset α) = (xs : Multiset α) := by
  rw [mset_listOfA, mset_heapOfA]

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `merge_height`. -/
theorem merge_height (l r : BraunTree α) :
    height (merge l r) ≤ max (height l) (height r) + 1 := by
  induction l, r using merge.induct with
  | case1 r => simp [merge, height]
  | case2 l => simp [merge, height]
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_true]
      simp only [height]
      have h1 := ih
      omega
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [merge, hle, ite_false]
      simp only [height]
      have h1 := ih
      omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP corollary `merge_height_display`: `merge` does not exceed the
    height of the node built from its arguments. -/
theorem merge_height_display (l r : BraunTree α) (x : α) :
    height (merge l r) ≤ height (BraunTree.Node l x r) := by
  have h := merge_height l r
  have hH : height (BraunTree.Node l x r) = max (height l) (height r) + 1 := rfl
  rw [hH]
  exact h

/-- Isabelle's `t_merge`. -/
def tMerge : BraunTree α → BraunTree α → ℕ
  | .Leaf, _ => 0
  | _, .Leaf => 0
  | .Node l₁ a₁ r₁, .Node l₂ a₂ r₂ =>
      if a₁ ≤ a₂ then 1 + tMerge l₁ r₁ else 1 + tMerge l₂ r₂
termination_by l r => size l + size r
decreasing_by all_goals simp only [size]; omega

/-- Isabelle's `t_list_of_A`, well-founded on `size t`. -/
def tListOfA : BraunTree α → ℕ
  | .Leaf => 0
  | .Node l a r => 1 + tMerge l r + tListOfA (merge l r)
termination_by t => size t
decreasing_by simp only [merge_size, size]; omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_merge_height`. -/
theorem tMerge_height (l r : BraunTree α) :
    tMerge l r ≤ max (height l) (height r) := by
  induction l, r using tMerge.induct with
  | case1 r => simp [tMerge]
  | case2 l => simp [tMerge]
  | case3 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [tMerge, hle, ite_true]
      have h1 := ih
      simp only [height] at *
      omega
  | case4 l₁ a₁ r₁ l₂ a₂ r₂ hle ih =>
      simp only [tMerge, hle, ite_false]
      have h1 := ih
      simp only [height] at *
      omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_list_of_A_induct`, by strong induction on `size t`. -/
theorem tListOfA_induct : ∀ (t : BraunTree α) (n : ℕ),
    height t ≤ n → tListOfA t ≤ 2 * n * size t := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf => simp [tListOfA]
      | Node l a r =>
          intro n hn
          have ht : tListOfA (BraunTree.Node l a r) = 1 + tMerge l r + tListOfA (merge l r) := by
            simp [tListOfA]
          have hmh : height (merge l r) ≤ height (BraunTree.Node l a r) := by
            have h1 := merge_height l r
            simp only [height] at h1 ⊢
            omega
          have hlt : size (merge l r) < m := by
            have : size (BraunTree.Node l a r) = m := h
            have hms := merge_size l r
            simp only [size] at this ⊢
            omega
          have hih := ih (size (merge l r)) hlt (merge l r) rfl n (le_trans hmh hn)
          have htm := tMerge_height l r
          simp only [height] at hn
          have hexp : 2 * n * m = 2 * n * size (merge l r) + 2 * n := by
            have hms := merge_size l r
            have hsz2 : size (BraunTree.Node l a r) = size l + size r + 1 := rfl
            have hm : m = size (merge l r) + 1 := by omega
            rw [hm]
            ring
          rw [ht, hexp]
          omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_list_of_A_bound`. -/
theorem tListOfA_bound (t : BraunTree α) :
    tListOfA t ≤ 2 * height t * size t :=
  tListOfA_induct t (height t) le_rfl

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_list_of_A_log_bound`. -/
theorem tListOfA_log_bound (t : BraunTree α) (hb : Braun t) :
    tListOfA t ≤ 2 * nlog2 (size t + 1) * size t := by
  have hbound := tListOfA_bound t
  have hheight : height t = nlog2 (size t + 1) := by
    have hac : acomplete t := acomplete_if_braun hb
    have h := height_acomplete hac
    rw [size1_size] at h
    exact h
  rw [hheight] at hbound
  exact hbound

omit [DecidableEq α] in
/-- AFP theorem `t_sortA`: `O(n log n)` for sorting via insertion-heap
    + merge extraction. -/
theorem t_sortA (xs : List α) :
    T_heapOfA xs + tListOfA (heapOfA xs) ≤
      3 * xs.length * (nlog2 (xs.length + 1) + 1) := by
  have h1 := T_heapOfA_log_bound xs
  have h2 := tListOfA_log_bound (heapOfA xs) (braun_heapOfA xs)
  rw [size_heapOfA] at h2
  -- `3 * L * (N + 1) = (L * (N + 1) + 2 * N * L) + 2 * L`: the
  -- two `A`-bounds leave `2 * L` of slack.
  have h3 : 3 * xs.length * (nlog2 (xs.length + 1) + 1) =
      (xs.length * (nlog2 (xs.length + 1) + 1) + 2 * nlog2 (xs.length + 1) * xs.length) +
        2 * xs.length := by
    ring
  rw [h3]
  exact Nat.le_trans (Nat.add_le_add h1 h2) (Nat.le_add_right _ _)



omit [LinearOrder α] [DecidableLT α] [DecidableLE α] in
/-- `y ∈ s - t → y ∈ s` (via `count`, since `Multiset.sub_le`
    is not in scope). -/
theorem mem_mset_sub_of_mem {s t : Multiset α} {y : α} (h : y ∈ s - t) : y ∈ s := by
  have hc := Multiset.count_pos.mpr h
  rw [Multiset.count_sub] at hc
  have hc2 : 0 < s.count y := by omega
  exact Multiset.count_pos.mp hc2

/-! ### Phase 2, Algorithm B: `list_of_B` and `heap_of_B` -/

/-- Isabelle's `list_of_B`, by fuel. Isabelle's version is only
    conditionally terminating (it terminates on Braun trees, since
    `delMin` removes one element); the fuel `size t` is the
    termination certificate, and `listOfB'_node` is the unfolding
    equation on Braun trees. -/
def listOfB : ℕ → BraunTree α → List α
  | _, .Leaf => []
  | 0, .Node _ _ _ => []
  | (n + 1), .Node l a r => a :: listOfB n (delMin (BraunTree.Node l a r))

/-- `list_of_B` of a tree, with fuel `size t`. -/
def listOfB' (t : BraunTree α) : List α := listOfB (size t) t

omit [DecidableLT α] [DecidableEq α] in
/-- Unfolding equation for `listOfB'` on a Braun node. -/
theorem listOfB'_node {l : BraunTree α} {a : α} {r : BraunTree α}
    (hb : Braun (BraunTree.Node l a r)) :
    listOfB' (BraunTree.Node l a r) = a :: listOfB' (delMin (BraunTree.Node l a r)) := by
  change listOfB (size (BraunTree.Node l a r)) (BraunTree.Node l a r) =
    a :: listOfB (size (delMin (BraunTree.Node l a r))) (delMin (BraunTree.Node l a r))
  have hsz : size (delMin (BraunTree.Node l a r)) = size (BraunTree.Node l a r) - 1 :=
    size_delMin hb
  have hfuel : size (BraunTree.Node l a r) =
      size (delMin (BraunTree.Node l a r)) + 1 := by
    have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
    omega
  rw [hfuel]
  simp only [listOfB]

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `mset_list_of_B`, by strong induction on `size t`. -/
theorem mset_listOfB : ∀ (t : BraunTree α), Braun t →
    ((listOfB' t : List α) : Multiset α) = msetTree t := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf => intro _; simp [listOfB', listOfB, msetTree]
      | Node l a r =>
          intro hb
          rw [listOfB'_node hb]
          have hlt : size (delMin (BraunTree.Node l a r)) < m := by
            have hsz := size_delMin (t := BraunTree.Node l a r) hb
            have : size (BraunTree.Node l a r) = m := h
            have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
            omega
          have h1 := ih (size (delMin (BraunTree.Node l a r))) hlt
            (delMin (BraunTree.Node l a r)) rfl (braun_delMin hb)
          have hdelm : msetTree (delMin (BraunTree.Node l a r)) =
              msetTree (BraunTree.Node l a r) - {a} :=
            mset_delMin hb (by simp) l a r rfl
          have hcoe : ((a :: listOfB' (delMin (BraunTree.Node l a r)) : List α) : Multiset α) =
              {a} + ((listOfB' (delMin (BraunTree.Node l a r)) : List α) : Multiset α) := by simp
          have hle : ({a} : Multiset α) ≤ msetTree (BraunTree.Node l a r) :=
            Multiset.singleton_le.mpr (by simp [msetTree])
          rw [hcoe, h1, hdelm, add_tsub_cancel_of_le hle]

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `set_list_of_B`. -/
theorem set_listOfB : ∀ (t : BraunTree α), Braun t →
    ∀ (y : α), y ∈ listOfB' t ↔ y ∈ setTree t := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf => intro _ y; simp [listOfB', listOfB, setTree]
      | Node l a r =>
          intro hb y
          rw [listOfB'_node hb]
          simp only [List.mem_cons]
          constructor
          · rintro (rfl | hy)
            · simp [setTree]
            · have hlt : size (delMin (BraunTree.Node l a r)) < m := by
                have hsz := size_delMin (t := BraunTree.Node l a r) hb
                have : size (BraunTree.Node l a r) = m := h
                have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
                omega
              have h1 := ih (size (delMin (BraunTree.Node l a r))) hlt
                (delMin (BraunTree.Node l a r)) rfl (braun_delMin hb) y
              have hy' : y ∈ setTree (delMin (BraunTree.Node l a r)) := h1.mp hy
              have hy_mset : y ∈ msetTree (delMin (BraunTree.Node l a r)) :=
                mem_setTree.mp hy'
              have hy_le : y ∈ msetTree (BraunTree.Node l a r) := by
                have hdelm : msetTree (delMin (BraunTree.Node l a r)) =
                    msetTree (BraunTree.Node l a r) - {a} :=
                  mset_delMin hb (by simp) l a r rfl
                rw [hdelm] at hy_mset
                exact mem_mset_sub_of_mem hy_mset
              exact mem_setTree.mpr hy_le
          · intro hy
            by_cases hya : y = a
            · exact Or.inl hya
            · right
              have hlt : size (delMin (BraunTree.Node l a r)) < m := by
                have hsz := size_delMin (t := BraunTree.Node l a r) hb
                have : size (BraunTree.Node l a r) = m := h
                have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
                omega
              have h1 := ih (size (delMin (BraunTree.Node l a r))) hlt
                (delMin (BraunTree.Node l a r)) rfl (braun_delMin hb) y
              apply h1.mpr
              have hy_mset : y ∈ msetTree (BraunTree.Node l a r) :=
                mem_setTree.mp hy
              have hdelm : msetTree (delMin (BraunTree.Node l a r)) =
                  msetTree (BraunTree.Node l a r) - {a} :=
                mset_delMin hb (by simp) l a r rfl
              rw [mem_setTree, hdelm]
              have hcount : (msetTree (BraunTree.Node l a r) - {a}).count y =
                  (msetTree (BraunTree.Node l a r)).count y := by
                rw [Multiset.count_sub, Multiset.count_singleton]
                simp [hya]
              rw [← Multiset.count_pos, hcount]
              exact Multiset.count_pos.mpr hy_mset

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `sorted_list_of_B`, by strong induction on `size t`. -/
theorem sorted_listOfB : ∀ (t : BraunTree α), Braun t → Heap t →
    List.Pairwise (· ≤ ·) (listOfB' t) := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf => intro _ _; simp [listOfB', listOfB]
      | Node l a r =>
          intro hb ht
          rw [listOfB'_node hb]
          have htNode : Heap (BraunTree.Node l a r) := ht
          have hlt : size (delMin (BraunTree.Node l a r)) < m := by
            have hsz := size_delMin (t := BraunTree.Node l a r) hb
            have : size (BraunTree.Node l a r) = m := h
            have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
            omega
          have h1 := ih (size (delMin (BraunTree.Node l a r))) hlt
            (delMin (BraunTree.Node l a r)) rfl (braun_delMin hb) (heap_delMin ht hb)
          refine List.pairwise_cons.mpr ⟨?_, h1⟩
          intro b hb_mem
          have hb' : b ∈ setTree (delMin (BraunTree.Node l a r)) := by
            have hs := set_listOfB (delMin (BraunTree.Node l a r)) (braun_delMin hb) b
            exact hs.mp hb_mem
          have hb_mset : b ∈ msetTree (delMin (BraunTree.Node l a r)) :=
            mem_setTree.mp hb'
          have hb_le : b ∈ msetTree (BraunTree.Node l a r) := by
            have hdelm : msetTree (delMin (BraunTree.Node l a r)) =
                msetTree (BraunTree.Node l a r) - {a} :=
              mset_delMin hb (by simp) l a r rfl
            rw [hdelm] at hb_mset
            exact mem_mset_sub_of_mem hb_mset
          exact heap_root_le htNode b hb_le

/-- Isabelle's `heap_of_B`: the `heapify` heap of a list. -/
def heapOfB (xs : List α) : BraunTree α := (heapify xs.length xs).1

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `sortedB`. -/
theorem sortedB (xs : List α) : List.Pairwise (· ≤ ·) (listOfB' (heapOfB xs)) :=
  sorted_listOfB (heapOfB xs) (braun_heapify (le_refl _)) (heap_heapify (le_refl _))

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `msetB`. -/
theorem msetB (xs : List α) :
    ((listOfB' (heapOfB xs) : List α) : Multiset α) = (xs : Multiset α) := by
  rw [mset_listOfB (heapOfB xs) (braun_heapify (le_refl _))]
  rw [heapOfB, mset_heapify (le_refl _)]
  simp

/-- Isabelle's `t_heap_of_B`: `length xs + t_heapify (length xs) xs`. -/
def T_heapOfB (xs : List α) : ℕ := xs.length + tHeapify xs.length xs

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `size_heapify` (through `heap_of_B`): the `heapify` heap
    has `length xs` elements. -/
theorem size_heapOfB (xs : List α) : size (heapOfB xs) = xs.length := by
  rw [heapOfB, size_eq_card_msetTree, mset_heapify (le_refl _), List.take_length]
  simp

/-! ### Phase 2, Algorithm B: running time -/

/-- Isabelle's `t_del_left`. -/
def tDelLeft : BraunTree α → ℕ
  | .Leaf => 0
  | .Node .Leaf _ _ => 1
  | .Node (.Node l₁ x₁ r₁) _x _r =>
      match delLeft (BraunTree.Node l₁ x₁ r₁) with
      | some (_, _) => 2 + tDelLeft (BraunTree.Node l₁ x₁ r₁)
      | none => 2 + tDelLeft (BraunTree.Node l₁ x₁ r₁)

/-- Isabelle's `t_del_min`. -/
def tDelMin : BraunTree α → ℕ
  | .Leaf => 0
  | .Node .Leaf _ _ => 0
  | .Node (.Node l₁ x₁ r₁) _ r =>
      match delLeft (BraunTree.Node l₁ x₁ r₁) with
      | some (y, l') => tDelLeft (BraunTree.Node l₁ x₁ r₁) + tSiftDown r y l'
      | none => tDelLeft (BraunTree.Node l₁ x₁ r₁)

/-- Isabelle's `t_list_of_B`, by fuel (it is only conditionally
    terminating; the fuel `size t` is the certificate on Braun trees). -/
def tListOfB : ℕ → BraunTree α → ℕ
  | _, .Leaf => 0
  | 0, .Node _ _ _ => 0
  | (n + 1), .Node l a r =>
      1 + tDelMin (BraunTree.Node l a r) + tListOfB n (delMin (BraunTree.Node l a r))

/-- `t_list_of_B` of a tree, with fuel `size t`. -/
def tListOfB' (t : BraunTree α) : ℕ := tListOfB (size t) t

omit [DecidableLT α] [DecidableEq α] in
/-- Unfolding equation for `tListOfB'` on a Braun node. -/
theorem tListOfB'_node {l : BraunTree α} {a : α} {r : BraunTree α}
    (hb : Braun (BraunTree.Node l a r)) :
    tListOfB' (BraunTree.Node l a r) =
      1 + tDelMin (BraunTree.Node l a r) + tListOfB' (delMin (BraunTree.Node l a r)) := by
  change tListOfB (size (BraunTree.Node l a r)) (BraunTree.Node l a r) =
    1 + tDelMin (BraunTree.Node l a r)
      + tListOfB (size (delMin (BraunTree.Node l a r)))
        (delMin (BraunTree.Node l a r))
  have hsz : size (delMin (BraunTree.Node l a r)) = size (BraunTree.Node l a r) - 1 :=
    size_delMin hb
  have hfuel : size (BraunTree.Node l a r) =
      size (delMin (BraunTree.Node l a r)) + 1 := by
    have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
    omega
  rw [hfuel]
  simp only [tListOfB]

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `t_del_left_bound`. -/
theorem tDelLeft_bound {t : BraunTree α} (ht : t ≠ BraunTree.Leaf) :
    tDelLeft t ≤ 2 * height t := by
  induction t with
  | Leaf => exact absurd rfl ht
  | Node l c r ih =>
      cases l with
      | Leaf =>
          simp only [tDelLeft, height]
          omega
      | Node l₁ x₁ r₁ =>
          have h1 : tDelLeft (BraunTree.Node l₁ x₁ r₁) ≤ 2 * height (BraunTree.Node l₁ x₁ r₁) :=
            ih (by simp)
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              obtain ⟨y, l', hdl'⟩ := delLeft_some_of_ne_leaf
                (show (BraunTree.Node l₁ x₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
              rw [hdl'] at hdl; contradiction
          | some p =>
              simp [tDelLeft, hdl]
              have hd : height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r) =
                  max (height (BraunTree.Node l₁ x₁ r₁)) (height r) + 1 := rfl
              omega

omit [LinearOrder α] [DecidableLT α] [DecidableLE α] [DecidableEq α] in
/-- AFP lemma `del_left_height`. -/
theorem delLeft_height {t : BraunTree α} {y : α} {t' : BraunTree α}
    (h : delLeft t = some (y, t')) (ht : t ≠ BraunTree.Leaf) :
    height t' ≤ height t := by
  induction t generalizing y t' with
  | Leaf =>
      simp only [delLeft] at h
      cases h
  | Node l c r ih =>
      cases l with
      | Leaf =>
          simp only [delLeft] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [height]
          omega
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              obtain ⟨z, l'', hdl'⟩ := delLeft_some_of_ne_leaf
                (show (BraunTree.Node l₁ x₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
              rw [hdl'] at hdl; contradiction
          | some q =>
              obtain ⟨z, l''⟩ := q
              have h1 : delLeft (BraunTree.Node l₁ x₁ r₁) = some (z, l'') := hdl
              have h2 := ih h1 (by simp)
              simp only [delLeft, hdl] at h
              obtain ⟨rfl, rfl⟩ := h
              have hmax : max (height r) (height l'') ≤
                  max (height (BraunTree.Node l₁ x₁ r₁)) (height r) := by
                simp only [max_def]
                split_ifs
                all_goals omega
              exact Nat.add_le_add_right hmax 1

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_del_min_bound`. -/
theorem tDelMin_bound {t : BraunTree α} (hb : Braun t) :
    tDelMin t ≤ 3 * height t := by
  cases t with
  | Leaf => simp [tDelMin, height]
  | Node l c r =>
      cases l with
      | Leaf => simp [tDelMin, height]
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              obtain ⟨y, l', hdl'⟩ := delLeft_some_of_ne_leaf
                (show (BraunTree.Node l₁ x₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
              rw [hdl'] at hdl; contradiction
          | some p =>
              obtain ⟨y, l'⟩ := p
              have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
              have hbl : Braun (BraunTree.Node l₁ x₁ r₁) := by
                rw [braun_node] at hb
                exact hb.2.1
              have hbr : Braun (BraunTree.Node r y l') := by
                exact braun_siftDown_arg hb hdl'
              have h1 : tDelLeft (BraunTree.Node l₁ x₁ r₁) ≤
                  2 * height (BraunTree.Node l₁ x₁ r₁) :=
                tDelLeft_bound (by simp)
              have h2 : tSiftDown r y l' ≤ height (BraunTree.Node r y l') :=
                tSiftDown_height hbr
              have h3 : height (BraunTree.Node r y l') ≤
                  height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r) := by
                have hh1 := delLeft_height hdl' (by simp)
                simp only [height] at *
                omega
              have ha : height (BraunTree.Node l₁ x₁ r₁) ≤
                  height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r) := by
                simp only [height]
                omega
              simp [tDelMin, hdl]
              omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `del_min_height`. -/
theorem delMin_height {t : BraunTree α} (hb : Braun t) :
    height (delMin t) ≤ height t := by
  cases t with
  | Leaf => simp [delMin, height]
  | Node l c r =>
      cases l with
      | Leaf => simp [delMin, height]
      | Node l₁ x₁ r₁ =>
          cases hdl : delLeft (BraunTree.Node l₁ x₁ r₁) with
          | none =>
              obtain ⟨y, l', hdl'⟩ := delLeft_some_of_ne_leaf
                (show (BraunTree.Node l₁ x₁ r₁ : BraunTree α) ≠ BraunTree.Leaf by simp)
              rw [hdl'] at hdl; contradiction
          | some p =>
              obtain ⟨y, l'⟩ := p
              have hdl' : delLeft (BraunTree.Node l₁ x₁ r₁) = some (y, l') := hdl
              have hbr : Braun (BraunTree.Node r y l') := braun_siftDown_arg hb hdl'
              have h1 : height (siftDown r y l') ≤ height (BraunTree.Node r y l') :=
                siftDown_height hbr
              have h2 : height (BraunTree.Node r y l') ≤
                  height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r) := by
                have hh1 := delLeft_height hdl' (by simp)
                simp only [height] at *
                omega
              have hsd : delMin (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) c r)
                  = siftDown r y l' := by
                simp [delMin, hdl]
              rw [hsd]
              omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_list_of_B_induct`, by strong induction on `size t`. -/
theorem tListOfB_induct : ∀ (t : BraunTree α) (n : ℕ),
    Braun t → height t ≤ n → tListOfB' t ≤ 3 * (n + 1) * size t := by
  intro t
  induction h : size t using Nat.strong_induction_on generalizing t with
  | _ m ih =>
      cases t with
      | Leaf => intro _ n _; simp [tListOfB', tListOfB, size]
      | Node l a r =>
          intro n hb hn
          rw [tListOfB'_node hb]
          have hlt : size (delMin (BraunTree.Node l a r)) < m := by
            have hsz := size_delMin (t := BraunTree.Node l a r) hb
            have : size (BraunTree.Node l a r) = m := h
            have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
            omega
          have hih := ih (size (delMin (BraunTree.Node l a r))) hlt
            (delMin (BraunTree.Node l a r)) rfl n (braun_delMin hb) (le_trans (delMin_height hb) hn)
          have htm := tDelMin_bound hb
          have hsz : size (BraunTree.Node l a r) = size (delMin (BraunTree.Node l a r)) + 1 := by
            have h1 := size_delMin (t := BraunTree.Node l a r) hb
            have hpos : 0 < size (BraunTree.Node l a r) := by simp [size]
            omega
          have hexp : 3 * (n + 1) * m =
              3 * (n + 1) * size (delMin (BraunTree.Node l a r)) + 3 * (n + 1) := by
            have : m = size (delMin (BraunTree.Node l a r)) + 1 := by omega
            rw [this]
            ring
          have hgoal : 1 + tDelMin (BraunTree.Node l a r)
              + tListOfB' (delMin (BraunTree.Node l a r)) ≤ 3 * (n + 1) * m := by
            have hn' : height (BraunTree.Node l a r) ≤ n := hn
            omega
          exact hgoal

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_list_of_B_bound`. -/
theorem tListOfB_bound (t : BraunTree α) (hb : Braun t) :
    tListOfB' t ≤ 3 * (height t + 1) * size t :=
  tListOfB_induct t (height t) hb le_rfl

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_list_of_B_log_bound`. -/
theorem tListOfB_log_bound (t : BraunTree α) (hb : Braun t) :
    tListOfB' t ≤ 3 * (nlog2 (size t + 1) + 1) * size t := by
  have hbound := tListOfB_bound t hb
  have hheight : height t = nlog2 (size t + 1) := by
    have hac : acomplete t := acomplete_if_braun hb
    have h := height_acomplete hac
    rw [size1_size] at h
    exact h
  rw [hheight] at hbound
  exact hbound

omit [DecidableLT α] [DecidableEq α] in
/-- AFP lemma `t_heap_of_B_bound`. -/
theorem tHeapOfB_bound (xs : List α) :
    T_heapOfB xs ≤ 6 * xs.length + 1 := by
  change xs.length + tHeapify xs.length xs ≤ 6 * xs.length + 1
  have h := t_heapify_bound (le_refl xs.length)
  omega

omit [DecidableLT α] [DecidableEq α] in
/-- AFP theorem `t_sortB`: `O(n log n)` for sorting via `heapify` +
    `delMin` extraction. -/
theorem t_sortB (xs : List α) :
    T_heapOfB xs + tListOfB' (heapOfB xs) ≤
      3 * xs.length * (nlog2 (xs.length + 1) + 3) + 1 := by
  have h1 : T_heapOfB xs ≤ 6 * xs.length + 1 := tHeapOfB_bound xs
  have h2 := tListOfB_log_bound (heapOfB xs) (braun_heapify (le_refl _))
  rw [size_heapOfB] at h2
  have h3 : 3 * xs.length * (nlog2 (xs.length + 1) + 3) + 1 =
      (6 * xs.length + 1) + 3 * (nlog2 (xs.length + 1) + 1) * xs.length := by
    ring
  rw [h3]
  exact Nat.add_le_add h1 h2

end Cslib.Algorithms.Lean.BraunTree.Sorting
