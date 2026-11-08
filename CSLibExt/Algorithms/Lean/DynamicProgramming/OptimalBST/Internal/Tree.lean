/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import all CSLibExt.Algorithms.Lean.DynamicProgramming.OptimalBST.Internal.Table

/-!
# Private optimal-BST tree attainment and minimality

Source: CLRS, fourth edition, Section 14.5, pages 400-407 and Figure 14.10.
Complete inorder trees retain every key and all dummy positions. The interval
split relates their full search cost to saved table values. Attainment uses the
selected root; minimality compares every competing tree's own root and subtrees.
-/

set_option autoImplicit false
universe u
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BinarySearchTree
open scoped BigOperators
namespace Cslib.Algorithms.Lean.OptimalBST
variable {R : Type u}

private def rankInterval {n : Nat} (a b : Nat) : List (Fin n) :=
  ((List.finRange n).drop a).take (b - a)

private def IntervalTree {n : Nat} (a b : Nat)
    (tree : BinaryTree (Fin n)) : Prop :=
  inorder tree = rankInterval a b

private theorem rankInterval_length {n a b : Nat} (_ha : a ≤ b) (hb : b ≤ n) :
    (rankInterval (n := n) a b).length = b - a := by
  simp [rankInterval, List.length_take, List.length_drop]
  omega

private theorem rankInterval_self {n a : Nat} :
    rankInterval (n := n) a a = [] := by
  simp [rankInterval]

private theorem rankInterval_full (n : Nat) :
    rankInterval (n := n) 0 n = List.finRange n := by
  simp [rankInterval]

private theorem rankInterval_split {n a r b : Nat}
    (ha : a ≤ r) (hr : r < b) (hb : b ≤ n) :
    rankInterval (n := n) a b =
      rankInterval a r ++ (⟨r, by omega⟩ : Fin n) :: rankInterval (r + 1) b := by
  have hWidth : b - a = (r - a) + (1 + (b - (r + 1))) := by omega
  have hOffset : a + (r - a) = r := by omega
  unfold rankInterval
  rw [hWidth, List.take_add, List.take_add, List.drop_drop, hOffset, List.drop_drop]
  rw [List.take_one_drop_eq_of_lt_length (by simpa using (show r < n by omega))]
  simp

private theorem intervalTree_nil_iff {n a b : Nat} (ha : a ≤ b) (hb : b ≤ n) :
    IntervalTree (n := n) a b .nil ↔ a = b := by
  constructor
  · intro h
    have hLength := congrArg List.length h
    simp only [inorder_nil, List.length_nil, rankInterval_length ha hb] at hLength
    omega
  · rintro rfl
    simp [IntervalTree, rankInterval_self]

private theorem intervalTree_node_iff {n a b : Nat} (key : Fin n)
    (left right : BinaryTree (Fin n)) (ha : a ≤ b) (hb : b ≤ n) :
    IntervalTree a b (.node key left right) ↔
      a ≤ key.val ∧ key.val < b ∧
        IntervalTree a key.val left ∧ IntervalTree (key.val + 1) b right := by
  constructor
  · intro hTree
    have hInorder : inorder left ++ key :: inorder right = rankInterval a b := by
      simpa [IntervalTree] using hTree
    have hWidth : (inorder left).length < b - a := by
      have hLength := congrArg List.length hInorder
      simp only [List.length_append, List.length_cons, rankInterval_length ha hb] at hLength
      omega
    have hIndex : a + (inorder left).length < n := by omega
    have hAt := congrArg (fun xs => xs[(inorder left).length]?) hInorder
    have hKey : key = (⟨a + (inorder left).length, hIndex⟩ : Fin n) := by
      apply Option.some.inj
      simpa [rankInterval, hWidth, hIndex] using hAt
    have hKeyVal := congrArg Fin.val hKey
    have hBounds : a ≤ key.val ∧ key.val < b := by
      dsimp only at hKeyVal
      omega
    have hLeftLength : (inorder left).length = key.val - a := by
      dsimp only at hKeyVal
      omega
    refine ⟨hBounds.1, hBounds.2, ?_, ?_⟩
    · have hTake := congrArg (List.take (inorder left).length) hInorder
      simp only [List.take_left, rankInterval, List.take_take,
        Nat.min_eq_left (le_of_lt hWidth)] at hTake
      simpa only [IntervalTree, rankInterval, hLeftLength] using hTake
    · have hDrop := congrArg (List.drop ((inorder left).length + 1)) hInorder
      have hOffset : a + ((inorder left).length + 1) = key.val + 1 := by omega
      have hRest : (b - a) - ((inorder left).length + 1) = b - (key.val + 1) := by omega
      simpa [IntervalTree, rankInterval, List.drop_take, List.drop_drop,
        hOffset, hRest] using hDrop
  · rintro ⟨haKey, hKeyB, hLeft, hRight⟩
    rw [IntervalTree, inorder_node, hLeft, hRight]
    exact (rankInterval_split haKey hKeyB hb).symm

private def afterKey {n : Nat} (key : Fin n) : Fin (n + 1) :=
  ⟨key.val + 1, by omega⟩

private def treeMass [AddCommMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) : Fin (n + 1) → BinaryTree (Fin n) → R
  | a, .nil => q[a.val]
  | a, .node key left right =>
      p[key.val] + treeMass p q a left + treeMass p q (afterKey key) right

private def dummyCost [AddCommMonoid R] {n : Nat} (q : Vector R (n + 1)) :
    Fin (n + 1) → Nat → BinaryTree (Fin n) → R
  | a, depth, .nil => (depth + 1) • q[a.val]
  | a, depth, .node key left right =>
      dummyCost q a (depth + 1) left +
        dummyCost q (afterKey key) (depth + 1) right

private noncomputable def intervalTreeCost [AddCommMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) (a : Fin (n + 1))
    (tree : BinaryTree (Fin n)) : R :=
  keyCost p 0 tree + dummyCost q a 0 tree

private theorem treeCost_depth [AddCommMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) (a : Fin (n + 1))
    (tree : BinaryTree (Fin n)) (depth : Nat) :
    keyCost p depth tree + dummyCost q a depth tree =
      intervalTreeCost p q a tree + depth • treeMass p q a tree := by
  induction tree generalizing a depth with
  | nil =>
      simp [keyCost, dummyCost, intervalTreeCost, treeMass, add_nsmul, add_comm]
  | node key left right ihLeft ihRight =>
      have hLeft := ihLeft a (depth + 1)
      have hRight := ihRight (afterKey key) (depth + 1)
      have hLeftOne := ihLeft a 1
      have hRightOne := ihRight (afterKey key) 1
      dsimp only [intervalTreeCost] at hLeft hRight hLeftOne hRightOne ⊢
      calc
        keyCost p depth (.node key left right) + dummyCost q a depth (.node key left right) =
            (depth + 1) • p[key.val] +
              (keyCost p (depth + 1) left + dummyCost q a (depth + 1) left) +
              (keyCost p (depth + 1) right + dummyCost q (afterKey key) (depth + 1) right) := by
                simp only [keyCost, dummyCost]
                ac_rfl
        _ = (depth + 1) • p[key.val] +
              (keyCost p 0 left + dummyCost q a 0 left + (depth + 1) • treeMass p q a left) +
              (keyCost p 0 right + dummyCost q (afterKey key) 0 right +
                (depth + 1) • treeMass p q (afterKey key) right) := by rw [hLeft, hRight]
        _ = keyCost p 0 (.node key left right) + dummyCost q a 0 (.node key left right) +
              depth • treeMass p q a (.node key left right) := by
                simp only [keyCost, dummyCost, treeMass, zero_add, one_nsmul]
                have hLeftOne' := hLeftOne
                have hRightOne' := hRightOne
                simp only [one_nsmul] at hLeftOne' hRightOne'
                calc
                  _ = p[key.val] + (keyCost p 1 left + dummyCost q a 1 left) +
                      (keyCost p 1 right + dummyCost q (afterKey key) 1 right) +
                      depth • (p[key.val] + treeMass p q a left +
                        treeMass p q (afterKey key) right) := by
                          rw [hLeftOne', hRightOne']
                          simp only [add_nsmul, one_nsmul, nsmul_add]
                          ac_rfl
                  _ = _ := by ac_rfl

private theorem treeCost_node [AddCommMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1)) (a : Fin (n + 1)) (key : Fin n)
    (left right : BinaryTree (Fin n)) :
    intervalTreeCost p q a (.node key left right) =
      intervalTreeCost p q a left + intervalTreeCost p q (afterKey key) right +
        treeMass p q a (.node key left right) := by
  have hLeft := treeCost_depth p q a left 1
  have hRight := treeCost_depth p q (afterKey key) right 1
  simp only [one_nsmul] at hLeft hRight
  calc
    _ = p[key.val] + (keyCost p 1 left + dummyCost q a 1 left) +
        (keyCost p 1 right + dummyCost q (afterKey key) 1 right) := by
          simp only [intervalTreeCost, keyCost, dummyCost, zero_add, one_nsmul]
          ac_rfl
    _ = _ := by rw [hLeft, hRight]; simp only [treeMass]; ac_rfl

private theorem fin_sum_halfOpen_split [AddCommMonoid R] {N : Nat}
    (f : Fin N → R) (a r b : Nat) (har : a ≤ r) (hrb : r ≤ b) :
    (∑ i : Fin N, if a ≤ i.val ∧ i.val < b then f i else 0) =
      (∑ i : Fin N, if a ≤ i.val ∧ i.val < r then f i else 0) +
        ∑ i : Fin N, if r ≤ i.val ∧ i.val < b then f i else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hLeft : a ≤ i.val ∧ i.val < r
  · have hAll : a ≤ i.val ∧ i.val < b := by omega
    have hRight : ¬(r ≤ i.val ∧ i.val < b) := by omega
    rw [ite_eq_left hAll, ite_eq_left hLeft, ite_eq_right hRight, add_zero]
  · by_cases hRight : r ≤ i.val ∧ i.val < b
    · have hAll : a ≤ i.val ∧ i.val < b := by omega
      rw [ite_eq_left hAll, ite_eq_right hLeft, ite_eq_left hRight, zero_add]
    · have hAll : ¬(a ≤ i.val ∧ i.val < b) := by omega
      rw [ite_eq_right hAll, ite_eq_right hLeft, ite_eq_right hRight, add_zero]

private theorem fin_sum_halfOpen_singleton [AddCommMonoid R] {N : Nat}
    (f : Fin N → R) (r : Fin N) :
    (∑ i : Fin N, if r.val ≤ i.val ∧ i.val < r.val + 1 then f i else 0) = f r := by
  exact (Finset.sum_eq_single_of_mem
    (f := fun i : Fin N =>
      if r.val ≤ i.val ∧ i.val < r.val + 1 then f i else 0)
    r (Finset.mem_univ _) (by
      intro i _ hi
      have hNot : ¬(r.val ≤ i.val ∧ i.val < r.val + 1) := by
        intro h
        apply hi
        exact Fin.ext (by omega)
      exact ite_eq_right hNot)).trans (by simp)

private theorem intervalMass_split [AddCommMonoid R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1)) (a : Nat) (r : Fin n) (b : Nat)
    (har : a ≤ r.val) (hrb : r.val < b) (_hb : b ≤ n) :
    intervalMass p q a b =
      intervalMass p q a r.val + p[r.val] + intervalMass p q (r.val + 1) b := by
  have hKeys₁ := fin_sum_halfOpen_split (fun i : Fin n => p[i.val])
    a r.val b har (by omega)
  have hKeys₂ := fin_sum_halfOpen_split (fun i : Fin n => p[i.val])
    r.val (r.val + 1) b (by omega) (by omega)
  have hKeyOne := fin_sum_halfOpen_singleton (fun i : Fin n => p[i.val]) r
  have hDummies := fin_sum_halfOpen_split (fun i : Fin (n + 1) => q[i.val])
    a (r.val + 1) (b + 1) (by omega) (by omega)
  simp only [Nat.lt_succ_iff] at hDummies
  dsimp only [intervalMass]
  rw [hKeys₁, hKeys₂, hKeyOne, hDummies]
  ac_rfl

private theorem treeMass_eq_intervalMass [AddCommMonoid R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1)) (a b : Nat)
    (ha : a ≤ b) (hb : b ≤ n) (tree : BinaryTree (Fin n))
    (hTree : IntervalTree a b tree) :
    treeMass p q ⟨a, by omega⟩ tree = intervalMass p q a b := by
  induction tree generalizing a b with
  | nil =>
      have hab := (intervalTree_nil_iff ha hb).mp hTree
      subst b
      exact (intervalMass_diagonal p q ⟨a, by omega⟩).symm
  | node key left right ihLeft ihRight =>
      rcases (intervalTree_node_iff key left right ha hb).mp hTree with
        ⟨haKey, hKeyB, hLeft, hRight⟩
      rw [treeMass]
      dsimp only [afterKey]
      rw [ihLeft a key.val haKey (by omega) hLeft,
        ihRight (key.val + 1) b (by omega) hb hRight,
        intervalMass_split p q a key b haKey hKeyB hb]
      ac_rfl

private def dummyListCost [AddCommMonoid R] {n : Nat}
    (q : Vector R (n + 1)) (a : Nat) (depths : List Nat)
    (h : a + depths.length ≤ n + 1) : R :=
  match depths with
  | [] => 0
  | depth :: rest =>
      (depth + 1) • q[a]'(by simp only [List.length_cons] at h; omega) +
        dummyListCost q (a + 1) rest (by simp only [List.length_cons] at h; omega)

private theorem dummyListCost_append [AddCommMonoid R] {n : Nat}
    (q : Vector R (n + 1)) (a : Nat) (xs ys : List Nat)
    (h : a + (xs ++ ys).length ≤ n + 1) :
    dummyListCost q a (xs ++ ys) h =
      dummyListCost q a xs (by simp only [List.length_append] at h; omega) +
        dummyListCost q (a + xs.length) ys (by simp only [List.length_append] at h; omega) := by
  induction xs generalizing a with
  | nil => simp [dummyListCost]
  | cons x xs ih =>
      simp only [List.cons_append, List.length_cons, dummyListCost]
      rw [ih]
      have hIndex : a + 1 + xs.length = a + (xs.length + 1) := by omega
      simp only [hIndex, add_assoc]

private theorem dummyListCost_eq_finSum [AddCommMonoid R] {n : Nat}
    (q : Vector R (n + 1)) (a : Nat) (depths : List Nat)
    (h : a + depths.length ≤ n + 1) :
    dummyListCost q a depths h =
      ∑ i : Fin depths.length, (depths[i.val] + 1) • q[a + i.val]'(by omega) := by
  induction depths generalizing a with
  | nil => simp [dummyListCost]
  | cons depth rest ih =>
      simp only [List.length_cons]
      rw [Fin.univ_succ, Finset.sum_cons, Finset.sum_map]
      simp only [dummyListCost, Fin.val_zero, List.getElem_cons_zero, Nat.add_zero]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have hIndex : a + (i.val + 1) = a + 1 + i.val := by omega
      change (rest[i.val] + 1) • q[a + 1 + i.val]'(by simp only [List.length_cons] at h; omega) =
        (rest[i.val] + 1) • q[a + (i.val + 1)]'(by simp only [List.length_cons] at h; omega)
      simp only [hIndex]

private theorem dummyListCost_eq_sum [AddCommMonoid R] {n : Nat}
    (q : Vector R (n + 1)) (depths : List Nat)
    (hLength : depths.length = n + 1) :
    dummyListCost q 0 depths (by omega) =
      ∑ i : Fin (n + 1), (depths[i.val]'(by omega) + 1) • q[i.val] := by
  have hSum := dummyListCost_eq_finSum q 0 depths (by omega)
  rw [hSum]
  let e : Fin depths.length ≃ Fin (n + 1) :=
    { toFun := fun i => ⟨i.val, by omega⟩
      invFun := fun i => ⟨i.val, by omega⟩
      left_inv := fun _ => Fin.ext rfl
      right_inv := fun _ => Fin.ext rfl }
  exact Fintype.sum_equiv e _ _ (fun i => by
    change (depths[i.val] + 1) • q[0 + i.val]'(by omega) =
      (depths[i.val] + 1) • q[i.val]'(by omega)
    simp only [zero_add])

private theorem dummyCost_eq_listCost [AddCommMonoid R] {n : Nat}
    (q : Vector R (n + 1)) (a b : Nat) (ha : a ≤ b) (hb : b ≤ n)
    (tree : BinaryTree (Fin n)) (hTree : IntervalTree a b tree)
    (depth : Nat) :
    dummyCost q ⟨a, by omega⟩ depth tree =
      dummyListCost q a (dummyDepths tree depth) (by
        rw [dummyDepths_length, BinaryTree.numLeaves_eq_numNodes_succ,
          numNodes_eq_length_inorder, hTree, rankInterval_length ha hb]
        omega) := by
  induction tree generalizing a b depth with
  | nil =>
      have hab := (intervalTree_nil_iff ha hb).mp hTree
      subst b
      simp [dummyCost, dummyDepths, dummyListCost]
  | node key left right ihLeft ihRight =>
      rcases (intervalTree_node_iff key left right ha hb).mp hTree with
        ⟨haKey, hKeyB, hLeft, hRight⟩
      have hLeftLength : (dummyDepths left (depth + 1)).length = key.val - a + 1 := by
        rw [dummyDepths_length, BinaryTree.numLeaves_eq_numNodes_succ,
          numNodes_eq_length_inorder, hLeft, rankInterval_length haKey (by omega)]
      have hOffset : a + (dummyDepths left (depth + 1)).length = key.val + 1 := by omega
      rw [dummyCost]
      simp only [dummyDepths]
      rw [dummyListCost_append]
      dsimp only [afterKey]
      rw [ihLeft a key.val haKey (by omega) hLeft (depth + 1),
        ihRight (key.val + 1) b (by omega) hb hRight (depth + 1)]
      simp only [hOffset]

private theorem expectedSearchCost_eq_intervalTreeCost [AddCommMonoid R] {n : Nat}
    (p : Vector R n) (q : Vector R (n + 1))
    (tree : BinaryTree (Fin n)) (complete : inorder tree = List.finRange n) :
    expectedSearchCost n p q tree complete =
      intervalTreeCost p q ⟨0, by omega⟩ tree := by
  have hTree : IntervalTree (n := n) 0 n tree := by
    simpa [IntervalTree, rankInterval_full] using complete
  have hLength : (dummyDepths tree 0).length = n + 1 := by
    rw [dummyDepths_length, BinaryTree.numLeaves_eq_numNodes_succ,
      numNodes_eq_length_inorder, complete]
    simp
  rw [expectedSearchCost]
  change keyCost p 0 tree +
      (∑ i : Fin (n + 1),
        ((dummyDepths tree 0)[i.val]'(by omega) + 1) • q[i.val]) =
    intervalTreeCost p q ⟨0, by omega⟩ tree
  rw [← dummyListCost_eq_sum q (dummyDepths tree 0) hLength,
    ← dummyCost_eq_listCost q 0 n (by omega) (by omega) tree hTree 0]
  rfl

private theorem interval_attains_and_minimal [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1))
    (e : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n)
    (hDiagonal : ∀ i : Fin (n + 1), e[i.val][i.val] = q[i.val])
    (hCells : ∀ (a : Fin n) (b : Fin (n + 1)) (hab : a.val < b.val),
      CellSpec p q e root a b hab)
    (a b : Nat) (ha : a ≤ b) (hb : b ≤ n) :
    ∃ tree : BinaryTree (Fin n),
      IntervalTree a b tree ∧
      intervalTreeCost p q ⟨a, by omega⟩ tree = e[a][b] ∧
      ∀ competitor : BinaryTree (Fin n), IntervalTree a b competitor →
        e[a][b] ≤ intervalTreeCost p q ⟨a, by omega⟩ competitor := by
  generalize hWidth : b - a = width
  induction width using Nat.strong_induction_on generalizing a b with
  | h width ih =>
      by_cases hab : a = b
      · subst b
        refine ⟨.nil, (intervalTree_nil_iff le_rfl hb).mpr rfl, ?_, ?_⟩
        · simp only [intervalTreeCost, keyCost, dummyCost, zero_add, one_nsmul]
          change q[a] = e[a][a]
          exact (hDiagonal ⟨a, by omega⟩).symm
        · intro competitor hCompetitor
          have hNil : competitor = .nil := by
            cases competitor with
            | nil => rfl
            | node key left right =>
                have hFalse := (intervalTree_node_iff key left right le_rfl hb).mp hCompetitor
                omega
          subst competitor
          simp only [intervalTreeCost, keyCost, dummyCost, zero_add, one_nsmul]
          change e[a][a] ≤ q[a]
          exact le_of_eq (hDiagonal ⟨a, by omega⟩)
      · have habLt : a < b := by omega
        let af : Fin n := ⟨a, by omega⟩
        let bf : Fin (n + 1) := ⟨b, by omega⟩
        rcases hCells af bf (by simpa only [af, bf] using habLt) with
          ⟨r, har, hrb, _hSaved, hRecurrence, hMinimum⟩
        dsimp only [af, bf] at har hrb hRecurrence hMinimum
        rcases ih (r.val - a) (by omega) a r.val har (by omega) rfl with
          ⟨left, hLeftTree, hLeftCost, _hLeftLower⟩
        rcases ih (b - (r.val + 1)) (by omega) (r.val + 1) b
            (by omega) hb rfl with
          ⟨right, hRightTree, hRightCost, _hRightLower⟩
        have hTree : IntervalTree a b (.node r left right) :=
          (intervalTree_node_iff r left right ha hb).mpr
            ⟨har, hrb, hLeftTree, hRightTree⟩
        have hMass := treeMass_eq_intervalMass p q a b ha hb (.node r left right) hTree
        refine ⟨.node r left right, hTree, ?_, ?_⟩
        · rw [treeCost_node]
          dsimp only [afterKey]
          rw [hLeftCost, hRightCost, hMass]
          exact hRecurrence.symm
        · intro competitor hCompetitor
          cases competitor with
          | nil =>
              have hFalse := (intervalTree_nil_iff ha hb).mp hCompetitor
              omega
          | node t tLeft tRight =>
              rcases (intervalTree_node_iff t tLeft tRight ha hb).mp hCompetitor with
                ⟨hat, htb, hTLeft, hTRight⟩
              rcases ih (t.val - a) (by omega) a t.val hat (by omega) rfl with
                ⟨_, _, _, hTLeftLower⟩
              rcases ih (b - (t.val + 1)) (by omega) (t.val + 1) b
                  (by omega) hb rfl with ⟨_, _, _, hTRightLower⟩
              have hLeftBound := hTLeftLower tLeft hTLeft
              have hRightBound := hTRightLower tRight hTRight
              have hCandidate := (hMinimum t hat htb).1
              have hCompetitorMass := treeMass_eq_intervalMass p q a b ha hb
                (.node t tLeft tRight) hCompetitor
              rw [treeCost_node, hCompetitorMass]
              dsimp only [afterKey]
              exact hCandidate.trans
                (add_le_add (add_le_add hLeftBound hRightBound) (le_refl (intervalMass p q a b)))

private theorem tree_minimal_of_cells [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n)
    (q : Vector R (n + 1))
    (e : Vector (Vector R (n + 1)) (n + 1))
    (root : Vector (Vector (Option (Fin n)) n) n) :
  (∀ i : Fin (n + 1), e[i.val][i.val] = q[i.val]) →
    (∀ (a : Fin n) (b : Fin (n + 1)) (hab : a.val < b.val),
      CellSpec p q e root a b hab) →
    IsLeast {z : R | ∃ (tree : BinaryTree (Fin n))
      (complete : inorder tree = List.finRange n),
      expectedSearchCost n p q tree complete = z} e[0][n] := by
  intro hDiagonal hCells
  rcases interval_attains_and_minimal p q e root hDiagonal hCells
      0 n (by omega) (by omega) with
    ⟨tree, hTree, hCost, hLower⟩
  have complete : inorder tree = List.finRange n := by
    simpa [IntervalTree, rankInterval_full] using hTree
  refine ⟨?_, ?_⟩
  · refine ⟨tree, complete, ?_⟩
    rw [expectedSearchCost_eq_intervalTreeCost p q tree complete, hCost]
  · intro z hz
    rcases hz with ⟨competitor, competitorComplete, rfl⟩
    have hCompetitor : IntervalTree (n := n) 0 n competitor := by
      simpa [IntervalTree, rankInterval_full] using competitorComplete
    rw [expectedSearchCost_eq_intervalTreeCost p q competitor competitorComplete]
    exact hLower competitor hCompetitor

private theorem actual_tree_minimal [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : Nat} (p : Vector R n) (q : Vector R (n + 1)) :
    IsLeast {z : R | ∃ (tree : BinaryTree (Fin n))
      (complete : inorder tree = List.finRange n),
      expectedSearchCost n p q tree complete = z} (optimalBST p q).ret.1[0][n] := by
  have hActual := execute_table_complete p q
  exact tree_minimal_of_cells p q (execute p q).1 (execute p q).2.2.1
    hActual.1 hActual.2.2

end Cslib.Algorithms.Lean.OptimalBST
