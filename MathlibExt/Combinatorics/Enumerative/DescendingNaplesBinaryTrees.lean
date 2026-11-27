/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import MathlibExt.Combinatorics.Enumerative.DescendingNaplesDyckPath
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Descending strictly Naples parking functions and binary trees

We remove only the required part of each left spine. The subtrees at the open child
slots form an ordered forest. Splitting on whether its first tree is empty gives
the ballot recurrence for its cardinality.

## References

* J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
  *Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
  Article A44, pp. 1–18. The binary-tree class is in Proposition 5 (p. 16), and the
  parking count used here is Theorem 7 (p. 15).
-/

namespace MetaMathlibExt

/-- The number of nodes on the left spine of a binary tree: the root, its left child, that
child's left child, and so on (`0` for the empty tree).

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Section 5 (Proposition 5). -/
@[expose] public def leftSpineLength {α : Type*} : BinaryTree α → ℕ
  | .nil => 0
  | .node _ l _ => leftSpineLength l + 1

private theorem leftSpineLength_le_numNodes {α : Type*} (t : BinaryTree α) :
    leftSpineLength t ≤ t.numNodes := by
  induction t with
  | nil => simp [leftSpineLength]
  | node _ l r ih _ =>
    simp only [leftSpineLength, BinaryTree.numNodes]
    omega

private abbrev UnitTree := BinaryTree Unit

private def forestWeight (f : List UnitTree) : ℕ := (f.map BinaryTree.numNodes).sum

@[simp] private theorem forestWeight_nil : forestWeight [] = 0 := rfl

@[simp] private theorem forestWeight_cons (t : UnitTree) (f : List UnitTree) :
    forestWeight (t :: f) = t.numNodes + forestWeight f := rfl

private theorem forestWeight_append (f g : List UnitTree) :
    forestWeight (f ++ g) = forestWeight f + forestWeight g := by
  simp [forestWeight, List.sum_append]

private theorem numNodes_le_forestWeight {t : UnitTree} {f : List UnitTree} (h : t ∈ f) :
    t.numNodes ≤ forestWeight f := by
  induction f with
  | nil => simp at h
  | cons u f ih =>
    rw [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := ih h
      simp only [forestWeight_cons]
      omega

/-- Forests of `r` ordered trees with a total of `m` internal nodes. -/
private def Forest (m r : ℕ) := {f : List UnitTree // f.length = r ∧ forestWeight f = m}

private instance (m r : ℕ) : Finite (Forest m r) := by
  let s := (Finset.range (m + 1)).biUnion BinaryTree.treesOfNumNodesEq
  let entry (f : Forest m r) (i : Fin r) : UnitTree := f.val.get (i.cast f.property.1.symm)
  have hentry (f : Forest m r) (i : Fin r) : entry f i ∈ s := by
    have h := numNodes_le_forestWeight (t := entry f i) (List.get_mem _ _)
    rw [f.property.2] at h
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le h),
      BinaryTree.mem_treesOfNumNodesEq_numNodes _⟩
  refine Finite.of_injective (fun (f : Forest m r) (i : Fin r) =>
    (⟨entry f i, hentry f i⟩ : ↥s)) ?_
  intro f g hfg
  apply Subtype.ext
  apply List.ext_get (f.property.1.trans g.property.1.symm)
  intro i hi hj
  let j : Fin r := ⟨i, f.property.1 ▸ hi⟩
  exact congrArg Subtype.val (congrFun hfg j)

private theorem card_forest_zero_slots (m : ℕ) : Nat.card (Forest (m + 1) 0) = 0 := by
  let _ : IsEmpty (Forest (m + 1) 0) := ⟨fun ⟨f, hf, hw⟩ => by
    rw [List.length_eq_zero_iff.mp hf, forestWeight_nil] at hw
    omega⟩
  simp

private theorem card_forest_zero_nodes (r : ℕ) : Nat.card (Forest 0 r) = 1 := by
  have hnil (f : List UnitTree) (hf : forestWeight f = 0) :
      f = List.replicate f.length .nil := by
    induction f with
    | nil => rfl
    | cons t f ih =>
      simp only [forestWeight_cons, Nat.add_eq_zero_iff] at hf
      have ht : t = .nil := by
        cases t with
        | nil => rfl
        | node u l r =>
          have h := hf.1
          simp only [BinaryTree.numNodes] at h
          omega
      simpa only [ht, List.length_cons, List.replicate_succ] using
        congrArg (List.cons (.nil : UnitTree)) (ih hf.2)
  let _ : Unique (Forest 0 r) :=
    { default := ⟨List.replicate r .nil, by simp [forestWeight]⟩
      uniq := fun ⟨f, hf, hw⟩ => by
        apply Subtype.ext
        change f = List.replicate r .nil
        rw [← hf]
        exact hnil f hw }
  exact Nat.card_unique

-- An empty first tree uses a slot. A nonempty first tree uses a node and exposes two slots.
private def forestStep (m r : ℕ) :
    Forest (m + 1) (r + 1) ≃ Forest (m + 1) r ⊕ Forest m (r + 2) where
  toFun
    | ⟨[], h, _⟩ => False.elim (by simp at h)
    | ⟨.nil :: f, h, hw⟩ => .inl ⟨f, by simpa using h, by simpa using hw⟩
    | ⟨.node _ l t :: f, h, hw⟩ => .inr ⟨l :: t :: f, by simp at h ⊢; omega, by
        simp only [forestWeight_cons, BinaryTree.numNodes] at hw ⊢
        omega⟩
  invFun
    | .inl ⟨f, h, hw⟩ => ⟨.nil :: f, by simpa using h, by simpa using hw⟩
    | .inr ⟨[], h, _⟩ => False.elim (by simp at h)
    | .inr ⟨[_], h, _⟩ => False.elim (by simp at h)
    | .inr ⟨l :: t :: f, h, hw⟩ => ⟨.node () l t :: f, by simp at h ⊢; omega, by
        simp only [forestWeight_cons, BinaryTree.numNodes] at hw ⊢
        omega⟩
  left_inv := by
    rintro ⟨_ | ⟨_ | ⟨⟨⟩, l, t⟩, f⟩, h, hw⟩
    · simp at h
    · rfl
    · rfl
  right_inv := by
    rintro (⟨f, h, hw⟩ | ⟨_ | ⟨l, _ | ⟨t, f⟩⟩, h, hw⟩)
    · rfl
    · simp at h
    · simp at h
    · rfl

-- The additive ballot formula obeys the forest recurrence by Pascal's identity.
private theorem card_forest_add_choose (m r : ℕ) :
    Nat.card (Forest (m + 1) r) + (2 * m + r + 1).choose m =
      (2 * m + r + 1).choose (m + 1) := by
  induction h : 2 * m + r using Nat.strong_induction_on generalizing m r with
  | ind s ih =>
    subst s
    cases r with
    | zero =>
      rw [card_forest_zero_slots, Nat.zero_add, show 2 * m + 0 + 1 = m + (m + 1) by omega]
      exact Nat.choose_symm_add
    | succ r =>
      rw [Nat.card_congr (forestStep m r), Nat.card_sum]
      have h₁ := ih (2 * m + r) (by omega) m r rfl
      cases m with
      | zero =>
        simp only [Nat.zero_add, Nat.mul_zero, Nat.choose_zero_right, Nat.choose_one_right,
          card_forest_zero_nodes] at h₁ ⊢
        omega
      | succ m =>
        let s' := 2 * (m + 1) + r + 1
        have h₂ := ih (2 * m + (r + 2)) (by omega) m (r + 2) rfl
        rw [show 2 * m + (r + 2) + 1 = s' by dsimp [s']; omega] at h₂
        rw [show 2 * (m + 1) + (r + 1) + 1 = s' + 1 by dsimp [s']; omega,
          Nat.choose_succ_succ' s' m, Nat.choose_succ_succ' s' (m + 1)]
        dsimp only [s'] at h₂ ⊢
        omega

private theorem card_forest_mul (m r : ℕ) :
    Nat.card (Forest m r) * (2 * m + r) = r * (2 * m + r).choose m := by
  cases m with
  | zero => simp [card_forest_zero_nodes]
  | succ m =>
    let s := 2 * m + r + 1
    have h := congrArg (fun x : ℕ => x * (s + 1)) (card_forest_add_choose m r)
    change ((Nat.card (Forest (m + 1) r) + s.choose m) * (s + 1)) =
      s.choose (m + 1) * (s + 1) at h
    rw [Nat.add_mul, mul_comm (s.choose m), Nat.add_one_mul_choose_eq, Nat.choose_mul_succ_eq,
      show s + 1 - (m + 1) = r + (m + 1) by dsimp [s]; omega,
      Nat.mul_add ((s + 1).choose (m + 1)) r (m + 1), Nat.add_right_cancel_iff] at h
    simpa only [show s + 1 = 2 * (m + 1) + r by dsimp [s]; omega, mul_comm r] using h

-- Cutting `a` left-spine nodes gives their right subtrees, followed by the final left subtree.
private def peel : ℕ → UnitTree → List UnitTree
  | 0, t => [t]
  | _ + 1, .nil => []
  | a + 1, .node _ l r => r :: peel a l

-- Consume the first `a + 1` entries, leaving the remaining forest untouched.
private def graft : ℕ → List UnitTree → UnitTree × List UnitTree
  | _, [] => (.nil, [])
  | 0, t :: f => (t, f)
  | a + 1, r :: f => let (l, rest) := graft a f; (.node () l r, rest)

private theorem peel_spec {a : ℕ} {t : UnitTree} (h : a ≤ leftSpineLength t) :
    (peel a t).length = a + 1 ∧ forestWeight (peel a t) + a = t.numNodes := by
  induction a generalizing t with
  | zero => simp [peel]
  | succ a ih =>
    cases t using BinaryTree.unitRecOn with
    | base => simp [leftSpineLength] at h
    | ind l r =>
      have hl : a ≤ leftSpineLength l := Nat.le_of_succ_le_succ h
      obtain ⟨hlen, hw⟩ := ih hl
      refine ⟨by rw [peel, List.length_cons, hlen], ?_⟩
      calc
        forestWeight (peel (a + 1) (.node () l r)) + (a + 1) =
            (forestWeight (peel a l) + a) + r.numNodes + 1 := by
          rw [peel, forestWeight_cons]
          omega
        _ = (BinaryTree.node () l r).numNodes := by rw [hw, BinaryTree.numNodes]

private theorem graft_peel_append {a : ℕ} {t : UnitTree} (h : a ≤ leftSpineLength t)
    (f : List UnitTree) : graft a (peel a t ++ f) = (t, f) := by
  induction a generalizing t with
  | zero => rfl
  | succ a ih =>
    cases t using BinaryTree.unitRecOn with
    | base => simp [leftSpineLength] at h
    | ind l r =>
      have hl : a ≤ leftSpineLength l := Nat.le_of_succ_le_succ h
      simp [peel, graft, ih hl]

private theorem graft_spec {a : ℕ} {f : List UnitTree} (h : a + 1 ≤ f.length) :
    a ≤ leftSpineLength (graft a f).1 ∧
      peel a (graft a f).1 ++ (graft a f).2 = f ∧
      (graft a f).2.length + (a + 1) = f.length := by
  induction a generalizing f with
  | zero => cases f <;> simp_all [graft, peel]
  | succ a ih =>
    cases f with
    | nil => simp at h
    | cons r f =>
      have hf : a + 1 ≤ f.length := Nat.le_of_succ_le_succ h
      obtain ⟨hs, he, hl⟩ := ih hf
      simp only [graft, leftSpineLength, peel, List.cons_append, he, List.length_cons,
        Nat.add_le_add_iff_right, hs, true_and]
      omega

private def removeSkeleton (a b : ℕ) : UnitTree → List UnitTree
  | .nil => []
  | .node _ l r => peel a l ++ peel b r

private def fillSkeleton (a b : ℕ) (f : List UnitTree) : UnitTree :=
  let (l, rest) := graft a f
  .node () l (graft b rest).1

private theorem removeSkeleton_mem {a b m : ℕ} {t : UnitTree}
    (hn : t.numNodes = m + (a + b + 1)) (ha : a + 1 ≤ leftSpineLength t)
    (hb : b ≤ leftSpineLength t.right) :
    (removeSkeleton a b t).length = (a + 1) + (b + 1) ∧
      forestWeight (removeSkeleton a b t) = m := by
  cases t using BinaryTree.unitRecOn with
  | base => simp [leftSpineLength] at ha
  | ind l r =>
    obtain ⟨hla, hwa⟩ := peel_spec (t := l) (Nat.le_of_succ_le_succ ha)
    have hb' : b ≤ leftSpineLength r := hb
    obtain ⟨hlb, hwb⟩ := peel_spec hb'
    simp only [BinaryTree.numNodes] at hn
    simp only [removeSkeleton, List.length_append, hla, hlb, forestWeight_append, true_and]
    omega

private theorem fillSkeleton_removeSkeleton {a b : ℕ} {t : UnitTree}
    (ha : a + 1 ≤ leftSpineLength t) (hb : b ≤ leftSpineLength t.right) :
    fillSkeleton a b (removeSkeleton a b t) = t := by
  cases t using BinaryTree.unitRecOn with
  | base => simp [leftSpineLength] at ha
  | ind l r =>
    simp only [removeSkeleton, fillSkeleton, graft_peel_append (Nat.le_of_succ_le_succ ha)]
    rw [← List.append_nil (peel b r), graft_peel_append (t := r) hb]

private theorem fillSkeleton_spec {a b m : ℕ} {f : List UnitTree}
    (hl : f.length = (a + 1) + (b + 1)) (hw : forestWeight f = m) :
    (fillSkeleton a b f).numNodes = m + (a + b + 1) ∧
      a + 1 ≤ leftSpineLength (fillSkeleton a b f) ∧
      b ≤ leftSpineLength (fillSkeleton a b f).right ∧
      removeSkeleton a b (fillSkeleton a b f) = f := by
  obtain ⟨ha, he, hlen⟩ := graft_spec (a := a) (f := f) (by omega)
  obtain ⟨hb, hr, hrest⟩ := graft_spec (a := b) (f := (graft a f).2) (by omega)
  have hempty : (graft b (graft a f).2).2 = [] := List.length_eq_zero_iff.mp (by omega)
  rw [hempty, List.append_nil] at hr
  rw [← hr] at he
  have hweights := congrArg forestWeight he
  rw [forestWeight_append, hw] at hweights
  have hwa := (peel_spec ha).2
  have hwb := (peel_spec hb).2
  simp only [fillSkeleton, BinaryTree.numNodes, leftSpineLength, BinaryTree.right,
    Nat.add_le_add_iff_right, ha, hb, removeSkeleton, he, and_true]
  omega

private theorem card_spines (a b m : ℕ) :
    ((BinaryTree.treesOfNumNodesEq (m + (a + b + 1))).filter fun t =>
      a + 1 ≤ leftSpineLength t ∧ b ≤ leftSpineLength t.right).card =
      Nat.card (Forest m ((a + 1) + (b + 1))) := by
  let s := (BinaryTree.treesOfNumNodesEq (m + (a + b + 1))).filter fun t =>
    a + 1 ≤ leftSpineLength t ∧ b ≤ leftSpineLength t.right
  have hs {t : UnitTree} : t ∈ s ↔ t.numNodes = m + (a + b + 1) ∧
      a + 1 ≤ leftSpineLength t ∧ b ≤ leftSpineLength t.right := by simp [s]
  let e : ↥s ≃ Forest m ((a + 1) + (b + 1)) :=
    { toFun := fun ⟨t, ht⟩ =>
        let ⟨hn, ha, hb⟩ := hs.mp ht
        ⟨removeSkeleton a b t, removeSkeleton_mem hn ha hb⟩
      invFun := fun ⟨f, hl, hw⟩ =>
        let ⟨hn, ha, hb, _⟩ := fillSkeleton_spec hl hw
        ⟨fillSkeleton a b f, hs.mpr ⟨hn, ha, hb⟩⟩
      left_inv := fun ⟨_, ht⟩ =>
        Subtype.ext (fillSkeleton_removeSkeleton (hs.mp ht).2.1 (hs.mp ht).2.2)
      right_inv := fun ⟨_, hl, hw⟩ => Subtype.ext (fillSkeleton_spec hl hw).2.2.2 }
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, s] using
    (Nat.card_congr e : Nat.card ↥s = _)

private theorem card_spines_eq_zero {n k : ℕ} (hk : 1 ≤ k) (h : n ≤ k) :
    ((BinaryTree.treesOfNumNodesEq (n + k)).filter fun t =>
      k ≤ leftSpineLength t ∧ k + 1 ≤ leftSpineLength t.right).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro t ht
  simp only [Finset.mem_filter, BinaryTree.mem_treesOfNumNodesEq] at ht
  rcases ht with ⟨hn, hl, hr⟩
  cases t using BinaryTree.unitRecOn with
  | base => simp [leftSpineLength] at hl; omega
  | ind l r =>
    have h₁ := leftSpineLength_le_numNodes l
    have h₂ := leftSpineLength_le_numNodes r
    simp only [BinaryTree.numNodes, leftSpineLength, BinaryTree.right] at hn hl hr
    omega

/-- **Descending strictly $k$-Naples parking functions and binary trees.** For every $n$ and
every $k \ge 1$, the number of descending strictly $k$-Naples parking functions of length $n$
(descending preferences that are $k$-Naples but not $(k - 1)$-Naples) equals the number of
binary trees $t$ with $n + k$ nodes such that the left spine of $t$ (the root, its left child,
that child's left child, and so on) has at least $k$ nodes and the left spine of the right
subtree of $t$ has at least $k + 1$ nodes.

Source: J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez,
*Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024),
Article A44, Proposition 5. -/
public theorem descendingStrictNaplesCount_eq_card_binaryTree {n k : ℕ} (hk : 1 ≤ k) :
    descendingStrictNaplesCount n k = ((BinaryTree.treesOfNumNodesEq (n + k)).filter fun t =>
      k ≤ leftSpineLength t ∧ k + 1 ≤ leftSpineLength t.right).card := by
  rcases n with _ | n
  · rw [card_spines_eq_zero hk (Nat.zero_le k), descendingStrictNaplesCount, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    intro α hα
    exact (Finset.mem_filter.mp hα).2.2.2 (by simp [IsNaplesParkingFunction, naplesPark])
  have hstrict := (descendingNaplesCount_eq_choose (Nat.succ_pos n) hk).2
  apply Nat.cast_injective (R := ℚ)
  rw [hstrict]
  by_cases hsmall : n + 1 ≤ k
  · rw [card_spines_eq_zero hk hsmall, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  let m := n - (a + 1)
  let r := (a + 1) + (a + 2 + 1)
  have hnodes : m + (a + (a + 2) + 1) = n + 1 + (a + 1) := by dsimp [m]; omega
  have hcard := card_spines a (a + 2) m
  rw [hnodes] at hcard
  change ((BinaryTree.treesOfNumNodesEq (n + 1 + (a + 1))).filter fun t =>
    a + 1 ≤ leftSpineLength t ∧ a + 2 ≤ leftSpineLength t.right).card =
    Nat.card (Forest m r) at hcard
  rw [hcard]
  have htotal : 2 * m + r = 2 * (n + 1) := by dsimp [m, r]; omega
  have hchoose : (2 * (n + 1)).choose (n + 1 + (a + 1) + 1) = (2 * (n + 1)).choose m := by
    rw [show 2 * (n + 1) = (n + 1 + (a + 1) + 1) + m by dsimp [m]; omega]
    exact Nat.choose_symm_add
  have hf := card_forest_mul m r
  rw [htotal] at hf
  have hcast : (Nat.card (Forest m r) : ℚ) * (2 * ((n : ℚ) + 1)) =
      2 * ((a : ℚ) + 1 + 1) * ((2 * (n + 1)).choose m : ℚ) := by
    have hslots : r = 2 * (a + 1 + 1) := by dsimp [r]; omega
    conv at hf => rhs; rw [hslots]
    exact_mod_cast hf
  rw [hchoose]
  push_cast
  have hnQ : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  linear_combination -hcast / 2

end MetaMathlibExt
