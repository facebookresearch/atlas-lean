/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Pauplin's formula and the balanced minimum-evolution length

A *binary* (trivalent) phylogenetic tree with real edge lengths is represented here rooted at an
edge: a `UTree X` is two rooted binary trees `left`, `right` (`RTree X`, with leaf labels in `X`
and a real length on every child edge) joined by an edge of length `len`. Every vertex other than
a leaf then has degree three, and every unrooted binary tree with at least two leaves arises
this way (root it at any edge).

For two leaves `i, j` write `d_T(i, j)` for the total length of the path between them and
`τ_ij` for its number of edges. `UTree.pairs` lists the unordered pairs of leaves with these two
numbers (one entry per pair of leaf occurrences).

* **Pauplin's formula** (Pauplin 2000): the total edge length of the tree is
  `L(T) = ∑_{i<j} 2^{1-τ_ij} d_T(i, j)` (`UTree.bmeLength_pathLength`). It holds for all real edge
  lengths, not only nonnegative ones.
* The **balanced minimum-evolution length** of a topology `T` for an arbitrary dissimilarity `d`
  (Desper and Gascuel 2002) is the same linear form `∑_{i<j} 2^{1-τ_ij} d(i, j)`
  (`UTree.bmeLength`); by Pauplin's formula it is the tree length whenever `d` is the path-length
  metric of `T` (`UTree.bmeLength_eq_length`).
* The **Kraft equality**: for every leaf `i`, `∑_{j ≠ i} 2^{1-τ_ij} = 1`
  (`UTree.kraft_leaf`), from Kraft's equality `∑ 2^{-depth} = 1` for the leaves of a rooted
  binary tree (`RTree.kraft`).

The general form for phylogenetic trees with vertices of any degree, with coefficient
`∏ (deg v - 1)⁻¹` over the interior vertices of the path, is Semple and Steel (2004),
Theorem 4.2; it is not formalized here.

## Main results

* `UTree.bmeLength_pathLength`, `UTree.bmeLength_eq_length`: Pauplin's formula.
* `RTree.kraft`, `UTree.kraft_leaf`: Kraft equalities.

## References

* Y. Pauplin, *Direct calculation of a tree length using a distance matrix*, J. Mol. Evol. 51
  (2000), 41–47.
* R. Desper and O. Gascuel, *Fast and accurate phylogeny reconstruction algorithms based on the
  minimum-evolution principle*, J. Comput. Biol. 9 (2002), 687–705.
* C. Semple and M. Steel, *Cyclic permutations and evolutionary trees*, Adv. in Appl. Math. 32
  (2004), 669–680.
* K. Eickmeyer, P. Huggins, L. Pachter and R. Yoshida, *On the optimality of the
  neighbor-joining algorithm*, Algorithms Mol. Biol. 3 (2008), 5.
* S. Fiorini and G. Joret, *Approximating the balanced minimum evolution problem*, Oper. Res.
  Lett. 40 (2012), 31–35.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution

universe u

/-- A rooted binary tree with leaf labels in `X`; `node a l b r` has the child `l` at the end of
an edge of length `a` and the child `r` at the end of an edge of length `b`. -/
inductive RTree (X : Type u) where
  /-- A leaf with label `x`. -/
  | leaf : X → RTree X
  /-- An internal vertex with children `l` and `r` on edges of lengths `a` and `b`. -/
  | node : ℝ → RTree X → ℝ → RTree X → RTree X

/-- An unrooted binary tree, rooted at its edge of length `len` that joins the roots of the
rooted binary trees `left` and `right`. -/
structure UTree (X : Type u) where
  /-- The subtree on one side of the root edge. -/
  left : RTree X
  /-- The length of the root edge. -/
  len : ℝ
  /-- The subtree on the other side of the root edge. -/
  right : RTree X

variable {X : Type u}

/-- The Pauplin coefficient `2 ^ (1 - τ)` of a pair of leaves at topological distance `τ`. -/
noncomputable def pauplinCoeff (τ : ℕ) : ℝ :=
  2 / 2 ^ τ

private theorem sum_map_flatMap {α β γ : Type*} (L₁ : List α) (L₂ : List β) (h : α → β → γ)
    (g : γ → ℝ) :
    ((L₁.flatMap fun p => L₂.map (h p)).map g).sum =
      (L₁.map fun p => (L₂.map fun q => g (h p q)).sum).sum := by
  induction L₁ with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.sum_append, ih, Function.comp_def]

private theorem pauplinCoeff_add_two (m n : ℕ) :
    pauplinCoeff (m + n + 2) = ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ n)⁻¹ * 2⁻¹ := by
  unfold pauplinCoeff
  rw [pow_add, pow_add]
  field_simp

private theorem pauplinCoeff_add_one (m n : ℕ) :
    pauplinCoeff (m + n + 1) = ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ n)⁻¹ := by
  unfold pauplinCoeff
  rw [pow_add, pow_add]
  field_simp

namespace RTree

/-- The total length of the edges. -/
def length : RTree X → ℝ
  | leaf _ => 0
  | node a l b r => a + length l + b + length r

/-- The leaves, each with its label, its distance to the root and its number of edges to the
root. -/
def leaves : RTree X → List (X × ℝ × ℕ)
  | leaf x => [(x, 0, 0)]
  | node a l b r =>
    (leaves l).map (fun p => (p.1, p.2.1 + a, p.2.2 + 1)) ++
      (leaves r).map (fun p => (p.1, p.2.1 + b, p.2.2 + 1))

/-- The unordered pairs of leaves, each with the two labels, the length of the path between the
two leaves and its number of edges. -/
def pairs : RTree X → List (X × X × ℝ × ℕ)
  | leaf _ => []
  | node a l b r =>
    pairs l ++ pairs r ++
      (leaves l).flatMap fun p =>
        (leaves r).map fun q => (p.1, q.1, p.2.1 + a + b + q.2.1, p.2.2 + q.2.2 + 2)

/-- **Kraft's equality** for a rooted binary tree: `∑_{leaves} 2^{-depth} = 1`. -/
theorem kraft (t : RTree X) : (t.leaves.map fun p => ((2 : ℝ) ^ p.2.2)⁻¹).sum = 1 := by
  induction t with
  | leaf x => simp [leaves]
  | node a l b r ihl ihr =>
    simp only [leaves, List.map_append, List.map_map, List.sum_append, Function.comp_def,
      pow_succ, mul_inv, List.sum_map_mul_right, ihl, ihr]
    norm_num

/-- The Kraft-weighted sum of leaf depths `∑_{leaves} 2^{-k} d` (a proof device). -/
private noncomputable def wsum (t : RTree X) : ℝ :=
  (t.leaves.map fun p => ((2 : ℝ) ^ p.2.2)⁻¹ * p.2.1).sum

private theorem wsum_node (a b : ℝ) (l r : RTree X) :
    wsum (node a l b r) = (wsum l + a) / 2 + (wsum r + b) / 2 := by
  have hl := kraft l
  have hr := kraft r
  have key : ∀ (t : RTree X) (c : ℝ), (t.leaves.map fun p =>
      ((2 : ℝ) ^ (p.2.2 + 1))⁻¹ * (p.2.1 + c)).sum = (wsum t + c) / 2 := by
    intro t c
    have : (fun p : X × ℝ × ℕ => ((2 : ℝ) ^ (p.2.2 + 1))⁻¹ * (p.2.1 + c)) =
        fun p => (((2 : ℝ) ^ p.2.2)⁻¹ * p.2.1 + c * ((2 : ℝ) ^ p.2.2)⁻¹) * 2⁻¹ := by
      funext p; rw [pow_succ, mul_inv]; ring
    rw [this, List.sum_map_mul_right, List.sum_map_add, List.sum_map_mul_left, kraft]
    unfold wsum; ring
  unfold wsum
  simp only [leaves, List.map_append, List.map_map, List.sum_append, Function.comp_def]
  rw [key l a, key r b]
  rfl

/-- Summing `c 2^{-k} (e + d)` over the leaves gives `c (e + wsum t)`. -/
private theorem sum_leaves_affine (t : RTree X) (c e : ℝ) :
    (t.leaves.map fun q => c * ((2 : ℝ) ^ q.2.2)⁻¹ * (e + q.2.1)).sum = c * (e + wsum t) := by
  have : (fun q : X × ℝ × ℕ => c * ((2 : ℝ) ^ q.2.2)⁻¹ * (e + q.2.1)) =
      fun q => c * e * ((2 : ℝ) ^ q.2.2)⁻¹ + c * (((2 : ℝ) ^ q.2.2)⁻¹ * q.2.1) := by
    funext q; ring
  rw [this, List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left, kraft]
  unfold wsum; ring

/-- The invariant behind Pauplin's formula on a rooted tree. -/
private theorem pairs_add_wsum (t : RTree X) :
    (t.pairs.map fun p => pauplinCoeff p.2.2.2 * p.2.2.1).sum + wsum t = t.length := by
  induction t with
  | leaf x => simp [pairs, wsum, leaves, length]
  | node a l b r ihl ihr =>
    rw [wsum_node]
    simp only [pairs, List.map_append, List.sum_append, sum_map_flatMap, length]
    have cross : (l.leaves.map fun p => (r.leaves.map fun q =>
        pauplinCoeff (p.2.2 + q.2.2 + 2) * (p.2.1 + a + b + q.2.1)).sum).sum =
        (wsum l + a + b + wsum r) / 2 := by
      have h1 : ∀ p : X × ℝ × ℕ, (r.leaves.map fun q =>
          pauplinCoeff (p.2.2 + q.2.2 + 2) * (p.2.1 + a + b + q.2.1)).sum =
          (((2 : ℝ) ^ p.2.2)⁻¹ * 2⁻¹) * ((p.2.1 + a + b) + wsum r) := by
        intro p
        rw [← sum_leaves_affine r]
        congr 1
        apply List.map_congr_left
        intro q _
        rw [pauplinCoeff_add_two]; ring
      rw [List.map_congr_left (fun p _ => h1 p)]
      have h2 : (fun p : X × ℝ × ℕ => ((2 : ℝ) ^ p.2.2)⁻¹ * 2⁻¹ * (p.2.1 + a + b + wsum r)) =
          fun p => 2⁻¹ * ((2 : ℝ) ^ p.2.2)⁻¹ * ((a + b + wsum r) + p.2.1) := by
        funext p; ring
      rw [h2, sum_leaves_affine]; ring
    rw [cross]
    linarith

end RTree

section KraftLeaf

variable [DecidableEq X]

private theorem cross_sum (L₁ L₂ : List (X × ℝ × ℕ)) (x : X) (c : ℝ)
    (hdisj : ∀ p ∈ L₁, ∀ q ∈ L₂, ¬(p.1 = x ∧ q.1 = x)) :
    (L₁.map fun p => (L₂.map fun q => if p.1 = x ∨ q.1 = x then
      ((2 : ℝ) ^ p.2.2)⁻¹ * ((2 : ℝ) ^ q.2.2)⁻¹ * c else 0).sum).sum =
      c * ((L₁.map fun p => if p.1 = x then ((2 : ℝ) ^ p.2.2)⁻¹ else 0).sum *
          (L₂.map fun q => ((2 : ℝ) ^ q.2.2)⁻¹).sum +
        (L₁.map fun p => ((2 : ℝ) ^ p.2.2)⁻¹).sum *
          (L₂.map fun q => if q.1 = x then ((2 : ℝ) ^ q.2.2)⁻¹ else 0).sum) := by
  have inner : ∀ p ∈ L₁, (L₂.map fun q => if p.1 = x ∨ q.1 = x then
      ((2 : ℝ) ^ p.2.2)⁻¹ * ((2 : ℝ) ^ q.2.2)⁻¹ * c else 0).sum =
      (if p.1 = x then ((2 : ℝ) ^ p.2.2)⁻¹ else 0) * (c * (L₂.map fun q =>
        ((2 : ℝ) ^ q.2.2)⁻¹).sum) +
      ((2 : ℝ) ^ p.2.2)⁻¹ * (c * (L₂.map fun q =>
        if q.1 = x then ((2 : ℝ) ^ q.2.2)⁻¹ else 0).sum) := by
    intro p hp
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
      ← List.sum_map_mul_left, ← List.sum_map_add]
    apply congrArg
    apply List.map_congr_left
    intro q hq
    have := hdisj p hp q hq
    by_cases h1 : p.1 = x <;> by_cases h2 : q.1 = x <;> simp_all <;> ring
  rw [List.map_congr_left inner, List.sum_map_add, List.sum_map_mul_right,
    List.sum_map_mul_right]
  ring

namespace RTree

/-- The Kraft weight `2^{-k}` of the leaf labelled `x` (`0` if there is none). -/
private noncomputable def lsum (t : RTree X) (x : X) : ℝ :=
  (t.leaves.map fun p => if p.1 = x then ((2 : ℝ) ^ p.2.2)⁻¹ else 0).sum

/-- The sum of the Pauplin coefficients of the pairs of `t` containing the label `x`. -/
private noncomputable def psum (t : RTree X) (x : X) : ℝ :=
  (t.pairs.map fun p => if p.1 = x ∨ p.2.1 = x then pauplinCoeff p.2.2.2 else 0).sum

omit [DecidableEq X] in
private theorem labels_node (a b : ℝ) (l r : RTree X) :
    (node a l b r).leaves.map Prod.fst = l.leaves.map Prod.fst ++ r.leaves.map Prod.fst := by
  simp [leaves, List.map_map, Function.comp_def]

private theorem lsum_node (a b : ℝ) (l r : RTree X) (x : X) :
    lsum (node a l b r) x = lsum l x * 2⁻¹ + lsum r x * 2⁻¹ := by
  unfold lsum
  simp only [leaves, List.map_append, List.map_map, List.sum_append, Function.comp_def]
  rw [← List.sum_map_mul_right, ← List.sum_map_mul_right]
  congr 1 <;> apply congrArg <;> apply List.map_congr_left <;> intro p _ <;>
    split_ifs <;> simp [pow_succ, mul_comm]

omit [DecidableEq X] in
private theorem disj_of_nodup {l r : RTree X} {x : X}
    (h : (l.leaves.map Prod.fst ++ r.leaves.map Prod.fst).Nodup) :
    ∀ p ∈ l.leaves, ∀ q ∈ r.leaves, ¬(p.1 = x ∧ q.1 = x) := by
  intro p hp q hq ⟨h1, h2⟩
  rw [List.nodup_append] at h
  exact h.2.2 p.1 (List.mem_map_of_mem hp) q.1 (List.mem_map_of_mem hq) (h1.trans h2.symm)

/-- Per-leaf Kraft invariant on a rooted tree. -/
private theorem psum_add_lsum (t : RTree X) (ht : (t.leaves.map Prod.fst).Nodup) (x : X) :
    psum t x + lsum t x = if x ∈ t.leaves.map Prod.fst then 1 else 0 := by
  induction t with
  | leaf y =>
    by_cases h : y = x <;> simp [psum, lsum, pairs, leaves, h, eq_comm]
  | node a l b r ihl ihr =>
    rw [labels_node] at ht ⊢
    have hd := disj_of_nodup (x := x) ht
    have hl := ihl (List.nodup_append.mp ht).1
    have hr := ihr (List.nodup_append.mp ht).2.1
    have cross := cross_sum l.leaves r.leaves x 2⁻¹ hd
    rw [kraft, kraft] at cross
    rw [lsum_node]
    unfold psum at hl hr ⊢
    simp only [pairs, List.map_append, List.sum_append, sum_map_flatMap]
    have hc : (l.leaves.map fun p => (r.leaves.map fun q =>
        if p.1 = x ∨ q.1 = x then pauplinCoeff (p.2.2 + q.2.2 + 2) else 0).sum).sum =
        2⁻¹ * (lsum l x * 1 + 1 * lsum r x) := by
      unfold lsum
      rw [← cross]
      congr 1; apply List.map_congr_left; intro p _
      congr 1; apply List.map_congr_left; intro q _
      rw [pauplinCoeff_add_two]
    rw [hc]
    have hdis : ¬(x ∈ l.leaves.map Prod.fst ∧ x ∈ r.leaves.map Prod.fst) := by
      rintro ⟨h1, h2⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
      obtain ⟨q, hq, hpq⟩ := List.mem_map.mp h2
      exact hd p hp q hq ⟨rfl, hpq⟩
    have hind : (if x ∈ l.leaves.map Prod.fst ++ r.leaves.map Prod.fst then (1 : ℝ) else 0) =
        (if x ∈ l.leaves.map Prod.fst then 1 else 0) +
          (if x ∈ r.leaves.map Prod.fst then 1 else 0) := by
      by_cases h1 : x ∈ l.leaves.map Prod.fst <;> by_cases h2 : x ∈ r.leaves.map Prod.fst <;>
        simp_all
    rw [hind]
    linarith

end RTree

end KraftLeaf

namespace UTree

/-- The total length of the edges. -/
def length (T : UTree X) : ℝ :=
  T.left.length + T.len + T.right.length

/-- The leaf labels (with multiplicity). -/
def labels (T : UTree X) : List X :=
  T.left.leaves.map Prod.fst ++ T.right.leaves.map Prod.fst

/-- The unordered pairs of leaves, each with the two labels, the length `d_T(i, j)` of the path
between the two leaves and its number of edges `τ_ij`. -/
def pairs (T : UTree X) : List (X × X × ℝ × ℕ) :=
  T.left.pairs ++ T.right.pairs ++
    T.left.leaves.flatMap fun p =>
      T.right.leaves.map fun q => (p.1, q.1, p.2.1 + T.len + q.2.1, p.2.2 + q.2.2 + 1)

/-- The **balanced minimum-evolution length** of the topology of `T` for a dissimilarity `d`
(Desper and Gascuel 2002): `∑_{i<j} 2^{1-τ_ij} d(i, j)`. It depends on `T` only through the
topological distances `τ_ij`. -/
noncomputable def bmeLength (T : UTree X) (d : X → X → ℝ) : ℝ :=
  (T.pairs.map fun p => pauplinCoeff p.2.2.2 * d p.1 p.2.1).sum

/-- **Pauplin's formula** (Pauplin 2000): the total edge length of a binary tree with real edge
lengths is `∑_{i<j} 2^{1-τ_ij} d_T(i, j)`, the sum over pairs of leaves of the path length
weighted by `2` to the power one minus the number of edges on the path. -/
theorem bmeLength_pathLength (T : UTree X) :
    (T.pairs.map fun p => pauplinCoeff p.2.2.2 * p.2.2.1).sum = T.length := by
  unfold pairs length
  simp only [List.map_append, List.sum_append, sum_map_flatMap]
  have cross : (T.left.leaves.map fun p => (T.right.leaves.map fun q =>
      pauplinCoeff (p.2.2 + q.2.2 + 1) * (p.2.1 + T.len + q.2.1)).sum).sum =
      RTree.wsum T.left + T.len + RTree.wsum T.right := by
    have h1 : ∀ p : X × ℝ × ℕ, (T.right.leaves.map fun q =>
        pauplinCoeff (p.2.2 + q.2.2 + 1) * (p.2.1 + T.len + q.2.1)).sum =
        ((2 : ℝ) ^ p.2.2)⁻¹ * ((p.2.1 + T.len) + RTree.wsum T.right) := by
      intro p
      rw [← RTree.sum_leaves_affine T.right]
      congr 1
      apply List.map_congr_left
      intro q _
      rw [pauplinCoeff_add_one]
    rw [List.map_congr_left (fun p _ => h1 p)]
    have h2 : (fun p : X × ℝ × ℕ =>
        ((2 : ℝ) ^ p.2.2)⁻¹ * (p.2.1 + T.len + RTree.wsum T.right)) =
        fun p => 1 * ((2 : ℝ) ^ p.2.2)⁻¹ * ((T.len + RTree.wsum T.right) + p.2.1) := by
      funext p; ring
    rw [h2, RTree.sum_leaves_affine]; ring
  rw [cross]
  have hl := RTree.pairs_add_wsum T.left
  have hr := RTree.pairs_add_wsum T.right
  linarith

/-- **The balanced minimum-evolution length of a tree metric is the tree length**: if `d` is the
path-length dissimilarity of `T` on its leaves, `bmeLength T d = length T`. -/
theorem bmeLength_eq_length (T : UTree X) (d : X → X → ℝ)
    (hd : ∀ p ∈ T.pairs, d p.1 p.2.1 = p.2.2.1) : T.bmeLength d = T.length := by
  rw [← bmeLength_pathLength, bmeLength]
  congr 1
  exact List.map_congr_left fun p hp => by rw [hd p hp]

/-- **Kraft equality** for unrooted binary trees: for every leaf `i` of a tree with distinct leaf
labels, `∑_{j ≠ i} 2^{1-τ_ij} = 1`. -/
theorem kraft_leaf [DecidableEq X] (T : UTree X) (hT : T.labels.Nodup) (x : X) (hx : x ∈ T.labels) :
    (T.pairs.map fun p => if p.1 = x ∨ p.2.1 = x then pauplinCoeff p.2.2.2 else 0).sum = 1 := by
  have hd : ∀ p ∈ T.left.leaves, ∀ q ∈ T.right.leaves, ¬(p.1 = x ∧ q.1 = x) :=
    RTree.disj_of_nodup hT
  have hl := RTree.psum_add_lsum T.left (List.nodup_append.mp hT).1 x
  have hr := RTree.psum_add_lsum T.right (List.nodup_append.mp hT).2.1 x
  have cross := cross_sum T.left.leaves T.right.leaves x 1 hd
  rw [RTree.kraft, RTree.kraft] at cross
  unfold RTree.psum at hl hr
  unfold pairs
  simp only [List.map_append, List.sum_append, sum_map_flatMap]
  have hc : (T.left.leaves.map fun p => (T.right.leaves.map fun q =>
      if p.1 = x ∨ q.1 = x then pauplinCoeff (p.2.2 + q.2.2 + 1) else 0).sum).sum =
      1 * (RTree.lsum T.left x * 1 + 1 * RTree.lsum T.right x) := by
    unfold RTree.lsum
    rw [← cross]
    congr 1; apply List.map_congr_left; intro p _
    congr 1; apply List.map_congr_left; intro q _
    rw [pauplinCoeff_add_one, mul_one]
  rw [hc]
  have hdis : ¬(x ∈ T.left.leaves.map Prod.fst ∧ x ∈ T.right.leaves.map Prod.fst) := by
    rintro ⟨h1, h2⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
    obtain ⟨q, hq, hpq⟩ := List.mem_map.mp h2
    exact hd p hp q hq ⟨rfl, hpq⟩
  unfold labels at hx
  have hind : (if x ∈ T.left.leaves.map Prod.fst then (1 : ℝ) else 0) +
      (if x ∈ T.right.leaves.map Prod.fst then 1 else 0) = 1 := by
    rw [List.mem_append] at hx
    by_cases h1 : x ∈ T.left.leaves.map Prod.fst <;>
      by_cases h2 : x ∈ T.right.leaves.map Prod.fst <;> simp_all
  linarith

end UTree

end MathlibExt.Biology.Phylogenetics.BalancedMinimumEvolution
