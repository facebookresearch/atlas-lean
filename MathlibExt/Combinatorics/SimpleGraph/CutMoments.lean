/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-!
# Moments of the edge cut of a uniform random vertex subset

Let `G` be a finite simple graph on `n` vertices with `M` edges, and let
`S₂ = ∑ v, (G.degree v) ^ 2`. Choose `S` uniformly among the `t`-element
subsets of the vertices. The number of edges with exactly one endpoint in `S`
is `#(G.interedges S Sᶜ)`: `G.interedges S Sᶜ` is the set of ordered adjacent
pairs `(x, y)` with `x ∈ S` and `y ∉ S`, so each cut edge is counted once.

The uniform law on `t`-subsets is the finite average over
`(univ : Finset V).powersetCard t`, a set with `n.choose t` elements: the
expectation of `f S` is `(∑ S ∈ univ.powersetCard t, f S) / n.choose t`.

Put `a = 2t(n-t)/(n(n-1))` and `b = 4t(t-1)(n-t)(n-t-1)/(n(n-1)(n-2)(n-3))`,
with real subtraction and division. For `1 ≤ t < n`:

* `SimpleGraph.sum_card_interedges_compl_powersetCard`: the cut sizes of all
  `t`-subsets add up to `2 * M * (n - 2).choose (t - 1)`.
* `SimpleGraph.mean_card_interedges_compl_powersetCard`: the mean cut size is
  `a * M`.
* `SimpleGraph.variance_card_interedges_compl_powersetCard`: if moreover
  `4 ≤ n`, the population variance (the average squared deviation from the
  mean) is `b * M + (a / 2 - b) * S₂ + (b - a ^ 2) * M ^ 2`.

The proof writes the cut size as a sum over ordered adjacent pairs, expands its
square over pairs of such pairs and counts, for each coincidence pattern, the
`t`-subsets that contain one prescribed vertex set and avoid a disjoint one
(`Finset.card_powersetCard_filter_subset_disjoint`). In the dart form, a fixed
oriented pair of vertex-disjoint adjacent pairs is cut in
`(n - 4).choose (t - 2)` subsets when `2 ≤ t`, that is with probability `b / 4`;
the four orientations of a pair of disjoint edges give `b`. For `t = 1` every
pattern with two prescribed inside vertices has count `0`.

The variance can vanish: in the complete graph every `t`-subset cuts
`t * (n - t)` edges. Nothing here assumes or proves positive variance, a
normalisation, a central limit theorem or a `p`-value statement.
-/

@[expose] public section

open Finset

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Counting `t`-subsets with a prescribed inside and outside.** In a finite
type with `n` elements, if `A` and `B` are disjoint and `#A ≤ t`, the
`t`-subsets that contain `A` and are disjoint from `B` number
`(n - #A - #B).choose (t - #A)`. The hypothesis `#A ≤ t` is needed: without it
the count is `0` while the truncated right-hand side need not be; see
`card_powersetCard_filter_subset_disjoint_eq_ite`. -/
theorem card_powersetCard_filter_subset_disjoint {A B : Finset α}
    (hAB : Disjoint A B) {t : ℕ} (ht : #A ≤ t) :
    #{S ∈ (univ : Finset α).powersetCard t | A ⊆ S ∧ Disjoint S B} =
      (Fintype.card α - #A - #B).choose (t - #A) := by
  have hfilt : ({S ∈ (univ : Finset α).powersetCard t | A ⊆ S ∧ Disjoint S B} :
      Finset (Finset α)) = (Bᶜ.powersetCard t).filter (A ⊆ ·) := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and,
      subset_compl_iff_disjoint_right]
    tauto
  rw [hfilt, card_filter_powersetCard_subset A Bᶜ t
    (subset_compl_iff_disjoint_right.2 hAB) ht, card_compl]
  congr 1
  omega

/-- **Counting `t`-subsets with a prescribed inside and outside, in general.**
For arbitrary `A` and `B` in a finite type with `n` elements, the number of
`t`-subsets that contain `A` and are disjoint from `B` is
`(n - #A - #B).choose (t - #A)` when `A` and `B` are disjoint and `#A ≤ t`,
and `0` otherwise. -/
theorem card_powersetCard_filter_subset_disjoint_eq_ite (A B : Finset α)
    (t : ℕ) :
    #{S ∈ (univ : Finset α).powersetCard t | A ⊆ S ∧ Disjoint S B} =
      if Disjoint A B ∧ #A ≤ t then
        (Fintype.card α - #A - #B).choose (t - #A) else 0 := by
  split_ifs with h
  · exact card_powersetCard_filter_subset_disjoint h.1 h.2
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro S hS ⟨hAS, hSB⟩
    refine h ⟨hSB.mono_left hAS, ?_⟩
    rw [← (mem_powersetCard.1 hS).2]
    exact card_le_card hAS

end Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

private lemma card_interedges_compl_eq_sum (S : Finset V) :
    (#(G.interedges S Sᶜ) : ℝ) =
      ∑ x, ∑ y, (if G.Adj x y then (1 : ℝ) else 0) *
        (if x ∈ S ∧ y ∉ S then 1 else 0) := by
  have h : G.interedges S Sᶜ =
      (univ : Finset (V × V)).filter
        (fun p => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S) := by
    ext p
    simp only [interedges, Rel.mem_interedges_iff, mem_compl, mem_filter,
      mem_univ, true_and]
    tauto
  rw [h, card_filter, Nat.cast_sum, ← univ_product_univ, sum_product]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hxy : G.Adj x y <;> simp [hxy]

omit [DecidableEq V] in
private lemma sum_degree_eq_sum_adj_real :
    ∑ x, ∑ y, (if G.Adj x y then (1 : ℝ) else 0) = 2 * #G.edgeFinset := by
  have : ∀ x, ∑ y, (if G.Adj x y then (1 : ℝ) else 0) = G.degree x := by
    intro x
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, sum_boole]
  simp_rw [this]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

private lemma sum_adj_mul_eq_left (x : V) :
    ∑ z, ∑ w, (if G.Adj z w then (1 : ℝ) else 0) * (if z = x then 1 else 0) =
      G.degree x := by
  rw [Fintype.sum_eq_single x (fun z hz => by simp [hz])]
  simp only [ite_true, mul_one]
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, sum_boole]

private lemma sum_adj_mul_eq_right (x : V) :
    ∑ z, ∑ w, (if G.Adj z w then (1 : ℝ) else 0) * (if w = x then 1 else 0) =
      G.degree x := by
  rw [sum_comm]
  simp_rw [G.adj_comm]
  exact G.sum_adj_mul_eq_left x

private lemma sum_adj_mul_eq_pair (x y : V) :
    ∑ z, ∑ w, (if G.Adj z w then (1 : ℝ) else 0) *
      (if z = x ∧ w = y then 1 else 0) = if G.Adj x y then 1 else 0 := by
  rw [Fintype.sum_eq_single x (fun z hz => by simp [hz]),
    Fintype.sum_eq_single y (fun w hw => by simp [hw])]
  simp

/-- The number of `t`-subsets that contain a prescribed set of `a` vertices and
avoid a disjoint prescribed set of `b` vertices, as a real number. The guard
`a ≤ t` makes the count `0` when the prescribed inside set is too large. -/
private noncomputable def patternCount (t a b : ℕ) : ℝ :=
  if a ≤ t then ((Fintype.card V - a - b).choose (t - a) : ℕ) else 0

private lemma sum_cut_mul_cut (t : ℕ) (x y z w : V) :
    ∑ S ∈ (univ : Finset V).powersetCard t,
      (if x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) *
        (if z ∈ S ∧ w ∉ S then 1 else 0) =
      if Disjoint ({x, z} : Finset V) {y, w} then
        patternCount (V := V) t #({x, z} : Finset V) #({y, w} : Finset V)
      else 0 := by
  have h1 : ∀ S : Finset V, (if x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) *
      (if z ∈ S ∧ w ∉ S then 1 else 0) =
      if ({x, z} : Finset V) ⊆ S ∧ Disjoint S {y, w} then 1 else 0 := by
    intro S
    have : (({x, z} : Finset V) ⊆ S ∧ Disjoint S {y, w}) ↔
        ((x ∈ S ∧ y ∉ S) ∧ (z ∈ S ∧ w ∉ S)) := by
      simp only [insert_subset_iff, singleton_subset_iff, disjoint_insert_right,
        disjoint_singleton_right]
      tauto
    rw [if_congr this rfl rfl, ite_zero_mul_ite_zero, mul_one]
  simp_rw [h1]
  rw [sum_boole, card_powersetCard_filter_subset_disjoint_eq_ite]
  unfold patternCount
  split_ifs <;> simp_all

private lemma sum_adj_mul_pattern (t : ℕ) {x y : V} (hxy : G.Adj x y) :
    ∑ z, ∑ w, (if G.Adj z w then (1 : ℝ) else 0) *
      (if Disjoint ({x, z} : Finset V) {y, w} then
        patternCount (V := V) t #({x, z} : Finset V) #({y, w} : Finset V)
      else 0) =
    patternCount (V := V) t 1 1 +
      patternCount (V := V) t 1 2 * (G.degree x - 1) +
      patternCount (V := V) t 2 1 * (G.degree y - 1) +
      patternCount (V := V) t 2 2 *
        (2 * #G.edgeFinset - 2 * G.degree x - 2 * G.degree y + 2) := by
  have hne : x ≠ y := G.ne_of_adj hxy
  have key : ∀ z w, (if G.Adj z w then (1 : ℝ) else 0) *
      (if Disjoint ({x, z} : Finset V) {y, w} then
        patternCount (V := V) t #({x, z} : Finset V) #({y, w} : Finset V)
      else 0) =
      patternCount (V := V) t 2 2 * (if G.Adj z w then (1 : ℝ) else 0)
      - patternCount (V := V) t 2 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) * (if z = x then 1 else 0))
      - patternCount (V := V) t 2 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) * (if z = y then 1 else 0))
      - patternCount (V := V) t 2 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) * (if w = x then 1 else 0))
      - patternCount (V := V) t 2 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) * (if w = y then 1 else 0))
      + patternCount (V := V) t 2 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) *
          (if z = x ∧ w = y then 1 else 0))
      + patternCount (V := V) t 2 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) *
          (if z = y ∧ w = x then 1 else 0))
      + patternCount (V := V) t 1 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) * (if z = x then 1 else 0))
      - patternCount (V := V) t 1 2 *
        ((if G.Adj z w then (1 : ℝ) else 0) *
          (if z = x ∧ w = y then 1 else 0))
      + patternCount (V := V) t 2 1 *
        ((if G.Adj z w then (1 : ℝ) else 0) * (if w = y then 1 else 0))
      - patternCount (V := V) t 2 1 *
        ((if G.Adj z w then (1 : ℝ) else 0) *
          (if z = x ∧ w = y then 1 else 0))
      + patternCount (V := V) t 1 1 *
        ((if G.Adj z w then (1 : ℝ) else 0) *
          (if z = x ∧ w = y then 1 else 0)) := by
    intro z w
    by_cases hzw : G.Adj z w
    · have hzw' : z ≠ w := G.ne_of_adj hzw
      by_cases h1 : z = x <;> by_cases h2 : w = y <;> by_cases h3 : z = y <;>
        by_cases h4 : w = x <;>
        simp_all [disjoint_insert_right, Ne.symm]
    · simp [hzw]
  simp only [key, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [sum_degree_eq_sum_adj_real, sum_adj_mul_eq_left, sum_adj_mul_eq_left,
    sum_adj_mul_eq_right, sum_adj_mul_eq_right, sum_adj_mul_eq_pair,
    sum_adj_mul_eq_pair]
  simp only [hxy, hxy.symm, ite_true]
  ring

omit [DecidableEq V] in
private lemma sum_adj_mul_degree_left :
    ∑ x, ∑ y, (if G.Adj x y then (1 : ℝ) else 0) * G.degree x =
      ∑ v, (G.degree v : ℝ) ^ 2 := by
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_mul, sq]
  congr 1
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, sum_boole]

omit [DecidableEq V] in
private lemma sum_adj_mul_degree_right :
    ∑ x, ∑ y, (if G.Adj x y then (1 : ℝ) else 0) * G.degree y =
      ∑ v, (G.degree v : ℝ) ^ 2 := by
  rw [sum_comm]
  simp_rw [G.adj_comm]
  exact G.sum_adj_mul_degree_left

private lemma sum_cut (t : ℕ) {x y : V} (hne : x ≠ y) :
    ∑ S ∈ (univ : Finset V).powersetCard t,
      (if x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) = patternCount (V := V) t 1 1 := by
  have h := sum_cut_mul_cut (V := V) t x y x y
  simp only [insert_eq_of_mem (mem_singleton_self _), card_singleton,
    disjoint_singleton, ne_eq, hne, not_false_eq_true, ite_true] at h
  rw [← h]
  refine sum_congr rfl fun S _ => ?_
  split_ifs <;> simp

private lemma sum_card_interedges_compl_eq (t : ℕ) :
    ∑ S ∈ (univ : Finset V).powersetCard t, (#(G.interedges S Sᶜ) : ℝ) =
      2 * #G.edgeFinset * patternCount (V := V) t 1 1 := by
  rw [sum_congr rfl fun S _ => G.card_interedges_compl_eq_sum S, sum_comm]
  have : ∀ x y, (if G.Adj x y then (1 : ℝ) else 0) *
      ∑ S ∈ (univ : Finset V).powersetCard t,
        (if x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) =
      (if G.Adj x y then (1 : ℝ) else 0) * patternCount (V := V) t 1 1 := by
    intro x y
    by_cases hxy : G.Adj x y
    · rw [sum_cut t (G.ne_of_adj hxy)]
    · simp [hxy]
  calc _ = ∑ x, ∑ y, (if G.Adj x y then (1 : ℝ) else 0) *
        ∑ S ∈ (univ : Finset V).powersetCard t,
          (if x ∈ S ∧ y ∉ S then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun y _ => (mul_sum _ _ _).symm
    _ = _ := by
        simp_rw [this, ← sum_mul, sum_degree_eq_sum_adj_real]

private lemma sum_sq_card_interedges_compl_eq (t : ℕ) :
    ∑ S ∈ (univ : Finset V).powersetCard t, (#(G.interedges S Sᶜ) : ℝ) ^ 2 =
      2 * #G.edgeFinset * patternCount (V := V) t 1 1 +
      (patternCount (V := V) t 1 2 + patternCount (V := V) t 2 1) *
        (∑ v, (G.degree v : ℝ) ^ 2 - 2 * #G.edgeFinset) +
      patternCount (V := V) t 2 2 *
        (4 * (#G.edgeFinset : ℝ) ^ 2 + 4 * #G.edgeFinset -
          4 * ∑ v, (G.degree v : ℝ) ^ 2) := by
  set A : V → V → ℝ := fun x y => if G.Adj x y then 1 else 0 with hA
  set I : Finset V → V → V → ℝ := fun S x y => if x ∈ S ∧ y ∉ S then 1 else 0
    with hI
  have hR : ∀ S : Finset V, (#(G.interedges S Sᶜ) : ℝ) =
      ∑ x, ∑ y, A x y * I S x y := G.card_interedges_compl_eq_sum
  calc _ = ∑ S ∈ (univ : Finset V).powersetCard t,
        ∑ x, ∑ y, ∑ z, ∑ w, (A x y * A z w) * (I S x y * I S z w) := by
        refine sum_congr rfl fun S _ => ?_
        rw [hR, sq, sum_mul]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun y _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun z _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun w _ => ?_
        ring
    _ = ∑ x, ∑ y, ∑ z, ∑ w, (A x y * A z w) *
          ∑ S ∈ (univ : Finset V).powersetCard t, (I S x y * I S z w) := by
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun z _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun w _ => ?_
        rw [mul_sum]
    _ = ∑ x, ∑ y, A x y * (patternCount (V := V) t 1 1 +
          patternCount (V := V) t 1 2 * (G.degree x - 1) +
          patternCount (V := V) t 2 1 * (G.degree y - 1) +
          patternCount (V := V) t 2 2 *
            (2 * #G.edgeFinset - 2 * G.degree x - 2 * G.degree y + 2)) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
        simp only [hI, sum_cut_mul_cut]
        by_cases hxy : G.Adj x y
        · rw [← G.sum_adj_mul_pattern t hxy, mul_sum]
          refine sum_congr rfl fun z _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun w _ => ?_
          simp only [hA, hxy, ite_true]
          ring
        · simp [hA, hxy]
    _ = _ := by
        have e : ∀ x y, A x y * (patternCount (V := V) t 1 1 +
            patternCount (V := V) t 1 2 * (G.degree x - 1) +
            patternCount (V := V) t 2 1 * (G.degree y - 1) +
            patternCount (V := V) t 2 2 *
              (2 * #G.edgeFinset - 2 * G.degree x - 2 * G.degree y + 2)) =
            (patternCount (V := V) t 1 1 - patternCount (V := V) t 1 2 -
              patternCount (V := V) t 2 1 +
              patternCount (V := V) t 2 2 * (2 * #G.edgeFinset + 2)) * A x y
            + (patternCount (V := V) t 1 2 - 2 * patternCount (V := V) t 2 2) *
              (A x y * G.degree x)
            + (patternCount (V := V) t 2 1 - 2 * patternCount (V := V) t 2 2) *
              (A x y * G.degree y) := by
          intro x y; ring
        simp only [e, sum_add_distrib, ← mul_sum]
        rw [hA, sum_degree_eq_sum_adj_real, sum_adj_mul_degree_left,
          sum_adj_mul_degree_right]
        ring

private lemma choose_mul_ratio_two {n t : ℕ} (ht : 1 ≤ t) (htn : t < n) :
    ((n - 2).choose (t - 1) : ℝ) * (n * (n - 1)) =
      t * (n - t) * n.choose t := by
  obtain ⟨a, rfl⟩ : ∃ a, t = a + 1 := ⟨t - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = a + b + 2 := ⟨n - a - 2, by omega⟩
  have h1 := Nat.add_one_mul_choose_eq (a + b + 1) a
  have h2 := Nat.choose_mul_succ_eq (a + b) a
  rw [show a + b + 1 - a = b + 1 by omega] at h2
  rw [show a + b + 2 - 2 = a + b by omega, show a + 1 - 1 = a by omega]
  have h1' : ((a + b + 1 + 1 : ℕ) : ℝ) * ((a + b + 1).choose a : ℕ) =
      ((a + b + 1 + 1).choose (a + 1) : ℕ) * ((a + 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (((a + b).choose a : ℕ) : ℝ) * ((a + b + 1 : ℕ) : ℝ) =
      ((a + b + 1).choose a : ℕ) * ((b + 1 : ℕ) : ℝ) := by
    exact_mod_cast h2
  push_cast at h1' h2' ⊢
  linear_combination (↑a + ↑b + 2) * h2' + (↑b + 1) * h1'

private lemma choose_mul_ratio_four {n t : ℕ} (hn4 : 4 ≤ n) (ht : 1 ≤ t)
    (htn : t < n) :
    (if 2 ≤ t then ((n - 2 - 2).choose (t - 2) : ℝ) else 0) *
      (n * (n - 1) * (n - 2) * (n - 3)) =
      t * (t - 1) * (n - t) * (n - t - 1) * n.choose t := by
  obtain rfl | ht2 := eq_or_lt_of_le ht
  · simp
  obtain ⟨a, rfl⟩ : ∃ a, t = a + 2 := ⟨t - 2, by omega⟩
  have h2 : 2 ≤ a + 2 := by omega
  simp only [h2, ite_true]
  obtain hn | hn : n = a + 3 ∨ a + 4 ≤ n := by omega
  · subst hn
    rw [Nat.choose_eq_zero_of_lt (show a + 3 - 2 - 2 < a + 2 - 2 by omega)]
    push_cast
    ring
  obtain ⟨b, rfl⟩ : ∃ b, n = a + b + 4 := ⟨n - a - 4, by omega⟩
  rw [show a + b + 4 - 2 - 2 = a + b by omega,
    show a + 2 - 2 = a by omega]
  have k1 := Nat.add_one_mul_choose_eq (a + b + 3) (a + 1)
  have k2 := Nat.add_one_mul_choose_eq (a + b + 2) a
  have k3 := Nat.choose_mul_succ_eq (a + b + 1) a
  have k4 := Nat.choose_mul_succ_eq (a + b) a
  rw [show a + b + 1 + 1 - a = b + 2 by omega] at k3
  rw [show a + b + 1 - a = b + 1 by omega] at k4
  have k1' : ((a + b + 3 + 1 : ℕ) : ℝ) * ((a + b + 3).choose (a + 1) : ℕ) =
      ((a + b + 3 + 1).choose (a + 1 + 1) : ℕ) * ((a + 1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast k1
  have k2' : ((a + b + 2 + 1 : ℕ) : ℝ) * ((a + b + 2).choose a : ℕ) =
      ((a + b + 2 + 1).choose (a + 1) : ℕ) * ((a + 1 : ℕ) : ℝ) := by
    exact_mod_cast k2
  have k3' : (((a + b + 1).choose a : ℕ) : ℝ) * ((a + b + 1 + 1 : ℕ) : ℝ) =
      ((a + b + 1 + 1).choose a : ℕ) * ((b + 2 : ℕ) : ℝ) := by
    exact_mod_cast k3
  have k4' : (((a + b).choose a : ℕ) : ℝ) * ((a + b + 1 : ℕ) : ℝ) =
      ((a + b + 1).choose a : ℕ) * ((b + 1 : ℕ) : ℝ) := by
    exact_mod_cast k4
  push_cast at k1' k2' k3' k4' ⊢
  linear_combination (↑a + ↑b + 4) * (↑a + ↑b + 3) * (↑a + ↑b + 2) * k4' +
    (↑a + ↑b + 4) * (↑a + ↑b + 3) * (↑b + 1) * k3' +
    (↑a + ↑b + 4) * (↑b + 1) * (↑b + 2) * k2' +
    (↑b + 1) * (↑b + 2) * (↑a + 1) * k1'

omit [DecidableEq V] in
private lemma patternCount_one_one {t : ℕ} (ht : 1 ≤ t) :
    patternCount (V := V) t 1 1 =
      ((Fintype.card V - 2).choose (t - 1) : ℕ) := by
  simp [patternCount, ht, Nat.sub_sub]

omit [DecidableEq V] in
private lemma patternCount_pascal {t : ℕ} (hn : 3 ≤ Fintype.card V)
    (ht : 1 ≤ t) :
    patternCount (V := V) t 1 2 + patternCount (V := V) t 2 1 =
      patternCount (V := V) t 1 1 := by
  obtain rfl | ht2 := eq_or_lt_of_le ht
  · simp [patternCount]
  obtain ⟨a, rfl⟩ : ∃ a, t = a + 2 := ⟨t - 2, by omega⟩
  have h := Nat.choose_succ_succ' (Fintype.card V - 3) a
  rw [show Fintype.card V - 3 + 1 = Fintype.card V - 1 - 1 by omega] at h
  simp only [patternCount, show 1 ≤ a + 2 by omega, show 2 ≤ a + 2 by omega,
    ite_true, show a + 2 - 1 = a + 1 by omega, show a + 2 - 2 = a by omega,
    show Fintype.card V - 1 - 2 = Fintype.card V - 3 by omega,
    show Fintype.card V - 2 - 1 = Fintype.card V - 3 by omega, h]
  push_cast
  ring

/-- **Sum of the edge cut over all `t`-subsets.** For `1 ≤ t`, the numbers of
edges of `G` with exactly one endpoint in `S`, summed over the `t`-subsets `S`
of the vertices, give `2 * M * (n - 2).choose (t - 1)`, where `M` is the number
of edges and `n` the number of vertices. -/
theorem sum_card_interedges_compl_powersetCard {t : ℕ} (ht : 1 ≤ t) :
    ∑ S ∈ (univ : Finset V).powersetCard t, #(G.interedges S Sᶜ) =
      2 * #G.edgeFinset * (Fintype.card V - 2).choose (t - 1) := by
  have h := G.sum_card_interedges_compl_eq t
  rw [patternCount_one_one ht] at h
  exact_mod_cast h

/-- **Mean edge cut of a uniform `t`-subset.** Let `n` be the number of
vertices, `M` the number of edges and `1 ≤ t < n`. The average, over the
`n.choose t` subsets `S` with `t` elements, of the number of edges with exactly
one endpoint in `S` is `2t(n-t)/(n(n-1)) * M`.

Only `1 ≤ t < n` is assumed, so `n ≥ 2`; this covers the domain `4 ≤ n` of
`variance_card_interedges_compl_powersetCard`. -/
theorem mean_card_interedges_compl_powersetCard {t : ℕ} (ht : 1 ≤ t)
    (htn : t < Fintype.card V) :
    (∑ S ∈ (univ : Finset V).powersetCard t, (#(G.interedges S Sᶜ) : ℝ)) /
        (Fintype.card V).choose t =
      2 * t * (Fintype.card V - t) /
        (Fintype.card V * (Fintype.card V - 1)) * #G.edgeFinset := by
  have r := choose_mul_ratio_two ht htn
  have hN : ((Fintype.card V).choose t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos htn.le).ne'
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by
    have : 0 < Fintype.card V := by omega
    positivity
  have hn1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by
    have h2 : 2 ≤ Fintype.card V := by omega
    have : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast h2
    linarith
  rw [G.sum_card_interedges_compl_eq t, patternCount_one_one ht]
  field_simp
  linear_combination (#G.edgeFinset : ℝ) * r

/-- **Variance of the edge cut of a uniform `t`-subset.** Let `n ≥ 4` be the
number of vertices, `M` the number of edges, `S₂ = ∑ v, (G.degree v) ^ 2` and
`1 ≤ t < n`. Put `a = 2t(n-t)/(n(n-1))` and
`b = 4t(t-1)(n-t)(n-t-1)/(n(n-1)(n-2)(n-3))`. For `S` uniform among the
`t`-subsets, the population variance of the cut size
`R S = #(G.interedges S Sᶜ)`, written as the average of `(R S - μ) ^ 2` with
`μ` the average of `R`, is `b * M + (a / 2 - b) * S₂ + (b - a ^ 2) * M ^ 2`.

It is not a sample variance, and it can be `0` (for example for the complete
graph); no positivity is asserted. -/
theorem variance_card_interedges_compl_powersetCard {t : ℕ}
    (hn : 4 ≤ Fintype.card V) (ht : 1 ≤ t) (htn : t < Fintype.card V) :
    (∑ S ∈ (univ : Finset V).powersetCard t,
        ((#(G.interedges S Sᶜ) : ℝ) -
          (∑ T ∈ (univ : Finset V).powersetCard t,
            (#(G.interedges T Tᶜ) : ℝ)) / (Fintype.card V).choose t) ^ 2) /
        (Fintype.card V).choose t =
      4 * t * (t - 1) * (Fintype.card V - t) * (Fintype.card V - t - 1) /
          (Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 2) *
            (Fintype.card V - 3)) * #G.edgeFinset +
        (2 * t * (Fintype.card V - t) /
            (Fintype.card V * (Fintype.card V - 1)) / 2 -
          4 * t * (t - 1) * (Fintype.card V - t) * (Fintype.card V - t - 1) /
            (Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 2) *
              (Fintype.card V - 3))) * ∑ v, (G.degree v : ℝ) ^ 2 +
        (4 * t * (t - 1) * (Fintype.card V - t) * (Fintype.card V - t - 1) /
            (Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 2) *
              (Fintype.card V - 3)) -
          (2 * t * (Fintype.card V - t) /
            (Fintype.card V * (Fintype.card V - 1))) ^ 2) *
          (#G.edgeFinset : ℝ) ^ 2 := by
  have r2 := choose_mul_ratio_two ht htn
  have r4 := choose_mul_ratio_four hn ht htn
  have hNpos : 0 < ((Fintype.card V).choose t : ℝ) := by
    exact_mod_cast Nat.choose_pos htn.le
  have hN : ((Fintype.card V).choose t : ℝ) ≠ 0 := hNpos.ne'
  have hn4 : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
  have hn2 : (Fintype.card V : ℝ) - 2 ≠ 0 := by linarith
  have hn3 : (Fintype.card V : ℝ) - 3 ≠ 0 := by linarith
  have hcard : (#((univ : Finset V).powersetCard t) : ℝ) =
      (Fintype.card V).choose t := by
    simp [card_powersetCard]
  set N : ℝ := ((Fintype.card V).choose t : ℝ) with hNdef
  set R : Finset V → ℝ := fun S => (#(G.interedges S Sᶜ) : ℝ) with hR
  have hdev : ∑ S ∈ (univ : Finset V).powersetCard t,
      (R S - (∑ T ∈ (univ : Finset V).powersetCard t, R T) / N) ^ 2 =
      ∑ S ∈ (univ : Finset V).powersetCard t, R S ^ 2 -
        (∑ T ∈ (univ : Finset V).powersetCard t, R T) ^ 2 / N := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const,
      nsmul_eq_mul, hcard, ← sum_mul, ← mul_sum]
    field_simp
    ring
  simp only [hR] at hdev
  rw [hdev, G.sum_sq_card_interedges_compl_eq t,
    G.sum_card_interedges_compl_eq t,
    patternCount_pascal (by omega) ht, patternCount_one_one ht]
  have e2 : (((Fintype.card V - 2).choose (t - 1) : ℕ) : ℝ) =
      t * (Fintype.card V - t) * N /
        (Fintype.card V * (Fintype.card V - 1)) := by
    rw [eq_div_iff (mul_ne_zero hn0 hn1)]
    exact r2
  have e4 : patternCount (V := V) t 2 2 =
      t * (t - 1) * (Fintype.card V - t) * (Fintype.card V - t - 1) * N /
        (Fintype.card V * (Fintype.card V - 1) * (Fintype.card V - 2) *
          (Fintype.card V - 3)) := by
    rw [eq_div_iff (by simp [hn0, hn1, hn2, hn3])]
    simpa [patternCount, Nat.sub_sub] using r4
  rw [e2, e4]
  field_simp
  ring

end SimpleGraph
