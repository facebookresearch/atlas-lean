/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Data.List.Forall2
public import Mathlib.Order.WithBot

/-!
# Multiple-choice knapsack: the dynamic-programming recurrence

In the multiple-choice knapsack problem (Sinha and Zoltners 1979) the items come in groups,
exactly one item must be chosen from every group, and the chosen items' total weight is
constrained. Items have natural weights and values in any linearly ordered additive monoid
(`ℤ`, `ℝ`, …). Two constraint forms are covered:

* the *packing* form `total weight ≤ capacity`, the classical problem;
* the *covering* form `total weight ≥ target`, the form CellBender uses to choose integer noise
  counts (Fleming et al. 2023, Methods, eq. 12): one noise count per count-matrix entry
  (a group), value the log posterior probability of that count, weight the count, and a lower
  bound on the total noise count.

Both are solved by the pseudo-polynomial recurrence over groups, with `⊥` marking infeasible
residual constraints:
`best (g :: gs) c = max_{item ∈ g} (value item + best gs (c - weight item))`
(for packing only items with `weight ≤ c` qualify; for covering the residual target uses
truncated subtraction, which is exactly "the target is already met").

## Main results

* `le_bestPacking`, `exists_eq_of_bestPacking_eq_coe`, `bestPacking_eq_bot_iff`: the packing
  recurrence is the optimum over feasible selections, attained, and `⊥` exactly when no feasible
  selection exists.
* `le_bestCovering`, `exists_eq_of_bestCovering_eq_coe`, `bestCovering_eq_bot_iff`: the same for
  the covering form.
* `packingTable_eq`: the bottom-up table (one row of `capacity + 1` cells per suffix of the
  groups, each cell scanning its group once) computes `bestPacking` at every capacity, so the
  optimum costs `(capacity + 1) * Σ |group|` cell-item evaluations.

Not covered: CellBender's specialised solver for strictly log-concave posteriors (its running
time `O(|M| · |L - L*|)`); here the general recurrence is verified.

## References

* P. Sinha and A. A. Zoltners, *The multiple-choice knapsack problem*, Operations Research 27
  (1979), 503–515.
* H. Kellerer, U. Pferschy and D. Pisinger, *Knapsack Problems*, Springer, 2004, Chapter 11.
* S. J. Fleming, M. D. Chaffin, A. Arduini, A.-D. Akkad, E. Banks, J. C. Marioni,
  A. A. Philippakis, P. T. Ellinor and M. Babadi, *Unsupervised removal of systematic background
  noise from droplet-based single-cell experiments using CellBender*, Nature Methods 20 (2023),
  1323–1335.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MultipleChoiceKnapsack

universe u

/-- A knapsack item with a natural weight and a value in `β`. -/
structure Item (β : Type u) where
  /-- The weight counted against the constraint. -/
  weight : ℕ
  /-- The value collected when the item is chosen. -/
  value : β
deriving DecidableEq, Repr

variable {β : Type u}

/-- A selection chooses exactly one item from each group, in group order. -/
def IsSelection (groups : List (List (Item β))) (choice : List (Item β)) : Prop :=
  List.Forall₂ (fun item group => item ∈ group) choice groups

/-- The total weight of a selection. -/
def totalWeight (choice : List (Item β)) : ℕ := (choice.map Item.weight).sum

/-- The total value of a selection. -/
def totalValue [AddMonoid β] (choice : List (Item β)) : β := (choice.map Item.value).sum

section Recurrence

variable [AddCommMonoid β] [LinearOrder β]

/-- The packing recurrence: the best total value of a selection with total weight at most `c`,
`⊥` if none exists. -/
def bestPacking : List (List (Item β)) → ℕ → WithBot β
  | [], _ => 0
  | group :: groups, c =>
      (group.map fun item =>
        if item.weight ≤ c then (item.value : WithBot β) + bestPacking groups (c - item.weight)
        else ⊥).foldr max ⊥

/-- The covering recurrence: the best total value of a selection with total weight at least
`L`, `⊥` if none exists. The residual target `L - weight` is truncated subtraction. -/
def bestCovering : List (List (Item β)) → ℕ → WithBot β
  | [], L => if L = 0 then 0 else ⊥
  | group :: groups, L =>
      (group.map fun item =>
        (item.value : WithBot β) + bestCovering groups (L - item.weight)).foldr max ⊥

omit [AddCommMonoid β] in
private theorem le_foldr_max {γ : Type*} (f : γ → WithBot β) :
    ∀ {l : List γ} {x : γ}, x ∈ l → f x ≤ (l.map f).foldr max ⊥
  | [], _, hx => absurd hx (List.not_mem_nil)
  | y :: l, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact (le_foldr_max f hx).trans (le_max_right _ _)

omit [AddCommMonoid β] in
private theorem foldr_max_mem {γ : Type*} (f : γ → WithBot β) :
    ∀ (l : List γ), (l.map f).foldr max ⊥ = ⊥ ∨ ∃ x ∈ l, f x = (l.map f).foldr max ⊥
  | [] => Or.inl rfl
  | y :: l => by
      simp only [List.map_cons, List.foldr_cons]
      rcases le_total (f y) ((l.map f).foldr max ⊥) with h | h
      · rw [max_eq_right h]
        rcases foldr_max_mem f l with h' | ⟨x, hx, hfx⟩
        · exact Or.inl h'
        · exact Or.inr ⟨x, List.mem_cons_of_mem y hx, hfx⟩
      · rw [max_eq_left h]
        exact Or.inr ⟨y, List.mem_cons_self, rfl⟩

omit [LinearOrder β] in
private theorem coe_sum_cons (a : β) (l : List β) :
    (((a :: l).sum : β) : WithBot β) = (a : WithBot β) + ((l.sum : β) : WithBot β) := by
  rw [List.sum_cons, WithBot.coe_add]

/-- The packing recurrence is an upper bound: every feasible selection's value is at most
`bestPacking`. -/
theorem le_bestPacking [IsOrderedAddMonoid β] :
    ∀ {groups : List (List (Item β))} {choice : List (Item β)} {c : ℕ},
      IsSelection groups choice → totalWeight choice ≤ c →
        ((totalValue choice : β) : WithBot β) ≤ bestPacking groups c
  | [], [], _, _, _ => by simp [totalValue, bestPacking]
  | group :: groups, item :: choice, c, hsel, hw => by
      rcases List.forall₂_cons.mp hsel with ⟨hmem, hrest⟩
      simp only [totalWeight, List.map_cons, List.sum_cons] at hw
      have hle : item.weight ≤ c := by omega
      have ih := le_bestPacking (c := c - item.weight) hrest (by
        simp only [totalWeight]; omega)
      refine le_trans ?_ (le_foldr_max _ hmem)
      simp only [hle, ↓reduceIte, totalValue, List.map_cons, coe_sum_cons]
      exact add_le_add_right ih _
  | [], _ :: _, _, hsel, _ => absurd hsel (by simp [IsSelection])
  | _ :: _, [], _, hsel, _ => absurd hsel (by simp [IsSelection])

/-- The packing recurrence is attained: a finite value is the value of a feasible selection. -/
theorem exists_eq_of_bestPacking_eq_coe :
    ∀ {groups : List (List (Item β))} {c : ℕ} {v : β}, bestPacking groups c = v →
      ∃ choice, IsSelection groups choice ∧ totalWeight choice ≤ c ∧ totalValue choice = v
  | [], c, v, h => by
      simp only [bestPacking] at h
      have hv : v = 0 := WithBot.coe_eq_zero.mp h.symm
      exact ⟨[], List.Forall₂.nil, by simp [totalWeight], by simp [totalValue, hv]⟩
  | group :: groups, c, v, h => by
      simp only [bestPacking] at h
      rcases foldr_max_mem (β := β) _ group with hbot | ⟨item, hmem, hitem⟩
      · rw [hbot] at h
        exact absurd h WithBot.bot_ne_coe
      · rw [h] at hitem
        by_cases hle : item.weight ≤ c
        · simp only [hle, ↓reduceIte] at hitem
          cases hrest : bestPacking groups (c - item.weight) with
          | bot => rw [hrest, WithBot.add_bot] at hitem; exact absurd hitem WithBot.bot_ne_coe
          | coe r =>
              rw [hrest, ← WithBot.coe_add, WithBot.coe_inj] at hitem
              obtain ⟨choice, hsel, hw, hv⟩ := exists_eq_of_bestPacking_eq_coe hrest
              refine ⟨item :: choice, List.Forall₂.cons hmem hsel, ?_, ?_⟩
              · simp only [totalWeight, List.map_cons, List.sum_cons] at hw ⊢; omega
              · simp only [totalValue, List.map_cons, List.sum_cons] at hv ⊢
                rw [hv, hitem]
        · simp only [hle, ↓reduceIte] at hitem
          exact absurd hitem WithBot.bot_ne_coe

/-- The packing recurrence is `⊥` exactly when no selection fits the capacity. -/
theorem bestPacking_eq_bot_iff [IsOrderedAddMonoid β] {groups : List (List (Item β))} {c : ℕ} :
    bestPacking groups c = ⊥ ↔
      ¬ ∃ choice, IsSelection groups choice ∧ totalWeight choice ≤ c := by
  constructor
  · rintro h ⟨choice, hsel, hw⟩
    have := le_bestPacking hsel hw
    rw [h] at this
    exact WithBot.coe_ne_bot (le_bot_iff.mp this)
  · intro h
    cases hb : bestPacking groups c with
    | bot => rfl
    | coe v =>
        obtain ⟨choice, hsel, hw, -⟩ := exists_eq_of_bestPacking_eq_coe hb
        exact absurd ⟨choice, hsel, hw⟩ h

/-- The covering recurrence is an upper bound: every selection of total weight at least `L` has
value at most `bestCovering`. -/
theorem le_bestCovering [IsOrderedAddMonoid β] :
    ∀ {groups : List (List (Item β))} {choice : List (Item β)} {L : ℕ},
      IsSelection groups choice → L ≤ totalWeight choice →
        ((totalValue choice : β) : WithBot β) ≤ bestCovering groups L
  | [], [], L, _, hw => by
      simp only [totalWeight, List.map_nil, List.sum_nil, Nat.le_zero] at hw
      subst hw
      simp [totalValue, bestCovering]
  | group :: groups, item :: choice, L, hsel, hw => by
      rcases List.forall₂_cons.mp hsel with ⟨hmem, hrest⟩
      simp only [totalWeight, List.map_cons, List.sum_cons] at hw
      have ih := le_bestCovering (L := L - item.weight) hrest (by
        simp only [totalWeight]; omega)
      refine le_trans ?_ (le_foldr_max _ hmem)
      simp only [totalValue, List.map_cons, coe_sum_cons]
      exact add_le_add_right ih _
  | [], _ :: _, _, hsel, _ => absurd hsel (by simp [IsSelection])
  | _ :: _, [], _, hsel, _ => absurd hsel (by simp [IsSelection])

/-- The covering recurrence is attained: a finite value is the value of a selection of total
weight at least `L`. -/
theorem exists_eq_of_bestCovering_eq_coe :
    ∀ {groups : List (List (Item β))} {L : ℕ} {v : β}, bestCovering groups L = v →
      ∃ choice, IsSelection groups choice ∧ L ≤ totalWeight choice ∧ totalValue choice = v
  | [], L, v, h => by
      simp only [bestCovering] at h
      by_cases hL : L = 0
      · simp only [hL, ↓reduceIte] at h
        refine ⟨[], List.Forall₂.nil, by simp [totalWeight, hL], ?_⟩
        have : (0 : β) = v := WithBot.coe_inj.mp h
        simp [totalValue, this]
      · simp only [hL, ↓reduceIte] at h
        exact absurd h WithBot.bot_ne_coe
  | group :: groups, L, v, h => by
      simp only [bestCovering] at h
      rcases foldr_max_mem (β := β) _ group with hbot | ⟨item, hmem, hitem⟩
      · rw [hbot] at h
        exact absurd h WithBot.bot_ne_coe
      · rw [h] at hitem
        cases hrest : bestCovering groups (L - item.weight) with
        | bot => rw [hrest, WithBot.add_bot] at hitem; exact absurd hitem WithBot.bot_ne_coe
        | coe r =>
            rw [hrest, ← WithBot.coe_add, WithBot.coe_inj] at hitem
            obtain ⟨choice, hsel, hw, hv⟩ := exists_eq_of_bestCovering_eq_coe hrest
            refine ⟨item :: choice, List.Forall₂.cons hmem hsel, ?_, ?_⟩
            · simp only [totalWeight, List.map_cons, List.sum_cons] at hw ⊢; omega
            · simp only [totalValue, List.map_cons, List.sum_cons] at hv ⊢
              rw [hv, hitem]

/-- The covering recurrence is `⊥` exactly when no selection reaches the target. -/
theorem bestCovering_eq_bot_iff [IsOrderedAddMonoid β] {groups : List (List (Item β))} {L : ℕ} :
    bestCovering groups L = ⊥ ↔
      ¬ ∃ choice, IsSelection groups choice ∧ L ≤ totalWeight choice := by
  constructor
  · rintro h ⟨choice, hsel, hw⟩
    have := le_bestCovering hsel hw
    rw [h] at this
    exact WithBot.coe_ne_bot (le_bot_iff.mp this)
  · intro h
    cases hb : bestCovering groups L with
    | bot => rfl
    | coe v =>
        obtain ⟨choice, hsel, hw, -⟩ := exists_eq_of_bestCovering_eq_coe hb
        exact absurd ⟨choice, hsel, hw⟩ h

/-- The bottom-up packing table: for each suffix of the groups, the row of best values at
capacities `0, …, capacity`, each row computed from the next one by one scan of its group per
cell. -/
def packingTable (capacity : ℕ) : List (List (Item β)) → List (WithBot β)
  | [] => (List.range (capacity + 1)).map fun _ => 0
  | group :: groups =>
      let next := packingTable capacity groups
      (List.range (capacity + 1)).map fun c =>
        (group.map fun item =>
          if item.weight ≤ c then (item.value : WithBot β) + next.getD (c - item.weight) ⊥
          else ⊥).foldr max ⊥

/-- The table computes the recurrence at every capacity `0, …, capacity`. -/
theorem packingTable_eq (capacity : ℕ) :
    ∀ groups : List (List (Item β)),
      packingTable capacity groups = (List.range (capacity + 1)).map (bestPacking groups)
  | [] => by simp [packingTable, bestPacking]
  | group :: groups => by
      simp only [packingTable, bestPacking, packingTable_eq capacity groups]
      refine List.map_congr_left fun c hc => ?_
      have hc' : c < capacity + 1 := List.mem_range.mp hc
      congr 1
      refine List.map_congr_left fun item _ => ?_
      split_ifs with hle
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        rfl
      · rfl

end Recurrence

end Cslib.Algorithms.Lean.MultipleChoiceKnapsack
