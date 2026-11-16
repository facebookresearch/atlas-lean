/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.GeneralGraph
public import MathlibExtTest.Biology.PopulationGenetics.AdmixtureGraph

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.GeneralGraph

open MathlibExt.Biology.PopulationGenetics
open MathlibExtTest.Biology.PopulationGenetics.AdmixtureGraph

/-- In the four-node witness graph, every parent has a smaller index than its child. -/
private theorem parent_lt {Y X : Fin 4} (h : Y ∈ G.parents X) : (Y : ℕ) < (X : ℕ) := by
  fin_cases X <;> fin_cases Y <;> simp_all [G, par]

/-- Every ancestral chain in the witness graph strictly increases the child index. -/
private theorem transGen_lt {a b : Fin 4}
    (h : Relation.TransGen (fun Y X => Y ∈ G.parents X) a b) : (a : ℕ) < (b : ℕ) := by
  induction h with
  | single hstep => exact parent_lt hstep
  | tail _ hstep ih => exact lt_trans ih (parent_lt hstep)

/-- Node `1` is not an ancestor of its sibling `2` in the witness graph. -/
private theorem not_transGen_one_two :
    ¬ Relation.TransGen (fun Y X => Y ∈ G.parents X) (1 : Fin 4) (2 : Fin 4) := by
  intro h
  cases h with
  | single hstep => simp [G, par] at hstep
  | tail hpre hstep =>
    have hz := hstep
    simp [G, par] at hz
    subst hz
    have hlt := transGen_lt hpre
    norm_num at hlt

/-- Node `2` is not an ancestor of its sibling `1` in the witness graph. -/
private theorem not_transGen_two_one :
    ¬ Relation.TransGen (fun Y X => Y ∈ G.parents X) (2 : Fin 4) (1 : Fin 4) := by
  intro h
  cases h with
  | single hstep => simp [G, par] at hstep
  | tail hpre hstep =>
    have hz := hstep
    simp [G, par] at hz
    subst hz
    have hlt := transGen_lt hpre
    norm_num at hlt

/-- The two parents of the admixture node form an antichain. -/
private theorem antichain_one_two :
    IsAntichain (Relation.TransGen fun Y X => Y ∈ G.parents X)
      (({1, 2} : Finset (Fin 4)) : Set (Fin 4)) := by
  intro a ha b hb _hab htrans
  have ha12 : a = 1 ∨ a = 2 := by simpa using ha
  have hb12 : b = 1 ∨ b = 2 := by simpa using hb
  rcases ha12 with rfl | rfl <;> rcases hb12 with rfl | rfl
  · exact (lt_irrefl _ (transGen_lt htrans)).elim
  · exact not_transGen_one_two htrans
  · exact not_transGen_two_one htrans
  · exact (lt_irrefl _ (transGen_lt htrans)).elim

/-- Every root-ward chain from the admixture node meets one of its two parents. -/
private theorem separates_one_two :
    ∀ π : List (Fin 4), π.head? = some 3 → π.getLast? = some G.root →
      π.IsChain (fun a b => b ∈ G.parents a) → ∃ c ∈ ({1, 2} : Finset (Fin 4)), c ∈ π := by
  intro π hhead hlast hchain
  cases π with
  | nil => simp at hhead
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead, G] at hlast
    | cons b tl =>
      have ha : a = 3 := by simpa using hhead
      subst ha
      have hb : b ∈ G.parents 3 := (List.isChain_cons_cons.mp hchain).1
      have hb12 : b = 1 ∨ b = 2 := by simpa [G, par] using hb
      exact ⟨b, by simpa using hb12, by simp⟩

/-- The lineage of the root does not visit node `2`. -/
theorem visit_0_2 : G.visit 0 2 = 0 := by
  rw [G.visit_eq]
  simp [G, par]

/-- The lineage of `1` does not pass through its sibling `2`. -/
theorem visit_1_2 : G.visit 1 2 = 0 := by
  rw [G.visit_eq]
  simpa [G, par, pr] using visit_0_2

/-- The admixed lineage passes through population `2` with probability `2 / 3`. -/
theorem visit_3_2 : G.visit 3 2 = 2 / 3 := by
  rw [G.visit_eq, show G.parents 3 = {1, 2} from rfl, Finset.sum_pair (by decide),
    visit_1_2, G.visit_self]
  simp [G, pr]

/-- Diamond-graph cut at the two parents of the admixture node. -/
example : ∑ c ∈ ({1, 2} : Finset (Fin 4)), G.visit 3 c = 1 :=
  G.sum_visit_cut_eq_one _ _ antichain_one_two separates_one_two

/-- The same diamond calculation in expanded form: `1 / 3 + 2 / 3 = 1`. -/
example : G.visit 3 1 + G.visit 3 2 = 1 := by
  rw [visit_3_1, visit_3_2]
  norm_num

/-- The singleton root cut recovers the statement that every lineage reaches the root. -/
example : ∑ c ∈ ({G.root} : Finset (Fin 4)), G.visit 3 c = 1 := by
  simp [G.visit_root]

/-- Parents for a three-parent abstract example: node `4` has parents `1`, `2`, and `3`. -/
private def par5 : Fin 5 → Finset (Fin 5) := ![∅, {0}, {0}, {0}, {1, 2, 3}]

/-- Proportions for the three-parent abstract example. -/
private noncomputable def pr5 : Fin 5 → Fin 5 → ℝ :=
  ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 0],
    ![0, 1 / 2, 1 / 3, 1 / 6, 0]]

/-- Visit probabilities for the three-parent abstract example, by start node and target node. -/
private noncomputable def vis5 : Fin 5 → Fin 5 → ℝ :=
  ![![1, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0],
    ![1, 1 / 2, 1 / 3, 1 / 6, 1]]

/-- In the three-parent example, every parent has a smaller index than its child. -/
private theorem parent5_lt {Y X : Fin 5} (h : Y ∈ par5 X) : (Y : ℕ) < (X : ℕ) := by
  fin_cases X <;> fin_cases Y <;> simp_all [par5]

/-- The parent relation of the three-parent example is well founded. -/
private theorem wf5 : WellFounded fun Y X : Fin 5 => Y ∈ par5 X :=
  Subrelation.wf (r := fun Y X : Fin 5 => (Y : ℕ) < X)
    (fun h => parent5_lt h) (measure fun x : Fin 5 => (x : ℕ)).wf

/-- Every ancestral chain in the three-parent example strictly increases the child index. -/
private theorem transGen5_lt {a b : Fin 5}
    (h : Relation.TransGen (fun Y X => Y ∈ par5 X) a b) : (a : ℕ) < (b : ℕ) := by
  induction h with
  | single hstep => exact parent5_lt hstep
  | tail _ hstep ih => exact lt_trans ih (parent5_lt hstep)

/-- No nonzero start node has an ancestral chain ending at one of the three parents. -/
private theorem not_transGen5_to_cut {a b : Fin 5} (hb : b = 1 ∨ b = 2 ∨ b = 3)
    (ha : a ≠ 0) (h : Relation.TransGen (fun Y X => Y ∈ par5 X) a b) : False := by
  cases h with
  | single hstep =>
    have ha0 : a = 0 := by
      rcases hb with rfl | rfl | rfl <;> simpa [par5] using hstep
    exact ha ha0
  | tail hpre hstep =>
    have hz := hstep
    rcases hb with rfl | rfl | rfl <;> simp [par5] at hz
    all_goals subst hz
    all_goals have hlt := transGen5_lt hpre
    all_goals norm_num at hlt

/-- The proportions of every non-root node in the three-parent example sum to `1`. -/
private theorem sum_prop5 : ∀ X, X ≠ (0 : Fin 5) → ∑ Y ∈ par5 X, pr5 X Y = 1 := by
  intro X hX
  fin_cases X <;> simp_all [par5, pr5]
  norm_num

/-- The displayed visit table satisfies the first-step recursion. -/
private theorem visit_eq5 : ∀ X c,
    vis5 X c = if X = c then 1 else ∑ Y ∈ par5 X, pr5 X Y * vis5 Y c := by
  intro X c
  fin_cases X <;> fin_cases c <;> norm_num [par5, pr5, vis5]

/-- The three parents of node `4` form an antichain. -/
private theorem antichain5 :
    IsAntichain (Relation.TransGen fun Y X => Y ∈ par5 X)
      (({1, 2, 3} : Finset (Fin 5)) : Set (Fin 5)) := by
  intro a ha b hb _hab htrans
  have ha123 : a = 1 ∨ a = 2 ∨ a = 3 := by simpa using ha
  have hb123 : b = 1 ∨ b = 2 ∨ b = 3 := by simpa using hb
  exact not_transGen5_to_cut hb123 (by rcases ha123 with rfl | rfl | rfl <;> norm_num) htrans

/-- Every root-ward chain from node `4` meets one of its three parents. -/
private theorem separates5 :
    ∀ π : List (Fin 5), π.head? = some 4 → π.getLast? = some 0 →
      π.IsChain (fun a b => b ∈ par5 a) → ∃ c ∈ ({1, 2, 3} : Finset (Fin 5)), c ∈ π := by
  intro π hhead hlast hchain
  cases π with
  | nil => simp at hhead
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp [hhead] at hlast
    | cons b tl =>
      have ha : a = 4 := by simpa using hhead
      subst ha
      have hb : b ∈ par5 4 := (List.isChain_cons_cons.mp hchain).1
      have hb123 : b = 1 ∨ b = 2 ∨ b = 3 := by simpa [par5] using hb
      exact ⟨b, by simpa using hb123, by simp⟩

/-- Three-parent cut in the abstract parent-relation form. -/
example : ∑ c ∈ ({1, 2, 3} : Finset (Fin 5)), vis5 4 c = 1 :=
  Admixture.sum_visit_eq_one_of_isAntichain_of_separates 0 par5 pr5 vis5 wf5
    sum_prop5 visit_eq5 _ _ antichain5 separates5

/-- The same three-parent cut in expanded form: `1 / 2 + 1 / 3 + 1 / 6 = 1`. -/
example : vis5 4 1 + vis5 4 2 + vis5 4 3 = 1 := by
  norm_num [vis5]

end MathlibExtTest.Biology.PopulationGenetics.Admixture.GeneralGraph
