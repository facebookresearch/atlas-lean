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

end MathlibExtTest.Biology.PopulationGenetics.Admixture.GeneralGraph
