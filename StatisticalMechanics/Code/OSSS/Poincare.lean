/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Code.Inequalities.OSSS

open scoped BigOperators
open Finset

set_option linter.style.longLine false

namespace StatMech
namespace OSSS
namespace Poincare

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]










def fullTree (φ : ConfigSpace E → Bool) : List E → DecisionTree E
  | [] => .leaf (φ (fun _ => false))
  | (e :: l) =>
      .node e (fullTree (fun ω => φ (setOpen e ω)) l)
              (fullTree (fun ω => φ (setClosed e ω)) l)



def InsensOutside (φ : ConfigSpace E → Bool) (l : List E) : Prop :=
  ∀ ω ω', (∀ e ∈ l, ω e = ω' e) → φ ω = φ ω'

omit [Fintype E] in


lemma eval_fullTree (φ : ConfigSpace E → Bool) (l : List E)
    (h : InsensOutside φ l) (ω : ConfigSpace E) :
    (fullTree φ l).eval ω = φ ω := by
  induction l generalizing φ with
  | nil =>
      simp only [fullTree, DecisionTree.eval]
      exact h (fun _ => false) ω (by intro e he; simp at he)
  | cons e l ih =>
      simp only [fullTree, DecisionTree.eval]
      by_cases he : ω e = true
      · rw [if_pos he]
        have hins : InsensOutside (fun ω => φ (setOpen e ω)) l := by
          intro a b hab
          apply h
          intro x hx
          rcases List.mem_cons.1 hx with h1 | h1
          · subst h1; simp [setOpen]
          · by_cases hxe : x = e
            · subst hxe; simp [setOpen]
            · rw [setOpen_of_ne hxe, setOpen_of_ne hxe]; exact hab x h1
        rw [ih _ hins]
        congr 1
        funext x
        by_cases hxe : x = e
        · subst hxe; simp [setOpen, he]
        · rw [setOpen_of_ne hxe]
      · rw [if_neg he]
        have he' : ω e = false := by cases ho : ω e; rfl; exact absurd ho he
        have hins : InsensOutside (fun ω => φ (setClosed e ω)) l := by
          intro a b hab
          apply h
          intro x hx
          rcases List.mem_cons.1 hx with h1 | h1
          · subst h1; simp [setClosed]
          · by_cases hxe : x = e
            · subst hxe; simp [setClosed]
            · rw [setClosed_of_ne hxe, setClosed_of_ne hxe]; exact hab x h1
        rw [ih _ hins]
        congr 1
        funext x
        by_cases hxe : x = e
        · subst hxe; simp [setClosed, he']
        · rw [setClosed_of_ne hxe]

omit [Fintype E] in


lemma mem_queried_fullTree (e : E) (φ : ConfigSpace E → Bool) (l : List E)
    (he : e ∈ l) (ω : ConfigSpace E) :
    e ∈ (fullTree φ l).queried ω := by
  induction l generalizing φ ω with
  | nil => exact absurd he (by simp)
  | cons a l ih =>
      simp only [fullTree, DecisionTree.queried]
      rcases List.mem_cons.1 he with h1 | h1
      · subst h1; exact Finset.mem_insert_self e _
      · apply Finset.mem_insert_of_mem
        by_cases hae : ω a = true
        · rw [if_pos hae]; exact ih (fun ω => φ (setOpen a ω)) h1 ω
        · rw [if_neg hae]; exact ih (fun ω => φ (setClosed a ω)) h1 ω







noncomputable def fullTreeUniv (φ : ConfigSpace E → Bool) : DecisionTree E :=
  fullTree φ (Finset.univ.toList)



lemma eval_fullTreeUniv (φ : ConfigSpace E → Bool) (ω : ConfigSpace E) :
    (fullTreeUniv φ).eval ω = φ ω := by
  apply eval_fullTree
  intro a b hab
  congr 1
  funext e
  exact hab e (by simp)


lemma evalR_fullTreeUniv (φ : ConfigSpace E → Bool) (ω : ConfigSpace E) :
    (fullTreeUniv φ).evalR ω = if φ ω then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  rw [eval_fullTreeUniv]


lemma mem_queried_fullTreeUniv (e : E) (φ : ConfigSpace E → Bool) (ω : ConfigSpace E) :
    e ∈ (fullTreeUniv φ).queried ω :=
  mem_queried_fullTree e φ _ (by simp) ω




lemma reveal_fullTreeUniv {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (φ : ConfigSpace E → Bool) (e : E) :
    reveal ν (fullTreeUniv φ) e = 1 := by
  unfold reveal
  have hone : (fun ω => if e ∈ (fullTreeUniv φ).queried ω then (1 : ℝ) else 0)
      = (fun _ => (1 : ℝ)) := by
    funext ω
    rw [if_pos (mem_queried_fullTreeUniv e φ ω)]
  rw [hone, expect_one hν]














theorem poincare {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (φ : ConfigSpace E → Bool) :
    var ν (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ ∑ e, infl ν (fun ω => if φ ω then (1 : ℝ) else 0) e := by
  
  have hfun : (fun ω => if φ ω then (1 : ℝ) else 0) = (fullTreeUniv φ).evalR := by
    funext ω; rw [evalR_fullTreeUniv]
  rw [hfun]
  
  refine (osss_var hν (fullTreeUniv φ)).trans ?_
  
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro e _
  rw [reveal_fullTreeUniv hν φ e, one_mul]










theorem poincare_cov {ν : E → Bool → ℝ} (hν : IsProbWeight ν) (φ : ConfigSpace E → Bool)
    (g : ConfigSpace E → ℝ) :
    cov ν (fun ω => if φ ω then (1 : ℝ) else 0) g ≤ ∑ e, infl ν g e := by
  have hfun : (fun ω => if φ ω then (1 : ℝ) else 0) = (fullTreeUniv φ).evalR := by
    funext ω; rw [evalR_fullTreeUniv]
  rw [hfun]
  refine (osss hν (fullTreeUniv φ) g).trans ?_
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro e _
  rw [reveal_fullTreeUniv hν φ e, one_mul]





theorem poincare_bernoulli {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (φ : ConfigSpace E → Bool) :
    var (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ ∑ e, infl (bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e :=
  poincare (bernoulliWeight_isProbWeight hp0 hp1) φ

end Poincare
end OSSS
end StatMech
