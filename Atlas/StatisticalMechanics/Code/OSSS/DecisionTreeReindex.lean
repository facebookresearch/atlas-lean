/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Inequalities.OSSS

namespace StatMech
namespace OSSS

open DecisionTree

variable {I E : Type*}


def restrictConfig (iota : I -> E) (omega : ConfigSpace E) : ConfigSpace I :=
  fun i => omega (iota i)

namespace DecisionTree


def reindex (iota : I -> E) : DecisionTree I -> DecisionTree E
  | .leaf b => .leaf b
  | .node i t f => .node (iota i) (reindex iota t) (reindex iota f)

@[simp] theorem eval_reindex (iota : I -> E) (T : DecisionTree I)
    (omega : ConfigSpace E) :
    (T.reindex iota).eval omega = T.eval (restrictConfig iota omega) := by
  induction T with
  | leaf b => rfl
  | node i t f iht ihf =>
      simp only [reindex, eval, restrictConfig]
      split <;> simp_all

@[simp] theorem evalR_reindex (iota : I -> E) (T : DecisionTree I)
    (omega : ConfigSpace E) :
    (T.reindex iota).evalR omega = T.evalR (restrictConfig iota omega) := by
  simp only [evalR, eval_reindex]

variable [DecidableEq I] [DecidableEq E]



theorem queried_reindex (iota : I -> E) (T : DecisionTree I)
    (omega : ConfigSpace E) :
    (T.reindex iota).queried omega =
      (T.queried (restrictConfig iota omega)).image iota := by
  induction T with
  | leaf b => simp [reindex, queried]
  | node i t f iht ihf =>
      simp only [reindex, queried, restrictConfig]
      by_cases h : omega (iota i)
      · rw [if_pos h, if_pos h, iht]
        simp
      · rw [if_neg h, if_neg h, ihf]
        simp



theorem mem_queried_reindex_iff (iota : I -> E) (hiota : Function.Injective iota)
    (T : DecisionTree I) (omega : ConfigSpace E) (i : I) :
    iota i ∈ (T.reindex iota).queried omega ↔
      i ∈ T.queried (restrictConfig iota omega) := by
  rw [queried_reindex]
  simp [hiota.eq_iff]


theorem not_mem_queried_reindex_of_not_range (iota : I -> E)
    (T : DecisionTree I) (omega : ConfigSpace E) (e : E)
    (he : e ∉ Set.range iota) :
    e ∉ (T.reindex iota).queried omega := by
  rw [queried_reindex]
  intro h
  rw [Finset.mem_image] at h
  obtain ⟨i, _, rfl⟩ := h
  exact he ⟨i, rfl⟩

end DecisionTree
end OSSS
end StatMech
