/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.GeneNetworks.Aracne
public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# ARACNE tests

The chain of three genes `0 - 1 - 2` (`pathGraph 3`) with mutual informations `I 0 1 = I 1 2 = 2`
and `I 0 2 = 1`, threshold `I₀ = 0`:

* ARACNE keeps the direct edges `0 - 1` and `1 - 2` and removes the indirect edge `0 - 2`.
* The hypotheses of `aracne_eq_of_isTree` hold for this chain (non-vacuity witness), so ARACNE
  returns the chain.
* Boundary: with equal values `I 0 2 = I 0 1 = I 1 2` (the data-processing inequality holds with
  equality), ARACNE keeps the indirect edge, so the strict inequality in `aracne_le_of_isTree`
  cannot be relaxed.
-/

namespace Cslib.Bioinformatics.GeneNetworks.Aracne

open SimpleGraph

/-- Mutual informations on the chain `0 - 1 - 2`: `1` for the indirect pair, `2` otherwise. -/
noncomputable def chainMI (a b : Fin 3) : ℝ := if a.val + b.val = 2 ∧ a ≠ b then 1 else 2

theorem chainMI_symm (a b : Fin 3) : chainMI a b = chainMI b a := by
  simp only [chainMI, add_comm a.val, ne_comm]

example : (aracne chainMI chainMI_symm 0).Adj 0 1 := by
  refine ⟨by decide, by norm_num [chainMI], fun j hj0 hj1 _ _ ↦ ?_⟩
  fin_cases j <;> simp_all [chainMI]

example : ¬ (aracne chainMI chainMI_symm 0).Adj 0 2 := by
  rintro ⟨-, -, h⟩
  have := h 1 (by decide) (by decide) (by norm_num [chainMI]) (by norm_num [chainMI])
  norm_num [chainMI] at this

/-- The chain satisfies the hypotheses of `aracne_eq_of_isTree`, so ARACNE recovers it. -/
example : aracne chainMI chainMI_symm 0 = pathGraph 3 := by
  refine aracne_eq_of_isTree _ (isTree_pathGraph_add_one 2) _ _ _
    (fun i k _ ↦ by unfold chainMI; split_ifs <;> norm_num) ?_
  intro a b c hca hcb hsep
  by_cases hab : a = b
  · subst hab
    have := hsep Walk.nil
    simp_all
  by_cases hadj : (pathGraph 3).Adj a b
  · have := hsep (Walk.cons hadj Walk.nil)
    simp_all
  rw [pathGraph_adj] at hadj
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all [chainMI]

/-- With equal values the indirect edge survives: the data-processing inequality must be strict
for exact recovery. -/
example : (aracne (fun _ _ ↦ (1 : ℝ)) (fun _ _ ↦ rfl) 0).Adj (0 : Fin 3) 2 :=
  ⟨by decide, by norm_num, fun _ _ _ _ _ ↦ by simp⟩

end Cslib.Bioinformatics.GeneNetworks.Aracne
