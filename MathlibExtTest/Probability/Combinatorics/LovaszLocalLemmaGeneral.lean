/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Combinatorics.LovaszLocalLemmaGeneral
import Mathlib.Tactic.NormNum

open MathlibExt.Probability.Combinatorics.LovaszLocalLemmaGeneralWanted

attribute [local instance] Classical.propDecidable

-- With no bad events, the product lower bound is one on any finite probability space.
example {Ω : Type*} [Fintype Ω] (pmf : Ω → ℝ) (hn : ∀ ω, 0 ≤ pmf ω)
    (hs : ∑ ω, pmf ω = 1) (A : Empty → Set Ω) :
    1 ≤ ∑ ω, if ∀ i, ω ∉ A i then pmf ω else 0 := by
  simpa only [Finset.prod_empty, Finset.univ_eq_empty] using
    lovasz_local_lemma_general_finite pmf hn hs A ⊥ (fun i ↦ i.elim)
      (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)

-- The two coordinates are independent bad events of probabilities 1/2 and 1/3.
-- Their joint avoidance probability attains the product bound 1/3.
example : (1 / 3 : ℝ) ≤ ∑ ω : Bool × Bool,
    if ω.1 = false ∧ ω.2 = false then (if ω.2 then 1 / 6 else 1 / 3) else 0 := by
  classical
  let pmf (ω : Bool × Bool) : ℝ := if ω.2 then 1 / 6 else 1 / 3
  let A (i : Bool) : Set (Bool × Bool) := {ω | (if i then ω.2 else ω.1) = true}
  let x (i : Bool) : ℝ := if i then 1 / 3 else 1 / 2
  have h := lovasz_local_lemma_general_finite pmf (by
      intro ω
      dsimp [pmf]
      split <;> norm_num) (by norm_num [pmf, Fintype.sum_prod_type, Fintype.sum_bool])
    A ⊥ (by
      intro i S hS
      have hi : i ∉ S := fun h ↦ hS i h (Set.mem_insert i _)
      cases i with
      | false =>
        by_cases h : true ∈ S <;>
          norm_num [A, pmf, Fintype.sum_prod_type, Fintype.sum_bool, Bool.forall_bool, hi, h]
      | true =>
        by_cases h : false ∈ S <;>
          norm_num [A, pmf, Fintype.sum_prod_type, Fintype.sum_bool, Bool.forall_bool, hi, h])
    x (by intro i; cases i <;> norm_num [x]) (by intro i; cases i <;> norm_num [x]) (by
      intro i
      cases i <;> norm_num [pmf, A, x, Fintype.sum_prod_type, Fintype.sum_bool])
  norm_num [x, A, pmf, Fintype.prod_bool, Bool.forall_bool] at h
  exact h
