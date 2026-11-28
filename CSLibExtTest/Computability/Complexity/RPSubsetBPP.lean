/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.RPSubsetBPP
import CSLibExt.Computability.Complexity.BoolClosure

open Cslib.Complexity.Classes MetaMathlibExt.ComplexityTheory
open MetaMathlibExt.Complexity.KeyTheorems.RPSubsetBPP

-- This verifier accepts exactly one of the two coin strings when the input starts with true.
example : (fun x : List Bool => x.headD false) ∈ BPP := by
  apply rp_subset_bpp
  refine ⟨1, _, isPolyTime_heads (fun coin first => first && coin), fun x => ?_⟩
  rw [Polynomial.eval_one]
  have h : {r : Fin 1 → Bool | r 0 = true} = {fun _ => true} := by
    ext r
    change (r 0 = true) ↔ r = fun _ => true
    constructor
    · intro hr
      funext i
      rwa [Subsingleton.elim i 0]
    · rintro rfl
      rfl
  constructor
  · intro hx
    simp only [List.headD_eq_head?_getD] at hx
    simp [List.ofFn_succ, hx, h]
  · intro hx
    simp only [List.headD_eq_head?_getD] at hx
    simp [List.ofFn_succ, hx]

-- There is one possible empty coin string, even after doubling the coin budget.
example : (fun _ : List Bool => true) ∈ BPP := by
  apply rp_subset_bpp
  refine ⟨0, _, isPolyTime_heads (fun _ _ => true), fun x => ?_⟩
  simp
