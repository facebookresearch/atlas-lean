/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Walls.gc_binomsplit

open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]














theorem gc3_tripleWeight_aux (β : ℝ) (J : Sym2 V → ℝ) (n₁ n₂ n₃ : Current V) :
    weight G β J n₁ * weight G β J n₂ * weight G β J n₃
      = (∏ e ∈ G.edgeFinset,
          ((Nat.choose (n₁ e + n₂ e + n₃ e) (n₁ e) : ℝ)
            * (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ)))
        * weight G β J (fun e => n₁ e + n₂ e + n₃ e) := by
  
  have hinner := gc_binomSplit_two G β J n₂ n₃
  
  
  have houter := gc_binomSplit_two G β J n₁ (fun e => n₂ e + n₃ e)
  
  have hsup : (fun e => n₁ e + (n₂ e + n₃ e)) = (fun e => n₁ e + n₂ e + n₃ e) := by
    funext e; omega
  
  have hmerge : (∏ e ∈ G.edgeFinset,
        ((Nat.choose (n₁ e + n₂ e + n₃ e) (n₁ e) : ℝ) * (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ)))
      = (∏ e ∈ G.edgeFinset, (Nat.choose (n₁ e + (n₂ e + n₃ e)) (n₁ e) : ℝ))
        * (∏ e ∈ G.edgeFinset, (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    have he : n₁ e + n₂ e + n₃ e = n₁ e + (n₂ e + n₃ e) := by omega
    rw [he]
  
  rw [mul_assoc, hinner, ← mul_assoc,
    show weight G β J n₁ * (weight G β J (fun e => n₂ e + n₃ e))
        * (∏ e ∈ G.edgeFinset, (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ))
      = (weight G β J n₁ * weight G β J (fun e => n₂ e + n₃ e))
        * (∏ e ∈ G.edgeFinset, (Nat.choose (n₂ e + n₃ e) (n₂ e) : ℝ)) from by ring,
    houter, hsup, hmerge]
  ring


















theorem gc3_tripleWeight (β : ℝ) (J : Sym2 V → ℝ) (n₁ n₂ n₃ : Current V)
    (m : Current V) (hm : m = fun e => n₁ e + n₂ e + n₃ e) :
    weight G β J n₁ * weight G β J n₂ * weight G β J n₃
      = (∏ e ∈ G.edgeFinset,
          ((Nat.choose (m e) (n₁ e) : ℝ)
            * (Nat.choose (m e - n₁ e) (n₂ e) : ℝ)))
        * weight G β J m := by
  subst hm
  rw [gc3_tripleWeight_aux G β J n₁ n₂ n₃]
  
  
  refine congrArg (fun t => t * weight G β J (fun e => n₁ e + n₂ e + n₃ e)) ?_
  refine Finset.prod_congr rfl (fun e _ => ?_)
  have hsub : n₁ e + n₂ e + n₃ e - n₁ e = n₂ e + n₃ e := by omega
  rw [hsub]

end StatMech.Walls
