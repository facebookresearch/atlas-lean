/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Sharpness.TwoReplica
import Code.Sharpness.MultiReplica

open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]










noncomputable def gc3_sourceTripleSum (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) : ℝ :=
  sourceTripleSum G β J A B C

theorem gc3_sourceTripleSum_def (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    gc3_sourceTripleSum G β J A B C
      = ∑' z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G z.1) = A then weight G β J (ofEdgeFun G z.1) else 0)
          * (if sources G (ofEdgeFun G z.2.1) = B then weight G β J (ofEdgeFun G z.2.1) else 0)
          * (if sources G (ofEdgeFun G z.2.2) = C then weight G β J (ofEdgeFun G z.2.2) else 0) :=
  rfl






theorem gc3_sourceTripleSum_eq_mul (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    gc3_sourceTripleSum G β J A B C
      = currentSum G β J A * currentSum G β J B * currentSum G β J C :=
  sourceTripleSum_eq_mul G β J A B C






















theorem gc3_tripleConv (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    gc3_sourceTripleSum G β J A B C
      = ∑' m : ↥G.edgeFinset → ℕ,
          ∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
            (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0)
            * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0)
            * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C
                  then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) :=
  sourceTripleSum_eq_superposition G β J A B C












theorem gc3_tripleConv_superposition_source (m K₁ K₂ : ↥G.edgeFinset → ℕ)
    (hK : ∀ e, K₁ e + K₂ e ≤ m e) {A B C : Finset V}
    (hA : sources G (ofEdgeFun G K₁) = A) (hB : sources G (ofEdgeFun G K₂) = B)
    (hC : sources G (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) = C) :
    sources G (ofEdgeFun G m) = A ∆ B ∆ C :=
  sourceTripleSum_superposition_source G m K₁ K₂ hK hA hB hC











theorem gc3_tripleConv_weight_split (β : ℝ) (J : Sym2 V → ℝ)
    (m K₁ K₂ : ↥G.edgeFinset → ℕ) (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
    weight G β J (ofEdgeFun G K₁) * weight G β J (ofEdgeFun G K₂)
        * weight G β J (ofEdgeFun G (fun e => m e - K₁ e - K₂ e))
      = (∏ e ∈ G.edgeFinset,
          ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K₁) e) : ℝ)
            * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K₁) e) ((ofEdgeFun G K₂) e) : ℝ)))
        * weight G β J (ofEdgeFun G m) :=
  weight_split₃_eq_binom G β J m K₁ K₂ hK

















theorem gc3_tripleConv_pinned (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V) :
    gc3_sourceTripleSum G β J A B C
      = ∑' m : ↥G.edgeFinset → ℕ,
          (if sources G (ofEdgeFun G m) = A ∆ B ∆ C then (1 : ℝ) else 0)
          * ∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
            (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0)
            * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0)
            * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C
                  then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0) := by
  rw [gc3_tripleConv G β J A B C]
  refine tsum_congr (fun m => ?_)
  by_cases hm : sources G (ofEdgeFun G m) = A ∆ B ∆ C
  · rw [if_pos hm, one_mul]
  · 
    rw [if_neg hm, zero_mul]
    refine Finset.sum_eq_zero (fun K _ => ?_)
    
    by_cases hA : sources G (ofEdgeFun G K.1.1) = A
    · by_cases hB : sources G (ofEdgeFun G K.1.2) = B
      · by_cases hC : sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C
        · exact absurd
            (gc3_tripleConv_superposition_source G m K.1.1 K.1.2 K.2 hA hB hC) hm
        · rw [if_neg hC, mul_zero]
      · rw [if_neg hB, mul_zero, zero_mul]
    · rw [if_neg hA, zero_mul, zero_mul]

end StatMech.Walls
