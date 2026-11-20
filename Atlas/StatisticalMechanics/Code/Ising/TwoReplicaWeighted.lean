/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Ising.TwoReplica
import Code.Sharpness.TwoReplica

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














theorem weight_reflect_split_eq (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (P : Finset (Sym2 V))
    {K : Current V} (hK : ∀ e, K e ≤ m e) :
    Sharpness.weight G β J (reflect m P K)
        * Sharpness.weight G β J (fun e => m e - reflect m P K e)
      = Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e) := by
  have hcompl_K : (fun e => K e + (m e - K e)) = m := by
    funext e; exact Nat.add_sub_cancel' (hK e)
  have hRle := reflect_le m P hK
  have hcompl_R : (fun e => reflect m P K e + (m e - reflect m P K e)) = m := by
    funext e; exact Nat.add_sub_cancel' (hRle e)
  rw [Sharpness.weight_mul_eq G β J (reflect m P K) (fun e => m e - reflect m P K e),
      Sharpness.weight_mul_eq G β J K (fun e => m e - K e), hcompl_R, hcompl_K]
  congr 1
  refine Finset.prod_congr rfl (fun e _ => ?_)
  congr 1
  have hr : reflect m P K e + (m e - reflect m P K e) = m e := Nat.add_sub_cancel' (hRle e)
  have hk : K e + (m e - K e) = m e := Nat.add_sub_cancel' (hK e)
  rw [hr, hk]
  unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; rw [Nat.choose_symm (hK e)]
  · simp only [if_neg h]





noncomputable def reflectEquiv (m : Current V) (P : Finset (Sym2 V)) :
    {K : Current V // ∀ e, K e ≤ m e} ≃ {K : Current V // ∀ e, K e ≤ m e} where
  toFun K := ⟨reflect m P K.1, reflect_le m P K.2⟩
  invFun K := ⟨reflect m P K.1, reflect_le m P K.2⟩
  left_inv K := Subtype.ext (reflect_involutive m P K.2)
  right_inv K := Subtype.ext (reflect_involutive m P K.2)








noncomputable def splitWeightedSum (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (F : ℝ)
    (A : Finset V) : ℝ :=
  ∑ K : {K : Current V // ∀ e, K e ≤ m e},
    (if Sharpness.sources G K.1 = A
      then F * (Sharpness.weight G β J K.1 * Sharpness.weight G β J (fun e => m e - K.1 e))
      else 0)















theorem ising_switching_weighted (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges G.edgeFinset m) u v)
    (F : ℝ) (A : Finset V) :
    splitWeightedSum G β J m F (A ∆ {u, v}) = splitWeightedSum G β J m F A := by
  
  obtain ⟨P, hPodd, hPsrc⟩ := exists_conn_set (oddEdges G.edgeFinset m) hconn huv
  have hPE : P ⊆ G.edgeFinset := hPodd.trans (oddEdges_subset G.edgeFinset m)
  have hPoddE : ∀ e ∈ P, Odd (m e) := by
    intro e he
    have := hPodd he; rw [oddEdges, Finset.mem_filter] at this; exact this.2
  
  unfold splitWeightedSum
  rw [← hPsrc]
  refine (Fintype.sum_equiv (reflectEquiv m P) _ _ ?_).symm
  intro K
  simp only [reflectEquiv, Equiv.coe_fn_mk]
  
  have hsrc : Sharpness.sources G (reflect m P K.1) = Sharpness.sources G K.1 ∆ srcP P :=
    sources_reflect (V := V) G.edgeFinset m P K.1 K.2 hPE hPoddE
  rw [hsrc]
  have hw := weight_reflect_split_eq G β J m P K.2
  by_cases hA : Sharpness.sources G K.1 = A
  · rw [hA]; simp only; rw [hw]
  · 
    have hne : Sharpness.sources G K.1 ∆ srcP P ≠ A ∆ srcP P := by
      intro h
      exact hA (by
        have := congrArg (· ∆ srcP P) h
        simpa [symmDiff_symmDiff_cancel_right] using this)
    rw [if_neg hne, if_neg hA]














theorem ising_switching_weighted_vanishing (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {u v : V} (huv : u ≠ v) (hconn : ¬ connP (posEdges G.edgeFinset m) u v) (F : ℝ) :
    splitWeightedSum G β J m F (A ∆ {u, v}) = 0 := by
  unfold splitWeightedSum
  refine Finset.sum_eq_zero (fun K _ => ?_)
  by_cases hKsrc : Sharpness.sources G K.1 = A ∆ {u, v}
  · 
    exfalso
    apply hconn
    
    set L : Current V := fun e => m e - K.1 e with hLdef
    have hLle : ∀ e, L e ≤ m e := fun e => Nat.sub_le _ _
    have hsplit : m = fun e => K.1 e + L e := by
      funext e; exact (Nat.add_sub_cancel' (K.2 e)).symm
    have hadd : Sharpness.sources G m
        = Sharpness.sources G K.1 ∆ Sharpness.sources G L := by
      conv_lhs => rw [hsplit]
      exact sources_add G.edgeFinset K.1 L
    rw [hm, hKsrc] at hadd
    have hLsrc : Sharpness.sources G L = {u, v} := by
      have key : ∀ X Y Z : Finset V, X = Y ∆ Z → Z = Y ∆ X := by
        intro X Y Z h; rw [h, symmDiff_symmDiff_cancel_left]
      have h1 : Sharpness.sources G L = (A ∆ {u, v}) ∆ A := key A (A ∆ {u, v}) _ hadd
      rw [h1, symmDiff_comm A {u, v}, symmDiff_assoc, symmDiff_self, symmDiff_bot]
    
    have hconnOddL : connP (oddEdges G.edgeFinset L) u v :=
      connOdd_of_sources G.edgeFinset L hnd huv hLsrc
    have hconnPosL : connP (posEdges G.edgeFinset L) u v :=
      connOdd_imp_connPos G.edgeFinset L hconnOddL
    refine connP_mono ?_ hconnPosL
    intro e he
    rw [posEdges, Finset.mem_filter] at he ⊢
    exact ⟨he.1, le_trans he.2 (hLle e)⟩
  · rw [if_neg hKsrc]











theorem ising_switching_weighted_sourceless (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) {u v : V} (huv : u ≠ v)
    (hsrc : Sharpness.sources G m = {u, v}) (F : ℝ) :
    splitWeightedSum G β J m F {u, v} = splitWeightedSum G β J m F ∅ := by
  have hconn : connP (oddEdges G.edgeFinset m) u v :=
    connOdd_of_sources G.edgeFinset m hnd huv hsrc
  have h := ising_switching_weighted G β J m huv hconn F ∅
  rwa [show (∅ : Finset V) ∆ {u, v} = {u, v} from symmDiff_eq_right.mpr rfl] at h
















theorem ising_two_point_switching (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (F : ℝ)
    (A : Finset V) :
    splitWeightedSum G β J m F A
      = F * Sharpness.weight G β J m
        * ∑ K : {K : Current V // ∀ e, K e ≤ m e},
            (if Sharpness.sources G K.1 = A
              then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) := by
  unfold splitWeightedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  by_cases hA : Sharpness.sources G K.1 = A
  · simp only [if_pos hA]
    
    have hcompl : (fun e => K.1 e + (m e - K.1 e)) = m := by
      funext e; exact Nat.add_sub_cancel' (K.2 e)
    rw [Sharpness.weight_mul_eq G β J K.1 (fun e => m e - K.1 e), hcompl]
    have hbin : (∏ e ∈ G.edgeFinset, ((K.1 e + (m e - K.1 e)).choose (K.1 e) : ℝ))
        = ∏ e ∈ G.edgeFinset, ((m e).choose (K.1 e) : ℝ) := by
      refine Finset.prod_congr rfl (fun e _ => ?_)
      rw [Nat.add_sub_cancel' (K.2 e)]
    rw [hbin]; ring
  · simp only [if_neg hA, mul_zero]

end Ising

end StatMech
