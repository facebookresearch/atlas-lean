/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Sharpness.RandomCurrent

open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness















theorem gc_binomSplit_scalar (X : ℝ) (a b : ℕ) :
    X ^ a / (Nat.factorial a) * (X ^ b / (Nat.factorial b))
      = X ^ (a + b) / (Nat.factorial (a + b)) * (Nat.choose (a + b) a : ℝ) := by
  
  have hnat : (a + b).choose a * (Nat.factorial a * Nat.factorial b) = Nat.factorial (a + b) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [Nat.add_comm b a] at h
    rw [← h]; ring
  have hfac : ((a + b).choose a : ℝ) * (Nat.factorial a * Nat.factorial b)
      = (Nat.factorial (a + b) : ℝ) := by exact_mod_cast hnat
  have haf : (Nat.factorial a : ℝ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hbf : (Nat.factorial b : ℝ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have habf : (Nat.factorial (a + b) : ℝ) ≠ 0 := by exact_mod_cast (a + b).factorial_ne_zero
  rw [pow_add]
  field_simp
  rw [← hfac]
  ring



variable {V : Type*}










theorem gc_binomSplit_edge (β : ℝ) (J : Sym2 V → ℝ) (m n : Current V) (e : Sym2 V)
    (hn : n e ≤ m e) :
    (β * J e) ^ (n e) / (Nat.factorial (n e))
        * ((β * J e) ^ (m e - n e) / (Nat.factorial (m e - n e)))
      = (β * J e) ^ (m e) / (Nat.factorial (m e)) * (Nat.choose (m e) (n e) : ℝ) := by
  have hsum : n e + (m e - n e) = m e := Nat.add_sub_cancel' hn
  have h := gc_binomSplit_scalar (β * J e) (n e) (m e - n e)
  rw [hsum] at h
  exact h



variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]












theorem gc_binomSplit (β : ℝ) (J : Sym2 V → ℝ) (m n : Current V) (hn : n ≤ m) :
    weight G β J n * weight G β J (fun e => m e - n e)
      = weight G β J m * (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (n e) : ℝ)) := by
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  exact gc_binomSplit_edge β J m n e (hn e)












theorem gc_binomSplit_two (β : ℝ) (J : Sym2 V → ℝ) (n₁ n₂ : Current V) :
    weight G β J n₁ * weight G β J n₂
      = weight G β J (fun e => n₁ e + n₂ e)
        * (∏ e ∈ G.edgeFinset, (Nat.choose (n₁ e + n₂ e) (n₁ e) : ℝ)) := by
  have hn : n₁ ≤ (fun e => n₁ e + n₂ e) := fun e => Nat.le_add_right _ _
  have h := gc_binomSplit G β J (fun e => n₁ e + n₂ e) n₁ hn
  
  have hcompl : (fun e => (n₁ e + n₂ e) - n₁ e) = n₂ := by
    funext e; exact Nat.add_sub_cancel_left _ _
  rw [hcompl] at h
  exact h

end StatMech.Walls
