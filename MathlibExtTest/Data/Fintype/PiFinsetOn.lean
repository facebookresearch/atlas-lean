/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Data.Fintype.PiFinsetOn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

open Finset

-- An infinite value type still gives a finite set of two padded tuples.
example : (Fintype.piFinsetOn (fun i : Fin 2 => i = 0)
    (fun _ => ({10, 20} : Finset ℕ)) 9).card = 2 := by
  rw [Fintype.card_piFinsetOn]
  rw [Finset.prod_filter, Fin.prod_univ_two]
  norm_num

example : (fun i : Fin 2 => if i = 0 then 10 else 9) ∈
    Fintype.piFinsetOn (fun i => i = 0) (fun _ => ({10, 20} : Finset ℕ)) 9 := by
  simp [Fintype.mem_piFinsetOn]

-- An inactive coordinate cannot contain a value different from the default.
example : (fun _ : Fin 2 => 10) ∉
    Fintype.piFinsetOn (fun i => i = 0) (fun _ => ({10, 20} : Finset ℕ)) 9 := by
  simp [Fintype.mem_piFinsetOn, Fin.forall_fin_two]

-- No active coordinates gives one tuple, even when every allowed set is empty.
example : (Fintype.piFinsetOn (fun _ : Fin 2 => False)
    (fun _ => (∅ : Finset ℕ)) 9).card = 1 := by
  simp [Fintype.card_piFinsetOn]

-- An empty index type also has exactly one tuple.
example : (Fintype.piFinsetOn (fun _ : Fin 0 => True)
    (fun _ => (∅ : Finset ℕ)) 9).card = 1 := by
  simp [Fintype.card_piFinsetOn]

-- An active coordinate with no allowed value gives no tuple.
example : (Fintype.piFinsetOn (fun _ : Fin 1 => True)
    (fun _ => (∅ : Finset ℕ)) 9).card = 0 := by
  simp [Fintype.card_piFinsetOn]

-- Signed weights and ignored inactive coordinates exercise the generalized sum/product law.
example : ∑ t ∈ Fintype.piFinsetOn (fun i : Fin 2 => i = 0)
    (fun _ => ({10, 20} : Finset ℕ)) 9,
    ∏ i with i = 0, (-(t i : ℤ)) = -30 := by
  rw [Fintype.sum_piFinsetOn_prod
    (P := fun i : Fin 2 => i = 0)
    (T := fun _ => ({10, 20} : Finset ℕ))
    (d := 9)
    (H := fun _ x => -(x : ℤ))]
  rw [Finset.prod_filter, Fin.prod_univ_two]
  norm_num

example {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (P : ι → Prop) [DecidablePred P] (T : ι → Finset σ) (d : σ) (f g : ι → σ → R) :
    ∏ i with P i, ∑ x ∈ T i, f i x * g i x =
      ∑ t ∈ Fintype.piFinsetOn P T d,
        (∏ i with P i, f i (t i)) * ∏ i with P i, g i (t i) :=
  Fintype.prod_sum_eq_sum_piFinsetOn_mul P T d f g

example {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] (T : ι → Finset σ) (d : σ)
    (t : ι → σ) (ht : ∀ i, P i → t i ∈ T i) :
    ∃! b : ι → σ, b ∈ Fintype.piFinsetOn P T d ∧ ∀ i, P i → b i = t i :=
  Fintype.existsUnique_piFinsetOn P T d t ht

#print axioms Fintype.piFinsetOn
#print axioms Fintype.sum_piFinsetOn_prod
#print axioms Fintype.prod_sum_eq_sum_piFinsetOn_mul
#print axioms Fintype.existsUnique_piFinsetOn
