/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Mathlib
import Code.Ising.KWSelfDuality

open scoped BigOperators
open Finset

namespace StatMech.Walls

open StatMech.Ising








section HighTemp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] in

lemma bond_eq_one_or_neg_one (s : ConfigSpace V) (e : Sym2 V) :
    bond s e = 1 ∨ bond s e = -1 := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]





theorem exp_mul_eq_cosh_mul (β b : ℝ) (hb : b = 1 ∨ b = -1) :
    Real.exp (β * b) = Real.cosh β * (1 + Real.tanh β * b) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rcases hb with h | h
  · subst h
    rw [mul_one]; field_simp; rw [← Real.cosh_add_sinh]
  · subst h
    rw [show β * (-1) = -β by ring, Real.exp_neg]
    field_simp
    rw [show Real.cosh β + -Real.sinh β = Real.cosh β - Real.sinh β by ring,
      Real.cosh_sub_sinh, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

omit [DecidableEq V] in


theorem isingWeight_field_free_eq_prod (β : ℝ) (s : ConfigSpace V) :
    isingWeight G β 0 s = ∏ e ∈ G.edgeFinset, Real.exp (β * bond s e) := by
  unfold isingWeight hamiltonian
  simp only [zero_mul, sub_zero]
  rw [show -β * -(∑ e ∈ G.edgeFinset, bond s e)
        = β * (∑ e ∈ G.edgeFinset, bond s e) by ring,
    Finset.mul_sum, Real.exp_sum]

omit [DecidableEq V] in


theorem prod_exp_bond_eq (β : ℝ) (s : ConfigSpace V) :
    (∏ e ∈ G.edgeFinset, Real.exp (β * bond s e))
      = (Real.cosh β) ^ G.edgeFinset.card
        * ∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e) := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  rw [exp_mul_eq_cosh_mul β (bond s e) (bond_eq_one_or_neg_one s e)]











theorem prod_bond_eq_prod_pow_incCount (s : ConfigSpace V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∏ e ∈ F, bond s e) = ∏ v : V, (spin s v) ^ (incCount F v) := by
  induction F using Finset.induction with
  | empty => simp [incCount]
  | insert e F he ih =>
    rw [Finset.prod_insert he, ih (fun e' he' => hF e' (Finset.mem_insert_of_mem he'))]
    simp_rw [incCount_insert e F he, pow_add]
    rw [Finset.prod_mul_distrib, mul_comm]
    congr 1
    have hd : ¬ e.IsDiag := hF e (Finset.mem_insert_self e F)
    induction e using Sym2.ind with
    | _ x y =>
      rw [Sym2.mk_isDiag_iff] at hd
      rw [bond_mk]
      have hcvt : ∀ v : V, (spin s v) ^ (if v ∈ (s(x, y) : Sym2 V) then 1 else 0)
          = if v ∈ ({x, y} : Finset V) then spin s v else 1 := by
        intro v
        simp only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        by_cases h : v = x ∨ v = y <;> simp [h]
      simp_rw [hcvt]
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pair hd]

omit [Fintype V] [DecidableEq V] in


lemma spin_pow (s : ConfigSpace V) (v : V) (n : ℕ) :
    (spin s v) ^ n = if Even n then 1 else spin s v := by
  have hsq : (spin s v) ^ 2 = 1 := by rw [sq]; exact spin_sq s v
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos he]
    obtain ⟨k, rfl⟩ := he
    rw [show k + k = 2 * k by ring, pow_mul, hsq, one_pow]
  · rw [if_neg (by simp [Nat.not_even_iff_odd, ho])]
    obtain ⟨k, rfl⟩ := ho
    rw [pow_add, pow_mul, hsq, one_pow, one_mul, pow_one]




theorem sum_prod_spin_set (S : Finset V) :
    (∑ s : ConfigSpace V, ∏ v ∈ S, spin s v)
      = if S = ∅ then (2 : ℝ) ^ Fintype.card V else 0 := by
  have key :
      (∑ s : ConfigSpace V, ∏ v : V,
        (fun v b => if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1) v (s v))
        = ∏ v : V, ∑ b : Bool,
            (if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1) :=
    (Fintype.prod_sum
      (fun v b => if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1)).symm
  have h1 : ∀ s : ConfigSpace V, (∏ v ∈ S, spin s v)
      = ∏ v : V,
          (fun v b => if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1) v (s v) := by
    intro s
    rw [Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  simp_rw [h1]
  rw [key]
  have hfac : ∀ v : V, (∑ b : Bool, if v ∈ S then (if b = true then (1 : ℝ) else -1) else 1)
      = if v ∈ S then 0 else 2 := by
    intro v; by_cases hv : v ∈ S <;> simp [hv]
  simp_rw [hfac]
  by_cases hS : S = ∅
  · subst hS; simp
  · rw [if_neg hS]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [if_pos hv])




theorem sum_prod_bond_subgraph (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    (∑ s : ConfigSpace V, ∏ e ∈ F, bond s e)
      = if IsEvenSubgraph F then (2 : ℝ) ^ Fintype.card V else 0 := by
  have hstep : ∀ s : ConfigSpace V,
      (∏ e ∈ F, bond s e)
        = ∏ v ∈ Finset.univ.filter (fun v => ¬ Even (incCount F v)), spin s v := by
    intro s
    rw [prod_bond_eq_prod_pow_incCount s F hF]
    simp_rw [spin_pow s]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v _
    by_cases h : Even (incCount F v) <;> simp [h]
  simp_rw [hstep]
  rw [sum_prod_spin_set]
  by_cases hev : IsEvenSubgraph F
  · rw [if_pos hev, if_pos]
    rw [Finset.filter_eq_empty_iff]
    intro v _
    simpa using hev v
  · rw [if_neg hev, if_neg]
    rw [IsEvenSubgraph, not_forall] at hev
    obtain ⟨v, hv⟩ := hev
    exact Finset.ne_empty_of_mem (a := v) (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)










theorem isingZ_high_temp (β : ℝ) :
    isingZ G β 0
      = (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card
        * ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
            (Real.tanh β) ^ F.card := by
  unfold isingZ
  
  have hweight : ∀ s : ConfigSpace V,
      isingWeight G β 0 s
        = (Real.cosh β) ^ G.edgeFinset.card
          * ∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e) := by
    intro s
    rw [isingWeight_field_free_eq_prod, prod_exp_bond_eq]
  simp_rw [hweight]
  
  have hexpand : ∀ s : ConfigSpace V,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh β * bond s e))
        = ∑ F ∈ G.edgeFinset.powerset,
            ∏ e ∈ F, (Real.tanh β * bond s e) := by
    intro s; exact Finset.prod_one_add _
  simp_rw [hexpand]
  
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ G.edgeFinset.card
        * ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh β) ^ F.card
      = (Real.cosh β) ^ G.edgeFinset.card
        * ((2 : ℝ) ^ Fintype.card V
            * ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh β) ^ F.card) by ring]
  congr 1
  
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mem_powerset] at hF
  
  have hpull : ∀ s : ConfigSpace V,
      (∏ e ∈ F, (Real.tanh β * bond s e))
        = (Real.tanh β) ^ F.card * ∏ e ∈ F, bond s e := by
    intro s
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  rw [← Finset.mul_sum]
  have hnd : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact SimpleGraph.not_isDiag_of_mem_edgeSet G
      (by rw [← SimpleGraph.mem_edgeFinset]; exact hF he)
  rw [sum_prod_bond_subgraph F hnd]
  by_cases hev : IsEvenSubgraph F
  · rw [if_pos hev, if_pos hev]; ring
  · rw [if_neg hev, if_neg hev]; ring

end HighTemp

end StatMech.Walls
