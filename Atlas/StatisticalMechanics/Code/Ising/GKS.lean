/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.Ising.Gibbs

open scoped BigOperators
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]





def spinB (b : Bool) : ℝ := if b then 1 else -1

omit [Fintype V] [DecidableEq V] in
lemma spin_eq_spinB (s : ConfigSpace V) (x : V) : spin s x = spinB (s x) := rfl



def monomial (m : V → ℕ) (s : ConfigSpace V) : ℝ := ∏ x : V, (spin s x) ^ (m x)

omit [DecidableEq V] in
@[simp] lemma monomial_zero (s : ConfigSpace V) : monomial (0 : V → ℕ) s = 1 := by
  unfold monomial; simp

omit [DecidableEq V] in

lemma monomial_add (m₁ m₂ : V → ℕ) (s : ConfigSpace V) :
    monomial (m₁ + m₂) s = monomial m₁ s * monomial m₂ s := by
  unfold monomial
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun x _ => by rw [Pi.add_apply, pow_add])




lemma sum_monomial_nonneg (m : V → ℕ) : 0 ≤ ∑ s : ConfigSpace V, monomial m s := by
  have key : (∑ s : ConfigSpace V, monomial m s)
      = ∏ x : V, ∑ b : Bool, (spinB b) ^ (m x) := by
    unfold monomial
    simp_rw [spin_eq_spinB]
    rw [← Fintype.prod_sum (fun x b => (spinB b) ^ (m x))]
  rw [key]
  apply Finset.prod_nonneg
  intro x _
  rw [Fintype.sum_bool]
  show 0 ≤ (spinB true) ^ (m x) + (spinB false) ^ (m x)
  simp only [spinB]
  norm_num
  rcases Nat.even_or_odd (m x) with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num




def IsSpinMonomial (f : ConfigSpace V → ℝ) : Prop :=
  ∃ m : V → ℕ, ∀ s, f s = monomial m s

omit [DecidableEq V] in
lemma IsSpinMonomial.const_one : IsSpinMonomial (fun _ : ConfigSpace V => (1 : ℝ)) :=
  ⟨0, fun s => (monomial_zero s).symm⟩

omit [DecidableEq V] in

lemma IsSpinMonomial.mul {f g : ConfigSpace V → ℝ}
    (hf : IsSpinMonomial f) (hg : IsSpinMonomial g) :
    IsSpinMonomial (fun s => f s * g s) := by
  obtain ⟨mf, hmf⟩ := hf
  obtain ⟨mg, hmg⟩ := hg
  refine ⟨mf + mg, fun s => ?_⟩
  simp only [hmf s, hmg s, monomial_add]


lemma IsSpinMonomial.sum_nonneg {f : ConfigSpace V → ℝ} (hf : IsSpinMonomial f) :
    0 ≤ ∑ s : ConfigSpace V, f s := by
  obtain ⟨m, hm⟩ := hf
  simp_rw [hm]
  exact sum_monomial_nonneg m


lemma isSpinMonomial_spin (x : V) : IsSpinMonomial (fun s => spin s x) := by
  refine ⟨Pi.single x 1, fun s => ?_⟩
  unfold monomial
  rw [Finset.prod_eq_single x]
  · simp
  · intro y _ hy; rw [Pi.single_eq_of_ne hy]; simp
  · intro h; simp at h


lemma isSpinMonomial_bond (e : Sym2 V) : IsSpinMonomial (fun s => bond s e) := by
  induction e with
  | h a b =>
    have : (fun s : ConfigSpace V => bond s s(a, b))
        = (fun s => (fun s => spin s a) s * (fun s => spin s b) s) := by
      funext s; rw [bond_mk]
    rw [this]
    exact (isSpinMonomial_spin a).mul (isSpinMonomial_spin b)













lemma gks_kernel {ι : Type*} (I : Finset ι) (c d : ι → ℝ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hd : ∀ i ∈ I, 0 ≤ d i)
    (fac : ι → ConfigSpace V → ℝ) (hfac : ∀ i ∈ I, IsSpinMonomial (fac i))
    (obs : ConfigSpace V → ℝ) (hobs : IsSpinMonomial obs) :
    0 ≤ ∑ s : ConfigSpace V, obs s * ∏ i ∈ I, (c i + d i * fac i s) := by
  classical
  induction I using Finset.induction generalizing obs with
  | empty =>
    simp only [Finset.prod_empty, mul_one]
    exact hobs.sum_nonneg
  | @insert a I ha IH =>
    have hca : 0 ≤ c a := hc a (Finset.mem_insert_self a I)
    have hda : 0 ≤ d a := hd a (Finset.mem_insert_self a I)
    have hc' : ∀ i ∈ I, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ I, 0 ≤ d i := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hfac' : ∀ i ∈ I, IsSpinMonomial (fac i) :=
      fun i hi => hfac i (Finset.mem_insert_of_mem hi)
    have hfaca : IsSpinMonomial (fac a) := hfac a (Finset.mem_insert_self a I)
    have expand : ∀ s : ConfigSpace V,
        obs s * ∏ i ∈ insert a I, (c i + d i * fac i s)
        = c a * (obs s * ∏ i ∈ I, (c i + d i * fac i s))
          + d a * ((fun s => obs s * fac a s) s * ∏ i ∈ I, (c i + d i * fac i s)) := by
      intro s; rw [Finset.prod_insert ha]; simp only; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    exact add_nonneg (mul_nonneg hca (IH hc' hd' hfac' obs hobs))
      (mul_nonneg hda (IH hc' hd' hfac' _ (hobs.mul hfaca)))



variable (G : SimpleGraph V) [DecidableRel G.Adj]


def spinProd (A : Finset V) (s : ConfigSpace V) : ℝ := ∏ x ∈ A, spin s x

omit [Fintype V] [DecidableEq V] in
@[simp] lemma spinProd_empty (s : ConfigSpace V) : spinProd (∅ : Finset V) s = 1 := by
  simp [spinProd]

lemma isSpinMonomial_spinProd (A : Finset V) : IsSpinMonomial (spinProd A) := by
  classical
  refine ⟨fun x => if x ∈ A then 1 else 0, fun s => ?_⟩
  unfold spinProd monomial
  rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ A)
      (fun x => (spin s x) ^ (if x ∈ A then 1 else 0))]
  have h1 : (∏ x ∈ univ.filter (· ∈ A), (spin s x) ^ (if x ∈ A then 1 else 0))
      = ∏ x ∈ A, spin s x := by
    rw [Finset.filter_mem_eq_inter, univ_inter]
    exact Finset.prod_congr rfl (fun x hx => by rw [if_pos hx, pow_one])
  have h2 : (∏ x ∈ univ.filter (¬ · ∈ A), (spin s x) ^ (if x ∈ A then 1 else 0)) = 1 :=
    Finset.prod_eq_one (fun x hx => by
      rw [Finset.mem_filter] at hx; rw [if_neg hx.2, pow_zero])
  rw [h1, h2, mul_one]


noncomputable def isingExpectation (β h : ℝ) (f : ConfigSpace V → ℝ) : ℝ :=
  ∑ s : ConfigSpace V, isingProb G β h s * f s

omit [Fintype V] [DecidableEq V] in

lemma bond_eq_pm (s : ConfigSpace V) (e : Sym2 V) : bond s e = 1 ∨ bond s e = -1 := by
  induction e with
  | h x y =>
    rw [bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]

omit [Fintype V] [DecidableEq V] in

lemma spin_eq_pm (s : ConfigSpace V) (x : V) : spin s x = 1 ∨ spin s x = -1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]

omit [DecidableEq V] in

lemma exp_mul_pm (c t : ℝ) (ht : t = 1 ∨ t = -1) :
    Real.exp (c * t) = Real.cosh c + t * Real.sinh c := by
  rw [Real.cosh_eq, Real.sinh_eq]
  rcases ht with h | h <;> subst h
  · ring_nf
  · rw [mul_neg_one]; ring

omit [DecidableEq V] in





lemma isingWeight_factor (β h : ℝ) (s : ConfigSpace V) :
    isingWeight G β h s
      = (∏ e ∈ G.edgeFinset, (Real.cosh β + bond s e * Real.sinh β))
        * (∏ x : V, (Real.cosh (β * h) + spin s x * Real.sinh (β * h))) := by
  unfold isingWeight hamiltonian
  have hexp : -β * (-(∑ e ∈ G.edgeFinset, bond s e) - h * ∑ x, spin s x)
      = (∑ e ∈ G.edgeFinset, β * bond s e) + (∑ x, (β * h) * spin s x) := by
    have e1 : (∑ e ∈ G.edgeFinset, β * bond s e) = β * ∑ e ∈ G.edgeFinset, bond s e := by
      rw [Finset.mul_sum]
    have e2 : (∑ x, (β * h) * spin s x) = (β * h) * ∑ x, spin s x := by rw [Finset.mul_sum]
    rw [e1, e2]; ring
  rw [hexp, Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · exact Finset.prod_congr rfl (fun e _ => exp_mul_pm β (bond s e) (bond_eq_pm s e))
  · exact Finset.prod_congr rfl (fun x _ => exp_mul_pm (β * h) (spin s x) (spin_eq_pm s x))










lemma sum_spinProd_isingWeight_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (A : Finset V) :
    0 ≤ ∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s := by
  classical
  
  set ce : Sym2 V ⊕ V → ℝ := Sum.elim (fun _ => Real.cosh β) (fun _ => Real.cosh (β * h))
  set de : Sym2 V ⊕ V → ℝ := Sum.elim (fun _ => Real.sinh β) (fun _ => Real.sinh (β * h))
  set fac : (Sym2 V ⊕ V) → ConfigSpace V → ℝ :=
    Sum.elim (fun e s => bond s e) (fun x s => spin s x)
  
  set I : Finset (Sym2 V ⊕ V) :=
    G.edgeFinset.map ⟨Sum.inl, Sum.inl_injective⟩
      ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  
  have hint : ∀ s : ConfigSpace V,
      spinProd A s * isingWeight G β h s
        = spinProd A s * ∏ i ∈ I, (ce i + de i * fac i s) := by
    intro s
    rw [isingWeight_factor]
    congr 1
    have hdisj : Disjoint (G.edgeFinset.map ⟨Sum.inl, Sum.inl_injective⟩)
        ((Finset.univ : Finset V).map ⟨Sum.inr, Sum.inr_injective⟩) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi hj
      obtain ⟨a, _, rfl⟩ := hi
      obtain ⟨b, _, hb⟩ := hj
      exact Sum.inl_ne_inr hb.symm
    rw [Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
    simp only [ce, de, fac, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.prod_congr rfl (fun e _ => by ring)
    · exact Finset.prod_congr rfl (fun x _ => by ring)
  simp_rw [hint]
  
  apply gks_kernel I ce de
  · 
    intro i _; rcases i with e | x
    · exact (Real.cosh_pos β).le
    · exact (Real.cosh_pos (β * h)).le
  · 
    intro i _; rcases i with e | x
    · exact Real.sinh_nonneg_iff.mpr hβ
    · exact Real.sinh_nonneg_iff.mpr (mul_nonneg hβ hh)
  · 
    intro i _; rcases i with e | x
    · exact isSpinMonomial_bond e
    · exact isSpinMonomial_spin x
  · 
    exact isSpinMonomial_spinProd A






theorem gks_first (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    0 ≤ isingExpectation G β h (spinProd A) := by
  unfold isingExpectation isingProb
  
  have hrw : ∀ s : ConfigSpace V,
      isingWeight G β h s / isingZ G β h * spinProd A s
        = (isingZ G β h)⁻¹ * (spinProd A s * isingWeight G β h s) := by
    intro s; rw [div_eq_mul_inv]; ring
  simp_rw [hrw]
  rw [← Finset.mul_sum]
  exact mul_nonneg (inv_nonneg.mpr (isingZ_pos G β h).le)
    (sum_spinProd_isingWeight_nonneg G β h hβ hh A)

end Ising

end StatMech
