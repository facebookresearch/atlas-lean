/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Mathlib
import Code.Ising.GKS

open scoped BigOperators symmDiff
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]



omit [Fintype V] in



lemma spinProd_mul_self (A B : Finset V) (s : ConfigSpace V) :
    spinProd A s * spinProd B s = spinProd (A ∆ B) s := by
  classical
  unfold spinProd
  have h1 : (∏ x ∈ A, spin s x) * (∏ x ∈ B, spin s x)
      = (∏ x ∈ A ∪ B, spin s x) * (∏ x ∈ A ∩ B, spin s x) :=
    (Finset.prod_union_inter).symm
  have hdisj : Disjoint (A ∆ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    rw [Finset.mem_symmDiff] at hx
    rw [Finset.mem_inter] at hx2
    rcases hx with ⟨_, hb⟩ | ⟨_, ha⟩
    · exact hb hx2.2
    · exact ha hx2.1
  have hunion : A ∪ B = (A ∆ B) ∪ (A ∩ B) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]
    tauto
  have h2 : (∏ x ∈ A ∪ B, spin s x) = (∏ x ∈ A ∆ B, spin s x) * (∏ x ∈ A ∩ B, spin s x) := by
    rw [hunion, Finset.prod_union hdisj]
  rw [h1, h2, mul_assoc, ← Finset.prod_mul_distrib]
  have : (∏ x ∈ A ∩ B, spin s x * spin s x) = 1 :=
    Finset.prod_eq_one (fun x _ => spin_sq s x)
  rw [this, mul_one]






def xnor (σ q : ConfigSpace V) : ConfigSpace V := fun y => σ y == q y

omit [Fintype V] [DecidableEq V] in

lemma spin_xnor (σ q : ConfigSpace V) (x : V) :
    spin (xnor σ q) x = spin σ x * spin q x := by
  unfold spin xnor
  by_cases h1 : σ x <;> by_cases h2 : q x <;> simp [h1, h2]

omit [Fintype V] [DecidableEq V] in

lemma bond_xnor (σ q : ConfigSpace V) (e : Sym2 V) :
    bond (xnor σ q) e = bond σ e * bond q e := by
  induction e with
  | h a b => rw [bond_mk, bond_mk, bond_mk, spin_xnor, spin_xnor]; ring

omit [Fintype V] in


lemma spinProd_xnor (B : Finset V) (σ q : ConfigSpace V) :
    spinProd B (xnor σ q) = spinProd B σ * spinProd B q := by
  unfold spinProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun x _ => spin_xnor σ q x)


def dblFun (p : ConfigSpace V × ConfigSpace V) : ConfigSpace V × ConfigSpace V :=
  (p.1, xnor p.1 p.2)

omit [Fintype V] in


lemma dblFun_invol : Function.Involutive (dblFun (V := V)) := by
  intro p
  obtain ⟨σ, q⟩ := p
  ext x
  · rfl
  · simp only [dblFun, xnor]; cases σ x <;> cases q x <;> rfl


def dblEquiv : (ConfigSpace V × ConfigSpace V) ≃ (ConfigSpace V × ConfigSpace V) where
  toFun := dblFun
  invFun := dblFun
  left_inv := dblFun_invol
  right_inv := dblFun_invol



lemma sum_dbl_reindex (F : ConfigSpace V × ConfigSpace V → ℝ) :
    ∑ p : ConfigSpace V × ConfigSpace V, F p
      = ∑ p : ConfigSpace V × ConfigSpace V, F (p.1, xnor p.1 p.2) := by
  rw [← Equiv.sum_comp dblEquiv F]; rfl



omit [Fintype V] [DecidableEq V] in

lemma one_add_bond_nonneg (q : ConfigSpace V) (e : Sym2 V) : 0 ≤ 1 + bond q e := by
  rcases bond_eq_pm q e with h | h <;> rw [h] <;> norm_num

omit [Fintype V] [DecidableEq V] in

lemma one_add_spin_nonneg (q : ConfigSpace V) (x : V) : 0 ≤ 1 + spin q x := by
  rcases spin_eq_pm q x with h | h <;> rw [h] <;> norm_num

omit [Fintype V] in

lemma one_sub_spinProd_nonneg (B : Finset V) (q : ConfigSpace V) :
    0 ≤ 1 - spinProd B q := by
  classical
  have : spinProd B q = 1 ∨ spinProd B q = -1 := by
    unfold spinProd
    induction B using Finset.induction with
    | empty => simp
    | @insert a s ha IH =>
      rw [Finset.prod_insert ha]
      rcases IH with h | h <;> rcases spin_eq_pm q a with h2 | h2 <;>
        rw [h, h2] <;> [left; right; right; left] <;> ring
  rcases this with h | h <;> rw [h] <;> norm_num



variable (G : SimpleGraph V) [DecidableRel G.Adj]











lemma inner_sum_nonneg
    (ce de : Sym2 V → ℝ) (cx dx : V → ℝ)
    (hce : ∀ e, 0 ≤ ce e) (hde : ∀ e, 0 ≤ de e)
    (hcx : ∀ x, 0 ≤ cx x) (hdx : ∀ x, 0 ≤ dx x)
    (obs : ConfigSpace V → ℝ) (hobs : IsSpinMonomial obs) :
    0 ≤ ∑ s : ConfigSpace V,
        obs s * ((∏ e ∈ G.edgeFinset, (ce e + bond s e * de e))
          * (∏ x : V, (cx x + spin s x * dx x))) := by
  classical
  set C : Sym2 V ⊕ V → ℝ := Sum.elim ce cx with hC
  set D : Sym2 V ⊕ V → ℝ := Sum.elim de dx with hD
  set fac : (Sym2 V ⊕ V) → ConfigSpace V → ℝ :=
    Sum.elim (fun e s => bond s e) (fun x s => spin s x) with hfac
  set I : Finset (Sym2 V ⊕ V) :=
    G.edgeFinset.map ⟨Sum.inl, Sum.inl_injective⟩
      ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ with hI
  have hint : ∀ s : ConfigSpace V,
      obs s * ((∏ e ∈ G.edgeFinset, (ce e + bond s e * de e))
          * (∏ x : V, (cx x + spin s x * dx x)))
        = obs s * ∏ i ∈ I, (C i + D i * fac i s) := by
    intro s
    congr 1
    have hdisj : Disjoint (G.edgeFinset.map ⟨Sum.inl, Sum.inl_injective⟩)
        ((Finset.univ : Finset V).map ⟨Sum.inr, Sum.inr_injective⟩) := by
      rw [Finset.disjoint_left]
      intro i hi hj
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi hj
      obtain ⟨a, _, rfl⟩ := hi
      obtain ⟨b, _, hb⟩ := hj
      exact Sum.inl_ne_inr hb.symm
    rw [hI, Finset.prod_union hdisj, Finset.prod_map, Finset.prod_map]
    simp only [hC, hD, hfac, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · exact Finset.prod_congr rfl (fun e _ => by ring)
    · exact Finset.prod_congr rfl (fun x _ => by ring)
  simp_rw [hint]
  apply gks_kernel I C D
  · intro i _; rcases i with e | x
    · exact hce e
    · exact hcx x
  · intro i _; rcases i with e | x
    · exact hde e
    · exact hdx x
  · intro i _; rcases i with e | x
    · exact isSpinMonomial_bond e
    · exact isSpinMonomial_spin x
  · exact hobs



omit [DecidableEq V] in








lemma doubled_weight_factor (β h : ℝ) (σ q : ConfigSpace V) :
    isingWeight G β h σ * isingWeight G β h (xnor σ q)
      = (∏ e ∈ G.edgeFinset,
          (Real.cosh (β * (1 + bond q e)) + bond σ e * Real.sinh (β * (1 + bond q e))))
        * (∏ x : V,
          (Real.cosh (β * h * (1 + spin q x)) + spin σ x * Real.sinh (β * h * (1 + spin q x)))) := by
  rw [isingWeight, isingWeight, ← Real.exp_add, hamiltonian, hamiltonian]
  have hexp :
      -β * (-(∑ e ∈ G.edgeFinset, bond σ e) - h * ∑ x, spin σ x)
      + -β * (-(∑ e ∈ G.edgeFinset, bond (xnor σ q) e)
              - h * ∑ x, spin (xnor σ q) x)
      = (∑ e ∈ G.edgeFinset, (β * (1 + bond q e)) * bond σ e)
        + (∑ x, (β * h * (1 + spin q x)) * spin σ x) := by
    simp_rw [bond_xnor, spin_xnor]
    have eEdge : (∑ e ∈ G.edgeFinset, (β * (1 + bond q e)) * bond σ e)
        = β * (∑ e ∈ G.edgeFinset, bond σ e) + β * (∑ e ∈ G.edgeFinset, bond σ e * bond q e) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun e _ => by ring)
    have eVert : (∑ x, (β * h * (1 + spin q x)) * spin σ x)
        = (β * h) * (∑ x, spin σ x) + (β * h) * (∑ x, spin σ x * spin q x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [eEdge, eVert]; ring
  rw [hexp, Real.exp_add, Real.exp_sum, Real.exp_sum]
  congr 1
  · exact Finset.prod_congr rfl (fun e _ =>
      exp_mul_pm (β * (1 + bond q e)) (bond σ e) (bond_eq_pm σ e))
  · exact Finset.prod_congr rfl (fun x _ =>
      exp_mul_pm (β * h * (1 + spin q x)) (spin σ x) (spin_eq_pm σ x))









lemma inner_q_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A B : Finset V) (q : ConfigSpace V) :
    0 ≤ ∑ σ : ConfigSpace V,
      (spinProd (A ∆ B) σ * isingWeight G β h σ * isingWeight G β h (xnor σ q)
        - spinProd A σ * isingWeight G β h σ
            * (spinProd B (xnor σ q) * isingWeight G β h (xnor σ q))) := by
  have key : ∀ σ : ConfigSpace V,
      (spinProd (A ∆ B) σ * isingWeight G β h σ * isingWeight G β h (xnor σ q)
        - spinProd A σ * isingWeight G β h σ
            * (spinProd B (xnor σ q) * isingWeight G β h (xnor σ q)))
      = (1 - spinProd B q) *
          ((spinProd A σ * spinProd B σ) *
            ((∏ e ∈ G.edgeFinset,
                (Real.cosh (β * (1 + bond q e)) + bond σ e * Real.sinh (β * (1 + bond q e))))
              * (∏ x : V,
                (Real.cosh (β * h * (1 + spin q x))
                  + spin σ x * Real.sinh (β * h * (1 + spin q x)))))) := by
    intro σ
    rw [← doubled_weight_factor G β h σ q, spinProd_xnor, ← spinProd_mul_self]
    ring
  rw [Finset.sum_congr rfl (fun σ _ => key σ), ← Finset.mul_sum]
  apply mul_nonneg (one_sub_spinProd_nonneg B q)
  exact inner_sum_nonneg G
    (fun e => Real.cosh (β * (1 + bond q e)))
    (fun e => Real.sinh (β * (1 + bond q e)))
    (fun x => Real.cosh (β * h * (1 + spin q x)))
    (fun x => Real.sinh (β * h * (1 + spin q x)))
    (fun e => (Real.cosh_pos _).le)
    (fun e => Real.sinh_nonneg_iff.mpr (mul_nonneg hβ (one_add_bond_nonneg q e)))
    (fun x => (Real.cosh_pos _).le)
    (fun x => Real.sinh_nonneg_iff.mpr (mul_nonneg (mul_nonneg hβ hh) (one_add_spin_nonneg q x)))
    (fun s => spinProd A s * spinProd B s)
    ((isSpinMonomial_spinProd A).mul (isSpinMonomial_spinProd B))











lemma unnorm_gks2 (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A B : Finset V) :
    (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, spinProd B s * isingWeight G β h s)
      ≤ (∑ s, spinProd (A ∆ B) s * isingWeight G β h s) * (∑ s, isingWeight G β h s) := by
  rw [← sub_nonneg]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← Finset.sum_sub_distrib]
  rw [sum_dbl_reindex (fun p =>
      spinProd (A ∆ B) p.1 * isingWeight G β h p.1 * isingWeight G β h p.2
        - spinProd A p.1 * isingWeight G β h p.1 * (spinProd B p.2 * isingWeight G β h p.2))]
  rw [Fintype.sum_prod_type_right]
  exact Finset.sum_nonneg (fun q _ => inner_q_nonneg G β h hβ hh A B q)




lemma isingExpectation_spinProd_eq (β h : ℝ) (A : Finset V) :
    isingExpectation G β h (spinProd A)
      = (∑ s : ConfigSpace V, spinProd A s * isingWeight G β h s) / isingZ G β h := by
  unfold isingExpectation isingProb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [div_mul_eq_mul_div, mul_comm (spinProd A s)]










theorem gks_second (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A B : Finset V) :
    isingExpectation G β h (spinProd A) * isingExpectation G β h (spinProd B)
      ≤ isingExpectation G β h (spinProd (A ∆ B)) := by
  rw [isingExpectation_spinProd_eq, isingExpectation_spinProd_eq, isingExpectation_spinProd_eq]
  have hZ : 0 < isingZ G β h := isingZ_pos G β h
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hZ]
  have hsum : (∑ s, isingWeight G β h s) = isingZ G β h := rfl
  calc (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, spinProd B s * isingWeight G β h s)
          * isingZ G β h
      ≤ ((∑ s, spinProd (A ∆ B) s * isingWeight G β h s) * (∑ s, isingWeight G β h s))
          * isingZ G β h :=
        mul_le_mul_of_nonneg_right (unnorm_gks2 G β h hβ hh A B) hZ.le
    _ = (∑ s, spinProd (A ∆ B) s * isingWeight G β h s) * (isingZ G β h * isingZ G β h) := by
        rw [hsum]; ring

end Ising

end StatMech
