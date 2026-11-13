/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Mathlib
import Code.Ising.GKS2

open scoped BigOperators symmDiff
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatMech

namespace IsingFK

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]







noncomputable def energyObs (h : ℝ) (s : ConfigSpace V) : ℝ :=
  (∑ e ∈ G.edgeFinset, bond s e) + h * ∑ x, spin s x





lemma weight_hasDerivAt (h β₀ : ℝ) (s : ConfigSpace V) :
    HasDerivAt (fun β => isingWeight G β h s)
      (energyObs G h s * isingWeight G β₀ h s) β₀ := by
  unfold isingWeight energyObs
  have hH : -hamiltonian G h s = (∑ e ∈ G.edgeFinset, bond s e) + h * ∑ x, spin s x := by
    unfold hamiltonian; ring
  set U := (∑ e ∈ G.edgeFinset, bond s e) + h * ∑ x, spin s x with hU
  have hcoe : (fun β : ℝ => Real.exp (-β * hamiltonian G h s))
      = (fun β : ℝ => Real.exp (β * U)) := by
    funext β; rw [← hH]; ring_nf
  rw [hcoe]
  have h1 : HasDerivAt (fun β : ℝ => β * U) U β₀ := by
    simpa using (hasDerivAt_id β₀).mul_const U
  have h2 := (Real.hasDerivAt_exp (β₀ * U)).comp β₀ h1
  have hfun : (Real.exp ∘ fun β : ℝ => β * U) = (fun β : ℝ => Real.exp (β * U)) := rfl
  rw [hfun] at h2
  have hval : U * Real.exp (-β₀ * hamiltonian G h s) = Real.exp (β₀ * U) * U := by
    rw [← hH]; ring_nf
  rw [hval]; exact h2





lemma num_hasDerivAt (h β₀ : ℝ) (A : Finset V) :
    HasDerivAt (fun β => ∑ s, spinProd A s * isingWeight G β h s)
      (∑ s, spinProd A s * (energyObs G h s * isingWeight G β₀ h s)) β₀ := by
  have hp : ∀ s : ConfigSpace V,
      HasDerivAt (fun β => spinProd A s * isingWeight G β h s)
        (spinProd A s * (energyObs G h s * isingWeight G β₀ h s)) β₀ :=
    fun s => (weight_hasDerivAt G h β₀ s).const_mul (spinProd A s)
  have hsum := HasDerivAt.sum (fun s (_ : s ∈ (Finset.univ : Finset (ConfigSpace V))) => hp s)
  have heq : (∑ s, fun β => spinProd A s * isingWeight G β h s)
      = (fun β => ∑ s, spinProd A s * isingWeight G β h s) := by
    funext β; rw [Finset.sum_apply]
  rwa [heq] at hsum




lemma den_hasDerivAt (h β₀ : ℝ) :
    HasDerivAt (fun β => isingZ G β h)
      (∑ s, energyObs G h s * isingWeight G β₀ h s) β₀ := by
  have hp : ∀ s : ConfigSpace V,
      HasDerivAt (fun β => isingWeight G β h s)
        (energyObs G h s * isingWeight G β₀ h s) β₀ :=
    fun s => weight_hasDerivAt G h β₀ s
  have hsum := HasDerivAt.sum (fun s (_ : s ∈ (Finset.univ : Finset (ConfigSpace V))) => hp s)
  have heq : (∑ s, fun β => isingWeight G β h s) = (fun β => isingZ G β h) := by
    funext β; rw [Finset.sum_apply]; rfl
  rwa [heq] at hsum










lemma covar_spinProd_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A B : Finset V) :
    0 ≤ (∑ s, (spinProd A s * spinProd B s) * isingWeight G β h s) * isingZ G β h
        - (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, spinProd B s * isingWeight G β h s) := by
  rw [sub_nonneg]
  have key := unnorm_gks2 G β h hβ hh A B
  have hABe : (∑ s, spinProd (A ∆ B) s * isingWeight G β h s)
      = ∑ s, (spinProd A s * spinProd B s) * isingWeight G β h s :=
    Finset.sum_congr rfl (fun s _ => by rw [spinProd_mul_self])
  rw [hABe] at key
  have hZ : (∑ s, isingWeight G β h s) = isingZ G β h := rfl
  rw [hZ] at key
  linarith









lemma covarTerm_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V)
    (g : ConfigSpace V → ℝ) (B : Finset V) (hgB : ∀ s, g s = spinProd B s) :
    0 ≤ (∑ s, (spinProd A s * g s) * isingWeight G β h s) * isingZ G β h
        - (∑ s, spinProd A s * isingWeight G β h s) * (∑ s, g s * isingWeight G β h s) := by
  have h1 : (∑ s, (spinProd A s * g s) * isingWeight G β h s)
      = (∑ s, (spinProd A s * spinProd B s) * isingWeight G β h s) :=
    Finset.sum_congr rfl (fun s _ => by rw [hgB s])
  have h2 : (∑ s, g s * isingWeight G β h s) = (∑ s, spinProd B s * isingWeight G β h s) :=
    Finset.sum_congr rfl (fun s _ => by rw [hgB s])
  rw [h1, h2]
  exact covar_spinProd_nonneg G β h hβ hh A B



lemma exists_spinProd_eq_bond (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    ∃ B : Finset V, ∀ s : ConfigSpace V, bond s e = spinProd B s := by
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    have hab : a ≠ b := G.ne_of_adj he
    exact ⟨{a, b}, fun s => by rw [bond_mk]; unfold spinProd; rw [Finset.prod_pair hab]⟩


lemma spin_eq_spinProd_singleton (x : V) (s : ConfigSpace V) :
    spin s x = spinProd {x} s := by
  unfold spinProd; rw [Finset.prod_singleton]








lemma num_deriv_decomp (β h : ℝ) (A : Finset V) :
    (∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s))
      = (∑ e ∈ G.edgeFinset, ∑ s, (spinProd A s * bond s e) * isingWeight G β h s)
        + h * ∑ x, ∑ s, (spinProd A s * spin s x) * isingWeight G β h s := by
  have inner : ∀ s : ConfigSpace V,
      spinProd A s * (energyObs G h s * isingWeight G β h s)
        = (∑ e ∈ G.edgeFinset, (spinProd A s * bond s e) * isingWeight G β h s)
          + h * ∑ x, (spinProd A s * spin s x) * isingWeight G β h s := by
    intro s
    unfold energyObs
    have e1 : spinProd A s * (∑ e ∈ G.edgeFinset, bond s e) * isingWeight G β h s
        = (∑ e ∈ G.edgeFinset, (spinProd A s * bond s e) * isingWeight G β h s) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    have e2 : spinProd A s * (h * ∑ x, spin s x) * isingWeight G β h s
        = h * ∑ x, (spinProd A s * spin s x) * isingWeight G β h s := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [← e1, ← e2]; ring
  rw [Finset.sum_congr rfl (fun s _ => inner s)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
  · rw [← Finset.mul_sum, Finset.sum_comm]












lemma deriv_numerator_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    0 ≤ (∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s)) * isingZ G β h
        - (∑ s, spinProd A s * isingWeight G β h s)
            * (∑ s, energyObs G h s * isingWeight G β h s) := by
  
  set Z := isingZ G β h with hZdef
  set Na := ∑ s, spinProd A s * isingWeight G β h s with hNa
  
  set P : Sym2 V → ℝ := fun e => ∑ s, (spinProd A s * bond s e) * isingWeight G β h s with hP
  set Q : V → ℝ := fun x => ∑ s, (spinProd A s * spin s x) * isingWeight G β h s with hQ
  set R : Sym2 V → ℝ := fun e => ∑ s, bond s e * isingWeight G β h s with hR
  set S : V → ℝ := fun x => ∑ s, spin s x * isingWeight G β h s with hS
  
  have hNum : (∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s))
      = (∑ e ∈ G.edgeFinset, P e) + h * ∑ x, Q x := num_deriv_decomp G β h A
  have hDen : (∑ s, energyObs G h s * isingWeight G β h s)
      = (∑ e ∈ G.edgeFinset, R e) + h * ∑ x, S x := by
    have := num_deriv_decomp G β h (∅ : Finset V)
    simp only [spinProd_empty, one_mul] at this
    rw [hR, hS]; exact this
  rw [hNum, hDen]
  
  have hrearr :
      ((∑ e ∈ G.edgeFinset, P e) + h * ∑ x, Q x) * Z
        - Na * ((∑ e ∈ G.edgeFinset, R e) + h * ∑ x, S x)
      = (∑ e ∈ G.edgeFinset, (P e * Z - Na * R e))
        + h * ∑ x, (Q x * Z - Na * S x) := by
    have hE : (∑ e ∈ G.edgeFinset, (P e * Z - Na * R e))
        = (∑ e ∈ G.edgeFinset, P e) * Z - Na * (∑ e ∈ G.edgeFinset, R e) := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    have hW : (∑ x, (Q x * Z - Na * S x))
        = (∑ x, Q x) * Z - Na * (∑ x, S x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [hE, hW]; ring
  rw [hrearr]
  apply add_nonneg
  · 
    apply Finset.sum_nonneg
    intro e he
    obtain ⟨B, hB⟩ := exists_spinProd_eq_bond G e he
    have := covarTerm_nonneg G β h hβ hh A (fun s => bond s e) B hB
    simpa only [hP, hR] using this
  · 
    apply mul_nonneg hh
    apply Finset.sum_nonneg
    intro x _
    have := covarTerm_nonneg G β h hβ hh A (fun s => spin s x) {x}
      (fun s => spin_eq_spinProd_singleton x s)
    simpa only [hQ, hS] using this








lemma corr_hasDerivAt (h β₀ : ℝ) (A : Finset V) :
    HasDerivAt (fun β => isingExpectation G β h (spinProd A))
      (((∑ s, spinProd A s * (energyObs G h s * isingWeight G β₀ h s)) * isingZ G β₀ h
          - (∑ s, spinProd A s * isingWeight G β₀ h s)
              * (∑ s, energyObs G h s * isingWeight G β₀ h s))
        / (isingZ G β₀ h) ^ 2) β₀ := by
  have hfun : (fun β => isingExpectation G β h (spinProd A))
      = (fun β => (∑ s, spinProd A s * isingWeight G β h s) / isingZ G β h) := by
    funext β; rw [isingExpectation_spinProd_eq]
  rw [hfun]
  exact (num_hasDerivAt G h β₀ A).div (den_hasDerivAt G h β₀) (isingZ_ne_zero G β₀ h)







lemma corr_deriv_nonneg (h β : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    0 ≤ ((∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s)) * isingZ G β h
          - (∑ s, spinProd A s * isingWeight G β h s)
              * (∑ s, energyObs G h s * isingWeight G β h s))
        / (isingZ G β h) ^ 2 := by
  apply div_nonneg (deriv_numerator_nonneg G β h hβ hh A)
  positivity











theorem corr_monotone (h : ℝ) (hh : 0 ≤ h) (A : Finset V) :
    MonotoneOn (fun β => isingExpectation G β h (spinProd A)) (Set.Ici (0 : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun β =>
        ((∑ s, spinProd A s * (energyObs G h s * isingWeight G β h s)) * isingZ G β h
            - (∑ s, spinProd A s * isingWeight G β h s)
                * (∑ s, energyObs G h s * isingWeight G β h s))
          / (isingZ G β h) ^ 2)
  · 
    exact fun β _ => (corr_hasDerivAt G h β A).continuousAt.continuousWithinAt
  · 
    intro β hβ
    exact (corr_hasDerivAt G h β A).hasDerivWithinAt
  · 
    intro β hβ
    rw [interior_Ici, Set.mem_Ioi] at hβ
    exact corr_deriv_nonneg G h β hβ.le hh A






theorem twoPoint_monotone (h : ℝ) (hh : 0 ≤ h) (x y : V) :
    MonotoneOn (fun β => isingExpectation G β h (spinProd {x, y})) (Set.Ici (0 : ℝ)) :=
  corr_monotone G h hh {x, y}




theorem magnetization_monotone (h : ℝ) (hh : 0 ≤ h) (x : V) :
    MonotoneOn (fun β => isingExpectation G β h (spinProd {x})) (Set.Ici (0 : ℝ)) :=
  corr_monotone G h hh {x}

end IsingFK

end StatMech
