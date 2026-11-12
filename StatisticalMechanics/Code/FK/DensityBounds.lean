/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.Foundations.ConfigSpace
import Code.FK.RandomCluster
import Code.FK.FiniteEnergy
import Code.Inequalities.Pivotal

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]











noncomputable def edgeMarginalOpen (p q : ℝ) (e : Sym2 V) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = true), fkProb G p q ω











theorem edgeMarginalOpen_eq_closedFiber (p q : ℝ) (e : Sym2 V) :
    edgeMarginalOpen G p q e
      = ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
          fkProb G p q (setOpen e ψ) := by
  unfold edgeMarginalOpen
  apply Finset.sum_nbij' (fun ω => setClosed e ω) (fun ψ => setOpen e ψ)
  · intro ω _; simp [setClosed]
  · intro ψ _; simp [setOpen]
  · intro ω hω
    simp only [Finset.mem_filter] at hω
    funext x; by_cases hx : x = e
    · subst hx; simp [hω.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ψ hψ
    simp only [Finset.mem_filter] at hψ
    funext x; by_cases hx : x = e
    · subst hx; simp [hψ.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]
  · intro ω hω
    simp only [Finset.mem_filter] at hω
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hω.2]
    · simp [setOpen_of_ne hx, setClosed_of_ne hx]






theorem closedFiber_pairMass_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) = 1 := by
  rw [Finset.sum_add_distrib]
  
  rw [← edgeMarginalOpen_eq_closedFiber G p q e]
  
  have hclosed : (∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false),
        fkProb G p q (setClosed e ψ))
      = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = false),
          fkProb G p q ω := by
    apply Finset.sum_congr rfl
    intro ψ hψ
    simp only [Finset.mem_filter] at hψ
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hψ.2]
    · simp [setClosed_of_ne hx]
  rw [hclosed]
  
  unfold edgeMarginalOpen
  rw [show (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = false))
      = Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ¬ ω e = true) from ?_]
  · rw [Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun ω : ConfigSpace (Sym2 V) => ω e = true) (fkProb G p q)]
    exact fkProb_sum_eq_one G hp hp1 hq
  · ext ω; simp









theorem condOpen_setOpen (p q : ℝ) (e : Sym2 V) (ψ : ConfigSpace (Sym2 V)) :
    condOpen G p q e (setOpen e ψ) = condOpen G p q e ψ := by
  unfold condOpen; rw [setOpen_setOpen, setClosed_setOpen]





theorem fkProb_setOpen_eq_condOpen_mul {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) (ψ : ConfigSpace (Sym2 V)) :
    fkProb G p q (setOpen e ψ)
      = condOpen G p q e ψ
          * (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
  unfold condOpen
  have hpos : 0 < fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ) := by
    have h1 := fkProb_pos G hp hp1 hq (setOpen e ψ)
    have h0 := fkProb_pos G hp hp1 hq (setClosed e ψ)
    linarith
  field_simp









theorem condInterval_sandwiches_marginal {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) {lo hi : ℝ}
    (hlo : ∀ ψ : ConfigSpace (Sym2 V), lo ≤ condOpen G p q e ψ)
    (hhi : ∀ ψ : ConfigSpace (Sym2 V), condOpen G p q e ψ ≤ hi) :
    lo ≤ edgeMarginalOpen G p q e ∧ edgeMarginalOpen G p q e ≤ hi := by
  set S := Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false) with hS
  
  have hmass_nonneg : ∀ ψ ∈ S,
      (0 : ℝ) ≤ fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ) := by
    intro ψ _
    have h1 := fkProb_nonneg G hp hp1 hq (setOpen e ψ)
    have h0 := fkProb_nonneg G hp hp1 hq (setClosed e ψ)
    linarith
  
  have hmass_sum : ∑ ψ ∈ S,
      (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) = 1 :=
    closedFiber_pairMass_eq_one G hp hp1 hq e
  
  have hmarg : edgeMarginalOpen G p q e
      = ∑ ψ ∈ S, condOpen G p q e ψ
          * (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
    rw [edgeMarginalOpen_eq_closedFiber G p q e]
    exact Finset.sum_congr rfl
      (fun ψ _ => fkProb_setOpen_eq_condOpen_mul G hp hp1 hq e ψ)
  refine ⟨?_, ?_⟩
  · 
    rw [hmarg]
    calc lo = lo * 1 := (mul_one lo).symm
      _ = ∑ ψ ∈ S, lo * (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
            rw [← Finset.mul_sum, hmass_sum]
      _ ≤ ∑ ψ ∈ S, condOpen G p q e ψ
            * (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
            apply Finset.sum_le_sum
            intro ψ hψ
            exact mul_le_mul_of_nonneg_right (hlo ψ) (hmass_nonneg ψ hψ)
  · 
    rw [hmarg]
    calc ∑ ψ ∈ S, condOpen G p q e ψ
            * (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ))
        ≤ ∑ ψ ∈ S, hi * (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
            apply Finset.sum_le_sum
            intro ψ hψ
            exact mul_le_mul_of_nonneg_right (hhi ψ) (hmass_nonneg ψ hψ)
      _ = hi * 1 := by rw [← Finset.mul_sum, hmass_sum]
      _ = hi := mul_one hi















theorem edge_density_finiteEnergy {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) :
    cFE p q ≤ edgeMarginalOpen G p q e ∧ edgeMarginalOpen G p q e ≤ 1 - cFE p q :=
  condInterval_sandwiches_marginal G hp hp1 (lt_of_lt_of_le one_pos hq) e
    (fun ψ => (finite_energy G hp hp1 hq e ψ).1)
    (fun ψ => (finite_energy G hp hp1 hq e ψ).2)











theorem edge_density_bounds {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    p / (p + q * (1 - p)) ≤ edgeMarginalOpen G p q e ∧ edgeMarginalOpen G p q e ≤ p := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hden : 0 < p + q * (1 - p) := by nlinarith
  
  refine condInterval_sandwiches_marginal G hp hp1 hq0 e (fun ψ => ?_) (fun ψ => ?_)
  · 
    rw [condOpen_eq_weightRatio G hp hp1 hq0]
    set W1 := fkWeight G p q (setOpen e ψ) with hW1
    set W0 := fkWeight G p q (setClosed e ψ) with hW0
    have hW1pos : 0 < W1 := fkWeight_pos G hp hp1 hq0 _
    have hW0pos : 0 < W0 := fkWeight_pos G hp hp1 hq0 _
    have hlo : (1 - p) * W1 ≤ p * W0 := fkWeight_lo G hp hp1 hq he ψ
    have hhi : p * W0 ≤ q * (1 - p) * W1 := fkWeight_hi G hp hp1 hq he ψ
    have hsum : 0 < W1 + W0 := by linarith
    rw [div_le_div_iff₀ hden hsum]; nlinarith
  · 
    rw [condOpen_eq_weightRatio G hp hp1 hq0]
    set W1 := fkWeight G p q (setOpen e ψ) with hW1
    set W0 := fkWeight G p q (setClosed e ψ) with hW0
    have hW1pos : 0 < W1 := fkWeight_pos G hp hp1 hq0 _
    have hW0pos : 0 < W0 := fkWeight_pos G hp hp1 hq0 _
    have hlo : (1 - p) * W1 ≤ p * W0 := fkWeight_lo G hp hp1 hq he ψ
    have hsum : 0 < W1 + W0 := by linarith
    rw [div_le_iff₀ hsum]; nlinarith

end FK

end StatMech
