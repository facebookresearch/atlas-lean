/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Ising.PlusStateDLR
import Code.Lattice.ContourCountInjection

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}





noncomputable def ovrBox {n m : ℕ} (hnm : n ≤ m)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    {x // x ∈ box d m} → Bool :=
  fun x => if hn : (x : Site d) ∈ box d n then τ ⟨x, hn⟩ else σ x


noncomputable def resBox {n m : ℕ} (hnm : n ≤ m)
    (σ : {x // x ∈ box d m} → Bool) : {x // x ∈ box d n} → Bool :=
  fun x => σ ⟨x, box_mono d hnm x.2⟩


theorem resBox_ovrBox {n m : ℕ} (hnm : n ≤ m)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    resBox hnm (ovrBox hnm σ τ) = τ := by
  funext x
  simp only [resBox, ovrBox]
  rw [dif_pos x.2]


theorem ovrBox_ovrBox_resBox {n m : ℕ} (hnm : n ≤ m)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    ovrBox hnm (ovrBox hnm σ τ) (resBox hnm σ) = σ := by
  funext x
  simp only [ovrBox, resBox]
  by_cases hn : (x : Site d) ∈ box d n
  · rw [dif_pos hn]
  · rw [dif_neg hn, dif_neg hn]







theorem glue_glue_eq_glue_ovrBox {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d))
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    glue (glue η σ) τ = glue η (ovrBox hnm σ τ) := by
  funext x
  by_cases hn : x ∈ box d n
  · 
    have hm : x ∈ box d m := box_mono d hnm hn
    rw [glue_mem _ _ hn, glue_mem _ _ hm]
    simp only [ovrBox, dif_pos hn]
  · by_cases hm : x ∈ box d m
    · 
      rw [glue_not_mem _ _ hn, glue_mem _ _ hm, glue_mem _ _ hm]
      simp only [ovrBox, dif_neg hn]
    · 
      rw [glue_not_mem _ _ hn, glue_not_mem _ _ hm, glue_not_mem _ _ hm]



theorem glue_ovrBox_eq_off_box {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d))
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool)
    {x : Site d} (hx : x ∉ box d n) :
    glue η (ovrBox hnm σ τ) x = glue η σ x := by
  by_cases hm : x ∈ box d m
  · rw [glue_mem _ _ hm, glue_mem _ _ hm]
    simp only [ovrBox, dif_neg hx]
  · rw [glue_not_mem _ _ hm, glue_not_mem _ _ hm]




theorem bond_glue_ovrBox_eq_of_notMem {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d))
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool)
    {e : Sym2 (Site d)} (heE : e ∈ (hypercubicLattice d).edgeSet)
    (heB : e ∉ bondFinsetTouch d n) :
    bond (glue η (ovrBox hnm σ τ)) e = bond (glue η σ) e := by
  induction e with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at heE
    rw [bond_mk, bond_mk]
    
    have ha : a ∉ box d n := fun h => heB (StatMech.Lattice.mk_mem_bondFinsetTouch heE (Or.inl h))
    have hb : b ∉ box d n := fun h => heB (StatMech.Lattice.mk_mem_bondFinsetTouch heE (Or.inr h))
    rw [show spin (glue η (ovrBox hnm σ τ)) a = spin (glue η σ) a from by
          unfold spin; rw [glue_ovrBox_eq_off_box hnm η σ τ ha],
        show spin (glue η (ovrBox hnm σ τ)) b = spin (glue η σ) b from by
          unfold spin; rw [glue_ovrBox_eq_off_box hnm η σ τ hb]]



theorem bondFinsetTouch_subset {n m : ℕ} (hnm : n ≤ m) :
    bondFinsetTouch d n ⊆ bondFinsetTouch d m := by
  intro e he
  have heE : e ∈ (hypercubicLattice d).edgeSet :=
    StatMech.Lattice.bondFinsetTouch_subset_edgeSet n e he
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at heE
    
    rw [StatMech.Ising.bondFinsetTouch, Finset.mem_image] at he
    obtain ⟨p, hp, hpe⟩ := he
    rw [StatMech.Ising.bondPairsTouch, Finset.mem_filter] at hp
    obtain ⟨_, _, htouch⟩ := hp
    rw [Sym2.eq_iff] at hpe
    have htouchm : x ∈ box d m ∨ y ∈ box d m := by
      rcases hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases htouch with h | h
        · exact Or.inl (box_mono d hnm h)
        · exact Or.inr (box_mono d hnm h)
      · rcases htouch with h | h
        · exact Or.inr (box_mono d hnm h)
        · exact Or.inl (box_mono d hnm h)
    exact StatMech.Lattice.mk_mem_bondFinsetTouch heE htouchm






theorem bond_sum_diff_eq {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d))
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    (∑ e ∈ bondFinsetTouch d m, bond (glue η (ovrBox hnm σ τ)) e)
        - (∑ e ∈ bondFinsetTouch d m, bond (glue η σ) e)
      = (∑ e ∈ bondFinsetTouch d n, bond (glue η (ovrBox hnm σ τ)) e)
        - (∑ e ∈ bondFinsetTouch d n, bond (glue η σ) e) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.sum_subset (bondFinsetTouch_subset hnm) (fun e heM heN => ?_)).symm
  have heE : e ∈ (hypercubicLattice d).edgeSet :=
    StatMech.Lattice.bondFinsetTouch_subset_edgeSet m e heM
  rw [bond_glue_ovrBox_eq_of_notMem hnm η σ τ heE heN, sub_self]




theorem spin_sum_diff_eq {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d))
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    (∑ x ∈ boxFinset d m, spin (glue η (ovrBox hnm σ τ)) x)
        - (∑ x ∈ boxFinset d m, spin (glue η σ) x)
      = (∑ x ∈ boxFinset d n, spin (glue η (ovrBox hnm σ τ)) x)
        - (∑ x ∈ boxFinset d n, spin (glue η σ) x) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hsub : boxFinset d n ⊆ boxFinset d m := by
    intro x hx; rw [mem_boxFinset] at hx ⊢; exact box_mono d hnm hx
  refine (Finset.sum_subset hsub (fun x hxM hxN => ?_)).symm
  have hx : x ∉ box d n := fun h => hxN (mem_boxFinset.mpr h)
  unfold spin
  rw [glue_ovrBox_eq_off_box hnm η σ τ hx, sub_self]












theorem fv_energy_decomp {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d)) (h : ℝ)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    fvEnergy η m (bondFinsetTouch d m) h σ
        + fvEnergy (glue η σ) n (bondFinsetTouch d n) h τ
      = fvEnergy η m (bondFinsetTouch d m) h (ovrBox hnm σ τ)
        + fvEnergy (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) h (resBox hnm σ) := by
  
  unfold fvEnergy
  rw [glue_glue_eq_glue_ovrBox hnm η σ τ,
      glue_glue_eq_glue_ovrBox hnm η (ovrBox hnm σ τ) (resBox hnm σ),
      ovrBox_ovrBox_resBox hnm σ τ]
  
  have hb := bond_sum_diff_eq hnm η σ τ
  have hs := spin_sum_diff_eq hnm η σ τ
  linear_combination hb + h * hs









theorem fvWeight_spec_symm {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d)) (β h : ℝ)
    (σ : {x // x ∈ box d m} → Bool) (τ : {x // x ∈ box d n} → Bool) :
    fvWeight η m (bondFinsetTouch d m) β h σ
        * fvWeight (glue η σ) n (bondFinsetTouch d n) β h τ
      = fvWeight η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ)
        * fvWeight (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ) := by
  unfold fvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hE := fv_energy_decomp hnm η h σ τ
  ring_nf
  linear_combination (-β) * hE





theorem integral_fvMeasure_eq_sum (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (g : ConfigSpace (Site d) → ℝ) :
    ∫ y, g y ∂(fvMeasure η n B β h)
      = ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ * g (glue η τ) := by
  unfold fvMeasure
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (fvProb_nonneg η n B β h τ)]
  · intro τ _
    exact (integrable_dirac (by simp [enorm_eq_nnnorm])).smul_measure (by simp)



theorem plusMeasure_coe (m : ℕ) (β h : ℝ) :
    (plusMeasure d m β h : Measure (ConfigSpace (Site d)))
      = fvMeasure (plusField d) m (bondFinsetTouch d m) β h := rfl








theorem glue_eq_of_agree_off_box {n : ℕ} {ζ₁ ζ₂ : ConfigSpace (Site d)}
    (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x) (τ : {x // x ∈ box d n} → Bool) :
    glue ζ₁ τ = glue ζ₂ τ := by
  funext x
  by_cases hx : x ∈ box d n
  · rw [glue_mem _ _ hx, glue_mem _ _ hx]
  · rw [glue_not_mem _ _ hx, glue_not_mem _ _ hx]; exact hagree x hx


theorem fvWeight_eq_of_agree_off_box {n : ℕ} (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {ζ₁ ζ₂ : ConfigSpace (Site d)} (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x)
    (τ : {x // x ∈ box d n} → Bool) :
    fvWeight ζ₁ n B β h τ = fvWeight ζ₂ n B β h τ := by
  unfold fvWeight fvEnergy
  rw [glue_eq_of_agree_off_box hagree τ]


theorem fvZ_eq_of_agree_off_box {n : ℕ} (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {ζ₁ ζ₂ : ConfigSpace (Site d)} (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x) :
    fvZ ζ₁ n B β h = fvZ ζ₂ n B β h := by
  unfold fvZ
  exact Finset.sum_congr rfl (fun τ _ => fvWeight_eq_of_agree_off_box B β h hagree τ)


theorem fvProb_eq_of_agree_off_box {n : ℕ} (B : Finset (Sym2 (Site d))) (β h : ℝ)
    {ζ₁ ζ₂ : ConfigSpace (Site d)} (hagree : ∀ x ∉ box d n, ζ₁ x = ζ₂ x)
    (τ : {x // x ∈ box d n} → Bool) :
    fvProb ζ₁ n B β h τ = fvProb ζ₂ n B β h τ := by
  unfold fvProb
  rw [fvWeight_eq_of_agree_off_box B β h hagree τ, fvZ_eq_of_agree_off_box B β h hagree]




noncomputable def swapPair {n m : ℕ} (hnm : n ≤ m) :
    (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool))
      → (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool)) :=
  fun p => (ovrBox hnm p.1 p.2, resBox hnm p.1)


theorem swapPair_involutive {n m : ℕ} (hnm : n ≤ m) :
    Function.Involutive (swapPair (d := d) hnm) := by
  rintro ⟨σ, τ⟩
  simp only [swapPair]
  rw [ovrBox_ovrBox_resBox hnm σ τ, resBox_ovrBox hnm σ τ]

theorem swapPair_bijective {n m : ℕ} (hnm : n ≤ m) :
    Function.Bijective (swapPair (d := d) hnm) :=
  (swapPair_involutive hnm).bijective












theorem consistency_double_sum {n m : ℕ} (hnm : n ≤ m) (η : ConfigSpace (Site d)) (β h : ℝ)
    (g : ConfigSpace (Site d) → ℝ) :
    (∑ σ : {x // x ∈ box d m} → Bool,
        fvProb η m (bondFinsetTouch d m) β h σ
          * ∑ τ : {x // x ∈ box d n} → Bool,
              fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue (glue η σ) τ))
      = ∑ σ : {x // x ∈ box d m} → Bool,
          fvProb η m (bondFinsetTouch d m) β h σ * g (glue η σ) := by
  
  set F : (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool)) → ℝ :=
    fun p => fvProb η m (bondFinsetTouch d m) β h p.1
        * (fvProb (glue η p.1) n (bondFinsetTouch d n) β h p.2 * g (glue (glue η p.1) p.2))
    with hF
  
  have hLHS : (∑ σ : {x // x ∈ box d m} → Bool,
        fvProb η m (bondFinsetTouch d m) β h σ
          * ∑ τ : {x // x ∈ box d n} → Bool,
              fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue (glue η σ) τ))
      = ∑ p, F p := by
    rw [Fintype.sum_prod_type (f := F)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum]
  rw [hLHS]
  
  rw [← Function.Bijective.sum_comp (swapPair_bijective hnm) F]
  
  have hpoint : ∀ p : (({x // x ∈ box d m} → Bool) × ({x // x ∈ box d n} → Bool)),
      F (swapPair hnm p)
        = fvProb η m (bondFinsetTouch d m) β h p.1
            * (fvProb (glue η p.1) n (bondFinsetTouch d n) β h p.2 * g (glue η p.1)) := by
    rintro ⟨σ, τ⟩
    simp only [hF, swapPair]
    
    have harg : glue (glue η (ovrBox hnm σ τ)) (resBox hnm σ) = glue η σ := by
      rw [glue_glue_eq_glue_ovrBox hnm η (ovrBox hnm σ τ) (resBox hnm σ),
        ovrBox_ovrBox_resBox hnm σ τ]
    rw [harg]
    
    have hprob : fvProb η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ)
          * fvProb (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ)
        = fvProb η m (bondFinsetTouch d m) β h σ
          * fvProb (glue η σ) n (bondFinsetTouch d n) β h τ := by
      unfold fvProb
      
      have hagree : ∀ x ∉ box d n, glue η (ovrBox hnm σ τ) x = glue η σ x :=
        fun x hx => glue_ovrBox_eq_off_box hnm η σ τ hx
      rw [fvZ_eq_of_agree_off_box (bondFinsetTouch d n) β h hagree]
      have hw := fvWeight_spec_symm hnm η β h σ τ
      
      rw [div_mul_div_comm, div_mul_div_comm, hw]
    
    calc fvProb η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ)
            * (fvProb (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ)
                * g (glue η σ))
        = (fvProb η m (bondFinsetTouch d m) β h (ovrBox hnm σ τ)
              * fvProb (glue η (ovrBox hnm σ τ)) n (bondFinsetTouch d n) β h (resBox hnm σ))
            * g (glue η σ) := by ring
      _ = (fvProb η m (bondFinsetTouch d m) β h σ
              * fvProb (glue η σ) n (bondFinsetTouch d n) β h τ) * g (glue η σ) := by rw [hprob]
      _ = fvProb η m (bondFinsetTouch d m) β h σ
            * (fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue η σ)) := by ring
  rw [Finset.sum_congr rfl (fun p _ => hpoint p)]
  
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hcollapse : (∑ τ : {x // x ∈ box d n} → Bool,
        fvProb η m (bondFinsetTouch d m) β h σ
          * (fvProb (glue η σ) n (bondFinsetTouch d n) β h τ * g (glue η σ)))
      = fvProb η m (bondFinsetTouch d m) β h σ * g (glue η σ)
          * (∑ τ : {x // x ∈ box d n} → Bool, fvProb (glue η σ) n (bondFinsetTouch d n) β h τ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    ring
  rw [hcollapse, fvProb_sum_eq_one (glue η σ) n (bondFinsetTouch d n) β h, mul_one]













theorem fvConsistency_plus (β h : ℝ) : FVConsistency d β h := by
  intro n m hnm f
  
  rw [plusMeasure_coe,
    integral_fvMeasure_eq_sum (plusField d) m (bondFinsetTouch d m) β h
      (specApply n (bondFinsetTouch d n) β h (f : ConfigSpace (Site d) → ℝ)),
    integral_fvMeasure_eq_sum (plusField d) m (bondFinsetTouch d m) β h
      (f : ConfigSpace (Site d) → ℝ)]
  
  simp only [specApply_eq_sum]
  
  exact consistency_double_sum hnm (plusField d) β h (f : ConfigSpace (Site d) → ℝ)







theorem psdlr_plusState_isDLR_uncond (β h : ℝ) :
    IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  psdlr_plusState_isDLR β h (fvConsistency_plus β h)

end Ising

end StatMech
