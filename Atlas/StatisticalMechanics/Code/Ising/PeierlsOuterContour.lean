/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Ising.PeierlsClose
import Code.Ising.PeierlsContourCount
import Code.Lattice.ContourAnchor
import Code.Percolation.PcUpperUncond

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice
open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}













theorem poc_cyclesAtLen_card_le_real (ℓ : ℕ) :
    ((Percolation.cyclesAtLen ℓ).card : ℝ) ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by
  have h : ((Percolation.cyclesAtLen ℓ).card : ℕ) ≤ 2 * ℓ * 4 ^ ℓ := Percolation.cyclesAtLen_card ℓ
  calc ((Percolation.cyclesAtLen ℓ).card : ℝ)
      ≤ ((2 * ℓ * 4 ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h
    _ = 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by push_cast; ring








noncomputable def twoPeierlsBound (d : ℕ) (β : ℝ) : ℝ := 2 * peierlsBound d β


theorem poc_twoPeierlsBound_nonneg (d : ℕ) (β : ℝ) : 0 ≤ twoPeierlsBound d β := by
  unfold twoPeierlsBound; have := peierlsBound_nonneg d β; linarith



theorem poc_twoPeierlsBound_tendsto_atTop (d : ℕ) :
    Tendsto (fun β : ℝ => twoPeierlsBound d β) atTop (nhds 0) := by
  have h := (peierlsBound_tendsto_atTop d).const_mul (2 : ℝ)
  simpa [twoPeierlsBound] using h



theorem poc_exists_beta_two_peierlsBound_lt_half (d : ℕ) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → twoPeierlsBound d β < 1 / 2 := by
  have h := (poc_twoPeierlsBound_tendsto_atTop d).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  rw [eventually_atTop] at h
  obtain ⟨β₀, hβ₀⟩ := h
  exact ⟨β₀, hβ₀⟩







theorem poc_circuitLengthSum_le (β : ℝ) (hx : peierlsRatio 2 β < 1) (T : Finset ℕ) :
    ∑ ℓ ∈ T, ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
      ≤ twoPeierlsBound 2 β := by
  have hsummand : Summable
      (fun ℓ : ℕ => (ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) :=
    pcl_summable_peierlsSummand 2 β hx
  
  have hterm : ∀ ℓ ∈ T,
      ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
        ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
    intro ℓ _
    have hexp : (0 : ℝ) ≤ Real.exp (-(2 * β) * (ℓ : ℝ)) := (Real.exp_pos _).le
    calc ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
        ≤ (2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ)) * Real.exp (-(2 * β) * (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right (poc_cyclesAtLen_card_le_real ℓ) hexp
      _ = 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by ring
  calc ∑ ℓ ∈ T, ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
      ≤ ∑ ℓ ∈ T, 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ ℓ ∈ T, ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * peierlsBound 2 β := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pcl_lengthSum_le_peierlsBound 2 β hx T
    _ = twoPeierlsBound 2 β := rfl



















theorem poc_probContourCircuit_le (n : ℕ) (K : Set (Site d)) (hK : K ⊆ box d n)
    (η : ConfigSpace (Site d)) (β : ℝ) :
    probContour K η n (bondFinsetTouch d n) β
      ≤ Real.exp (-(2 * β) * (contourLen K (bondFinsetTouch d n) : ℝ)) :=
  contour_energy_bound n K hK η (bondFinsetTouch d n) β



















def InteriorAssignment : Type :=
  (u : Site 2) → (hypercubicLattice 2).Walk u u → Finset (Site 2)



















def OuterContourMap (n : ℕ) : Prop :=
  ∃ interiorOf : InteriorAssignment,
    
    
    
    
    (∀ (ℓ : ℕ) (u : Site 2) (γ : (hypercubicLattice 2).Walk u u),
        u ∈ anchorFinset ℓ → γ.length = ℓ → γ.IsCycle →
          (↑(interiorOf u γ) : Set (Site 2)) ⊆ box 2 n ∧
          contourLen (↑(interiorOf u γ)) (bondFinsetTouch 2 n) = ℓ) ∧
    
    (∀ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false →
      ∃ (ℓ : ℕ) (u : Site 2) (γ : (hypercubicLattice 2).Walk u u),
        u ∈ anchorFinset ℓ ∧ γ.length = ℓ ∧ γ.IsCycle ∧
        ContourEvent (↑(interiorOf u γ)) (bondFinsetTouch 2 n) (glue (plusField 2) τ))












noncomputable def poc_circuitFamily (M : ℕ) :
    Finset (Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u) :=
  (Finset.range M).sigma (fun ℓ => Percolation.cyclesAtLen ℓ)



noncomputable def poc_circuitSummand (n : ℕ) (β : ℝ) (interiorOf : InteriorAssignment)
    (σ : Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u) : ℝ :=
  probContour (↑(interiorOf σ.2.1 σ.2.2)) (plusField 2) n (bondFinsetTouch 2 n) β


theorem poc_circuitSummand_nonneg (n : ℕ) (β : ℝ) (interiorOf : InteriorAssignment)
    (σ : Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u) :
    0 ≤ poc_circuitSummand n β interiorOf σ :=
  probContour_nonneg _ _ _ _ _



theorem poc_mem_circuitFamily {M ℓ : ℕ} {u : Site 2} {γ : (hypercubicLattice 2).Walk u u}
    (hℓM : ℓ < M) (hu : u ∈ anchorFinset ℓ) (hlen : γ.length = ℓ) (hcyc : γ.IsCycle) :
    (⟨ℓ, ⟨u, γ⟩⟩ : Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u)
      ∈ poc_circuitFamily M := by
  classical
  unfold poc_circuitFamily Percolation.cyclesAtLen
  rw [Finset.mem_sigma]
  refine ⟨Finset.mem_range.mpr hℓM, ?_⟩
  rw [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff]
  exact ⟨hu, hlen, hcyc⟩








theorem poc_probOriginMinus_le_circuitSum (n : ℕ) (β : ℝ) (hMap : OuterContourMap n) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0
      ≤ ∑ σ ∈ poc_circuitFamily (2 * 2 * (boxFinset 2 n).card + 1),
          poc_circuitSummand n β (Classical.choose hMap) σ := by
  classical
  set interiorOf := Classical.choose hMap with hint
  have hspec := Classical.choose_spec hMap
  rw [← hint] at hspec
  obtain ⟨hglob, hpeierls⟩ := hspec
  set M := 2 * 2 * (boxFinset 2 n).card + 1 with hM
  
  have hexpand : ∑ σ ∈ poc_circuitFamily M, poc_circuitSummand n β interiorOf σ
      = ∑ τ : {x // x ∈ box 2 n} → Bool, ∑ σ ∈ poc_circuitFamily M,
          (if ContourEvent (↑(interiorOf σ.2.1 σ.2.2)) (bondFinsetTouch 2 n)
              (glue (plusField 2) τ)
            then fvProb (plusField 2) n (bondFinsetTouch 2 n) β 0 τ else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    unfold poc_circuitSummand probContour
    rfl
  rw [hexpand]
  unfold probOriginMinus
  refine Finset.sum_le_sum (fun τ _ => ?_)
  
  set g : (Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u) → ℝ := fun σ =>
    (if ContourEvent (↑(interiorOf σ.2.1 σ.2.2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ)
      then fvProb (plusField 2) n (bondFinsetTouch 2 n) β 0 τ else 0) with hg
  have hgnn : ∀ σ ∈ poc_circuitFamily M, 0 ≤ g σ := by
    intro σ _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField 2) τ (origin 2) = false
  · rw [if_pos ho]
    obtain ⟨ℓ, u, γ, hu, hlen, hcyc, hev⟩ := hpeierls τ ho
    obtain ⟨hKbox, hKlen⟩ := hglob ℓ u γ hu hlen hcyc
    
    have hℓle : ℓ ≤ 2 * 2 * (boxFinset 2 n).card := by
      rw [← hKlen]
      refine le_trans (pcc_contourLen_le_card_mul (interiorOf u γ) n) ?_
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      intro x hx
      rw [mem_boxFinset]
      exact hKbox hx
    have hℓM : ℓ < M := by rw [hM]; omega
    have hmem : (⟨ℓ, ⟨u, γ⟩⟩ : Σ _ℓ : ℕ, Σ u : Site 2, (hypercubicLattice 2).Walk u u)
        ∈ poc_circuitFamily M := poc_mem_circuitFamily hℓM hu hlen hcyc
    have hge : fvProb (plusField 2) n (bondFinsetTouch 2 n) β 0 τ
        = g ⟨ℓ, ⟨u, γ⟩⟩ := by rw [hg]; dsimp only; rw [if_pos hev]
    rw [hge]
    exact Finset.single_le_sum hgnn hmem
  · rw [if_neg ho]
    exact Finset.sum_nonneg hgnn













theorem poc_circuitSum_le_lengthSum (n : ℕ) (β : ℝ) (M : ℕ)
    (interiorOf : InteriorAssignment)
    (hglob : ∀ (ℓ : ℕ) (u : Site 2) (γ : (hypercubicLattice 2).Walk u u),
        u ∈ anchorFinset ℓ → γ.length = ℓ → γ.IsCycle →
          (↑(interiorOf u γ) : Set (Site 2)) ⊆ box 2 n ∧
          contourLen (↑(interiorOf u γ)) (bondFinsetTouch 2 n) = ℓ) :
    ∑ σ ∈ poc_circuitFamily M, poc_circuitSummand n β interiorOf σ
      ≤ ∑ ℓ ∈ Finset.range M,
          ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
  classical
  unfold poc_circuitFamily
  rw [Finset.sum_sigma]
  refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
  
  calc ∑ σ ∈ Percolation.cyclesAtLen ℓ,
          poc_circuitSummand n β interiorOf ⟨ℓ, σ⟩
      ≤ ∑ _σ ∈ Percolation.cyclesAtLen ℓ, Real.exp (-(2 * β) * (ℓ : ℝ)) := by
        refine Finset.sum_le_sum (fun σ hσ => ?_)
        
        have hσ' := hσ
        unfold Percolation.cyclesAtLen at hσ'
        rw [Finset.mem_sigma, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hσ'
        obtain ⟨hu, hlen, hcyc⟩ := hσ'
        obtain ⟨hKbox, hKlen⟩ := hglob ℓ σ.1 σ.2 hu hlen hcyc
        unfold poc_circuitSummand
        have hbnd := poc_probContourCircuit_le n (↑(interiorOf σ.1 σ.2)) hKbox (plusField 2) β
        rw [hKlen] at hbnd
        exact hbnd
      _ = ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]







theorem poc_probOriginMinus_le_two_peierls (n : ℕ) (β : ℝ) (hx : peierlsRatio 2 β < 1)
    (hMap : OuterContourMap n) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ twoPeierlsBound 2 β := by
  classical
  set interiorOf := Classical.choose hMap with hint
  have hspec := Classical.choose_spec hMap
  rw [← hint] at hspec
  obtain ⟨hglob, _⟩ := hspec
  set M := 2 * 2 * (boxFinset 2 n).card + 1 with hM
  calc probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0
      ≤ ∑ σ ∈ poc_circuitFamily M, poc_circuitSummand n β interiorOf σ :=
        poc_probOriginMinus_le_circuitSum n β hMap
    _ ≤ ∑ ℓ ∈ Finset.range M,
          ((Percolation.cyclesAtLen ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ)) :=
        poc_circuitSum_le_lengthSum n β M interiorOf hglob
    _ ≤ twoPeierlsBound 2 β := poc_circuitLengthSum_le β hx (Finset.range M)






















theorem poc_peierls_long_range_order (hMap : ∀ n : ℕ, OuterContourMap n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
  
  obtain ⟨β₂, hβ₂⟩ := pcl_exists_beta_ratio_lt_one 2
  
  obtain ⟨β₃, hβ₃⟩ := poc_exists_beta_two_peierlsBound_lt_half 2
  refine ⟨max β₂ β₃, fun n β hβ => ?_⟩
  have h2 : β₂ ≤ β := le_trans (le_max_left _ _) hβ
  have h3 : β₃ ≤ β := le_trans (le_max_right _ _) hβ
  have hratio : peierlsRatio 2 β < 1 := hβ₂ β h2
  
  have hbound : probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0
      ≤ twoPeierlsBound 2 β :=
    poc_probOriginMinus_le_two_peierls n β hratio (hMap n)
  
  have hlt : probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 < 1 / 2 :=
    lt_of_le_of_lt hbound (hβ₃ β h3)
  
  
  have hmag : 0 < fvMagOrigin (plusField 2) n (bondFinsetTouch 2 n) β 0 :=
    fvMagOrigin_pos_of_probOriginMinus_lt_half _ _ _ _ _ hlt
  exact peierls_lro_criterion (le_refl 2) n β hmag

end Ising

end StatMech
