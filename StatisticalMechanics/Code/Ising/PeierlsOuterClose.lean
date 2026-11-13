/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Ising.PeierlsOuterContour
import Code.Lattice.PeierlsContourFinal

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice
open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable

































def OuterContourWinding (n : ℕ) : Prop :=
  ∀ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false →
    ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster K ∧
      ContourEvent (↑K : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧
      ∃ (T : Finset (Site 2)) (j : ℕ),
        (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
        j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
        axisVertex 2 j ∈ T ∧
        (∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
          e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet)

















def IsHoleFreeBoxCluster (n : ℕ) (K : Finset (Site 2)) : Prop :=
  IsConnectedCluster K ∧
    ∃ (T : Finset (Site 2)) (j : ℕ),
      (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧
      j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
      axisVertex 2 j ∈ T ∧
      (∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
        e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet)




noncomputable def holeFreeClusterFamily (n : ℕ) : Finset (Finset (Site 2)) :=
  (clusterFamily (d := 2) n).filter (fun K => IsHoleFreeBoxCluster n K)

theorem mem_holeFreeClusterFamily {n : ℕ} {K : Finset (Site 2)} :
    K ∈ holeFreeClusterFamily n ↔
      K ∈ clusterFamily (d := 2) n ∧ IsHoleFreeBoxCluster n K := by
  unfold holeFreeClusterFamily; rw [Finset.mem_filter]


theorem holeFreeClusterFamily_subset_box {n : ℕ} {K : Finset (Site 2)}
    (hK : K ∈ holeFreeClusterFamily n) : (↑K : Set (Site 2)) ⊆ box 2 n :=
  clusterFamily_subset_box (mem_holeFreeClusterFamily.mp hK).1






theorem outerUnionBound_le_sum_probContour (n : ℕ) (β : ℝ) (hWind : OuterContourWinding n) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0
      ≤ ∑ K ∈ holeFreeClusterFamily n,
          probContour (↑K) (plusField 2) n (bondFinsetTouch 2 n) β := by
  classical
  unfold probOriginMinus probContour
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun τ _ => ?_)
  set g : Finset (Site 2) → ℝ := fun K =>
    (if ContourEvent (↑K) (bondFinsetTouch 2 n) (glue (plusField 2) τ)
      then fvProb (plusField 2) n (bondFinsetTouch 2 n) β 0 τ else 0) with hg
  have hgnn : ∀ K ∈ holeFreeClusterFamily n, 0 ≤ g K := by
    intro K _; rw [hg]; dsimp only; split
    · exact fvProb_nonneg _ _ _ _ _ _
    · exact le_refl 0
  by_cases ho : glue (plusField 2) τ (origin 2) = false
  · rw [if_pos ho]
    obtain ⟨K, hKbox, hKconn, hev, T, j, hsupp, hj, hax, hcov⟩ := hWind τ ho
    
    have hKbox' : K ⊆ boxFinset 2 n := by
      intro x hx; rw [mem_boxFinset]; exact hKbox (Finset.mem_coe.mpr hx)
    have hKfam : K ∈ clusterFamily (d := 2) n := by
      rw [clusterFamily, Finset.mem_powerset]; exact hKbox'
    have hKmem : K ∈ holeFreeClusterFamily n := by
      rw [mem_holeFreeClusterFamily]
      exact ⟨hKfam, hKconn, T, j, hsupp, hj, hax, hcov⟩
    have hge : fvProb (plusField 2) n (bondFinsetTouch 2 n) β 0 τ
        = g K := by rw [hg]; dsimp only; rw [if_pos hev]
    rw [hge]
    exact Finset.single_le_sum hgnn hKmem
  · rw [if_neg ho]
    exact Finset.sum_nonneg hgnn

set_option maxHeartbeats 1000000 in










theorem outerUnionBound_le_sum_exp (n : ℕ) (β : ℝ) (hWind : OuterContourWinding n) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0
      ≤ ∑ K ∈ holeFreeClusterFamily n,
          Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch 2 n) : ℝ)) := by
  refine le_trans (outerUnionBound_le_sum_probContour n β hWind) ?_
  apply Finset.sum_le_sum
  intro K hK
  have hKbox := holeFreeClusterFamily_subset_box hK
  have hbound := contour_energy_bound n (↑K) hKbox (plusField 2) (bondFinsetTouch 2 n) β
  exact hbound

















noncomputable def holeFreeAtLen (n ℓ : ℕ) : Finset (Finset (Site 2)) :=
  (holeFreeClusterFamily n).filter
    (fun K => contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ)

theorem mem_holeFreeAtLen {n ℓ : ℕ} {K : Finset (Site 2)} :
    K ∈ holeFreeAtLen n ℓ ↔ K ∈ holeFreeClusterFamily n ∧
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ := by
  unfold holeFreeAtLen; rw [Finset.mem_filter]






theorem holeFree_circuit_encoding {n ℓ : ℕ} {K : Finset (Site 2)} (hK : K ∈ holeFreeAtLen n ℓ) :
    ∃ (j : ℕ), j < ℓ ∧ axisVertex 2 j ∈ anchorFinset ℓ ∧
      ∃ W : (hypercubicLattice 2).Walk (axisVertex 2 j) (axisVertex 2 j),
        W.length = ℓ ∧
        dualWalkContour ⟨axisVertex 2 j, W⟩ = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
  classical
  rw [mem_holeFreeAtLen] at hK
  obtain ⟨hKfam, hKlen⟩ := hK
  have hKbox : (↑K : Set (Site 2)) ⊆ box 2 n := holeFreeClusterFamily_subset_box hKfam
  obtain ⟨_hKconn, T, j, hsupp, hj, hax, hcov⟩ := (mem_holeFreeClusterFamily.mp hKfam).2
  
  obtain ⟨c, htrail, hccov⟩ := dualCircuit_of_componentCovers hsupp hax hcov
  
  have hjℓ : j < ℓ := by rwa [hKlen] at hj
  have hanc : axisVertex 2 j ∈ anchorFinset ℓ := by
    rw [axisVertex_two_natCast]
    unfold anchorFinset
    rw [Finset.mem_union]; left; rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hjℓ, rfl⟩
  refine ⟨j, hjℓ, hanc, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_, ?_⟩
  · rw [circuit_length_eq_contourLen hKbox c htrail hccov, hKlen]
  · rw [circuit_decode_eq_contour hKbox c hccov]


theorem holeFreeAtLen_mem_connFamily {n ℓ : ℕ} {K : Finset (Site 2)}
    (hK : K ∈ holeFreeAtLen n ℓ) : K ∈ connClusterFamily (d := 2) n := by
  rw [mem_holeFreeAtLen] at hK
  rw [pcc_mem_connClusterFamily]
  exact ⟨(mem_holeFreeClusterFamily.mp hK.1).1, (mem_holeFreeClusterFamily.mp hK.1).2.1⟩














theorem holeFreeAtLen_card_le (n ℓ : ℕ) :
    (holeFreeAtLen n ℓ).card ≤ 2 * ℓ * (2 * 2) ^ ℓ := by
  classical
  
  set enc : Finset (Site 2) → Σ v : Site 2, (hypercubicLattice 2).Walk v v :=
    fun K => if hK : K ∈ holeFreeAtLen n ℓ
      then ⟨axisVertex 2 (holeFree_circuit_encoding hK).choose,
            (holeFree_circuit_encoding hK).choose_spec.2.2.choose⟩
      else ⟨origin 2, SimpleGraph.Walk.nil⟩ with henc
  
  have hinto : (holeFreeAtLen n ℓ).card ≤
      ((anchorFinset ℓ).sigma
        (fun v => (hypercubicLattice 2).finsetWalkLength ℓ v v)).card := by
    refine Finset.card_le_card_of_injOn enc ?_ ?_
    · 
      intro K hK
      rw [Finset.mem_coe] at hK
      have hspec := (holeFree_circuit_encoding hK).choose_spec
      obtain ⟨_hjℓ, hanc, hWspec⟩ := hspec
      have hWlen := hWspec.choose_spec.1
      have hencval : enc K = ⟨axisVertex 2 (holeFree_circuit_encoding hK).choose,
          (holeFree_circuit_encoding hK).choose_spec.2.2.choose⟩ := by
        simp only [henc, dif_pos hK]
      rw [Finset.mem_coe, hencval, Finset.mem_sigma]
      exact ⟨hanc, SimpleGraph.mem_finsetWalkLength_iff.mpr hWlen⟩
    · 
      intro K₁ hK₁ K₂ hK₂ heq
      rw [Finset.mem_coe] at hK₁ hK₂
      
      have hdec₁ : dualWalkContour (enc K₁)
          = crossEdges (↑K₁ : Set (Site 2)) (bondFinsetTouch 2 n) := by
        have hspec := (holeFree_circuit_encoding hK₁).choose_spec
        have hW := hspec.2.2.choose_spec.2
        simp only [henc, dif_pos hK₁]; exact hW
      have hdec₂ : dualWalkContour (enc K₂)
          = crossEdges (↑K₂ : Set (Site 2)) (bondFinsetTouch 2 n) := by
        have hspec := (holeFree_circuit_encoding hK₂).choose_spec
        have hW := hspec.2.2.choose_spec.2
        simp only [henc, dif_pos hK₂]; exact hW
      have hcross : crossEdges (↑K₁ : Set (Site 2)) (bondFinsetTouch 2 n)
          = crossEdges (↑K₂ : Set (Site 2)) (bondFinsetTouch 2 n) := by
        rw [← hdec₁, ← hdec₂, heq]
      
      exact connBoxCluster_crossEdges_injOn
        (Finset.mem_coe.mpr (holeFreeAtLen_mem_connFamily hK₁))
        (Finset.mem_coe.mpr (holeFreeAtLen_mem_connFamily hK₂)) hcross
  
  calc (holeFreeAtLen n ℓ).card
      ≤ ((anchorFinset ℓ).sigma
          (fun v => (hypercubicLattice 2).finsetWalkLength ℓ v v)).card := hinto
    _ ≤ (anchorFinset ℓ).card * (2 * 2) ^ ℓ := card_circuits_based_in_le_pow 2 _ ℓ
    _ ≤ 2 * ℓ * (2 * 2) ^ ℓ :=
        Nat.mul_le_mul_right _ (StatMech.Percolation.anchorFinset_card ℓ)












theorem holeFreeClusterFamily_contourLen_lt {n : ℕ} {K : Finset (Site 2)}
    (hK : K ∈ holeFreeClusterFamily n) :
    contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) < 2 * 2 * (boxFinset 2 n).card + 1 := by
  have h1 : contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ≤ 2 * 2 * K.card :=
    pcc_contourLen_le_card_mul K n
  have h2 : K.card ≤ (boxFinset 2 n).card :=
    Finset.card_le_card (clusterFamily_subset_boxFinset (mem_holeFreeClusterFamily.mp hK).1)
  have : 2 * 2 * K.card ≤ 2 * 2 * (boxFinset 2 n).card := Nat.mul_le_mul_left _ h2
  omega




theorem holeFreeSum_eq_lengthSum (n : ℕ) (β : ℝ) :
    ∑ K ∈ holeFreeClusterFamily n,
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch 2 n) : ℝ))
      = ∑ ℓ ∈ Finset.range (2 * 2 * (boxFinset 2 n).card + 1),
          ((holeFreeAtLen n ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
  classical
  have hmaps : ∀ K ∈ holeFreeClusterFamily n,
      contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n)
        ∈ Finset.range (2 * 2 * (boxFinset 2 n).card + 1) :=
    fun K hK => Finset.mem_range.mpr (holeFreeClusterFamily_contourLen_lt hK)
  
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  
  refine (Finset.sum_congr rfl (g := fun _ => Real.exp (-(2 * β) * (ℓ : ℝ)))
    (fun K hK => ?_)).trans ?_
  · rw [Finset.mem_filter] at hK
    rw [hK.2]
  · rw [Finset.sum_const, nsmul_eq_mul]
    rfl




theorem holeFreeAtLen_card_le_real (n ℓ : ℕ) :
    ((holeFreeAtLen n ℓ).card : ℝ) ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by
  have h : (holeFreeAtLen n ℓ).card ≤ 2 * ℓ * (2 * 2) ^ ℓ := holeFreeAtLen_card_le n ℓ
  calc ((holeFreeAtLen n ℓ).card : ℝ)
      ≤ ((2 * ℓ * (2 * 2) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h
    _ = 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by push_cast; ring








theorem holeFreeSum_le_twoPeierls (n : ℕ) (β : ℝ) (hx : peierlsRatio 2 β < 1) :
    ∑ K ∈ holeFreeClusterFamily n,
        Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch 2 n) : ℝ))
      ≤ twoPeierlsBound 2 β := by
  rw [holeFreeSum_eq_lengthSum n β]
  set T := Finset.range (2 * 2 * (boxFinset 2 n).card + 1) with hT
  
  have hterm : ∀ ℓ ∈ T,
      ((holeFreeAtLen n ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
        ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
    intro ℓ _
    have hexp : (0 : ℝ) ≤ Real.exp (-(2 * β) * (ℓ : ℝ)) := (Real.exp_pos _).le
    calc ((holeFreeAtLen n ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
        ≤ (2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ)) * Real.exp (-(2 * β) * (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_right (holeFreeAtLen_card_le_real n ℓ) hexp
      _ = 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by ring
  calc ∑ ℓ ∈ T, ((holeFreeAtLen n ℓ).card : ℝ) * Real.exp (-(2 * β) * (ℓ : ℝ))
      ≤ ∑ ℓ ∈ T, 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ ℓ ∈ T, ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * peierlsBound 2 β := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pcl_lengthSum_le_peierlsBound 2 β hx T
    _ = twoPeierlsBound 2 β := rfl







theorem outerProbOriginMinus_le_two_peierls (n : ℕ) (β : ℝ) (hx : peierlsRatio 2 β < 1)
    (hWind : OuterContourWinding n) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ twoPeierlsBound 2 β :=
  le_trans (outerUnionBound_le_sum_exp n β hWind) (holeFreeSum_le_twoPeierls n β hx)























theorem peierls_long_range_order_of_outerWinding
    (hWind : ∀ n : ℕ, OuterContourWinding n) :
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
    outerProbOriginMinus_le_two_peierls n β hratio (hWind n)
  
  have hlt : probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 < 1 / 2 :=
    lt_of_le_of_lt hbound (hβ₃ β h3)
  
  have hmag : 0 < fvMagOrigin (plusField 2) n (bondFinsetTouch 2 n) β 0 :=
    fvMagOrigin_pos_of_probOriginMinus_lt_half _ _ _ _ _ hlt
  exact peierls_lro_criterion (le_refl 2) n β hmag
















theorem singletonOrigin_isHoleFreeBoxCluster (hd : 1 ≤ 2) (n : ℕ) :
    IsHoleFreeBoxCluster n ({origin 2} : Finset (Site 2)) := by
  classical
  
  have hbox : (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_singleton] at hx
    subst hx; exact origin_mem_box n
  
  have hlen : 0 < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
      (bondFinsetTouch 2 n) :=
    pcc_one_le_contourLen hd hbox (Finset.mem_singleton_self _)
  refine ⟨singleton_origin_isConnectedCluster, singletonBoundarySupport, 0,
    support_singletonOrigin_subset, hlen, axisVertex_zero_mem_singletonBoundarySupport,
    singletonOrigin_componentCovers⟩




theorem singletonOrigin_mem_holeFreeClusterFamily (n : ℕ) :
    ({origin 2} : Finset (Site 2)) ∈ holeFreeClusterFamily n := by
  rw [mem_holeFreeClusterFamily]
  refine ⟨?_, singletonOrigin_isHoleFreeBoxCluster (by norm_num) n⟩
  rw [clusterFamily, Finset.mem_powerset]
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  rw [mem_boxFinset]; exact origin_mem_box n

end Ising

end StatMech
