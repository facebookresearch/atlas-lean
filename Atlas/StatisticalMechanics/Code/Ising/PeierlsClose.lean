/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Ising.PeierlsContourCount

open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal

namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}








theorem pcl_contourEnergy_eq_pow (β : ℝ) (ℓ : ℕ) :
    Real.exp (-(2 * β) * (ℓ : ℝ)) = (Real.exp (-(2 * β))) ^ ℓ := by
  rw [← Real.exp_nat_mul, mul_comm]




theorem pcl_summand_eq (d : ℕ) (β : ℝ) (ℓ : ℕ) :
    (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * (Real.exp (-(2 * β))) ^ ℓ
      = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) := by
  rw [pcl_contourEnergy_eq_pow]









theorem pcl_summable_peierlsSummand (d : ℕ) (β : ℝ) (hx : peierlsRatio d β < 1) :
    Summable (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))) := by
  have heq : (fun ℓ : ℕ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)))
      = (fun ℓ : ℕ => (ℓ : ℝ) * (peierlsRatio d β) ^ ℓ) :=
    funext (peierlsSummand_eq d β)
  rw [heq]
  have hnorm : ‖peierlsRatio d β‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (peierlsRatio_nonneg d β)]; exact hx
  have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  simpa using this




theorem pcl_lengthSum_le_peierlsBound (d : ℕ) (β : ℝ) (hx : peierlsRatio d β < 1)
    (T : Finset ℕ) :
    ∑ ℓ ∈ T, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) ≤ peierlsBound d β :=
  Summable.sum_le_tsum T (fun ℓ _ => by positivity) (pcl_summable_peierlsSummand d β hx)












theorem pcl_clusterSum_le_lengthSum {α : Type*} [DecidableEq α] (S : Finset α) (len : α → ℕ)
    (c : ℝ) (hc : 0 ≤ c) (count : ℕ → ℝ)
    (hcount : ∀ ℓ, ((S.filter (fun K => len K = ℓ)).card : ℝ) ≤ count ℓ) :
    ∑ K ∈ S, c ^ (len K) ≤ ∑ ℓ ∈ S.image len, count ℓ * c ^ ℓ := by
  have hmaps : ∀ K ∈ S, len K ∈ S.image len := fun K hK => Finset.mem_image_of_mem len hK
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun K => c ^ (len K))]
  refine Finset.sum_le_sum (fun ℓ _ => ?_)
  have hinner : ∑ K ∈ S.filter (fun K => len K = ℓ), c ^ (len K)
      = ((S.filter (fun K => len K = ℓ)).card : ℝ) * c ^ ℓ := by
    rw [Finset.sum_congr rfl (fun K hK => by rw [(Finset.mem_filter.mp hK).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hinner]
  exact mul_le_mul_of_nonneg_right (hcount ℓ) (by positivity)



















def ConnectedContourCount (d n : ℕ) : Prop :=
  ∀ ℓ : ℕ,
    (((connClusterFamily (d := d) n).filter
        (fun (K : Finset (Site d)) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card : ℝ)
      ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ














theorem pcl_connectedContourCountBound_of_count (n : ℕ) (β : ℝ)
    (hx : peierlsRatio d β < 1) (hCount : ConnectedContourCount d n) :
    ConnectedContourCountBound d n β := by
  classical
  unfold ConnectedContourCountBound
  
  let S : Finset (Finset (Site d)) := connClusterFamily (d := d) n
  let len : Finset (Site d) → ℕ := fun K => contourLen (↑K) (bondFinsetTouch d n)
  let c : ℝ := Real.exp (-(2 * β))
  show ∑ K ∈ S, Real.exp (-(2 * β) * (len K : ℝ)) ≤ peierlsBound d β
  
  have hrw : ∀ K ∈ S, Real.exp (-(2 * β) * (len K : ℝ)) = c ^ (len K) := fun K _ => by
    change Real.exp (-(2 * β) * (len K : ℝ)) = Real.exp (-(2 * β)) ^ (len K)
    rw [pcl_contourEnergy_eq_pow]
  rw [Finset.sum_congr rfl hrw]
  
  have hgroup := pcl_clusterSum_le_lengthSum (α := Finset (Site d)) S len c (Real.exp_pos _).le
    (fun ℓ => (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ) (fun ℓ => hCount ℓ)
  refine le_trans hgroup ?_
  
  have hpeierls : ∑ ℓ ∈ S.image len, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * c ^ ℓ
      = ∑ ℓ ∈ S.image len, (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ)) :=
    Finset.sum_congr rfl (fun ℓ _ => by
      change (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β)) ^ ℓ
        = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ * Real.exp (-(2 * β) * (ℓ : ℝ))
      rw [pcl_summand_eq])
  rw [hpeierls]
  exact pcl_lengthSum_le_peierlsBound d β hx (S.image len)













theorem pcl_exists_beta_ratio_lt_one (d : ℕ) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → peierlsRatio d β < 1 := by
  have h := (peierlsRatio_tendsto_atTop d).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [eventually_atTop] at h
  obtain ⟨β₀, hβ₀⟩ := h
  exact ⟨β₀, hβ₀⟩












theorem pcl_peierls_long_range_order_of_count (hd : 2 ≤ d)
    (hCount : ∀ n : ℕ, ConnectedContourCount d n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₀, hβ₀⟩ := pcl_exists_beta_ratio_lt_one d
  refine pcc_peierls_long_range_order_of_connected hd ⟨β₀, fun n β hβ => ?_⟩
  exact pcl_connectedContourCountBound_of_count n β (hβ₀ β hβ) (hCount n)

end Ising

end StatMech
