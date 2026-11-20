/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Percolation.TreePercolation

open scoped BigOperators
open Set Filter Topology

namespace StatMech

namespace BeffaraDC







noncomputable def clusterMoment (dist : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ d * dist n











theorem summable_pow_mul_of_geometricTail {dist : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hnn : ∀ n, 0 ≤ dist n) (htail : ∀ n, dist n ≤ C * r ^ n)
    (d : ℕ) : Summable (fun n : ℕ => (n : ℝ) ^ d * dist n) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ d * (C * r ^ n)) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
      (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left C
    exact h.congr (fun n => by ring)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeo
  · exact mul_nonneg (by positivity) (hnn n)
  · exact mul_le_mul_of_nonneg_left (htail n) (by positivity)



theorem clusterMoment_summand_summable {dist : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hnn : ∀ n, 0 ≤ dist n) (htail : ∀ n, dist n ≤ C * r ^ n)
    (d : ℕ) : Summable (fun n : ℕ => (n : ℝ) ^ d * dist n) :=
  summable_pow_mul_of_geometricTail hr0 hr1 hnn htail d


theorem clusterMoment_nonneg {dist : ℕ → ℝ} (hnn : ∀ n, 0 ≤ dist n) (d : ℕ) :
    0 ≤ clusterMoment dist d :=
  tsum_nonneg (fun n => mul_nonneg (by positivity) (hnn n))





theorem clusterMoment_le_of_geometricTail {dist : ℕ → ℝ} {C r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hnn : ∀ n, 0 ≤ dist n) (htail : ∀ n, dist n ≤ C * r ^ n)
    (d : ℕ) :
    clusterMoment dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (C * r ^ n) := by
  have hgeo : Summable (fun n : ℕ => (n : ℝ) ^ d * (C * r ^ n)) := by
    have h := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
      (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)).mul_left C
    exact h.congr (fun n => by ring)
  refine Summable.tsum_mono
    (summable_pow_mul_of_geometricTail hr0 hr1 hnn htail d) hgeo (fun n => ?_)
  exact mul_le_mul_of_nonneg_left (htail n) (by positivity)
























structure ClusterSizeDomination where
  
  dist : ℕ → ℝ
  
  const : ℝ
  
  rate : ℝ
  
  nonneg : ∀ n, 0 ≤ dist n
  
  rate_nonneg : 0 ≤ rate
  
  rate_lt_one : rate < 1
  
  geometricTail : ∀ n, dist n ≤ const * rate ^ n

namespace ClusterSizeDomination

variable (D : ClusterSizeDomination)



theorem summand_summable (d : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ d * D.dist n) :=
  summable_pow_mul_of_geometricTail D.rate_nonneg D.rate_lt_one D.nonneg D.geometricTail d






theorem allMoments_lt_top (d : ℕ) :
    clusterMoment D.dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (D.const * D.rate ^ n) :=
  clusterMoment_le_of_geometricTail D.rate_nonneg D.rate_lt_one D.nonneg D.geometricTail d


theorem moment_nonneg (d : ℕ) : 0 ≤ clusterMoment D.dist d :=
  clusterMoment_nonneg D.nonneg d

end ClusterSizeDomination








open StatMech.Percolation











theorem subcritical_expMomentRadius (b : ℕ) {p : ℝ} (hmean : (b : ℝ) * p < 1) :
    ∃ s, 1 < s ∧ treeGF b p s < s := by
  set g : ℝ → ℝ := fun s => treeGF b p s - s with hg
  have hg1 : g 1 = 0 := by simp [hg]
  have hgder : HasDerivAt g ((b : ℝ) * p - 1) 1 := by
    have := (treeGF_hasDerivAt_one b p).sub (hasDerivAt_id 1)
    simpa [hg] using this
  have hslope : Tendsto (slope g 1) (nhdsWithin 1 {1}ᶜ) (nhds ((b : ℝ) * p - 1)) :=
    hasDerivAt_iff_tendsto_slope.mp hgder
  have hev : ∀ᶠ y in nhdsWithin 1 {1}ᶜ, slope g 1 y < 0 :=
    hslope.eventually_lt_const (by linarith : (b : ℝ) * p - 1 < 0)
  have hsub : nhdsWithin 1 (Ioi (1 : ℝ)) ≤ nhdsWithin 1 {1}ᶜ := by
    refine nhdsWithin_mono _ (fun x hx => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx
  have hev2 : ∀ᶠ y in nhdsWithin 1 (Ioi (1 : ℝ)), slope g 1 y < 0 := hev.filter_mono hsub
  haveI : (nhdsWithin (1 : ℝ) (Ioi 1)).NeBot := nhdsGT_neBot 1
  obtain ⟨y, hyslope, hymem⟩ := (hev2.and self_mem_nhdsWithin).exists
  have hy1 : (1 : ℝ) < y := hymem
  refine ⟨y, hy1, ?_⟩
  have hslope_eq : slope g 1 y = (g y - g 1) / (y - 1) := slope_def_field g 1 y
  rw [hslope_eq, hg1, sub_zero] at hyslope
  have hypos : (0 : ℝ) < y - 1 := by linarith
  have hgy : g y < 0 := by
    by_contra hcon
    have := div_nonneg (le_of_not_gt hcon) (le_of_lt hypos)
    linarith
  have hgyeq : g y = treeGF b p y - y := rfl
  rw [hgyeq] at hgy; linarith



theorem subcritical_expMomentRadius_of_treeMean (b : ℕ) {p : ℝ}
    (hmean : treeMean b p < 1) : ∃ s, 1 < s ∧ treeGF b p s < s := by
  rw [treeMean] at hmean
  exact subcritical_expMomentRadius b hmean







theorem subcritical_expectedProgeny (b : ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hmean : (b : ℝ) * p < 1) :
    ∑' k : ℕ, ((b : ℝ) * p) ^ k = (1 - (b : ℝ) * p)⁻¹ :=
  tsum_geometric_of_lt_one (by positivity) hmean


theorem subcritical_expectedProgeny_pos (b : ℕ) {p : ℝ}
    (hmean : (b : ℝ) * p < 1) : 0 < (1 - (b : ℝ) * p)⁻¹ := by
  have : 0 < 1 - (b : ℝ) * p := by linarith
  positivity














def clusterSizeDomination_of_geometricTail {dist : ℕ → ℝ} {C r : ℝ}
    (hnn : ∀ n, 0 ≤ dist n) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ n, dist n ≤ C * r ^ n) : ClusterSizeDomination where
  dist := dist
  const := C
  rate := r
  nonneg := hnn
  rate_nonneg := hr0
  rate_lt_one := hr1
  geometricTail := htail







theorem clusterMoment_lt_top_of_subcriticalDomination {dist : ℕ → ℝ} {C r : ℝ}
    (hnn : ∀ n, 0 ≤ dist n) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ n, dist n ≤ C * r ^ n) (d : ℕ) :
    clusterMoment dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (C * r ^ n) :=
  (clusterSizeDomination_of_geometricTail hnn hr0 hr1 htail).allMoments_lt_top d

end BeffaraDC

end StatMech
