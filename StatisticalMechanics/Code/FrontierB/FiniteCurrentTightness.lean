/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.FiniteCurrentLaw

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatMech.FrontierB

open Sharpness
open Finset SimpleGraph


variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem unrestricted_current_mass (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    ∑' m : EdgeCurrent G, weight G beta J (ofEdgeFun G m) =
      Real.exp (∑ e ∈ G.edgeFinset, beta * J e) := by
  have hf := prod_tsum_fubini (fun (e : Sym2 V) k => wEdge beta J e k)
    (fun e => (summable_norm_wEdge beta J e).of_norm)
    (fun e k => div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ e)) _) (Nat.cast_nonneg _))
    G.edgeFinset
  have hmass :
      (∑' m : EdgeCurrent G, weight G beta J (ofEdgeFun G m)) =
        ∏ e ∈ G.edgeFinset, ∑' k : ℕ, wEdge beta J e k := by
    simpa only [weight_ofEdgeFun, wEdge] using hf.2.symm
  rw [hmass]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro e he
  simp only [wEdge]
  rw [Real.exp_eq_exp_ℝ]
  exact (congrFun (NormedSpace.exp_eq_tsum_div ( 𝔸 := ℝ)) (beta * J e)).symm

omit [Fintype V] [DecidableEq V] in

theorem summable_nat_mul_wEdge (beta : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V) :
    Summable (fun k : ℕ => (k : ℝ) * wEdge beta J e k) := by
  rw [← summable_nat_add_iff 1]
  have hw : Summable (wEdge beta J e) := by
    unfold wEdge
    have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (beta * J e)
    convert h using 2 with k
    rw [smul_eq_mul, div_eq_inv_mul]
  have h := hw.mul_left (beta * J e)
  refine h.congr (fun k => ?_)
  simp only [wEdge]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

omit [Fintype V] [DecidableEq V] in

theorem tsum_nat_mul_wEdge (beta : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V) :
    (∑' k : ℕ, (k : ℝ) * wEdge beta J e k) =
      (beta * J e) * Real.exp (beta * J e) := by
  rw [(summable_nat_mul_wEdge beta J e).tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  have hterm : (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * wEdge beta J e (k + 1)) =
      fun k => (beta * J e) * wEdge beta J e k := by
    funext k
    simp only [wEdge]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring
  rw [hterm, tsum_mul_left]
  congr 1
  rw [Real.exp_eq_exp_ℝ]
  exact (congrFun (NormedSpace.exp_eq_tsum_div ( 𝔸 := ℝ)) (beta * J e)).symm


theorem sources_zero_current :
    sources G (ofEdgeFun G (0 : EdgeCurrent G)) = ∅ := by
  ext x
  simp [sources, incidentFlux, ofEdgeFun]


theorem one_le_currentSum_empty (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    1 ≤ currentSum G beta J ∅ := by
  unfold currentSum
  have hs := (summable_norm_currentSum_summand G beta J ∅).of_norm
  calc
    1 = (if sources G (ofEdgeFun G (0 : EdgeCurrent G)) = ∅ then
        weight G beta J (ofEdgeFun G (0 : EdgeCurrent G)) else 0) := by
      rw [if_pos (sources_zero_current G)]
      rw [weight_ofEdgeFun]
      simp
    _ ≤ ∑' m : EdgeCurrent G,
        if sources G (ofEdgeFun G m) = ∅ then weight G beta J (ofEdgeFun G m) else 0 :=
      hs.le_tsum (0 : EdgeCurrent G) (fun m _ =>
        currentSummand_nonneg G beta J hbeta hJ ∅ m)


theorem unrestricted_current_first_moment (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (e : ↑G.edgeFinset) :
    ∑' m : EdgeCurrent G, (m e : ℝ) * weight G beta J (ofEdgeFun G m) =
      (beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g) := by
  let g : Sym2 V → ℕ → ℝ := fun f k =>
    if f = e.1 then (k : ℝ) * wEdge beta J f k else wEdge beta J f k
  have hg : ∀ f, Summable (g f) := by
    intro f
    by_cases hfe : f = e.1
    · subst f
      simp only [g, if_pos]
      exact summable_nat_mul_wEdge beta J e.1
    · simp only [g, hfe]
      exact (summable_norm_wEdge beta J f).of_norm
  have hgnn : ∀ f k, 0 ≤ g f k := by
    intro f k
    simp only [g]
    split
    · exact mul_nonneg (Nat.cast_nonneg _) <|
        div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ f)) _) (Nat.cast_nonneg _)
    · exact div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ f)) _) (Nat.cast_nonneg _)
  have hf := prod_tsum_fubini g hg hgnn G.edgeFinset
  have hsummand : ∀ m : EdgeCurrent G,
      (∏ i : ↑G.edgeFinset, g i.1 (m i)) =
        (m e : ℝ) * weight G beta J (ofEdgeFun G m) := by
    intro m
    rw [weight_ofEdgeFun]
    calc
      (∏ i : ↑G.edgeFinset, g i.1 (m i)) =
          ∏ i : ↑G.edgeFinset,
            (if e = i then (m i : ℝ) else 1) * wEdge beta J i.1 (m i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [g]
        by_cases hie : e = i
        · subst i
          simp
        · have hval : i.1 ≠ e.1 := fun h => hie (Subtype.ext h.symm)
          simp [hie, hval]
      _ = (∏ i : ↑G.edgeFinset, if e = i then (m i : ℝ) else 1) *
          ∏ i : ↑G.edgeFinset, wEdge beta J i.1 (m i) := by
        exact Finset.prod_mul_distrib
      _ = (m e : ℝ) * ∏ i : ↑G.edgeFinset, wEdge beta J i.1 (m i) := by
        rw [Fintype.prod_ite_eq]
      _ = (m e : ℝ) *
          ∏ i : ↑G.edgeFinset, (beta * J i.1) ^ (m i) / (m i).factorial := by
        rfl
  calc
    (∑' m : EdgeCurrent G, (m e : ℝ) * weight G beta J (ofEdgeFun G m)) =
        ∑' m : EdgeCurrent G, ∏ i : ↑G.edgeFinset, g i.1 (m i) := by
      apply tsum_congr
      intro m
      exact (hsummand m).symm
    _ = ∏ f ∈ G.edgeFinset, ∑' k : ℕ, g f k := hf.2.symm
    _ = (beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g) := by
      have hedge : ∀ f : Sym2 V,
          (∑' k : ℕ, g f k) =
            (if f = e.1 then beta * J f else 1) * Real.exp (beta * J f) := by
        intro f
        by_cases hfe : f = e.1
        · subst f
          simp only [g, if_pos]
          exact tsum_nat_mul_wEdge beta J e.1
        · rw [Real.exp_eq_exp_ℝ]
          simpa [g, hfe, wEdge] using
            (congrFun (NormedSpace.exp_eq_tsum_div ( 𝔸 := ℝ)) (beta * J f)).symm
      simp_rw [hedge]
      rw [Finset.prod_mul_distrib]
      have hindicator :
          (∏ f ∈ G.edgeFinset, if f = e.1 then beta * J f else 1) = beta * J e := by
        simp [e.2]
      rw [hindicator, ← Real.exp_sum]


theorem summable_unrestricted_current_first_moment (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (e : ↑G.edgeFinset) :
    Summable (fun m : EdgeCurrent G =>
      (m e : ℝ) * weight G beta J (ofEdgeFun G m)) := by
  let g : Sym2 V → ℕ → ℝ := fun f k =>
    if f = e.1 then (k : ℝ) * wEdge beta J f k else wEdge beta J f k
  have hg : ∀ f, Summable (g f) := by
    intro f
    by_cases hfe : f = e.1
    · subst f
      simp only [g, if_pos]
      exact summable_nat_mul_wEdge beta J e.1
    · simp only [g, hfe]
      exact (summable_norm_wEdge beta J f).of_norm
  have hgnn : ∀ f k, 0 ≤ g f k := by
    intro f k
    simp only [g]
    split
    · exact mul_nonneg (Nat.cast_nonneg _) <|
        div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ f)) _) (Nat.cast_nonneg _)
    · exact div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ f)) _) (Nat.cast_nonneg _)
  have hf := (prod_tsum_fubini g hg hgnn G.edgeFinset).1
  refine hf.congr (fun m => ?_)
  rw [weight_ofEdgeFun]
  calc
    (∏ i : ↑G.edgeFinset, g i.1 (m i)) =
        ∏ i : ↑G.edgeFinset,
          (if e = i then (m i : ℝ) else 1) * wEdge beta J i.1 (m i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [g]
      by_cases hie : e = i
      · subst i
        simp
      · have hval : i.1 ≠ e.1 := fun h => hie (Subtype.ext h.symm)
        simp [hie, hval]
    _ = (∏ i : ↑G.edgeFinset, if e = i then (m i : ℝ) else 1) *
        ∏ i : ↑G.edgeFinset, wEdge beta J i.1 (m i) :=
      Finset.prod_mul_distrib
    _ = (m e : ℝ) * ∏ i : ↑G.edgeFinset, wEdge beta J i.1 (m i) := by
      rw [Fintype.prod_ite_eq]
    _ = (m e : ℝ) *
        ∏ i : ↑G.edgeFinset, (beta * J i.1) ^ (m i) / (m i).factorial := by
      rfl


theorem unrestricted_current_tail_le (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (e : ↑G.edgeFinset)
    (K : ℕ) (hK : 0 < K) :
    (∑' m : EdgeCurrent G,
        if K ≤ m e then weight G beta J (ofEdgeFun G m) else 0) ≤
      ((beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) / K := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if K ≤ m e then weight G beta J (ofEdgeFun G m) else 0
  let major : EdgeCurrent G → ℝ := fun m =>
    ((K : ℝ)⁻¹) * ((m e : ℝ) * weight G beta J (ofEdgeFun G m))
  have hweight_nonneg : ∀ m : EdgeCurrent G, 0 ≤ weight G beta J (ofEdgeFun G m) := by
    intro m
    unfold weight
    exact Finset.prod_nonneg fun f _ =>
      div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ f)) _) (Nat.cast_nonneg _)
  have hmomentSummable : Summable (fun m : EdgeCurrent G =>
      (m e : ℝ) * weight G beta J (ofEdgeFun G m)) :=
    summable_unrestricted_current_first_moment G beta J hbeta hJ e
  have hmajor : Summable major := hmomentSummable.mul_left ((K : ℝ)⁻¹)
  have htail : Summable tail := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hmajor
    · simp only [tail]
      split <;> simp [hweight_nonneg]
    · simp only [tail, major]
      by_cases hm : K ≤ m e
      · rw [if_pos hm]
        have hcast : (K : ℝ) ≤ m e := Nat.cast_le.2 hm
        have hKreal : (0 : ℝ) < K := Nat.cast_pos.2 hK
        calc
          weight G beta J (ofEdgeFun G m) = 1 * weight G beta J (ofEdgeFun G m) := by ring
          _ ≤ ((K : ℝ)⁻¹ * (m e : ℝ)) * weight G beta J (ofEdgeFun G m) := by
            exact mul_le_mul_of_nonneg_right ((one_le_inv_mul₀ hKreal).2 hcast)
              (hweight_nonneg m)
          _ = (K : ℝ)⁻¹ * ((m e : ℝ) * weight G beta J (ofEdgeFun G m)) := by ring
      · rw [if_neg hm]
        exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (hweight_nonneg m))
  calc
    (∑' m : EdgeCurrent G,
        if K ≤ m e then weight G beta J (ofEdgeFun G m) else 0) = ∑' m, tail m := rfl
    _ ≤ ∑' m, major m := htail.tsum_le_tsum (fun m => by
      simp only [tail, major]
      by_cases hm : K ≤ m e
      · rw [if_pos hm]
        have hcast : (K : ℝ) ≤ m e := Nat.cast_le.2 hm
        have hKreal : (0 : ℝ) < K := Nat.cast_pos.2 hK
        calc
          weight G beta J (ofEdgeFun G m) = 1 * weight G beta J (ofEdgeFun G m) := by ring
          _ ≤ ((K : ℝ)⁻¹ * (m e : ℝ)) * weight G beta J (ofEdgeFun G m) := by
            exact mul_le_mul_of_nonneg_right ((one_le_inv_mul₀ hKreal).2 hcast)
              (hweight_nonneg m)
          _ = (K : ℝ)⁻¹ * ((m e : ℝ) * weight G beta J (ofEdgeFun G m)) := by ring
      · rw [if_neg hm]
        exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (hweight_nonneg m))) hmajor
    _ = (K : ℝ)⁻¹ * ((beta * J e) *
        Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) := by
      rw [show (∑' m, major m) = (K : ℝ)⁻¹ *
          ∑' m : EdgeCurrent G, (m e : ℝ) * weight G beta J (ofEdgeFun G m) by
        exact hmomentSummable.tsum_mul_left ((K : ℝ)⁻¹)]
      rw [unrestricted_current_first_moment G beta J hbeta hJ e]
    _ = ((beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) / K := by
      rw [div_eq_mul_inv]
      ring


theorem sourcelessCurrentMeasure_edge_tail_le (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (e : ↑G.edgeFinset)
    (K : ℕ) (hK : 0 < K) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal
        (((beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) / K) := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if K ≤ m e then weight G beta J (ofEdgeFun G m) else 0
  have hweight_nonneg : ∀ m : EdgeCurrent G, 0 ≤ weight G beta J (ofEdgeFun G m) := by
    intro m
    unfold weight
    exact Finset.prod_nonneg fun f _ =>
      div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ f)) _) (Nat.cast_nonneg _)
  have htail_nonneg : ∀ m, 0 ≤ tail m := by
    intro m
    simp only [tail]
    split <;> simp [hweight_nonneg]
  have htailSummable : Summable tail := by
    refine Summable.of_nonneg_of_le htail_nonneg (fun m => ?_)
      (summable_norm_weight_ofEdgeFun G beta J).of_norm
    simp only [tail]
    split
    · exact le_rfl
    · exact hweight_nonneg m
  have hden : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (currentSum G beta J ∅) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_currentSum_empty G beta J hbeta hJ)
  have hinv : (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 hden
  have hpoint : ∀ m : EdgeCurrent G,
      {m : EdgeCurrent G | K ≤ m e}.indicator
          (sourcelessCurrentPMF G beta J hbeta hJ) m ≤ ENNReal.ofReal (tail m) := by
    intro m
    by_cases hm : K ≤ m e
    · rw [Set.indicator_of_mem (show m ∈ {m : EdgeCurrent G | K ≤ m e} from hm)]
      rw [sourcelessCurrentPMF, currentPMF_apply]
      simp only [tail, hm, if_true]
      calc
        currentRawMass G beta J ∅ m * (ENNReal.ofReal (currentSum G beta J ∅))⁻¹ ≤
            currentRawMass G beta J ∅ m * 1 :=
          mul_le_mul_of_nonneg_left hinv zero_le
        _ = currentRawMass G beta J ∅ m := mul_one _
        _ ≤ ENNReal.ofReal (weight G beta J (ofEdgeFun G m)) := by
          unfold currentRawMass
          by_cases hsrc : sources G (ofEdgeFun G m) = ∅
          · simp [hsrc]
          · simp [hsrc]
    · rw [Set.indicator_of_notMem (show m ∉ {m : EdgeCurrent G | K ≤ m e} from hm)]
      simp [tail, hm]
  change (sourcelessCurrentPMF G beta J hbeta hJ).toMeasure {m | K ≤ m e} ≤ _
  rw [PMF.toMeasure_apply_eq_tsum]
  calc
    (∑' m : EdgeCurrent G,
        {m : EdgeCurrent G | K ≤ m e}.indicator
          (sourcelessCurrentPMF G beta J hbeta hJ) m) ≤
        ∑' m : EdgeCurrent G, ENNReal.ofReal (tail m) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (∑' m : EdgeCurrent G, tail m) :=
      (ENNReal.ofReal_tsum_of_nonneg htail_nonneg htailSummable).symm
    _ ≤ ENNReal.ofReal
        (((beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) / K) := by
      apply ENNReal.ofReal_le_ofReal
      exact unrestricted_current_tail_le G beta J hbeta hJ e K hK


theorem sourcelessCurrentMeasure_edge_tail_le_of_total_coupling
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (C : ℝ)
    (hC : ∑ g ∈ G.edgeFinset, beta * J g ≤ C)
    (e : ↑G.edgeFinset) (K : ℕ) (hK : 0 < K) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal ((C * Real.exp C) / K) := by
  calc
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
        ENNReal.ofReal
          (((beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g)) / K) :=
      sourcelessCurrentMeasure_edge_tail_le G beta J hbeta hJ e K hK
    _ ≤ ENNReal.ofReal ((C * Real.exp C) / K) := by
      apply ENNReal.ofReal_le_ofReal
      have hedge : beta * J e ≤ ∑ g ∈ G.edgeFinset, beta * J g := by
        exact Finset.single_le_sum (fun g _ => mul_nonneg hbeta (hJ g)) e.2
      have hedgeC : beta * J e ≤ C := hedge.trans hC
      have hexp : Real.exp (∑ g ∈ G.edgeFinset, beta * J g) ≤ Real.exp C :=
        Real.exp_le_exp.mpr hC
      have hCnonneg : 0 ≤ C :=
        (mul_nonneg hbeta (hJ e.1)).trans hedgeC
      have hnum : (beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g) ≤
          C * Real.exp C := by
        calc
          (beta * J e) * Real.exp (∑ g ∈ G.edgeFinset, beta * J g) ≤
              C * Real.exp (∑ g ∈ G.edgeFinset, beta * J g) :=
            mul_le_mul_of_nonneg_right hedgeC (Real.exp_pos _).le
          _ ≤ C * Real.exp C := mul_le_mul_of_nonneg_left hexp hCnonneg
      exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg K)


theorem sourcelessCurrentMeasure_finite_edges_tail_le_of_total_coupling
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (C : ℝ)
    (hC : ∑ g ∈ G.edgeFinset, beta * J g ≤ C)
    (S : Finset (↑G.edgeFinset)) (K : ℕ) (hK : 0 < K) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
        {m | ∃ e ∈ S, K ≤ m e} ≤
      S.card * ENNReal.ofReal ((C * Real.exp C) / K) := by
  let μ : Measure (EdgeCurrent G) :=
    sourcelessCurrentMeasure G beta J hbeta hJ
  let B : ℝ≥0∞ := ENNReal.ofReal ((C * Real.exp C) / K)
  have hevent : {m : EdgeCurrent G | ∃ e ∈ S, K ≤ m e} =
      ⋃ e ∈ S, {m : EdgeCurrent G | K ≤ m e} := by
    ext m
    simp
  change μ {m | ∃ e ∈ S, K ≤ m e} ≤ S.card * B
  rw [hevent]
  calc
    μ (⋃ e ∈ S, {m : EdgeCurrent G | K ≤ m e}) ≤
        ∑ e ∈ S, μ {m : EdgeCurrent G | K ≤ m e} :=
      measure_biUnion_finset_le S (fun e => {m : EdgeCurrent G | K ≤ m e})
    _ ≤ ∑ _e ∈ S, B := by
      apply Finset.sum_le_sum
      intro e he
      exact sourcelessCurrentMeasure_edge_tail_le_of_total_coupling
        G beta J hbeta hJ C hC e K hK
    _ = S.card * B := by simp

end StatMech.FrontierB
