/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.BoundaryCurrentParity
import Code.FrontierB.FiniteBoundarySourceLaw










open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def boundarySourceParityAllowed (interior internalSources : Finset V)
    (H : Finset (Sym2 V)) : Prop :=
  H ⊆ G.edgeFinset ∧
    sources G (edgeIndicatorCurrent H) ∩ interior = internalSources

noncomputable def boundarySourceParityRawMass (beta : ℝ)
    (interior internalSources : Finset V)
    (H : Finset (Sym2 V)) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal
    (if boundarySourceParityAllowed G interior internalSources H then
      Real.tanh beta ^ H.card else 0)

noncomputable def boundarySourceParityPartition (beta : ℝ)
    (interior internalSources : Finset V) : ℝ := by
  classical
  exact ∑ H : Finset (Sym2 V),
    if boundarySourceParityAllowed G interior internalSources H then
      Real.tanh beta ^ H.card else 0

theorem tsum_boundarySourceCurrentRawMass_fixedParity
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior internalSources : Finset V)
    (H : Finset (Sym2 V)) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
          interior internalSources m else 0) =
      boundarySourceParityRawMass G beta interior internalSources H *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  by_cases hH : H ⊆ G.edgeFinset
  · by_cases hsrc :
        sources G (edgeIndicatorCurrent H) ∩ interior = internalSources
    · let f : EdgeCurrent G → ℝ := fun m ↦
        if currentParitySupport G m = H then
          weight G beta (fun _ ↦ 1) (ofEdgeFun G m) else 0
      have hf_nonneg : ∀ m, 0 ≤ f m := by
        intro m
        simp only [f]
        split
        · exact acw_weight_nonneg G beta (fun _ ↦ 1)
            hbeta (fun _ ↦ zero_le_one) _
        · exact le_rfl
      have hf_summable : Summable f := by
        refine Summable.of_nonneg_of_le hf_nonneg (fun m ↦ ?_)
          (summable_norm_weight_ofEdgeFun G beta (fun _ ↦ 1)).of_norm
        simp only [f]
        split
        · exact le_rfl
        · exact acw_weight_nonneg G beta (fun _ ↦ 1)
            hbeta (fun _ ↦ zero_le_one) _
      calc
        (∑' m : EdgeCurrent G,
            if currentParitySupport G m = H then
              boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
                interior internalSources m else 0) =
            ∑' m : EdgeCurrent G, ENNReal.ofReal (f m) := by
          apply tsum_congr
          intro m
          by_cases hm : currentParitySupport G m = H
          · have hsource :
                sources G (ofEdgeFun G m) ∩ interior = internalSources := by
              rw [sources_eq_sources_currentParitySupport G m, hm]
              exact hsrc
            simp [boundarySourceCurrentRawMass, f, hm, hsource]
          · simp [f, hm]
        _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) :=
          (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_summable).symm
        _ = ENNReal.ofReal
              (Real.cosh beta ^ G.edgeFinset.card *
                Real.tanh beta ^ H.card) := by
          apply congrArg ENNReal.ofReal
          exact fixedParity_weight_tsum_closed G beta hbeta H hH
        _ = boundarySourceParityRawMass G beta interior internalSources H *
              ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp [boundarySourceParityRawMass,
            boundarySourceParityAllowed, hH, hsrc, mul_comm]
    · have hzero : ∀ m : EdgeCurrent G,
          (if currentParitySupport G m = H then
            boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
              interior internalSources m else 0) = 0 := by
        intro m
        by_cases hm : currentParitySupport G m = H
        · have hsource :
              sources G (ofEdgeFun G m) ∩ interior ≠ internalSources := by
            rw [sources_eq_sources_currentParitySupport G m, hm]
            exact hsrc
          simp [boundarySourceCurrentRawMass, hm, hsource]
        · simp [hm]
      simp_rw [hzero]
      simp [boundarySourceParityRawMass,
        boundarySourceParityAllowed, hH, hsrc]
  · have hne : ∀ m : EdgeCurrent G, currentParitySupport G m ≠ H := by
      intro m hm
      apply hH
      rw [← hm]
      exact currentParitySupport_subset G m
    simp_rw [if_neg (hne _)]
    simp [boundarySourceParityRawMass,
      boundarySourceParityAllowed, hH]

theorem boundarySourceCurrentSum_eq_parityPartition
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior internalSources : Finset V) :
    ENNReal.ofReal
        (boundarySourceCurrentSum G beta (fun _ ↦ 1)
          interior internalSources) =
      ENNReal.ofReal
          (boundarySourceParityPartition G beta interior internalSources) *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  rw [← tsum_boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
    hbeta (fun _ ↦ zero_le_one) interior internalSources]
  let p : EdgeCurrent G → Finset (Sym2 V) := currentParitySupport G
  have hfiber := ENNReal.tsum_fiberwise
    (boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
      interior internalSources) p
  rw [tsum_fintype] at hfiber
  rw [← hfiber]
  simp_rw [show ∀ H : Finset (Sym2 V),
      (∑' b : ↑(p ⁻¹' {H}),
        boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
          interior internalSources b.1) =
      ∑' m : EdgeCurrent G,
        if currentParitySupport G m = H then
          boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
            interior internalSources m else 0 by
    intro H
    rw [tsum_subtype]
    apply tsum_congr
    intro m
    by_cases hm : currentParitySupport G m = H
    · simp [p, hm]
    · simp [p, hm]]
  simp_rw [tsum_boundarySourceCurrentRawMass_fixedParity
    G beta hbeta interior internalSources]
  rw [← Finset.sum_mul]
  unfold boundarySourceParityRawMass boundarySourceParityPartition
  rw [← ENNReal.ofReal_sum_of_nonneg]
  intro H hH
  split
  · exact pow_nonneg (tanh_nonneg_of_nonneg hbeta) _
  · exact le_rfl

noncomputable def boundarySourceParityPMF
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources) : PMF (Finset (Sym2 V)) :=
  PMF.map (currentParitySupport G)
    (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta
      (fun _ ↦ zero_le_one) interior internalSources hpos)

theorem boundarySourceParityPMF_apply
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources)
    (H : Finset (Sym2 V)) :
    boundarySourceParityPMF G beta hbeta interior internalSources hpos H =
      boundarySourceParityRawMass G beta interior internalSources H *
        (ENNReal.ofReal
          (boundarySourceParityPartition G beta
            interior internalSources))⁻¹ := by
  rw [boundarySourceParityPMF, PMF.map_apply]
  simp_rw [boundarySourceCurrentPMF_apply]
  let Z := ENNReal.ofReal
    (boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources)
  calc
    (∑' m : EdgeCurrent G,
        if H = currentParitySupport G m then
          boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
            interior internalSources m * Z⁻¹ else 0) =
        (∑' m : EdgeCurrent G,
          if currentParitySupport G m = H then
            boundarySourceCurrentRawMass G beta (fun _ ↦ 1)
              interior internalSources m else 0) * Z⁻¹ := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro m
      by_cases hm : currentParitySupport G m = H
      · simp [hm]
      · have hm' : H ≠ currentParitySupport G m := Ne.symm hm
        simp [hm, hm']
    _ = boundarySourceParityRawMass G beta interior internalSources H *
          ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) * Z⁻¹ := by
      rw [tsum_boundarySourceCurrentRawMass_fixedParity
        G beta hbeta interior internalSources H]
    _ = boundarySourceParityRawMass G beta interior internalSources H *
          (ENNReal.ofReal
            (boundarySourceParityPartition G beta
              interior internalSources))⁻¹ := by
      have hc0 : ENNReal.ofReal
          (Real.cosh beta ^ G.edgeFinset.card) ≠ 0 :=
        (ENNReal.ofReal_pos.2 (by positivity)).ne'
      have hcT : ENNReal.ofReal
          (Real.cosh beta ^ G.edgeFinset.card) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      dsimp [Z]
      rw [boundarySourceCurrentSum_eq_parityPartition
        G beta hbeta interior internalSources]
      change _ * _ * (_ * _)⁻¹ = _
      rw [ENNReal.mul_inv (Or.inr hcT)
        (Or.inl ENNReal.ofReal_ne_top)]
      calc
        boundarySourceParityRawMass G beta interior internalSources H *
              ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
            ((ENNReal.ofReal
              (boundarySourceParityPartition G beta
                interior internalSources))⁻¹ *
              (ENNReal.ofReal
                (Real.cosh beta ^ G.edgeFinset.card))⁻¹) =
            boundarySourceParityRawMass G beta interior internalSources H *
              (ENNReal.ofReal
                (boundarySourceParityPartition G beta
                  interior internalSources))⁻¹ *
                (ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
                  (ENNReal.ofReal
                    (Real.cosh beta ^ G.edgeFinset.card))⁻¹) := by
          ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hcT, mul_one]

theorem boundarySourceCurrentPMF_apply_eq_parity_factor
    (beta : ℝ) (hbeta : 0 < beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources)
    (m : EdgeCurrent G) :
    boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le
        (fun _ ↦ zero_le_one) interior internalSources hpos m =
      boundarySourceParityPMF G beta hbeta.le
          interior internalSources hpos (currentParitySupport G m) *
        parityCurrentPMF G beta hbeta (currentParitySupport G m) m := by
  let H := currentParitySupport G m
  have hH : H ⊆ G.edgeFinset := currentParitySupport_subset G m
  rw [boundarySourceCurrentPMF_apply, boundarySourceParityPMF_apply,
    parityCurrentPMF_apply]
  by_cases hsrc :
      sources G (ofEdgeFun G m) ∩ interior = internalSources
  · have hallowed :
        boundarySourceParityAllowed G interior internalSources H := by
      exact ⟨hH, by
        rw [← sources_eq_sources_currentParitySupport G m]
        exact hsrc⟩
    have hkernel : 0 ≤ parityCurrentKernel G beta H m := by
      unfold parityCurrentKernel
      exact Finset.prod_nonneg fun e _ ↦
        parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) (m e)
    have htanh : 0 ≤ Real.tanh beta ^ H.card :=
      pow_nonneg (tanh_nonneg_of_nonneg hbeta.le) _
    have hcosh : 0 ≤ Real.cosh beta ^ G.edgeFinset.card := by
      positivity
    have hw : ENNReal.ofReal
          (weight G beta (fun _ ↦ 1) (ofEdgeFun G m)) =
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) *
          ENNReal.ofReal (Real.tanh beta ^ H.card) *
            ENNReal.ofReal (parityCurrentKernel G beta H m) := by
      rw [weight_eq_parityFiberMass_mul_kernel G beta hbeta H hH m rfl,
        parityFiberMass_closed G beta hbeta.le H hH,
        ENNReal.ofReal_mul (mul_nonneg hcosh htanh),
        ENNReal.ofReal_mul hcosh]
    let c : ℝ≥0∞ := ENNReal.ofReal
      (Real.cosh beta ^ G.edgeFinset.card)
    let t : ℝ≥0∞ := ENNReal.ofReal (Real.tanh beta ^ H.card)
    let p : ℝ≥0∞ := ENNReal.ofReal
      (boundarySourceParityPartition G beta interior internalSources)
    let k : ℝ≥0∞ := ENNReal.ofReal
      (parityCurrentKernel G beta H m)
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    simp only [boundarySourceCurrentRawMass, hsrc, if_true,
      boundarySourceParityRawMass, hallowed, H]
    rw [hw, boundarySourceCurrentSum_eq_parityPartition
      G beta hbeta.le interior internalSources]
    change c * t * k * (p * c)⁻¹ = t * p⁻¹ * k
    rw [ENNReal.mul_inv (Or.inr hcTop) (Or.inl ENNReal.ofReal_ne_top)]
    calc
      c * t * k * (p⁻¹ * c⁻¹) =
          (c * c⁻¹) * (t * p⁻¹ * k) := by ac_rfl
      _ = t * p⁻¹ * k := by
        rw [ENNReal.mul_inv_cancel hc0 hcTop, one_mul]
  · have hnotAllowed :
        ¬ boundarySourceParityAllowed G interior internalSources H := by
      intro ha
      apply hsrc
      rw [sources_eq_sources_currentParitySupport G m]
      exact ha.2
    have hraw : boundarySourceParityRawMass G beta interior
        internalSources (currentParitySupport G m) = 0 := by
      simp [boundarySourceParityRawMass, H, hnotAllowed]
    rw [hraw]
    simp [boundarySourceCurrentRawMass, hsrc]

theorem boundarySourceCurrentPMF_eq_parity_bind
    (beta : ℝ) (hbeta : 0 < beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources) :
    boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le
        (fun _ ↦ zero_le_one) interior internalSources hpos =
      (boundarySourceParityPMF G beta hbeta.le
        interior internalSources hpos).bind
          (parityCurrentPMF G beta hbeta) := by
  apply PMF.ext
  intro m
  rw [PMF.bind_apply,
    boundarySourceCurrentPMF_apply_eq_parity_factor
      G beta hbeta interior internalSources hpos m]
  symm
  rw [tsum_eq_single (currentParitySupport G m)]
  intro H hne
  by_cases hH : H ⊆ G.edgeFinset
  · have hk : parityCurrentKernel G beta H m = 0 :=
      parityCurrentKernel_eq_zero_of_support_ne
        G beta H hH m (Ne.symm hne)
    rw [parityCurrentPMF_apply]
    simp [hk]
  · rw [boundarySourceParityPMF_apply]
    simp [boundarySourceParityRawMass,
      boundarySourceParityAllowed, hH]

theorem boundarySourceCurrentFiniteMarginal_eq_localParity_bind
    (beta : ℝ) (hbeta : 0 < beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources)
    (S : Finset G.edgeFinset) :
    PMF.map (restrictCurrent S)
        (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le
          (fun _ ↦ zero_le_one) interior internalSources hpos) =
      (PMF.map (restrictParity G S)
        (boundarySourceParityPMF G beta hbeta.le
          interior internalSources hpos)).bind
            (finiteParityPMF S beta hbeta) := by
  rw [boundarySourceCurrentPMF_eq_parity_bind
    G beta hbeta interior internalSources hpos, PMF.map_bind]
  rw [PMF.bind_map]
  congr 1
  funext H
  rw [parityCurrentPMF_map_restrictCurrent G beta hbeta H S]
  rfl

theorem summable_two_pow_mul_parityEdgeKernel
    (beta : ℝ) (odd : Bool) :
    Summable (fun k : ℕ ↦
      (2 : ℝ) ^ k * parityEdgeKernel beta odd k) := by
  cases odd
  · refine ((summable_parityCurrentTerm_filter (2 * beta) Even).div_const
      (Real.cosh beta)).congr (fun k ↦ ?_)
    by_cases hk : Even k
    · simp [parityEdgeKernel, conditionalCurrentTerm,
        parityCurrentTerm, hk, mul_pow]
      ring
    · simp [parityEdgeKernel, hk]
  · refine ((summable_parityCurrentTerm_filter (2 * beta) Odd).div_const
      (Real.sinh beta)).congr (fun k ↦ ?_)
    by_cases hk : Odd k
    · simp [parityEdgeKernel, conditionalCurrentTerm,
        parityCurrentTerm, hk, mul_pow]
      ring
    · simp [parityEdgeKernel, hk]

theorem tsum_two_pow_mul_parityEdgeKernel
    (beta : ℝ) (odd : Bool) :
    (∑' k : ℕ, (2 : ℝ) ^ k * parityEdgeKernel beta odd k) =
      if odd then Real.sinh (2 * beta) / Real.sinh beta
      else Real.cosh (2 * beta) / Real.cosh beta := by
  cases odd
  · simp only [Bool.false_eq_true, if_false]
    rw [show (∑' k : ℕ,
        (2 : ℝ) ^ k * parityEdgeKernel beta false k) =
        ∑' k : ℕ,
          (if Even k then parityCurrentTerm (2 * beta) k else 0) /
            Real.cosh beta by
      apply tsum_congr
      intro k
      by_cases hk : Even k
      · simp [parityEdgeKernel, conditionalCurrentTerm,
          parityCurrentTerm, hk, mul_pow]
        ring
      · simp [parityEdgeKernel, hk]]
    rw [tsum_div_const, tsum_parityCurrentTerm_even]
  · rw [if_pos rfl]
    rw [show (∑' k : ℕ,
        (2 : ℝ) ^ k * parityEdgeKernel beta true k) =
        ∑' k : ℕ,
          (if Odd k then parityCurrentTerm (2 * beta) k else 0) /
            Real.sinh beta by
      apply tsum_congr
      intro k
      by_cases hk : Odd k
      · simp [parityEdgeKernel, conditionalCurrentTerm,
          parityCurrentTerm, hk, mul_pow]
        ring
      · simp [parityEdgeKernel, hk]]
    rw [tsum_div_const, tsum_parityCurrentTerm_odd]

theorem tsum_two_pow_mul_parityEdgeKernel_le
    (beta : ℝ) (hbeta : 0 < beta) (odd : Bool) :
    (∑' k : ℕ, (2 : ℝ) ^ k * parityEdgeKernel beta odd k) ≤
      2 * Real.exp beta := by
  rw [tsum_two_pow_mul_parityEdgeKernel beta odd]
  have hcoshPos : 0 < Real.cosh beta := Real.cosh_pos beta
  have hsinhPos : 0 < Real.sinh beta := Real.sinh_pos_iff.mpr hbeta
  have hsinhNonneg : 0 ≤ Real.sinh beta := hsinhPos.le
  have hcoshExp : Real.cosh beta ≤ Real.exp beta := by
    nlinarith [Real.exp_sub_cosh beta]
  cases odd
  · simp only [Bool.false_eq_true, if_false]
    apply (div_le_iff₀ hcoshPos).2
    rw [Real.cosh_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq beta]
  · change Real.sinh (2 * beta) / Real.sinh beta ≤
      2 * Real.exp beta
    rw [Real.sinh_two_mul]
    calc
      (2 * Real.sinh beta * Real.cosh beta) / Real.sinh beta =
          2 * Real.cosh beta := by field_simp [hsinhPos.ne']
      _ ≤ 2 * Real.exp beta :=
        mul_le_mul_of_nonneg_left hcoshExp (by norm_num)

theorem tsum_parityEdgeKernel_tail_le
    (beta : ℝ) (hbeta : 0 < beta) (odd : Bool) (K : ℕ) :
    (∑' k : ℕ,
      if K ≤ k then parityEdgeKernel beta odd k else 0) ≤
      2 * Real.exp beta / (2 : ℝ) ^ K := by
  let major := fun k : ℕ ↦
    ((2 : ℝ) ^ K)⁻¹ *
      ((2 : ℝ) ^ k * parityEdgeKernel beta odd k)
  have htailNonneg : ∀ k,
      0 ≤ if K ≤ k then parityEdgeKernel beta odd k else 0 := by
    intro k
    split
    · exact parityEdgeKernel_nonneg beta hbeta odd k
    · exact le_rfl
  have hmajorSummable : Summable major :=
    (summable_two_pow_mul_parityEdgeKernel beta odd).mul_left _
  have hpoint : ∀ k,
      (if K ≤ k then parityEdgeKernel beta odd k else 0) ≤ major k := by
    intro k
    by_cases hk : K ≤ k
    · rw [if_pos hk]
      have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) hk
      have hkernel := parityEdgeKernel_nonneg beta hbeta odd k
      dsimp only [major]
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith
    · rw [if_neg hk]
      exact mul_nonneg (inv_nonneg.2 (by positivity))
        (mul_nonneg (by positivity)
          (parityEdgeKernel_nonneg beta hbeta odd k))
  calc
    (∑' k : ℕ,
        if K ≤ k then parityEdgeKernel beta odd k else 0) ≤
        ∑' k, major k :=
      (Summable.of_nonneg_of_le htailNonneg hpoint hmajorSummable).tsum_le_tsum
        hpoint hmajorSummable
    _ = ((2 : ℝ) ^ K)⁻¹ *
        (∑' k : ℕ,
          (2 : ℝ) ^ k * parityEdgeKernel beta odd k) := by
      exact tsum_mul_left
    _ ≤ ((2 : ℝ) ^ K)⁻¹ * (2 * Real.exp beta) :=
      mul_le_mul_of_nonneg_left
        (tsum_two_pow_mul_parityEdgeKernel_le beta hbeta odd)
        (inv_nonneg.2 (by positivity))
    _ = 2 * Real.exp beta / (2 : ℝ) ^ K := by field_simp

theorem summable_parityCurrentKernel_edge_tail
    (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (e : G.edgeFinset) (K : ℕ) :
    Summable (fun m : EdgeCurrent G ↦
      if K ≤ m e then parityCurrentKernel G beta H m else 0) := by
  have hnonneg : ∀ m : EdgeCurrent G,
      0 ≤ if K ≤ m e then parityCurrentKernel G beta H m else 0 := by
    intro m
    split
    · unfold parityCurrentKernel
      exact Finset.prod_nonneg fun f _ ↦
        parityEdgeKernel_nonneg beta hbeta (f.1 ∈ H) (m f)
    · exact le_rfl
  apply Summable.of_nonneg_of_le hnonneg
    (fun m ↦ ?_) (summable_parityCurrentKernel G beta hbeta H)
  by_cases hm : K ≤ m e
  · rw [if_pos hm]
  · rw [if_neg hm]
    unfold parityCurrentKernel
    exact Finset.prod_nonneg fun f _ ↦
      parityEdgeKernel_nonneg beta hbeta (f.1 ∈ H) (m f)

theorem tsum_parityCurrentKernel_edge_tail
    (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (e : G.edgeFinset) (K : ℕ) :
    (∑' m : EdgeCurrent G,
      if K ≤ m e then parityCurrentKernel G beta H m else 0) =
      ∑' k : ℕ,
        if K ≤ k then parityEdgeKernel beta (e.1 ∈ H) k else 0 := by
  let g : Sym2 V → ℕ → ℝ := fun f k ↦
    if f = e.1 then
      if K ≤ k then parityEdgeKernel beta (f ∈ H) k else 0
    else parityEdgeKernel beta (f ∈ H) k
  have hg : ∀ f, Summable (g f) := by
    intro f
    by_cases hfe : f = e.1
    · subst f
      apply Summable.of_nonneg_of_le
        (fun k ↦ by
          simp only [g, if_pos rfl]
          split
          · exact parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) k
          · exact le_rfl)
        (fun k ↦ by
          simp only [g, if_pos rfl]
          split
          · exact le_rfl
          · exact parityEdgeKernel_nonneg beta hbeta (e.1 ∈ H) k)
        (summable_parityEdgeKernel beta (e.1 ∈ H))
    · simpa only [g, if_neg hfe] using
        summable_parityEdgeKernel beta (f ∈ H)
  have hgnn : ∀ f k, 0 ≤ g f k := by
    intro f k
    by_cases hfe : f = e.1
    · rw [show g f k = if K ≤ k then
          parityEdgeKernel beta (f ∈ H) k else 0 by
        simp [g, hfe]]
      split
      · exact parityEdgeKernel_nonneg beta hbeta _ _
      · exact le_rfl
    · rw [show g f k = parityEdgeKernel beta (f ∈ H) k by
        simp [g, hfe]]
      exact parityEdgeKernel_nonneg beta hbeta _ _
  have hfubini := prod_tsum_fubini g hg hgnn G.edgeFinset
  have hterm : ∀ m : EdgeCurrent G,
      (∏ f : G.edgeFinset, g f.1 (m f)) =
        if K ≤ m e then parityCurrentKernel G beta H m else 0 := by
    intro m
    by_cases hm : K ≤ m e
    · rw [if_pos hm]
      unfold parityCurrentKernel
      apply Fintype.prod_congr
      intro f
      by_cases hfe : f = e
      · subst f
        simp [g, hm]
      · have hval : f.1 ≠ e.1 := fun h ↦ hfe (Subtype.ext h)
        simp [g, hval]
    · rw [if_neg hm]
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [g, hm]
  calc
    (∑' m : EdgeCurrent G,
        if K ≤ m e then parityCurrentKernel G beta H m else 0) =
        ∑' m : EdgeCurrent G, ∏ f : G.edgeFinset, g f.1 (m f) := by
      apply tsum_congr
      intro m
      exact (hterm m).symm
    _ = ∏ f ∈ G.edgeFinset, ∑' k : ℕ, g f k := hfubini.2.symm
    _ = ∑' k : ℕ,
        if K ≤ k then parityEdgeKernel beta (e.1 ∈ H) k else 0 := by
      rw [Finset.prod_eq_single e.1]
      · simp [g]
      · intro f hf hfe
        simp only [g, if_neg hfe]
        exact tsum_parityEdgeKernel beta hbeta (f ∈ H)
      · exact fun hnot ↦ (hnot e.2).elim

theorem parityCurrentPMF_edge_exponential_tail_le
    (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (e : G.edgeFinset) (K : ℕ) :
    (parityCurrentPMF G beta hbeta H).toMeasure {m | K ≤ m e} ≤
      ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K) := by
  rw [PMF.toMeasure_apply_eq_tsum]
  let tail : EdgeCurrent G → ℝ := fun m ↦
    if K ≤ m e then parityCurrentKernel G beta H m else 0
  have htailNonneg : ∀ m, 0 ≤ tail m := by
    intro m
    dsimp only [tail]
    split
    · unfold parityCurrentKernel
      exact Finset.prod_nonneg fun f _ ↦
        parityEdgeKernel_nonneg beta hbeta (f.1 ∈ H) (m f)
    · exact le_rfl
  have htailSummable : Summable tail :=
    summable_parityCurrentKernel_edge_tail G beta hbeta H e K
  calc
    (∑' m : EdgeCurrent G,
        {m | K ≤ m e}.indicator
          (parityCurrentPMF G beta hbeta H) m) =
        ∑' m : EdgeCurrent G, ENNReal.ofReal (tail m) := by
      apply tsum_congr
      intro m
      by_cases hm : K ≤ m e
      · rw [Set.indicator_of_mem
          (show m ∈ {m : EdgeCurrent G | K ≤ m e} from hm),
          parityCurrentPMF_apply]
        simp [tail, hm]
      · rw [Set.indicator_of_notMem
          (show m ∉ {m : EdgeCurrent G | K ≤ m e} from hm)]
        simp [tail, hm]
    _ = ENNReal.ofReal (∑' m : EdgeCurrent G, tail m) :=
      (ENNReal.ofReal_tsum_of_nonneg htailNonneg htailSummable).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K) := by
      apply ENNReal.ofReal_le_ofReal
      rw [tsum_parityCurrentKernel_edge_tail G beta hbeta H e K]
      exact tsum_parityEdgeKernel_tail_le beta hbeta (e.1 ∈ H) K

theorem parityCurrentPMF_edge_inverse_tail_le
    (beta : ℝ) (hbeta : 0 < beta)
    (H : Finset (Sym2 V)) (e : G.edgeFinset)
    (K : ℕ) (hK : 0 < K) :
    (parityCurrentPMF G beta hbeta H).toMeasure {m | K ≤ m e} ≤
      ENNReal.ofReal (2 * Real.exp beta / K) := by
  calc
    (parityCurrentPMF G beta hbeta H).toMeasure {m | K ≤ m e} ≤
        ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K) :=
      parityCurrentPMF_edge_exponential_tail_le
        G beta hbeta H e K
    _ ≤ ENNReal.ofReal (2 * Real.exp beta / K) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (Real.exp_pos beta).le)
        (Nat.cast_pos.2 hK)
      exact_mod_cast nat_le_two_pow K

theorem boundarySourceCurrentPMF_edge_exponential_tail_le
    (beta : ℝ) (hbeta : 0 < beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources)
    (e : G.edgeFinset) (K : ℕ) :
    (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le
      (fun _ ↦ zero_le_one) interior internalSources hpos).toMeasure
        {m | K ≤ m e} ≤
      ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K) := by
  rw [boundarySourceCurrentPMF_eq_parity_bind
      G beta hbeta interior internalSources hpos]
  rw [PMF.toMeasure_bind_apply
    (boundarySourceParityPMF G beta hbeta.le
      interior internalSources hpos)
    (parityCurrentPMF G beta hbeta)
    {m : EdgeCurrent G | K ≤ m e} MeasurableSet.of_discrete]
  let q := boundarySourceParityPMF G beta hbeta.le
    interior internalSources hpos
  let C := ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K)
  calc
    (∑' H, q H *
        (parityCurrentPMF G beta hbeta H).toMeasure {m | K ≤ m e}) ≤
        ∑' H, q H * C := by
      apply ENNReal.tsum_le_tsum
      intro H
      exact mul_le_mul_right
        (parityCurrentPMF_edge_exponential_tail_le
          G beta hbeta H e K) (q H)
    _ = C := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem boundarySourceCurrentPMF_edge_inverse_tail_le
    (beta : ℝ) (hbeta : 0 < beta)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta (fun _ ↦ 1)
      interior internalSources)
    (e : G.edgeFinset) (K : ℕ) (hK : 0 < K) :
    (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le
      (fun _ ↦ zero_le_one) interior internalSources hpos).toMeasure
        {m | K ≤ m e} ≤
      ENNReal.ofReal (2 * Real.exp beta / K) := by
  calc
    (boundarySourceCurrentPMF G beta (fun _ ↦ 1) hbeta.le
      (fun _ ↦ zero_le_one) interior internalSources hpos).toMeasure
        {m | K ≤ m e} ≤
        ENNReal.ofReal (2 * Real.exp beta / (2 : ℝ) ^ K) :=
      boundarySourceCurrentPMF_edge_exponential_tail_le
        G beta hbeta interior internalSources hpos e K
    _ ≤ ENNReal.ofReal (2 * Real.exp beta / K) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (Real.exp_pos beta).le)
        (Nat.cast_pos.2 hK)
      exact_mod_cast nat_le_two_pow K

end StatMech.FrontierB
