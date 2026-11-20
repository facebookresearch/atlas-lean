/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationMiddleBalanced
import Code.Onsager.DecorationFormalClose
import Code.Onsager.DecorationEdgeClassification








namespace StatMech.Onsager

open BigOperators

def ons_secondDifferenceFactor (k : ℕ) : ℂ :=
  (2 : ℂ) ^ k - 2 + (0 : ℂ) ^ k

noncomputable def ons_decFormalSecondDifference
    {L : ℕ} (series : MvPowerSeries (ons_DecEdge L) ℂ)
    (edge : ons_DecEdge L) : MvPowerSeries (ons_DecEdge L) ℂ :=
  fun m ↦ ons_secondDifferenceFactor (m edge) *
    MvPowerSeries.coeff m series

theorem ons_mvMonomialValue_scaleDecEdgeWeight
    {L : ℕ} (weight : ons_DecEdge L → ℂ)
    (edge : ons_DecEdge L) (t : ℂ)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_mvMonomialValue (ons_scaleDecEdgeWeight weight edge t) m =
      t ^ m edge * ons_mvMonomialValue weight m := by
  exact ons_finsuppProd_scaleDecEdgeWeight m weight edge t

theorem ons_MvSeriesEvalSummable_decFormalSecondDifference
    {L : ℕ} (series : MvPowerSeries (ons_DecEdge L) ℂ)
    (edge : ons_DecEdge L) (weight : ons_DecEdge L → ℂ)
    (h2 : ons_MvSeriesEvalSummable series
      (ons_scaleDecEdgeWeight weight edge 2))
    (h1 : ons_MvSeriesEvalSummable series weight)
    (h0 : ons_MvSeriesEvalSummable series
      (ons_scaleDecEdgeWeight weight edge 0)) :
    ons_MvSeriesEvalSummable
      (ons_decFormalSecondDifference series edge) weight := by
  let term2 := fun m : ons_DecEdge L →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series *
      ons_mvMonomialValue (ons_scaleDecEdgeWeight weight edge 2) m‖
  let term1 := fun m : ons_DecEdge L →₀ ℕ ↦
    2 * ‖MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖
  let term0 := fun m : ons_DecEdge L →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series *
      ons_mvMonomialValue (ons_scaleDecEdgeWeight weight edge 0) m‖
  have hs2 : Summable term2 := h2
  have hs1 : Summable term1 := h1.mul_left 2
  have hs0 : Summable term0 := h0
  apply Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _)
    (fun m ↦ ?_) ((hs2.add hs1).add hs0)
  unfold ons_decFormalSecondDifference ons_secondDifferenceFactor
  simp only [MvPowerSeries.coeff_apply, term2, term1, term0]
  rw [ons_mvMonomialValue_scaleDecEdgeWeight,
    ons_mvMonomialValue_scaleDecEdgeWeight]
  let A := (2 : ℂ) ^ m edge * MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m
  let B := 2 * (MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m)
  let C := (0 : ℂ) ^ m edge * MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m
  calc
    ‖((2 : ℂ) ^ m edge - 2 + (0 : ℂ) ^ m edge) *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖ ≤
      ‖A‖ + ‖B‖ + ‖C‖ := by
      have heq : ((2 : ℂ) ^ m edge - 2 + (0 : ℂ) ^ m edge) *
          MvPowerSeries.coeff m series * ons_mvMonomialValue weight m =
        A - B + C := by simp only [A, B, C]; ring
      rw [heq]
      nlinarith [norm_add_le (A - B) C, norm_sub_le A B]
    _ = _ := by
      simp only [A, B, C, norm_mul, MvPowerSeries.coeff_apply]
      norm_num
      ring

theorem ons_mvSeriesEval_decFormalSecondDifference
    {L : ℕ} (series : MvPowerSeries (ons_DecEdge L) ℂ)
    (edge : ons_DecEdge L) (weight : ons_DecEdge L → ℂ)
    (h2 : ons_MvSeriesEvalSummable series
      (ons_scaleDecEdgeWeight weight edge 2))
    (h1 : ons_MvSeriesEvalSummable series weight)
    (h0 : ons_MvSeriesEvalSummable series
      (ons_scaleDecEdgeWeight weight edge 0)) :
    ons_mvSeriesEval (ons_decFormalSecondDifference series edge) weight =
      ons_mvSeriesEval series
          (ons_scaleDecEdgeWeight weight edge 2) -
        2 * ons_mvSeriesEval series weight +
        ons_mvSeriesEval series
          (ons_scaleDecEdgeWeight weight edge 0) := by
  let f2 := fun m : ons_DecEdge L →₀ ℕ ↦
    MvPowerSeries.coeff m series *
      ons_mvMonomialValue (ons_scaleDecEdgeWeight weight edge 2) m
  let f1 := fun m : ons_DecEdge L →₀ ℕ ↦
    MvPowerSeries.coeff m series * ons_mvMonomialValue weight m
  let f0 := fun m : ons_DecEdge L →₀ ℕ ↦
    MvPowerSeries.coeff m series *
      ons_mvMonomialValue (ons_scaleDecEdgeWeight weight edge 0) m
  have hs2 : Summable f2 := Summable.of_norm h2
  have hs1 : Summable f1 := Summable.of_norm h1
  have hs0 : Summable f0 := Summable.of_norm h0
  unfold ons_mvSeriesEval ons_decFormalSecondDifference
  simp only [MvPowerSeries.coeff_apply]
  have hterm : ∀ m : ons_DecEdge L →₀ ℕ,
      ons_secondDifferenceFactor (m edge) *
          MvPowerSeries.coeff m series * ons_mvMonomialValue weight m =
        f2 m - 2 * f1 m + f0 m := by
    intro m
    rw [show f2 m = (2 : ℂ) ^ m edge *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m by
      simp only [f2, ons_mvMonomialValue_scaleDecEdgeWeight]; ring,
      show f0 m = (0 : ℂ) ^ m edge *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m by
      simp only [f0, ons_mvMonomialValue_scaleDecEdgeWeight]; ring]
    simp only [f1, ons_secondDifferenceFactor]
    ring
  change (∑' m, ons_secondDifferenceFactor (m edge) *
      MvPowerSeries.coeff m series * ons_mvMonomialValue weight m) =
    (∑' m, f2 m) - 2 * (∑' m, f1 m) + ∑' m, f0 m
  rw [tsum_congr hterm, (hs2.sub (hs1.mul_left 2)).tsum_add hs0,
    hs2.tsum_sub (hs1.mul_left 2), tsum_mul_left]

theorem norm_ons_scaleDecEdgeWeight_le
    {L : ℕ} (weight : ons_DecEdge L → ℂ)
    (edge : ons_DecEdge L) (t : ℂ) (r : ℝ)
    (hr0 : 0 ≤ r) (ht : ‖t‖ ≤ 2)
    (hall : ∀ f, ‖weight f‖ ≤ r) (f : ons_DecEdge L) :
    ‖ons_scaleDecEdgeWeight weight edge t f‖ ≤ 2 * r := by
  unfold ons_scaleDecEdgeWeight
  split
  · rw [norm_mul]
    nlinarith [mul_le_mul ht (hall f) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  · nlinarith [hall f]

theorem ons_detWalkRoot_scaleDecEdge_secondDifference_small
    (L : ℕ) [Fact (2 < L)]
    (decWeight : ons_DecEdge L → ℂ) (a b : Fin 2)
    (edge : ons_DecEdge L)
    (hedge : edge ∈ (ons_decGraph L).edgeFinset)
    (r : ℝ) (hr : 0 < r) (hrOne : 2 * r ≤ 1)
    (hall : ∀ f, ‖decWeight f‖ ≤ r)
    (hsmallCompressed : 2 * r <
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹)
    (hsmallAugmented : 2 * r <
      (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹) :
    ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight edge 2)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) -
      2 * ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L decWeight
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) +
      ons_detWalkRoot
        (ons_KWmatDecorationWeightedPhase L
          (ons_scaleDecEdgeWeight decWeight edge 0)
          ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
  let q : ℝ := 2 * r
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcardCompressed :
      (Fintype.card (ons_Dart L) : ℝ) * q < 1 :=
    ons_card_mul_lt_one_of_Sherman_small q hsmallCompressed
  have hcardAugmented :
      (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) * q < 1 :=
    ons_card_mul_lt_one_of_Sherman_small q hsmallAugmented
  have hscaledBound (selected : ons_DecEdge L) (t : ℂ)
      (ht : ‖t‖ ≤ 2) :
      ∀ f, ‖ons_scaleDecEdgeWeight decWeight selected t f‖ ≤ q := by
    intro f
    exact norm_ons_scaleDecEdgeWeight_le
      decWeight selected t r hr.le ht hall f
  have hentry (selected : ons_DecEdge L) (t : ℂ)
      (ht : ‖t‖ ≤ 2) : ∀ d₂ d₁,
      ‖ons_KWmatDecorationWeightedPhase L
        (ons_scaleDecEdgeWeight decWeight selected t)
        ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d₂ d₁‖ ≤ q := by
    intro d₂ d₁
    exact norm_ons_KWmatDecorationWeightedPhase_entry_le L _ a b q hq
      (fun f ↦ (hscaledBound selected t ht f).trans hrOne)
      (fun d ↦ hscaledBound selected t ht s(d, ons_dartRev L d))
      d₂ d₁
  have hscaleOne (selected : ons_DecEdge L) :
      ons_scaleDecEdgeWeight decWeight selected 1 = decWeight := by
    funext f
    simp [ons_scaleDecEdgeWeight]
  have hcancel (A B : ℂ) :
      A * (1 - 2 * B) - 2 * (A * (1 - B)) +
        A * (1 - 0 * B) = 0 := by
    ring
  rcases ons_decGraph_edge_external_or_chain L edge hedge with
    ⟨d, hd⟩ | ⟨site, i, hi⟩
  · subst edge
    let A := ons_detWalkRoot
      (ons_maskMatrix ({d, ons_dartRev L d} : Finset (ons_Dart L))
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)))
    let B := ∑' s, ons_firstReturnWeight
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b))
      d (ons_dartRev L d) s
    have haff (t : ℂ) (ht : ‖t‖ ≤ 2) :
        ons_detWalkRoot
          (ons_KWmatDecorationWeightedPhase L
            (ons_scaleDecEdgeWeight decWeight
              s(d, ons_dartRev L d) t)
            ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
          A * (1 - t * B) := by
      simpa only [A, B] using
        ons_detWalkRoot_decoration_scaleExternal_affine
          L decWeight a b q hq t d
          (hentry s(d, ons_dartRev L d) t ht)
          hsmallCompressed hcardCompressed
    have haff1 :
        ons_detWalkRoot
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)) =
          A * (1 - B) := by
      simpa only [hscaleOne, one_mul] using haff 1 (by norm_num)
    rw [haff 2 (by norm_num), haff1, haff 0 (by norm_num)]
    exact hcancel A B
  · subst edge
    have hicases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hicases with rfl | rfl | rfl
    · let A := ons_detWalkRoot
        (ons_maskMatrix
          ({(site, 0), ons_dartRev L (site, 0)} : Finset (ons_Dart L))
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)))
      let B := ∑' s, ons_firstReturnWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (site, 0) (ons_dartRev L (site, 0)) s
      have haff (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_detWalkRoot
            (ons_KWmatDecorationWeightedPhase L
              (ons_scaleDecEdgeWeight decWeight
                (ons_decChainEdge site 0) t)
              ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
            A * (1 - t * B) := by
        simpa only [A, B] using
          ons_detWalkRoot_scale_chain_zero_affine L decWeight a b site t
            q hq
            (hentry s((site, 0), ons_dartRev L (site, 0)) t ht)
            hsmallCompressed hcardCompressed
      have haff1 :
          ons_detWalkRoot
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)) =
            A * (1 - B) := by
        simpa only [hscaleOne, one_mul] using haff 1 (by norm_num)
      rw [haff 2 (by norm_num), haff1, haff 0 (by norm_num)]
      exact hcancel A B
    · let lambda : ℂ := (r : ℂ)
      have hlambda : lambda ≠ 0 := by
        dsimp only [lambda]
        exact_mod_cast ne_of_gt hr
      have hlambdaNorm : ‖lambda‖ = r := by
        simp only [lambda, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr]
      have hseam : ∀ f,
          ‖ons_spinSeamDecWeight decWeight a b f‖ ≤ ‖lambda‖ := by
        intro f
        rw [norm_ons_spinSeamDecWeight, hlambdaNorm]
        exact hall f
      have hentryCompressed (t : ℂ) (ht : ‖t‖ ≤ 2) : ∀ x y,
          ‖ons_KWmatDecorationWeightedPhase L
            (ons_spinSeamDecWeight
              (ons_scaleDecEdgeWeight decWeight
                (ons_decChainEdge site 1) t) a b)
            ons_turnRoot 1 1 x y‖ ≤ q := by
        intro x y
        have hbound := norm_ons_KWmatDecorationWeightedPhase_entry_le
          L (ons_spinSeamDecWeight
            (ons_scaleDecEdgeWeight decWeight
              (ons_decChainEdge site 1) t) a b)
          (0 : Fin 2) (0 : Fin 2) q hq
          (fun f ↦ by
            rw [norm_ons_spinSeamDecWeight]
            exact (hscaledBound (ons_decChainEdge site 1) t ht f).trans
              hrOne)
          (fun d ↦ by
            rw [norm_ons_spinSeamDecWeight]
            exact hscaledBound (ons_decChainEdge site 1) t ht
              s(d, ons_dartRev L d)) x y
        simpa [ons_spinPhase] using hbound
      have hentryAugmented (t : ℂ) (ht : ‖t‖ ≤ 2) : ∀ x y,
          ‖ons_decMiddleBalanced L
            (ons_spinSeamDecWeight decWeight a b)
            ons_turnRoot t lambda site x y‖ ≤ q := by
        intro x y
        simpa only [q, hlambdaNorm] using
          norm_ons_decMiddleBalanced_entry_le L
            (ons_spinSeamDecWeight decWeight a b) t lambda hlambda site
            (by rw [hlambdaNorm]; linarith [hrOne]) ht hseam x y
      let A := ons_detWalkRoot
        (ons_maskMatrix
          ({Sum.inr 0, Sum.inr 1} : Finset (ons_Dart L ⊕ Fin 2))
          (ons_decMiddleBalanced L
            (ons_spinSeamDecWeight decWeight a b)
            ons_turnRoot 1 lambda site))
      let B := ∑' s, ons_firstReturnWeight
        (ons_decMiddleBalanced L
          (ons_spinSeamDecWeight decWeight a b)
          ons_turnRoot 1 lambda site)
        (Sum.inr 0) (Sum.inr 1) s
      have haff (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_detWalkRoot
            (ons_KWmatDecorationWeightedPhase L
              (ons_scaleDecEdgeWeight decWeight
                (ons_decChainEdge site 1) t)
              ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
            A * (1 - t * B) := by
        simpa only [A, B] using
          ons_detWalkRoot_scaleMiddle_balanced_affine_of_bounds
            L decWeight a b t lambda hlambda site q q hq hq
            (hentryCompressed t ht) (hentryAugmented t ht)
            hsmallCompressed hsmallAugmented
      have haff1 :
          ons_detWalkRoot
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)) =
            A * (1 - B) := by
        simpa only [hscaleOne, one_mul] using haff 1 (by norm_num)
      rw [haff 2 (by norm_num), haff1, haff 0 (by norm_num)]
      exact hcancel A B
    · let A := ons_detWalkRoot
        (ons_maskMatrix
          ({(site, 3), ons_dartRev L (site, 3)} : Finset (ons_Dart L))
          (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b)))
      let B := ∑' s, ons_firstReturnWeight
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (site, 3) (ons_dartRev L (site, 3)) s
      have haff (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_detWalkRoot
            (ons_KWmatDecorationWeightedPhase L
              (ons_scaleDecEdgeWeight decWeight
                (ons_decChainEdge site 2) t)
              ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
            A * (1 - t * B) := by
        simpa only [A, B] using
          ons_detWalkRoot_scale_chain_two_affine L decWeight a b site t
            q hq
            (hentry s((site, 3), ons_dartRev L (site, 3)) t ht)
            hsmallCompressed hcardCompressed
      have haff1 :
          ons_detWalkRoot
            (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)) =
            A * (1 - B) := by
        simpa only [hscaleOne, one_mul] using haff 1 (by norm_num)
      rw [haff 2 (by norm_num), haff1, haff 0 (by norm_num)]
      exact hcancel A B

theorem ons_degreeFiberCoeff_scale
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : MvPowerSeries E ℂ) (weight : E → ℂ)
    (c : ℂ) (n : ℕ) :
    ons_degreeFiberCoeff series (fun e ↦ c * weight e) n =
      c ^ n * ons_degreeFiberCoeff series weight n := by
  unfold ons_degreeFiberCoeff
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [ons_mvMonomialValue_smul, m.2]
  ring

theorem ons_secondDifferenceFactor_ne_zero
    (k : ℕ) (hk : 2 ≤ k) : ons_secondDifferenceFactor k ≠ 0 := by
  unfold ons_secondDifferenceFactor
  rw [zero_pow (by omega), add_zero, sub_ne_zero]
  intro hfactor
  have hkpos : 0 < k - 1 := by omega
  have hone : (2 : ℂ) ^ (k - 1) = 1 := by
    rw [show k = (k - 1) + 1 by omega, pow_add, pow_one] at hfactor
    apply mul_right_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
    exact hfactor.trans (by ring)
  have hnorm := congrArg norm hone
  have hgt : (1 : ℝ) < 2 ^ (k - 1) :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hkpos)
  norm_num [norm_pow] at hnorm
  exact (ne_of_gt hgt) hnorm

theorem ons_decFormalRoot_coeff_eq_zero_of_repeated_mem
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (m : ons_DecEdge L →₀ ℕ) (edge : ons_DecEdge L)
    (hedge : edge ∈ (ons_decGraph L).edgeFinset)
    (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
  let root := ons_decFormalRoot L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  let second := ons_decFormalSecondDifference root edge
  have hsecond : MvPowerSeries.coeff m second = 0 := by
    apply ons_coeff_eq_zero_of_degreeFiberCoeff second m
    intro weight
    let compressedRadius : ℝ :=
      (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹
    let augmentedRadius : ℝ :=
      (2 * (Fintype.card (ons_Dart L ⊕ Fin 2) : ℝ) ^ 2)⁻¹
    let R : ℝ := min 1 (min compressedRadius augmentedRadius)
    let r : ℝ := R / 4
    let q : ℝ := 2 * r
    let S : ℝ := ∑ e, ‖weight e‖
    let c : ℂ := ((r / (1 + S) : ℝ) : ℂ)
    let base : ons_DecEdge L → ℂ := fun e ↦ c * weight e
    have hcompressedRadius : 0 < compressedRadius := by
      dsimp only [compressedRadius]
      positivity
    have haugmentedRadius : 0 < augmentedRadius := by
      dsimp only [augmentedRadius]
      positivity
    have hR : 0 < R := by
      dsimp only [R]
      exact lt_min (by norm_num) (lt_min hcompressedRadius haugmentedRadius)
    have hRone : R ≤ 1 := by
      dsimp only [R]
      exact min_le_left _ _
    have hRcompressed : R ≤ compressedRadius := by
      exact (min_le_right (1 : ℝ) _).trans (min_le_left _ _)
    have hRaugmented : R ≤ augmentedRadius := by
      exact (min_le_right (1 : ℝ) _).trans (min_le_right _ _)
    have hr : 0 < r := by dsimp only [r]; linarith
    have hq : 0 < q := by dsimp only [q]; linarith
    have hrOne : 2 * r ≤ 1 := by
      dsimp only [r]
      linarith
    have hsmallCompressed : q < compressedRadius := by
      dsimp only [q, r]
      linarith
    have hsmallAugmented : q < augmentedRadius := by
      dsimp only [q, r]
      linarith
    have hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1 := by
      exact ons_card_mul_lt_one_of_Sherman_small q hsmallCompressed
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hden : 0 < 1 + S := by linarith
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact_mod_cast div_ne_zero (ne_of_gt hr) (ne_of_gt hden)
    have hbase : ∀ e, ‖base e‖ ≤ r := by
      intro e
      have he : ‖weight e‖ ≤ S := by
        dsimp only [S]
        exact Finset.single_le_sum (fun f _ ↦ norm_nonneg (weight f))
          (Finset.mem_univ e)
      dsimp only [base, c]
      rw [norm_mul]
      have hnorm : ‖((r / (1 + S) : ℝ) : ℂ)‖ = r / (1 + S) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hr.le hden.le)]
      rw [hnorm, div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith
    have hscaleOne :
        ons_scaleDecEdgeWeight base edge 1 = base := by
      funext e
      simp [ons_scaleDecEdgeWeight]
    have hrootSummable (t : ℂ) (ht : ‖t‖ ≤ 2) :
        ons_MvSeriesEvalSummable root
          (ons_scaleDecEdgeWeight base edge t) := by
      have hbound := norm_ons_scaleDecEdgeWeight_le
        base edge t r hr.le ht hbase
      apply ons_MvSeriesEvalSummable_decFormalRoot L
        (ons_scaleDecEdgeWeight base edge t) a b q hq.le
      · intro e
        exact (hbound e).trans hrOne
      · intro d
        exact hbound s(d, ons_dartRev L d)
      · exact hcard
    have hsumSecond : ons_MvSeriesEvalSummable second base := by
      apply ons_MvSeriesEvalSummable_decFormalSecondDifference
      · exact hrootSummable 2 (by norm_num)
      · simpa only [hscaleOne] using hrootSummable 1 (by norm_num)
      · exact hrootSummable 0 (by norm_num)
    have hzero : ∀ᶠ s : ℂ in nhds 0,
        ons_mvSeriesEval second (fun e ↦ s * base e) = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
        (by norm_num : (0 : ℝ) < 1)] with s hs
      have hs1 : ‖s‖ ≤ 1 := by
        have : ‖s‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using hs
        exact this.le
      let scaled : ons_DecEdge L → ℂ := fun e ↦ s * base e
      have hscaled : ∀ e, ‖scaled e‖ ≤ r := by
        intro e
        dsimp only [scaled]
        rw [norm_mul]
        simpa only [one_mul] using
          mul_le_mul hs1 (hbase e) (norm_nonneg _) (by norm_num)
      have hsum (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_MvSeriesEvalSummable root
            (ons_scaleDecEdgeWeight scaled edge t) := by
        have hbound := norm_ons_scaleDecEdgeWeight_le
          scaled edge t r hr.le ht hscaled
        apply ons_MvSeriesEvalSummable_decFormalRoot L
          (ons_scaleDecEdgeWeight scaled edge t) a b q hq.le
        · intro e
          exact (hbound e).trans hrOne
        · intro d
          exact hbound s(d, ons_dartRev L d)
        · exact hcard
      have heval (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_mvSeriesEval root
              (ons_scaleDecEdgeWeight scaled edge t) =
            ons_detWalkRoot
              (ons_KWmatDecorationWeightedPhase L
                (ons_scaleDecEdgeWeight scaled edge t)
                ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) := by
        have hbound := norm_ons_scaleDecEdgeWeight_le
          scaled edge t r hr.le ht hscaled
        exact ons_mvSeriesEval_decFormalRoot L
          (ons_scaleDecEdgeWeight scaled edge t) a b q hq.le
          (fun e ↦ (hbound e).trans hrOne)
          (fun d ↦ hbound s(d, ons_dartRev L d)) hcard
      have hscaleOneScaled :
          ons_scaleDecEdgeWeight scaled edge 1 = scaled := by
        funext e
        simp [ons_scaleDecEdgeWeight]
      rw [ons_mvSeriesEval_decFormalSecondDifference root edge scaled
        (hsum 2 (by norm_num))
        (by simpa only [hscaleOneScaled] using hsum 1 (by norm_num))
        (hsum 0 (by norm_num))]
      rw [heval 2 (by norm_num)]
      have heval1 : ons_mvSeriesEval root scaled =
          ons_detWalkRoot
            (ons_KWmatDecorationWeightedPhase L scaled ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b)) := by
        simpa only [hscaleOneScaled] using heval 1 (by norm_num)
      rw [heval1, heval 0 (by norm_num)]
      exact ons_detWalkRoot_scaleDecEdge_secondDifference_small
        L scaled a b edge hedge r hr hrOne hscaled
        hsmallCompressed hsmallAugmented
    have hfiber :=
      ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero
        second base hsumSecond hzero (Finsupp.degree m)
    change ons_degreeFiberCoeff second
      (fun e ↦ c * weight e) (Finsupp.degree m) = 0 at hfiber
    rw [ons_degreeFiberCoeff_scale] at hfiber
    exact (mul_eq_zero.mp hfiber).resolve_left (pow_ne_zero _ hc)
  change ons_secondDifferenceFactor (m edge) *
      MvPowerSeries.coeff m root = 0 at hsecond
  exact (mul_eq_zero.mp hsecond).resolve_left
    (ons_secondDifferenceFactor_ne_zero (m edge) hrepeated)

theorem ons_decFormalRoot_coeff_eq_zero_of_repeated
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (m : ons_DecEdge L →₀ ℕ) (edge : ons_DecEdge L)
    (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) = 0 := by
  by_cases hedge : edge ∈ (ons_decGraph L).edgeFinset
  · exact ons_decFormalRoot_coeff_eq_zero_of_repeated_mem
      L a b m edge hedge hrepeated
  · exact ons_decFormalRoot_coeff_eq_zero_of_offGraph
      L a b m edge hedge (by omega)

theorem ons_DecFormalRepeatedEdgeVanishes_proved :
    ons_DecFormalRepeatedEdgeVanishes := by
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  intro a b m edge hedge
  exact ons_decFormalRoot_coeff_eq_zero_of_repeated
    L a b m edge hedge

theorem ons_free_energy
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) :=
  ons_free_energy_of_repeatedEdgeVanishes
    ons_DecFormalRepeatedEdgeVanishes_proved beta hbeta

theorem ons_free_energy_unconditional
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) :=
  ons_free_energy beta hbeta

end StatMech.Onsager
