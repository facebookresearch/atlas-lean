/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.FiniteCurrentParity
import Code.Sharpness.BackboneSupportLexParityBridge

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def currentParitySupport (m : EdgeCurrent G) : Finset (Sym2 V) :=
  (G.edgeFinset.attach.filter fun e => Odd (m e)).map
    ⟨Subtype.val, Subtype.val_injective⟩

omit [DecidableEq V] in
@[simp] theorem mem_currentParitySupport (m : EdgeCurrent G)
    (e : G.edgeFinset) : e.1 ∈ currentParitySupport G m ↔ Odd (m e) := by
  simp [currentParitySupport]

omit [DecidableEq V] in
theorem currentParitySupport_subset (m : EdgeCurrent G) :
    currentParitySupport G m ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 he
  exact f.2

theorem currentParitySupport_eq_iff
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) :
    currentParitySupport G m = H ↔
      ∀ e : G.edgeFinset, if e.1 ∈ H then Odd (m e) else Even (m e) := by
  constructor
  · intro h e
    by_cases he : e.1 ∈ H
    · simp only [if_pos he]
      rw [← h] at he
      simpa using he
    · simp only [if_neg he]
      rw [← Nat.not_odd_iff_even]
      intro ho
      apply he
      rw [← h]
      simpa using ho
  · intro h
    ext e
    by_cases heG : e ∈ G.edgeFinset
    · let es : G.edgeFinset := ⟨e, heG⟩
      change (es.1 ∈ currentParitySupport G m ↔ e ∈ H)
      rw [mem_currentParitySupport]
      by_cases heH : e ∈ H
      · have ho : Odd (m es) := by simpa [es, heH] using h es
        simp [heH, ho]
      · have hev : Even (m es) := by simpa [es, heH] using h es
        rw [← Nat.not_odd_iff_even] at hev
        simp [heH, hev]
    · have heH : e ∉ H := fun he => heG (hH he)
      constructor
      · intro he
        exact (heG (currentParitySupport_subset G m he)).elim
      · intro he
        exact (heH he).elim

theorem sources_eq_sources_currentParitySupport (m : EdgeCurrent G) :
    sources G (ofEdgeFun G m) =
      sources G (edgeIndicatorCurrent (currentParitySupport G m)) := by
  ext v
  rw [Sharpness.mem_sources, Sharpness.mem_sources,
    incidentFlux_edgeIndicatorCurrent G (currentParitySupport G m)
      (currentParitySupport_subset G m)]
  let E := G.edgeFinset.filter (fun e => v ∈ e)
  have hfilter :
      E.filter (fun e => Odd (ofEdgeFun G m e)) =
        (currentParitySupport G m).filter (fun e => v ∈ e) := by
    ext e
    simp only [E, Finset.mem_filter]
    constructor
    · rintro ⟨⟨heG, hev⟩, ho⟩
      exact ⟨mem_currentParitySupport G m ⟨e, heG⟩ |>.2 (by
        simpa [ofEdgeFun, heG] using ho), hev⟩
    · rintro ⟨he, hev⟩
      have heG := currentParitySupport_subset G m he
      exact ⟨⟨heG, hev⟩, by
        simpa [ofEdgeFun, heG] using
          (mem_currentParitySupport G m ⟨e, heG⟩ |>.1 he)⟩
  unfold Sharpness.incidentFlux incCount
  rw [Finset.odd_sum_iff_odd_card_odd]
  exact iff_of_eq (congrArg Odd (congrArg Finset.card hfilter))

theorem sources_empty_iff_currentParitySupport_even (m : EdgeCurrent G) :
    sources G (ofEdgeFun G m) = ∅ ↔
      IsEvenSubgraph (currentParitySupport G m) := by
  rw [sources_eq_sources_currentParitySupport G m]
  constructor
  · intro hsrc v
    have hv : v ∉ sources G (edgeIndicatorCurrent (currentParitySupport G m)) := by
      rw [hsrc]
      simp
    rw [Sharpness.mem_sources,
      incidentFlux_edgeIndicatorCurrent G (currentParitySupport G m)
        (currentParitySupport_subset G m)] at hv
    exact Nat.not_odd_iff_even.1 hv
  · intro heven
    apply sources_edgeIndicatorCurrent G (currentParitySupport G m) ∅
      (currentParitySupport_subset G m)
    exact (hasOddBoundary_empty _).2 heven

noncomputable def parityCurrentTerm (beta : ℝ) (k : ℕ) : ℝ :=
  beta ^ k / k.factorial

theorem summable_parityCurrentTerm (beta : ℝ) :
    Summable (parityCurrentTerm beta) := by
  have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) beta
  exact h.congr (fun k => by simp [parityCurrentTerm, div_eq_inv_mul, mul_comm])

theorem summable_parityCurrentTerm_filter (beta : ℝ) (Q : ℕ → Prop)
    [DecidablePred Q] :
    Summable (fun k => if Q k then parityCurrentTerm beta k else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_parityCurrentTerm beta).norm
  split <;> simp

theorem tsum_parityCurrentTerm_even (beta : ℝ) :
    (∑' k : ℕ, if Even k then parityCurrentTerm beta k else 0) =
      Real.cosh beta := by
  rw [← shb_evenCurrentSeries_eq_cosh]
  unfold shbEvenCurrentSeries
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun k : ↑(Function.support (fun n : ℕ =>
      parityCurrentTerm beta (2 * n))) => 2 * k.1)
  · intro a b hab
    apply Subtype.ext
    dsimp at hab ⊢
    omega
  · intro k hk
    simp only [Function.mem_support] at hk
    have he : Even k := by
      by_contra hne
      rw [if_neg hne] at hk
      exact hk rfl
    obtain ⟨n, rfl⟩ := he
    have hterm : parityCurrentTerm beta (n + n) ≠ 0 := by simpa using hk
    exact ⟨⟨n, by simpa [two_mul] using hterm⟩, by simp [two_mul]⟩
  · intro k
    simp [parityCurrentTerm]

theorem tsum_parityCurrentTerm_odd (beta : ℝ) :
    (∑' k : ℕ, if Odd k then parityCurrentTerm beta k else 0) =
      Real.sinh beta := by
  rw [← shb_oddCurrentSeries_eq_sinh]
  unfold shbOddCurrentSeries
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun k : ↑(Function.support (fun n : ℕ =>
      parityCurrentTerm beta (2 * n + 1))) => 2 * k.1 + 1)
  · intro a b hab
    apply Subtype.ext
    dsimp at hab ⊢
    omega
  · intro k hk
    simp only [Function.mem_support] at hk
    have ho : Odd k := by
      by_contra hne
      rw [if_neg hne] at hk
      exact hk rfl
    obtain ⟨n, hn⟩ := ho
    refine ⟨⟨n, ?_⟩, hn.symm⟩
    simpa [hn, parityCurrentTerm] using hk
  · intro k
    simp [parityCurrentTerm]

theorem fixedParity_weight_tsum
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        weight G beta (fun _ => 1) (ofEdgeFun G m) else 0) =
      ∏ e ∈ G.edgeFinset,
        if e ∈ H then Real.sinh beta else Real.cosh beta := by
  let g : Sym2 V → ℕ → ℝ := fun e k =>
    if (if e ∈ H then Odd k else Even k) then
      parityCurrentTerm beta k else 0
  have hgsum : ∀ e, Summable (g e) := by
    intro e
    unfold g
    exact summable_parityCurrentTerm_filter beta _
  have hgnn : ∀ e k, 0 ≤ g e k := by
    intro e k
    by_cases h : if e ∈ H then Odd k else Even k
    · simp only [g, h, if_true]
      exact div_nonneg (pow_nonneg hbeta _) (by positivity)
    · simp [g, h]
  calc
    (∑' m : EdgeCurrent G,
        if currentParitySupport G m = H then
          weight G beta (fun _ => 1) (ofEdgeFun G m) else 0) =
        ∑' m : EdgeCurrent G, ∏ e : G.edgeFinset, g e.1 (m e) := by
      apply tsum_congr
      intro m
      rw [weight_ofEdgeFun]
      by_cases hs : currentParitySupport G m = H
      · rw [if_pos hs]
        have hall := (currentParitySupport_eq_iff G H hH m).mp hs
        apply Finset.prod_congr rfl
        intro e _
        simp only [g]
        rw [if_pos (hall e)]
        simp [parityCurrentTerm]
      · rw [if_neg hs]
        have hall : ¬ ∀ e : G.edgeFinset,
            if e.1 ∈ H then Odd (m e) else Even (m e) :=
          fun h => hs ((currentParitySupport_eq_iff G H hH m).mpr h)
        push Not at hall
        obtain ⟨e, he⟩ := hall
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        simp only [g]
        rw [if_neg he]
    _ = ∏ e ∈ G.edgeFinset, ∑' k : ℕ, g e k :=
      (prod_tsum_fubini g hgsum hgnn G.edgeFinset).2.symm
    _ = ∏ e ∈ G.edgeFinset,
          if e ∈ H then Real.sinh beta else Real.cosh beta := by
      apply Finset.prod_congr rfl
      intro e heG
      by_cases heH : e ∈ H
      · simp only [g, heH, if_true]
        exact tsum_parityCurrentTerm_odd beta
      · simp only [g, heH, if_false]
        exact tsum_parityCurrentTerm_even beta

theorem fixedParity_weight_tsum_closed
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        weight G beta (fun _ => 1) (ofEdgeFun G m) else 0) =
      Real.cosh beta ^ G.edgeFinset.card * Real.tanh beta ^ H.card := by
  rw [fixedParity_weight_tsum G beta hbeta H hH, Finset.prod_ite]
  have hfilter : G.edgeFinset.filter (fun e => e ∈ H) = H := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact fun he => he.2
    · exact fun he => ⟨hH he, he⟩
  have hcomplement : G.edgeFinset.filter (fun e => e ∉ H) =
      G.edgeFinset \ H := by
    ext e
    simp
  rw [hfilter, hcomplement]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset hH]
  have hsinh : Real.sinh beta = Real.cosh beta * Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [hsinh, mul_pow]
  calc
    Real.cosh beta ^ H.card * Real.tanh beta ^ H.card *
          Real.cosh beta ^ (G.edgeFinset.card - H.card) =
        (Real.cosh beta ^ H.card *
          Real.cosh beta ^ (G.edgeFinset.card - H.card)) *
            Real.tanh beta ^ H.card := by ring
    _ = Real.cosh beta ^ G.edgeFinset.card * Real.tanh beta ^ H.card := by
      rw [← pow_add, Nat.add_sub_of_le (Finset.card_le_card hH)]

theorem currentSum_unit_eq_parityPartition (beta : ℝ) :
    currentSum G beta (fun _ => 1) ∅ =
      Real.cosh beta ^ G.edgeFinset.card * freeParityPartition G beta := by
  have h := partitionJ_eq_currentSum G beta (fun _ => 1)
  rw [partitionJ_unit_highTemp] at h
  rw [mul_assoc] at h
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := by positivity
  exact (mul_left_cancel₀ htwo h).symm

theorem tsum_currentRawMass_fixedParity
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (H : Finset (Sym2 V)) :
    (∑' m : EdgeCurrent G,
      if currentParitySupport G m = H then
        currentRawMass G beta (fun _ => 1) ∅ m else 0) =
      freeParityRawMass G beta H *
        ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
  by_cases hH : H ⊆ G.edgeFinset
  · by_cases heven : IsEvenSubgraph H
    · let f : EdgeCurrent G → ℝ := fun m =>
        if currentParitySupport G m = H then
          weight G beta (fun _ => 1) (ofEdgeFun G m) else 0
      have hf_nonneg : ∀ m, 0 ≤ f m := by
        intro m
        simp only [f]
        split
        · exact Ising.acw_weight_nonneg G beta (fun _ => 1)
            hbeta (fun _ => zero_le_one) _
        · exact le_rfl
      have hf_summable : Summable f := by
        refine Summable.of_nonneg_of_le hf_nonneg (fun m => ?_)
          (summable_norm_weight_ofEdgeFun G beta (fun _ => 1)).of_norm
        simp only [f]
        split
        · exact le_rfl
        · exact Ising.acw_weight_nonneg G beta (fun _ => 1)
            hbeta (fun _ => zero_le_one) _
      calc
        (∑' m : EdgeCurrent G,
            if currentParitySupport G m = H then
              currentRawMass G beta (fun _ => 1) ∅ m else 0) =
            ∑' m : EdgeCurrent G, ENNReal.ofReal (f m) := by
          apply tsum_congr
          intro m
          by_cases hm : currentParitySupport G m = H
          · have hsrc : sources G (ofEdgeFun G m) = ∅ :=
              (sources_empty_iff_currentParitySupport_even G m).2
                (hm.symm ▸ heven)
            simp [f, hm, currentRawMass, hsrc]
          · simp [f, hm]
        _ = ENNReal.ofReal (∑' m : EdgeCurrent G, f m) :=
          (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_summable).symm
        _ = ENNReal.ofReal
              (Real.cosh beta ^ G.edgeFinset.card * Real.tanh beta ^ H.card) := by
          apply congrArg ENNReal.ofReal
          exact fixedParity_weight_tsum_closed G beta hbeta H hH
        _ = freeParityRawMass G beta H *
              ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp only [freeParityRawMass, hH, heven, and_self, if_true]
          rw [mul_comm]
    · have hzero : ∀ m : EdgeCurrent G,
          (if currentParitySupport G m = H then
            currentRawMass G beta (fun _ => 1) ∅ m else 0) = 0 := by
        intro m
        by_cases hm : currentParitySupport G m = H
        · have hsrc : sources G (ofEdgeFun G m) ≠ ∅ := by
            intro hsrc
            apply heven
            rw [← hm]
            exact (sources_empty_iff_currentParitySupport_even G m).1 hsrc
          simp [hm, currentRawMass, hsrc]
        · simp [hm]
      rw [show (∑' m : EdgeCurrent G,
          if currentParitySupport G m = H then
            currentRawMass G beta (fun _ => 1) ∅ m else 0) = 0 by
        simp_rw [hzero]
        simp]
      simp [freeParityRawMass, hH, heven]
  · have hzero : ∀ m : EdgeCurrent G,
        (if currentParitySupport G m = H then
          currentRawMass G beta (fun _ => 1) ∅ m else 0) = 0 := by
      intro m
      have hm : currentParitySupport G m ≠ H := by
        intro hm
        apply hH
        rw [← hm]
        exact currentParitySupport_subset G m
      simp [hm]
    rw [show (∑' m : EdgeCurrent G,
        if currentParitySupport G m = H then
          currentRawMass G beta (fun _ => 1) ∅ m else 0) = 0 by
      simp_rw [hzero]
      simp]
    simp [freeParityRawMass, hH]

theorem sourcelessCurrentPMF_map_currentParitySupport
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PMF.map (currentParitySupport G)
        (sourcelessCurrentPMF G beta (fun _ => 1) hbeta
          (fun _ => zero_le_one)) =
      freeParityPMF G beta hbeta := by
  apply PMF.ext
  intro H
  rw [PMF.map_apply, freeParityPMF_apply]
  simp only [sourcelessCurrentPMF]
  simp_rw [currentPMF_apply]
  let Z : ℝ≥0∞ := ENNReal.ofReal (currentSum G beta (fun _ => 1) ∅)
  calc
    (∑' a : EdgeCurrent G,
        if H = currentParitySupport G a then
          currentRawMass G beta (fun _ => 1) ∅ a * Z⁻¹ else 0) =
        (∑' a : EdgeCurrent G,
          if currentParitySupport G a = H then
            currentRawMass G beta (fun _ => 1) ∅ a else 0) * Z⁻¹ := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro a
      by_cases ha : currentParitySupport G a = H
      · simp [ha]
      · simp [ha, Ne.symm ha]
    _ = freeParityRawMass G beta H *
          ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card) * Z⁻¹ := by
      rw [tsum_currentRawMass_fixedParity G beta hbeta H]
    _ = freeParityRawMass G beta H *
          (ENNReal.ofReal (freeParityPartition G beta))⁻¹ := by
      let c : ℝ≥0∞ := ENNReal.ofReal (Real.cosh beta ^ G.edgeFinset.card)
      let p : ℝ≥0∞ := ENNReal.ofReal (freeParityPartition G beta)
      have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
      have hp0 : p ≠ 0 :=
        (ENNReal.ofReal_pos.2 (freeParityPartition_pos G beta hbeta)).ne'
      have hpTop : p ≠ ⊤ := ENNReal.ofReal_ne_top
      have hZ : Z = c * p := by
        simp only [Z, c, p]
        rw [currentSum_unit_eq_parityPartition G beta,
          ENNReal.ofReal_mul (by positivity)]
      rw [hZ, ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
      calc
        freeParityRawMass G beta H * c * (c⁻¹ * p⁻¹) =
            freeParityRawMass G beta H * (c * c⁻¹) * p⁻¹ := by
          ac_rfl
        _ = freeParityRawMass G beta H * p⁻¹ := by
          rw [ENNReal.mul_inv_cancel hc0 hcTop, mul_one]

theorem sourcelessCurrentMeasure_map_currentParitySupport
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map (currentParitySupport G)
        (sourcelessCurrentMeasure G beta (fun _ => 1) hbeta
          (fun _ => zero_le_one) : Measure (EdgeCurrent G)) =
      (freeParityMeasure G beta hbeta :
        Measure (Finset (Sym2 V))) := by
  change Measure.map (currentParitySupport G)
      (sourcelessCurrentPMF G beta (fun _ => 1) hbeta
        (fun _ => zero_le_one)).toMeasure =
    (freeParityPMF G beta hbeta).toMeasure
  rw [PMF.toMeasure_map _ _ Measurable.of_discrete,
    sourcelessCurrentPMF_map_currentParitySupport G beta hbeta]

theorem sourcelessCurrentMeasure_parityAvoid_eq_spinExpectation
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    (sourcelessCurrentMeasure G beta (fun _ => 1) hbeta
      (fun _ => zero_le_one) : Measure (EdgeCurrent G))
        {m | Disjoint (currentParitySupport G m) F} =
      ENNReal.ofReal
        (((∑ s : ConfigSpace V,
            boltzmannJ G beta (fun _ => 1) s *
              Real.exp (-beta * edgeSpinSum F s)) /
            partitionJ G beta (fun _ => 1)) *
          Real.cosh beta ^ F.card) := by
  let mu : Measure (EdgeCurrent G) :=
    sourcelessCurrentMeasure G beta (fun _ => 1) hbeta
      (fun _ => zero_le_one)
  calc
    mu {m | Disjoint (currentParitySupport G m) F} =
        Measure.map (currentParitySupport G) mu {H | Disjoint H F} := by
      rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
      rfl
    _ = (freeParityMeasure G beta hbeta :
          Measure (Finset (Sym2 V))) {H | Disjoint H F} := by
      rw [sourcelessCurrentMeasure_map_currentParitySupport G beta hbeta]
    _ = _ := freeParityMeasure_avoid_eq_spinExpectation G beta hbeta F hF

end StatMech.FrontierB
