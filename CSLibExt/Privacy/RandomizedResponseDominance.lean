/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacyKFold
public import CSLibExt.Privacy.HypothesisTesting
import CSLibExt.Privacy.MaxDivergenceDecomposition

/-!
# Randomized-response dominance under adaptive composition

For `0 ≤ eps` and `delta ∈ [0, 1]`, a pair of output laws on a finite type
satisfying the Kairouz-Oh-Viswanath condition `KOVpair` at `(eps, delta)` is the
image of the four-outcome pair `rrR0`, `rrR1` under one channel. Running such
channels stage by stage on independent copies of that pair reproduces a `k`-fold
adaptive composition `kfoldCompose` on a fixed pair of inputs, with channels that
depend on that pair and on the transcript so far. Hence, on `[0, 1]`, the tradeoff
of `k` stages of the four-outcome mechanism lies below the tradeoff of every such
composition, and every `(eps', delta')` guarantee of the former transfers to the
latter.

## Primary references

Kairouz, Oh and Viswanath, *The Composition Theorem for Differential Privacy*
(ICML 2015; arXiv:1311.0776). The one-stage simulation is their Theorem 2.5
(a corollary of Blackwell's comparison of experiments) applied to the pair of
Eqs. (12)-(13) of the supplementary material, Section 5.1, whose privacy region
is that of `(eps, delta)`-DP. The stage-by-stage simulation of an adaptive
composition and the resulting inclusion of privacy regions are Section 5.2 of
the supplementary material (arXiv:1311.0776v4, Section 6.2), with post-processing
(their Theorem 2.4) in the form `tradeoff_postprocess`.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

universe u

/-- Transcripts whose stage outputs are finite types are finite. -/
instance Transcript.instFintype {A : ℕ → Type u} [∀ n, Fintype (A n)] :
    (n : ℕ) → Fintype (Transcript A n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 =>
    letI := Transcript.instFintype (A := A) n
    inferInstanceAs (Fintype (Transcript A n × A n))

/-- Transcripts inherit decidable equality from their stage outputs. -/
instance Transcript.instDecidableEq {A : ℕ → Type u} [∀ n, DecidableEq (A n)] :
    (n : ℕ) → DecidableEq (Transcript A n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n + 1 =>
    letI := Transcript.instDecidableEq (A := A) n
    inferInstanceAs (DecidableEq (Transcript A n × A n))

end CSLibExt.Privacy.DifferentialPrivacy

namespace CSLibExt.Privacy.HypothesisTesting

open CSLibExt.Privacy.DifferentialPrivacy

universe u

/-! ## One stage -/

/-- Kairouz-Oh-Viswanath, Theorem 2.5 with the four-outcome pair of their
supplementary material, Section 5.1: a pair of laws on a finite type satisfying
`KOVpair` at `(eps, delta)` is the image of `rrR0`, `rrR1` under one channel. -/
theorem rr_exists_channel_of_kovpair (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (P Q : PMF Ω) (eps delta : ℝ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta)
    (hδ1 : delta ≤ 1) (hKov : KOVpair Ω P Q eps delta) :
    ∃ T : Fin 4 → PMF Ω,
      (rrR0 eps delta hδ0 hδ1).bind T = P ∧
        (rrR1 eps delta hδ0 hδ1).bind T = Q := by
  have hE1 : (1 : ℝ) ≤ Real.exp eps := Real.one_le_exp hε
  have hev := (kovpair_iff_event_bounds Ω P Q eps delta).mp hKov
  obtain ⟨w0, _⟩ := P.support_nonempty
  have hne : Nonempty Ω := ⟨w0⟩
  have hPQ : CSLibExt.Privacy.MaxDivergenceDecomposition.approxMaxDivLE
      P Q eps delta :=
    fun s => (hev s).1
  have hQP : CSLibExt.Privacy.MaxDivergenceDecomposition.approxMaxDivLE
      Q P eps delta :=
    fun s => (hev s).2
  have hex : ∃ P0 Q0 : PMF Ω,
      CSLibExt.Privacy.MaxDivergenceDecomposition.maxDivLE P0 Q0 eps ∧
        CSLibExt.Privacy.MaxDivergenceDecomposition.maxDivLE Q0 P0 eps ∧
        (∀ w, (1 - delta) * (P0 w).toReal ≤ (P w).toReal) ∧
        (∀ w, (1 - delta) * (Q0 w).toReal ≤ (Q w).toReal) := by
    rcases lt_or_eq_of_le hδ1 with hδlt | hδeq
    · exact MaxDivergenceDecomposition.exists_dominated_pure_pair_of_approxMaxDivLE_both
        P Q eps delta hε hδ0 hδlt hPQ hQP
    · refine ⟨P, P, ?_, ?_, ?_, ?_⟩
      · intro w
        have hx : (0 : ℝ) ≤ (P w).toReal := ENNReal.toReal_nonneg
        have h := mul_le_mul_of_nonneg_right hE1 hx
        simpa using h
      · intro w
        have hx : (0 : ℝ) ≤ (P w).toReal := ENNReal.toReal_nonneg
        have h := mul_le_mul_of_nonneg_right hE1 hx
        simpa using h
      · intro w
        rw [hδeq]
        simp only [sub_self, zero_mul]
        exact ENNReal.toReal_nonneg
      · intro w
        rw [hδeq]
        simp only [sub_self, zero_mul]
        exact ENNReal.toReal_nonneg
  obtain ⟨P0, Q0, hmaxPQ, hmaxQP, hdomP, hdomQ⟩ := hex
  have hsumP : ∑ w, (P w).toReal = 1 := pmf_toReal_sum Ω P
  have hsumQ : ∑ w, (Q w).toReal = 1 := pmf_toReal_sum Ω Q
  have hsumP0 : ∑ w, (P0 w).toReal = 1 := pmf_toReal_sum Ω P0
  have hsumQ0 : ∑ w, (Q0 w).toReal = 1 := pmf_toReal_sum Ω Q0
  have hp0eq : delta = 0 → ∀ w, (P0 w).toReal = (P w).toReal := by
    intro hδ0eq w
    have hle : ∀ i ∈ Finset.univ, (P0 i).toReal ≤ (P i).toReal := by
      intro i _
      have h := hdomP i
      rw [hδ0eq] at h
      simpa using h
    have hsum_eq : ∑ i ∈ Finset.univ, (P0 i).toReal
        = ∑ i ∈ Finset.univ, (P i).toReal := by
      simpa using hsumP0.trans hsumP.symm
    have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq
    exact hall w (Finset.mem_univ w)
  have hq0eq : delta = 0 → ∀ w, (Q0 w).toReal = (Q w).toReal := by
    intro hδ0eq w
    have hle : ∀ i ∈ Finset.univ, (Q0 i).toReal ≤ (Q i).toReal := by
      intro i _
      have h := hdomQ i
      rw [hδ0eq] at h
      simpa using h
    have hsum_eq : ∑ i ∈ Finset.univ, (Q0 i).toReal
        = ∑ i ∈ Finset.univ, (Q i).toReal := by
      simpa using hsumQ0.trans hsumQ.symm
    have hall := (Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq
    exact hall w (Finset.mem_univ w)
  have hpq0eq : Real.exp eps = 1 →
      ∀ w, (P0 w).toReal = (Q0 w).toReal := by
    intro hE1eq w
    have h1 := hmaxPQ w
    have h2 := hmaxQP w
    rw [hE1eq] at h1 h2
    have hle1 : (P0 w).toReal ≤ (Q0 w).toReal := by simpa using h1
    have hle2 : (Q0 w).toReal ≤ (P0 w).toReal := by simpa using h2
    exact le_antisymm hle1 hle2
  set m0 : Ω → ℝ := fun w =>
    (P0 w).toReal + ((P w).toReal - (P0 w).toReal) / delta with hm0def
  set m1 : Ω → ℝ := fun w => (P0 w).toReal +
    ((P0 w).toReal - (Q0 w).toReal) / (Real.exp eps - 1) with hm1def
  set m2 : Ω → ℝ := fun w => (Q0 w).toReal +
    ((Q0 w).toReal - (P0 w).toReal) / (Real.exp eps - 1) with hm2def
  set m3 : Ω → ℝ := fun w =>
    (Q0 w).toReal + ((Q w).toReal - (Q0 w).toReal) / delta with hm3def
  have hm0_nonneg : ∀ w, 0 ≤ m0 w := by
    intro w
    by_cases hδ : delta = 0
    · simp only [hm0def, hδ, div_zero, add_zero]
      exact ENNReal.toReal_nonneg
    · have hδpos : (0 : ℝ) < delta := lt_of_le_of_ne hδ0 (Ne.symm hδ)
      have hnum : (0 : ℝ) ≤ (P w).toReal - (1 - delta) * (P0 w).toReal := by
        linarith [hdomP w]
      have heq : m0 w
          = ((P w).toReal - (1 - delta) * (P0 w).toReal) / delta := by
        simp only [hm0def]
        field_simp
        ring
      rw [heq]
      exact div_nonneg hnum hδpos.le
  have hm3_nonneg : ∀ w, 0 ≤ m3 w := by
    intro w
    by_cases hδ : delta = 0
    · simp only [hm3def, hδ, div_zero, add_zero]
      exact ENNReal.toReal_nonneg
    · have hδpos : (0 : ℝ) < delta := lt_of_le_of_ne hδ0 (Ne.symm hδ)
      have hnum : (0 : ℝ) ≤ (Q w).toReal - (1 - delta) * (Q0 w).toReal := by
        linarith [hdomQ w]
      have heq : m3 w
          = ((Q w).toReal - (1 - delta) * (Q0 w).toReal) / delta := by
        simp only [hm3def]
        field_simp
        ring
      rw [heq]
      exact div_nonneg hnum hδpos.le
  have hm1_nonneg : ∀ w, 0 ≤ m1 w := by
    intro w
    by_cases hE : Real.exp eps = 1
    · simp only [hm1def, hE, sub_self, div_zero, add_zero]
      exact ENNReal.toReal_nonneg
    · have hEgt : (1 : ℝ) < Real.exp eps :=
        lt_of_le_of_ne hE1 (Ne.symm hE)
      have hdenom : (0 : ℝ) < Real.exp eps - 1 := sub_pos.mpr hEgt
      have hne : Real.exp eps - 1 ≠ 0 := sub_ne_zero.mpr hE
      have hnum : (0 : ℝ) ≤ Real.exp eps * (P0 w).toReal - (Q0 w).toReal := by
        linarith [hmaxQP w]
      have heq : m1 w = (Real.exp eps * (P0 w).toReal - (Q0 w).toReal)
          / (Real.exp eps - 1) := by
        simp only [hm1def]
        field_simp
        ring
      rw [heq]
      exact div_nonneg hnum hdenom.le
  have hm2_nonneg : ∀ w, 0 ≤ m2 w := by
    intro w
    by_cases hE : Real.exp eps = 1
    · simp only [hm2def, hE, sub_self, div_zero, add_zero]
      exact ENNReal.toReal_nonneg
    · have hEgt : (1 : ℝ) < Real.exp eps :=
        lt_of_le_of_ne hE1 (Ne.symm hE)
      have hdenom : (0 : ℝ) < Real.exp eps - 1 := sub_pos.mpr hEgt
      have hne : Real.exp eps - 1 ≠ 0 := sub_ne_zero.mpr hE
      have hnum : (0 : ℝ) ≤ Real.exp eps * (Q0 w).toReal - (P0 w).toReal := by
        linarith [hmaxPQ w]
      have heq : m2 w = (Real.exp eps * (Q0 w).toReal - (P0 w).toReal)
          / (Real.exp eps - 1) := by
        simp only [hm2def]
        field_simp
        ring
      rw [heq]
      exact div_nonneg hnum hdenom.le
  have hm0_sum : ∑ w, m0 w = 1 := by
    simp only [hm0def]
    rw [Finset.sum_add_distrib]
    have hdiv : ∑ w, ((P w).toReal - (P0 w).toReal) / delta
        = (∑ w, ((P w).toReal - (P0 w).toReal)) / delta := by
      rw [← Finset.sum_div]
    rw [hdiv]
    have hsub : ∑ w, ((P w).toReal - (P0 w).toReal) = 0 := by
      rw [Finset.sum_sub_distrib, hsumP, hsumP0, sub_self]
    rw [hsub, zero_div, add_zero]
    exact hsumP0
  have hm3_sum : ∑ w, m3 w = 1 := by
    simp only [hm3def]
    rw [Finset.sum_add_distrib]
    have hdiv : ∑ w, ((Q w).toReal - (Q0 w).toReal) / delta
        = (∑ w, ((Q w).toReal - (Q0 w).toReal)) / delta := by
      rw [← Finset.sum_div]
    rw [hdiv]
    have hsub : ∑ w, ((Q w).toReal - (Q0 w).toReal) = 0 := by
      rw [Finset.sum_sub_distrib, hsumQ, hsumQ0, sub_self]
    rw [hsub, zero_div, add_zero]
    exact hsumQ0
  have hm1_sum : ∑ w, m1 w = 1 := by
    simp only [hm1def]
    rw [Finset.sum_add_distrib]
    have hdiv : ∑ w, ((P0 w).toReal - (Q0 w).toReal) / (Real.exp eps - 1)
        = (∑ w, ((P0 w).toReal - (Q0 w).toReal)) / (Real.exp eps - 1) := by
      rw [← Finset.sum_div]
    rw [hdiv]
    have hsub : ∑ w, ((P0 w).toReal - (Q0 w).toReal) = 0 := by
      rw [Finset.sum_sub_distrib, hsumP0, hsumQ0, sub_self]
    rw [hsub, zero_div, add_zero]
    exact hsumP0
  have hm2_sum : ∑ w, m2 w = 1 := by
    simp only [hm2def]
    rw [Finset.sum_add_distrib]
    have hdiv : ∑ w, ((Q0 w).toReal - (P0 w).toReal) / (Real.exp eps - 1)
        = (∑ w, ((Q0 w).toReal - (P0 w).toReal)) / (Real.exp eps - 1) := by
      rw [← Finset.sum_div]
    rw [hdiv]
    have hsub : ∑ w, ((Q0 w).toReal - (P0 w).toReal) = 0 := by
      rw [Finset.sum_sub_distrib, hsumQ0, hsumP0, sub_self]
    rw [hsub, zero_div, add_zero]
    exact hsumQ0
  have hT0sum : ∑ w, ENNReal.ofReal (m0 w) = 1 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ m0 i := fun i _ => hm0_nonneg i
    have h := ENNReal.ofReal_sum_of_nonneg hnn
    simpa [hm0_sum] using h.symm
  have hT1sum : ∑ w, ENNReal.ofReal (m1 w) = 1 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ m1 i := fun i _ => hm1_nonneg i
    have h := ENNReal.ofReal_sum_of_nonneg hnn
    simpa [hm1_sum] using h.symm
  have hT2sum : ∑ w, ENNReal.ofReal (m2 w) = 1 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ m2 i := fun i _ => hm2_nonneg i
    have h := ENNReal.ofReal_sum_of_nonneg hnn
    simpa [hm2_sum] using h.symm
  have hT3sum : ∑ w, ENNReal.ofReal (m3 w) = 1 := by
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ m3 i := fun i _ => hm3_nonneg i
    have h := ENNReal.ofReal_sum_of_nonneg hnn
    simpa [hm3_sum] using h.symm
  set T0 : PMF Ω := PMF.ofFintype (fun w => ENNReal.ofReal (m0 w)) hT0sum
    with hT0def
  set T1 : PMF Ω := PMF.ofFintype (fun w => ENNReal.ofReal (m1 w)) hT1sum
    with hT1def
  set T2 : PMF Ω := PMF.ofFintype (fun w => ENNReal.ofReal (m2 w)) hT2sum
    with hT2def
  set T3 : PMF Ω := PMF.ofFintype (fun w => ENNReal.ofReal (m3 w)) hT3sum
    with hT3def
  have hT0 : ∀ w, (T0 w).toReal = m0 w := by
    intro w
    have h : (T0 w : ENNReal) = ENNReal.ofReal (m0 w) := rfl
    rw [h]
    exact ENNReal.toReal_ofReal (hm0_nonneg w)
  have hT1 : ∀ w, (T1 w).toReal = m1 w := by
    intro w
    have h : (T1 w : ENNReal) = ENNReal.ofReal (m1 w) := rfl
    rw [h]
    exact ENNReal.toReal_ofReal (hm1_nonneg w)
  have hT2 : ∀ w, (T2 w).toReal = m2 w := by
    intro w
    have h : (T2 w : ENNReal) = ENNReal.ofReal (m2 w) := rfl
    rw [h]
    exact ENNReal.toReal_ofReal (hm2_nonneg w)
  have hT3 : ∀ w, (T3 w).toReal = m3 w := by
    intro w
    have h : (T3 w : ENNReal) = ENNReal.ofReal (m3 w) := rfl
    rw [h]
    exact ENNReal.toReal_ofReal (hm3_nonneg w)
  have hadd : rrC eps delta + Real.exp eps * rrC eps delta = 1 - delta :=
    rrC_add_exp_mul eps delta
  have hδm0 : ∀ w, delta * m0 w
      = (P w).toReal - (1 - delta) * (P0 w).toReal := by
    intro w
    by_cases hδ : delta = 0
    · rw [hδ]
      have hp := hp0eq hδ w
      simp only [zero_mul, sub_zero, one_mul]
      linarith
    · simp only [hm0def]
      field_simp
      ring
  have hδm3 : ∀ w, delta * m3 w
      = (Q w).toReal - (1 - delta) * (Q0 w).toReal := by
    intro w
    by_cases hδ : delta = 0
    · rw [hδ]
      have hq := hq0eq hδ w
      simp only [zero_mul, sub_zero, one_mul]
      linarith
    · simp only [hm3def]
      field_simp
      ring
  have hE12P : ∀ w, Real.exp eps * rrC eps delta * m1 w
      + rrC eps delta * m2 w
      = rrC eps delta * (Real.exp eps + 1) * (P0 w).toReal := by
    intro w
    by_cases hE : Real.exp eps = 1
    · have hpq := hpq0eq hE w
      simp only [hm1def, hm2def, hE, sub_self, div_zero, add_zero]
      rw [← hpq]
      ring
    · have hne : Real.exp eps - 1 ≠ 0 := sub_ne_zero.mpr hE
      simp only [hm1def, hm2def]
      field_simp
      ring
  have hE12Q : ∀ w, rrC eps delta * m1 w
      + Real.exp eps * rrC eps delta * m2 w
      = rrC eps delta * (Real.exp eps + 1) * (Q0 w).toReal := by
    intro w
    by_cases hE : Real.exp eps = 1
    · have hpq := hpq0eq hE w
      simp only [hm1def, hm2def, hE, sub_self, div_zero, add_zero]
      rw [hpq]
      ring
    · have hne : Real.exp eps - 1 ≠ 0 := sub_ne_zero.mpr hE
      simp only [hm1def, hm2def]
      field_simp
      ring
  have hbind0 : ∀ w, (((rrR0 eps delta hδ0 hδ1).bind ![T0, T1, T2, T3]) w).toReal
      = (P w).toReal := by
    intro w
    rw [pmf_bind_toReal]
    rw [Fin.sum_univ_four]
    rw [rrR0_toReal_zero eps delta hδ0 hδ1,
      rrR0_toReal_one eps delta hδ0 hδ1,
      rrR0_toReal_two eps delta hδ0 hδ1,
      rrR0_toReal_three eps delta hδ0 hδ1]
    have e0 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 0 = T0 := rfl
    have e1 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 1 = T1 := by simp
    have e2 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 2 = T2 := by simp
    have e3 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 3 = T3 := by simp
    rw [e0, e1, e2, e3, hT0 w, hT1 w, hT2 w, hT3 w]
    linear_combination (hδm0 w) + (hE12P w) + (P0 w).toReal * hadd
  have hbind1 : ∀ w, (((rrR1 eps delta hδ0 hδ1).bind ![T0, T1, T2, T3]) w).toReal
      = (Q w).toReal := by
    intro w
    rw [pmf_bind_toReal]
    rw [Fin.sum_univ_four]
    rw [rrR1_toReal_zero eps delta hδ0 hδ1,
      rrR1_toReal_one eps delta hδ0 hδ1,
      rrR1_toReal_two eps delta hδ0 hδ1,
      rrR1_toReal_three eps delta hδ0 hδ1]
    have e0 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 0 = T0 := rfl
    have e1 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 1 = T1 := by simp
    have e2 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 2 = T2 := by simp
    have e3 : (![T0, T1, T2, T3] : Fin 4 → PMF Ω) 3 = T3 := by simp
    rw [e0, e1, e2, e3, hT0 w, hT1 w, hT2 w, hT3 w]
    linear_combination (hδm3 w) + (hE12Q w) + (Q0 w).toReal * hadd
  have hPMF0 : (rrR0 eps delta hδ0 hδ1).bind ![T0, T1, T2, T3] = P := by
    apply PMF.ext
    intro w
    have hto := hbind0 w
    have ha := ((rrR0 eps delta hδ0 hδ1).bind ![T0, T1, T2, T3]).apply_ne_top w
    have hb := P.apply_ne_top w
    have h := congrArg ENNReal.ofReal hto
    rw [ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb] at h
    exact h
  have hPMF1 : (rrR1 eps delta hδ0 hδ1).bind ![T0, T1, T2, T3] = Q := by
    apply PMF.ext
    intro w
    have hto := hbind1 w
    have ha := ((rrR1 eps delta hδ0 hδ1).bind ![T0, T1, T2, T3]).apply_ne_top w
    have hb := Q.apply_ne_top w
    have h := congrArg ENNReal.ofReal hto
    rw [ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb] at h
    exact h
  exact ⟨![T0, T1, T2, T3], hPMF0, hPMF1⟩

/-- The four-outcome pair as a mechanism on the two hypotheses: `false` gives
`rrR0` and `true` gives `rrR1`. -/
noncomputable def rrStage (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1) :
    Bool → PMF (Fin 4) :=
  fun b => cond b (rrR1 eps delta hδ0 hδ1) (rrR0 eps delta hδ0 hδ1)

/-- The four-outcome mechanism is `(eps, delta)`-DP for the adjacency that
relates the two hypotheses. -/
theorem isApproxDP_rrStage (eps delta : ℝ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta)
    (hδ1 : delta ≤ 1) :
    IsApproxDP (rrStage eps delta hδ0 hδ1) (fun b b' => b ≠ b') eps delta := by
  rw [isApproxDP_iff_forall_kovpair Bool (Fin 4) _ _ eps delta hε hδ0
    (by intro x y h; exact Ne.symm h)]
  intro b b' hne
  cases b <;> cases b' <;> simp_all [rrStage]
  · exact rr_kovpair eps delta hε hδ0 hδ1
  · exact kovpair_symm (Fin 4) _ _ eps delta
      (rr_kovpair eps delta hε hδ0 hδ1)

/-! ## `k` stages -/

/-- `k` stages of the four-outcome mechanism, each ignoring the transcript so
far, as a `kfoldCompose` run on the two hypotheses. -/
noncomputable def rrKfold (eps delta : ℝ) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (k : ℕ) : Bool → PMF (Transcript (fun _ => Fin 4) k) :=
  kfoldCompose (fun _ _ => rrStage eps delta hδ0 hδ1) k

private noncomputable def kfoldSim {A : ℕ → Type u}
    (Tch : ∀ (i : ℕ), Transcript A i → Fin 4 → PMF (A i))
    : ∀ (n : ℕ), Transcript (fun _ => Fin 4) n → PMF (Transcript A n)
  | 0, _ => PMF.pure PUnit.unit
  | n + 1, p => ((kfoldSim Tch n p.1).bind fun u =>
      ((Tch n u p.2).bind fun b => PMF.pure (u, b)))

/-- Stage-by-stage simulation (Kairouz-Oh-Viswanath, supplementary material,
Section 5.2): if at every stage before `k` and after every transcript the two
output laws on `d` and `d'` satisfy `KOVpair` at `(eps, delta)`, one channel
maps `k` stages of the four-outcome mechanism on `false` and `true` to the
`k`-fold composition on `d` and `d'`. -/
theorem rrKfold_exists_channel {D : Type*} {A : ℕ → Type u}
    [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    (K : (n : ℕ) → Transcript A n → D → PMF (A n)) (d d' : D)
    (eps delta : ℝ) (k : ℕ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta) (hδ1 : delta ≤ 1)
    (hK : ∀ i, i < k → ∀ t, KOVpair (A i) (K i t d) (K i t d') eps delta) :
    ∃ S : Transcript (fun _ => Fin 4) k → PMF (Transcript A k),
      (rrKfold eps delta hδ0 hδ1 k false).bind S = kfoldCompose K k d ∧
        (rrKfold eps delta hδ0 hδ1 k true).bind S = kfoldCompose K k d' := by
  set Tch : ∀ (i : ℕ), Transcript A i → Fin 4 → PMF (A i) :=
    fun i t => if h : i < k then
      Classical.choose (rr_exists_channel_of_kovpair (A i) (K i t d) (K i t d')
        eps delta hε hδ0 hδ1 (hK i h t))
    else fun _ => K i t d with hTchdef
  have hTch0 : ∀ (i : ℕ) (h : i < k) (t : Transcript A i),
      (rrR0 eps delta hδ0 hδ1).bind (Tch i t) = K i t d := by
    intro i h t
    have hspec := Classical.choose_spec (rr_exists_channel_of_kovpair (A i)
      (K i t d) (K i t d') eps delta hε hδ0 hδ1 (hK i h t))
    simp only [hTchdef, dite_eq_left h]
    exact hspec.1
  have hTch1 : ∀ (i : ℕ) (h : i < k) (t : Transcript A i),
      (rrR1 eps delta hδ0 hδ1).bind (Tch i t) = K i t d' := by
    intro i h t
    have hspec := Classical.choose_spec (rr_exists_channel_of_kovpair (A i)
      (K i t d) (K i t d') eps delta hε hδ0 hδ1 (hK i h t))
    simp only [hTchdef, dite_eq_left h]
    exact hspec.2
  have hRR : ∀ (n : ℕ) (b : Bool),
      rrKfold eps delta hδ0 hδ1 (n + 1) b =
        (((rrKfold eps delta hδ0 hδ1 n b).bind fun t =>
          (((rrStage eps delta hδ0 hδ1 b).bind fun a =>
            PMF.pure (t, a))))) := fun n b => rfl
  have hK : ∀ (n : ℕ) (d0 : D),
      kfoldCompose K (n + 1) d0 =
        ((((kfoldCompose K n d0).bind fun t =>
          (((K n t d0).bind fun b => PMF.pure (t, b)))))) :=
    fun n d0 => rfl
  have hRR0 : ∀ b : Bool,
      rrKfold eps delta hδ0 hδ1 0 b = PMF.pure PUnit.unit := fun b => rfl
  have hK0 : ∀ d0 : D, kfoldCompose K 0 d0 = PMF.pure PUnit.unit :=
    fun d0 => rfl
  have hS0 : ∀ p : Transcript (fun _ => Fin 4) 0,
      kfoldSim Tch 0 p = PMF.pure PUnit.unit := fun p => rfl
  have hSn : ∀ (n : ℕ) (t : Transcript (fun _ => Fin 4) n) (a : Fin 4),
      kfoldSim Tch (n + 1) (t, a) = (((kfoldSim Tch n t).bind fun u =>
        (((Tch n u a).bind fun b => PMF.pure (u, b))))) :=
    fun n t a => rfl
  have hch0 : ∀ (n : ℕ) (h : n < k) (u : Transcript A n),
      (rrStage eps delta hδ0 hδ1 false).bind (Tch n u) = K n u d :=
    fun n h u => hTch0 n h u
  have hch1 : ∀ (n : ℕ) (h : n < k) (u : Transcript A n),
      (rrStage eps delta hδ0 hδ1 true).bind (Tch n u) = K n u d' :=
    fun n h u => hTch1 n h u
  have key : ∀ (n : ℕ), n ≤ k →
      (rrKfold eps delta hδ0 hδ1 n false).bind (kfoldSim Tch n)
        = kfoldCompose K n d ∧
      (rrKfold eps delta hδ0 hδ1 n true).bind (kfoldSim Tch n)
        = kfoldCompose K n d' := by
    intro n
    induction n with
    | zero =>
      intro _
      constructor
      · have h1 : (rrKfold eps delta hδ0 hδ1 0 false).bind (kfoldSim Tch 0)
            = PMF.pure PUnit.unit :=
            PMF.pure_bind PUnit.unit (kfoldSim Tch 0)
        have h2 : kfoldCompose K 0 d = PMF.pure PUnit.unit := rfl
        exact h1.trans h2.symm
      · have h1 : (rrKfold eps delta hδ0 hδ1 0 true).bind (kfoldSim Tch 0)
            = PMF.pure PUnit.unit :=
            PMF.pure_bind PUnit.unit (kfoldSim Tch 0)
        have h2 : kfoldCompose K 0 d' = PMF.pure PUnit.unit := rfl
        exact h1.trans h2.symm
    | succ n ih =>
      intro hnk
      have hn_lt : n < k := by omega
      have hn_le : n ≤ k := by omega
      obtain ⟨ih0, ih1⟩ := ih hn_le
      constructor
      · -- false / d side
        have step1 : ((rrKfold eps delta hδ0 hδ1 (n + 1) false).bind
              (kfoldSim Tch (n + 1)) : PMF (Transcript A (n + 1)))
            = (((rrKfold eps delta hδ0 hδ1 n false).bind fun t =>
                (((rrStage eps delta hδ0 hδ1 false).bind fun a =>
                  PMF.pure (t, a))).bind (kfoldSim Tch (n + 1)))
              : PMF (Transcript A (n + 1))) :=
            PMF.bind_bind _ _ _
        have step2 : ∀ t : Transcript (fun _ => Fin 4) n,
            (((rrStage eps delta hδ0 hδ1 false).bind fun a =>
              PMF.pure (t, a))).bind (kfoldSim Tch (n + 1))
            = (rrStage eps delta hδ0 hδ1 false).bind fun a =>
              kfoldSim Tch (n + 1) (t, a) := by
          intro t
          have e1 : ((((rrStage eps delta hδ0 hδ1 false).bind fun a =>
                PMF.pure (t, a)))).bind (kfoldSim Tch (n + 1))
              = ((rrStage eps delta hδ0 hδ1 false).bind fun a =>
                ((PMF.pure (t, a)).bind (kfoldSim Tch (n + 1)))) :=
            PMF.bind_bind _ _ _
          have e2 : (fun a : Fin 4 => (PMF.pure (t, a)).bind
                (kfoldSim Tch (n + 1)))
              = (fun a : Fin 4 => kfoldSim Tch (n + 1) (t, a)) := by
            apply funext
            intro a
            exact PMF.pure_bind _ _
          have e3 := congrArg
            ((rrStage eps delta hδ0 hδ1 false).bind) e2
          exact e1.trans e3
        have step3 : ((rrKfold eps delta hδ0 hδ1 (n + 1) false).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n false).bind fun t =>
              (rrStage eps delta hδ0 hδ1 false).bind fun a =>
                kfoldSim Tch (n + 1) (t, a) := by
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n false).bind)
            (funext step2)
          exact step1.trans hcon
        have hSn1 : ∀ (t : Transcript (fun _ => Fin 4) n) (a : Fin 4),
            kfoldSim Tch (n + 1) (t, a)
            = ((kfoldSim Tch n t).bind fun u =>
              ((Tch n u a).bind fun b => PMF.pure (u, b))) :=
          fun t a => hSn n t a
        have step4 : ((rrKfold eps delta hδ0 hδ1 (n + 1) false).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n false).bind fun t =>
              (rrStage eps delta hδ0 hδ1 false).bind fun a =>
                ((kfoldSim Tch n t).bind fun u =>
                  ((Tch n u a).bind fun b => PMF.pure (u, b))) := by
          have hcon_inner : ∀ t : Transcript (fun _ => Fin 4) n,
              (fun a : Fin 4 => kfoldSim Tch (n + 1) (t, a))
              = (fun a : Fin 4 => ((kfoldSim Tch n t).bind fun u =>
                ((Tch n u a).bind fun b => PMF.pure (u, b)))) := by
            intro t
            exact funext (fun a => hSn1 t a)
          have hcon_mid : (fun t : Transcript (fun _ => Fin 4) n =>
                (rrStage eps delta hδ0 hδ1 false).bind fun a =>
                  kfoldSim Tch (n + 1) (t, a))
              = (fun t : Transcript (fun _ => Fin 4) n =>
                (rrStage eps delta hδ0 hδ1 false).bind fun a =>
                  ((kfoldSim Tch n t).bind fun u =>
                    ((Tch n u a).bind fun b => PMF.pure (u, b)))) := by
            apply funext
            intro t
            exact congrArg
              ((rrStage eps delta hδ0 hδ1 false).bind) (hcon_inner t)
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n false).bind) hcon_mid
          exact step3.trans hcon
        have step5t : ∀ t : Transcript (fun _ => Fin 4) n,
            (rrStage eps delta hδ0 hδ1 false).bind (fun a =>
              ((kfoldSim Tch n t).bind fun u =>
                ((Tch n u a).bind fun b => PMF.pure (u, b))))
            = (kfoldSim Tch n t).bind fun u =>
              ((rrStage eps delta hδ0 hδ1 false).bind fun a =>
                ((Tch n u a).bind fun b => PMF.pure (u, b))) := by
          intro t
          exact PMF.bind_comm _ _ _
        have step5 : ((rrKfold eps delta hδ0 hδ1 (n + 1) false).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n false).bind fun t =>
              ((kfoldSim Tch n t).bind fun u =>
                ((rrStage eps delta hδ0 hδ1 false).bind fun a =>
                  ((Tch n u a).bind fun b => PMF.pure (u, b)))) := by
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n false).bind) (funext step5t)
          exact step4.trans hcon
        have step6u : ∀ u : Transcript A n,
            (rrStage eps delta hδ0 hδ1 false).bind (fun a =>
              ((Tch n u a).bind fun b => PMF.pure (u, b)))
            = (K n u d).bind fun b => PMF.pure (u, b) := by
          intro u
          have e1 : (rrStage eps delta hδ0 hδ1 false).bind (fun a =>
                ((Tch n u a).bind fun b => PMF.pure (u, b)))
              = (((rrStage eps delta hδ0 hδ1 false).bind (Tch n u)).bind
                fun b => PMF.pure (u, b)) :=
            (PMF.bind_bind _ _ _).symm
          have e3 : (((rrStage eps delta hδ0 hδ1 false).bind (Tch n u)).bind
                fun b => PMF.pure (u, b))
              = ((K n u d).bind fun b => PMF.pure (u, b)) :=
            congrArg
              (fun P : PMF (A n) => P.bind fun b => PMF.pure (u, b))
              (hch0 n hn_lt u)
          exact e1.trans e3
        have step6 : ((rrKfold eps delta hδ0 hδ1 (n + 1) false).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n false).bind fun t =>
              ((kfoldSim Tch n t).bind fun u =>
                ((K n u d).bind fun b => PMF.pure (u, b))) := by
          have hcon_t : ∀ t : Transcript (fun _ => Fin 4) n,
              ((kfoldSim Tch n t).bind fun u =>
                ((rrStage eps delta hδ0 hδ1 false).bind fun a =>
                  ((Tch n u a).bind fun b => PMF.pure (u, b))))
              = ((kfoldSim Tch n t).bind fun u =>
                ((K n u d).bind fun b => PMF.pure (u, b))) := by
            intro t
            exact congrArg ((kfoldSim Tch n t).bind) (funext step6u)
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n false).bind) (funext hcon_t)
          exact step5.trans hcon
        have step7 : (rrKfold eps delta hδ0 hδ1 n false).bind (fun t =>
              ((kfoldSim Tch n t).bind fun u =>
                ((K n u d).bind fun b => PMF.pure (u, b))))
            = (((rrKfold eps delta hδ0 hδ1 n false).bind
              (kfoldSim Tch n)).bind fun u =>
              ((K n u d).bind fun b => PMF.pure (u, b))) :=
          (PMF.bind_bind _ _ _).symm
        have step8 : (((rrKfold eps delta hδ0 hδ1 n false).bind
              (kfoldSim Tch n)).bind fun u =>
              ((K n u d).bind fun b => PMF.pure (u, b)))
            = kfoldCompose K (n + 1) d := by
          have hcon := congrArg
            (fun P : PMF (Transcript A n) => P.bind fun u =>
              ((K n u d).bind fun b => PMF.pure (u, b))) ih0
          have hfin : (((kfoldCompose K n d).bind fun u =>
              ((K n u d).bind fun b => PMF.pure (u, b))))
              = kfoldCompose K (n + 1) d :=
            (hK n d).symm
          exact hcon.trans hfin
        exact step6.trans (step7.trans step8)
      · -- true / d' side
        have step1 : ((rrKfold eps delta hδ0 hδ1 (n + 1) true).bind
              (kfoldSim Tch (n + 1)) : PMF (Transcript A (n + 1)))
            = (((rrKfold eps delta hδ0 hδ1 n true).bind fun t =>
                (((rrStage eps delta hδ0 hδ1 true).bind fun a =>
                  PMF.pure (t, a))).bind (kfoldSim Tch (n + 1)))
              : PMF (Transcript A (n + 1))) :=
            PMF.bind_bind _ _ _
        have step2 : ∀ t : Transcript (fun _ => Fin 4) n,
            (((rrStage eps delta hδ0 hδ1 true).bind fun a =>
              PMF.pure (t, a))).bind (kfoldSim Tch (n + 1))
            = (rrStage eps delta hδ0 hδ1 true).bind fun a =>
              kfoldSim Tch (n + 1) (t, a) := by
          intro t
          have e1 : ((((rrStage eps delta hδ0 hδ1 true).bind fun a =>
                PMF.pure (t, a)))).bind (kfoldSim Tch (n + 1))
              = ((rrStage eps delta hδ0 hδ1 true).bind fun a =>
                ((PMF.pure (t, a)).bind (kfoldSim Tch (n + 1)))) :=
            PMF.bind_bind _ _ _
          have e2 : (fun a : Fin 4 => (PMF.pure (t, a)).bind
                (kfoldSim Tch (n + 1)))
              = (fun a : Fin 4 => kfoldSim Tch (n + 1) (t, a)) := by
            apply funext
            intro a
            exact PMF.pure_bind _ _
          have e3 := congrArg
            ((rrStage eps delta hδ0 hδ1 true).bind) e2
          exact e1.trans e3
        have step3 : ((rrKfold eps delta hδ0 hδ1 (n + 1) true).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n true).bind fun t =>
              (rrStage eps delta hδ0 hδ1 true).bind fun a =>
                kfoldSim Tch (n + 1) (t, a) := by
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n true).bind)
            (funext step2)
          exact step1.trans hcon
        have hSn1 : ∀ (t : Transcript (fun _ => Fin 4) n) (a : Fin 4),
            kfoldSim Tch (n + 1) (t, a)
            = ((kfoldSim Tch n t).bind fun u =>
              ((Tch n u a).bind fun b => PMF.pure (u, b))) :=
          fun t a => hSn n t a
        have step4 : ((rrKfold eps delta hδ0 hδ1 (n + 1) true).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n true).bind fun t =>
              (rrStage eps delta hδ0 hδ1 true).bind fun a =>
                ((kfoldSim Tch n t).bind fun u =>
                  ((Tch n u a).bind fun b => PMF.pure (u, b))) := by
          have hcon_inner : ∀ t : Transcript (fun _ => Fin 4) n,
              (fun a : Fin 4 => kfoldSim Tch (n + 1) (t, a))
              = (fun a : Fin 4 => ((kfoldSim Tch n t).bind fun u =>
                ((Tch n u a).bind fun b => PMF.pure (u, b)))) := by
            intro t
            exact funext (fun a => hSn1 t a)
          have hcon_mid : (fun t : Transcript (fun _ => Fin 4) n =>
                (rrStage eps delta hδ0 hδ1 true).bind fun a =>
                  kfoldSim Tch (n + 1) (t, a))
              = (fun t : Transcript (fun _ => Fin 4) n =>
                (rrStage eps delta hδ0 hδ1 true).bind fun a =>
                  ((kfoldSim Tch n t).bind fun u =>
                    ((Tch n u a).bind fun b => PMF.pure (u, b)))) := by
            apply funext
            intro t
            exact congrArg
              ((rrStage eps delta hδ0 hδ1 true).bind) (hcon_inner t)
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n true).bind) hcon_mid
          exact step3.trans hcon
        have step5t : ∀ t : Transcript (fun _ => Fin 4) n,
            (rrStage eps delta hδ0 hδ1 true).bind (fun a =>
              ((kfoldSim Tch n t).bind fun u =>
                ((Tch n u a).bind fun b => PMF.pure (u, b))))
            = (kfoldSim Tch n t).bind fun u =>
              ((rrStage eps delta hδ0 hδ1 true).bind fun a =>
                ((Tch n u a).bind fun b => PMF.pure (u, b))) := by
          intro t
          exact PMF.bind_comm _ _ _
        have step5 : ((rrKfold eps delta hδ0 hδ1 (n + 1) true).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n true).bind fun t =>
              ((kfoldSim Tch n t).bind fun u =>
                ((rrStage eps delta hδ0 hδ1 true).bind fun a =>
                  ((Tch n u a).bind fun b => PMF.pure (u, b)))) := by
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n true).bind) (funext step5t)
          exact step4.trans hcon
        have step6u : ∀ u : Transcript A n,
            (rrStage eps delta hδ0 hδ1 true).bind (fun a =>
              ((Tch n u a).bind fun b => PMF.pure (u, b)))
            = (K n u d').bind fun b => PMF.pure (u, b) := by
          intro u
          have e1 : (rrStage eps delta hδ0 hδ1 true).bind (fun a =>
                ((Tch n u a).bind fun b => PMF.pure (u, b)))
              = (((rrStage eps delta hδ0 hδ1 true).bind (Tch n u)).bind
                fun b => PMF.pure (u, b)) :=
            (PMF.bind_bind _ _ _).symm
          have e3 : (((rrStage eps delta hδ0 hδ1 true).bind (Tch n u)).bind
                fun b => PMF.pure (u, b))
              = ((K n u d').bind fun b => PMF.pure (u, b)) :=
            congrArg
              (fun P : PMF (A n) => P.bind fun b => PMF.pure (u, b))
              (hch1 n hn_lt u)
          exact e1.trans e3
        have step6 : ((rrKfold eps delta hδ0 hδ1 (n + 1) true).bind
              (kfoldSim Tch (n + 1)))
            = (rrKfold eps delta hδ0 hδ1 n true).bind fun t =>
              ((kfoldSim Tch n t).bind fun u =>
                ((K n u d').bind fun b => PMF.pure (u, b))) := by
          have hcon_t : ∀ t : Transcript (fun _ => Fin 4) n,
              ((kfoldSim Tch n t).bind fun u =>
                ((rrStage eps delta hδ0 hδ1 true).bind fun a =>
                  ((Tch n u a).bind fun b => PMF.pure (u, b))))
              = ((kfoldSim Tch n t).bind fun u =>
                ((K n u d').bind fun b => PMF.pure (u, b))) := by
            intro t
            exact congrArg ((kfoldSim Tch n t).bind) (funext step6u)
          have hcon := congrArg
            ((rrKfold eps delta hδ0 hδ1 n true).bind) (funext hcon_t)
          exact step5.trans hcon
        have step7 : (rrKfold eps delta hδ0 hδ1 n true).bind (fun t =>
              ((kfoldSim Tch n t).bind fun u =>
                ((K n u d').bind fun b => PMF.pure (u, b))))
            = (((rrKfold eps delta hδ0 hδ1 n true).bind
              (kfoldSim Tch n)).bind fun u =>
              ((K n u d').bind fun b => PMF.pure (u, b))) :=
          (PMF.bind_bind _ _ _).symm
        have step8 : (((rrKfold eps delta hδ0 hδ1 n true).bind
              (kfoldSim Tch n)).bind fun u =>
              ((K n u d').bind fun b => PMF.pure (u, b)))
            = kfoldCompose K (n + 1) d' := by
          have hcon := congrArg
            (fun P : PMF (Transcript A n) => P.bind fun u =>
              ((K n u d').bind fun b => PMF.pure (u, b))) ih1
          have hfin : (((kfoldCompose K n d').bind fun u =>
              ((K n u d').bind fun b => PMF.pure (u, b))))
              = kfoldCompose K (n + 1) d' :=
            (hK n d').symm
          exact hcon.trans hfin
        exact step6.trans (step7.trans step8)
  obtain ⟨h0, h1⟩ := key k (le_refl k)
  exact ⟨kfoldSim Tch k, h0, h1⟩

/-- Dominance under composition: on `[0, 1]`, the tradeoff of `k` stages of
the four-outcome mechanism lies below the tradeoff of the `k`-fold composition
on `d` and `d'` whenever every stage satisfies `KOVpair` at `(eps, delta)`. -/
theorem rrKfold_tradeoff_le {D : Type*} {A : ℕ → Type u}
    [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    (K : (n : ℕ) → Transcript A n → D → PMF (A n)) (d d' : D)
    (eps delta alpha : ℝ) (k : ℕ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta)
    (hδ1 : delta ≤ 1)
    (hK : ∀ i, i < k → ∀ t, KOVpair (A i) (K i t d) (K i t d') eps delta)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    tradeoff (Transcript (fun _ => Fin 4) k) (rrKfold eps delta hδ0 hδ1 k false)
        (rrKfold eps delta hδ0 hδ1 k true) alpha ≤
      tradeoff (Transcript A k) (kfoldCompose K k d) (kfoldCompose K k d') alpha := by
  obtain ⟨S, hS0, hS1⟩ := rrKfold_exists_channel K d d' eps delta k hε hδ0 hδ1 hK
  have hpost := tradeoff_postprocess (Transcript (fun _ => Fin 4) k)
    (Transcript A k) (rrKfold eps delta hδ0 hδ1 k false)
    (rrKfold eps delta hδ0 hδ1 k true) S alpha hα0 hα1
  rw [hS0, hS1] at hpost
  exact hpost

/-- Reduction to randomized response, pair form: a `KOVpair` condition at
`(eps', delta')` met by `k` stages of the four-outcome mechanism is met by the
`k`-fold composition on `d` and `d'` whenever every stage satisfies `KOVpair`
at `(eps, delta)`. -/
theorem kovpair_kfold_of_rrKfold {D : Type*} {A : ℕ → Type u}
    [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    (K : (n : ℕ) → Transcript A n → D → PMF (A n)) (d d' : D)
    (eps delta eps' delta' : ℝ) (k : ℕ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta)
    (hδ1 : delta ≤ 1)
    (hK : ∀ i, i < k → ∀ t, KOVpair (A i) (K i t d) (K i t d') eps delta)
    (hRR : KOVpair (Transcript (fun _ => Fin 4) k)
      (rrKfold eps delta hδ0 hδ1 k false) (rrKfold eps delta hδ0 hδ1 k true)
      eps' delta') :
    KOVpair (Transcript A k) (kfoldCompose K k d) (kfoldCompose K k d') eps' delta' := by
  apply kovpair_of_tradeoff_ge
  intro alpha hα0 hα1
  have hRRge := kovpair_forward_tradeoff_ge (Transcript (fun _ => Fin 4) k)
    (rrKfold eps delta hδ0 hδ1 k false)
    (rrKfold eps delta hδ0 hδ1 k true) eps' delta' alpha hRR hα0 hα1
  have hle := rrKfold_tradeoff_le K d d' eps delta alpha k hε hδ0 hδ1 hK hα0 hα1
  exact le_trans hRRge hle

/-- Reduction to randomized response, mechanism form: for a symmetric
adjacency, if `k` stages of the four-outcome mechanism are `(eps', delta')`-DP
between the two hypotheses, then every `k`-fold adaptive composition with finite
stage outputs whose stages are `(eps, delta)`-DP after every transcript is
`(eps', delta')`-DP. -/
theorem isApproxDP_kfold_of_rrKfold {D : Type*} {A : ℕ → Type u}
    [∀ n, Finite (A n)] {adj : D → D → Prop} [Std.Symm adj]
    (K : (n : ℕ) → Transcript A n → D → PMF (A n))
    (eps delta eps' delta' : ℝ) (k : ℕ) (hε : 0 ≤ eps) (hδ0 : 0 ≤ delta)
    (hδ1 : delta ≤ 1)
    (hK : ∀ i, i < k → ∀ t, IsApproxDP (fun d => K i t d) adj eps delta)
    (hRR : IsApproxDP (rrKfold eps delta hδ0 hδ1 k) (fun b b' => b ≠ b') eps' delta') :
    IsApproxDP (kfoldCompose K k) adj eps' delta' := by
  classical
  have hfin : ∀ n, Fintype (A n) := fun n => Fintype.ofFinite (A n)
  have hε' : 0 ≤ eps' := hRR.1
  have hδ' : 0 ≤ delta' := hRR.2.1
  rw [isApproxDP_iff_forall_kovpair D (Transcript A k) (kfoldCompose K k) adj
    eps' delta' hε' hδ' (by intro x y h; exact Std.Symm.symm x y h)]
  intro d0 d1 hadd
  apply kovpair_kfold_of_rrKfold K d0 d1 eps delta eps' delta' k hε hδ0 hδ1
  · intro i hi t
    have hstage := hK i hi t
    exact (isApproxDP_iff_forall_kovpair D (A i) (fun d => K i t d) adj eps delta
      hε hδ0 (by intro x y h; exact Std.Symm.symm x y h)).mp hstage d0 d1 hadd
  · exact (isApproxDP_iff_forall_kovpair Bool (Transcript (fun _ => Fin 4) k)
      (rrKfold eps delta hδ0 hδ1 k) (fun b b' => b ≠ b') eps' delta' hε' hδ'
      (by intro x y h; exact Ne.symm h)).mp hRR false true (by decide)

end CSLibExt.Privacy.HypothesisTesting
