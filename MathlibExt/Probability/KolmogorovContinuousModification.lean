/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovContinuity
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Continuous modifications of real-valued Kolmogorov processes

This file upgrades the dyadic Hölder estimate in
`MathlibExt.Probability.KolmogorovContinuity` to one continuous modification
on `NNReal`. This is the real-valued Kolmogorov–Chentsov continuity theorem.
The construction uses one measurable common good set, the dense extension of
the original process on nonnegative dyadic times, and the entire constant path
`X 0 ω` off the good set.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, Chapter I,
  Theorem 2.1.
* O. Kallenberg, *Foundations of Modern Probability*, third edition,
  Theorem 4.23.
-/

@[expose] public section

open MeasureTheory Filter Topology
open MathlibExt.Probability.KolmogorovContinuity
open scoped ENNReal NNReal

namespace MathlibExt.Probability.KolmogorovContinuousModification

private noncomputable def dyadicApprox (n : ℕ) (t : NNReal) : NNReal :=
  ((⌊t * (2 : NNReal) ^ n⌋₊ : ℕ) : NNReal) / (2 : NNReal) ^ n

@[simp]
private lemma coe_dyadicApprox (n : ℕ) (t : NNReal) :
    (dyadicApprox n t : ℝ) =
      ((⌊t * (2 : NNReal) ^ n⌋₊ : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  simp [dyadicApprox]

private lemma dyadicApprox_le (n : ℕ) (t : NNReal) : dyadicApprox n t ≤ t := by
  rw [dyadicApprox, div_le_iff₀ (by positivity : (0 : NNReal) < 2 ^ n)]
  exact Nat.floor_le (by positivity)

private lemma dist_dyadicApprox_le (n : ℕ) (t : NNReal) :
    dist (dyadicApprox n t) t ≤ (1 / 2 : ℝ) ^ n := by
  have hfloor := Nat.lt_floor_add_one (t * (2 : NNReal) ^ n)
  have hfloor' :
      (t : ℝ) * (2 : ℝ) ^ n <
        ((⌊t * (2 : NNReal) ^ n⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast hfloor
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [NNReal.dist_eq, abs_of_nonpos]
  · rw [neg_sub, coe_dyadicApprox, one_div_pow]
    apply le_of_lt
    rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hpos]
    linarith
  · exact sub_nonpos.mpr (by exact_mod_cast dyadicApprox_le n t)

private lemma tendsto_dyadicApprox (t : NNReal) :
    Tendsto (fun n => dyadicApprox n t) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n => dist_nonneg) (fun n => dist_dyadicApprox_le n t)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

@[simp]
private lemma dyadicApprox_zero (n : ℕ) : dyadicApprox n 0 = 0 := by
  simp [dyadicApprox]

private def dyadicNNReal : Set NNReal :=
  {t | (t : ℝ) ∈ MathlibExt.Probability.KolmogorovContinuity.dyadicRationals}

private lemma dyadicApprox_mem (n : ℕ) (t : NNReal) : dyadicApprox n t ∈ dyadicNNReal := by
  change ∃ k : ℤ, ∃ m : ℕ,
    (dyadicApprox n t : ℝ) = k / (2 : ℝ) ^ m
  refine ⟨(⌊t * (2 : NNReal) ^ n⌋₊ : ℕ), n, ?_⟩
  simp

private lemma countable_dyadicNNReal : dyadicNNReal.Countable := by
  have hcount :
      MathlibExt.Probability.KolmogorovContinuity.dyadicRationals.Countable := by
    refine (Set.countable_range fun p : ℤ × ℕ =>
      (p.1 : ℝ) / (2 : ℝ) ^ p.2).mono ?_
    intro x hx
    obtain ⟨k, n, rfl⟩ := hx
    exact ⟨(k, n), rfl⟩
  change ((fun t : NNReal => (t : ℝ)) ⁻¹'
    MathlibExt.Probability.KolmogorovContinuity.dyadicRationals).Countable
  exact hcount.preimage NNReal.coe_injective

private def compactDyadics (H : NNReal) : Set (Set.Icc (0 : NNReal) H) :=
  {t | (t : NNReal) ∈ dyadicNNReal}

private lemma countable_compactDyadics (H : NNReal) : (compactDyadics H).Countable := by
  change (Subtype.val ⁻¹' dyadicNNReal).Countable
  exact countable_dyadicNNReal.preimage Subtype.val_injective

private lemma dense_compactDyadics (H : NNReal) : Dense (compactDyadics H) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro t
  let a : ℕ → Set.Icc (0 : NNReal) H := fun n =>
    ⟨dyadicApprox n t, by
      exact ⟨by positivity, (dyadicApprox_le n t).trans t.property.2⟩⟩
  apply mem_closure_of_tendsto (f := a) (b := atTop)
  · rw [tendsto_subtype_rng]
    exact tendsto_dyadicApprox t
  · exact Eventually.of_forall fun n => dyadicApprox_mem n t

private noncomputable def pathLimit {Ω : Type*} (X : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω => atTop.limUnder fun n => X (dyadicApprox n t) ω

private lemma measurable_pathLimit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (t : NNReal) :
    Measurable (pathLimit X t) := by
  exact (StronglyMeasurable.limUnder fun n =>
    (hX.measurable (dyadicApprox n t)).stronglyMeasurable).measurable

private noncomputable def scaledTime (H : NNReal) (t : ℝ) : NNReal :=
  H * t.toNNReal

private lemma lipschitzWith_scaledTime (H : NNReal) :
    LipschitzWith H (scaledTime H) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  calc
    dist (scaledTime H s) (scaledTime H t) =
        (H : ℝ) * dist s.toNNReal t.toNNReal := by
      simp only [scaledTime, NNReal.dist_eq, NNReal.coe_mul, ← mul_sub, abs_mul]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ H from H.property)]
    _ ≤ (H : ℝ) * dist s t := by
      have h := Real.lipschitzWith_toNNReal.dist_le_mul s t
      simp only [NNReal.coe_one, one_mul] at h
      exact mul_le_mul_of_nonneg_left h H.property

private lemma isKolmogorovProcess_scaled {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (H : NNReal) :
    ProbabilityTheory.IsKolmogorovProcess
      (fun t : ℝ => X (scaledTime H t)) P p q (M * H.rpow q) where
  measurablePair s t := hX.measurablePair _ _
  kolmogorovCondition s t := by
    calc
      (∫⁻ ω, edist (X (scaledTime H s) ω) (X (scaledTime H t) ω) ^ p ∂P)
          ≤ (M : ENNReal) * edist (scaledTime H s) (scaledTime H t) ^ q :=
        hX.kolmogorovCondition _ _
      _ ≤ (M : ENNReal) * ((H : ENNReal) * edist s t) ^ q := by
        have hrpow := ENNReal.rpow_le_rpow
          ((lipschitzWith_scaledTime H).edist_le_mul s t) hX.q_pos.le
        have hmul := mul_le_mul_left hrpow (M : ENNReal)
        simpa [mul_comm] using hmul
      _ = ((M * H.rpow q : NNReal) : ENNReal) * edist s t ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hX.q_pos.le, ENNReal.coe_mul]
        have hcoe : ((H.rpow q : NNReal) : ENNReal) = (H : ENNReal) ^ q :=
          ENNReal.coe_rpow_of_nonneg H hX.q_pos.le
        rw [hcoe]
        ring
  p_pos := hX.p_pos
  q_pos := hX.q_pos

private abbrev PositiveNat := {n : ℕ // 0 < n}

private def holderEvent {Ω : Type*} (X : NNReal → Ω → ℝ) (γ : NNReal)
    (N : ℕ) (C : PositiveNat) : Set Ω :=
  {ω | HolderWith (C : NNReal) γ
    (fun t : compactDyadics ((2 : NNReal) ^ N) => X t.1.1 ω)}

private def goodSet {Ω : Type*} (X : NNReal → Ω → ℝ) (γ : NNReal) : Set Ω :=
  ⋂ N : ℕ, ⋃ C : PositiveNat, holderEvent X γ N C

private lemma measurableSet_holderEvent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (γ : NNReal)
    (N : ℕ) (C : PositiveNat) : MeasurableSet (holderEvent X γ N C) := by
  let _ : Countable (compactDyadics ((2 : NNReal) ^ N)) :=
    (countable_compactDyadics ((2 : NNReal) ^ N)).to_subtype
  simp only [holderEvent, HolderWith, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro s
  apply MeasurableSet.iInter
  intro t
  exact measurableSet_le hX.measurable_edist measurable_const

private lemma measurableSet_goodSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (γ : NNReal) :
    MeasurableSet (goodSet X γ) := by
  apply MeasurableSet.iInter
  intro N
  apply MeasurableSet.iUnion
  intro C
  exact measurableSet_holderEvent hX γ N C

private lemma normalized_compactDyadic (N : ℕ)
    (t : compactDyadics ((2 : NNReal) ^ N)) :
    (t.1.1 : ℝ) / (((2 : NNReal) ^ N : NNReal) : ℝ) ∈
        MathlibExt.Probability.KolmogorovContinuity.dyadicRationals ∩ Set.Icc 0 1 ∧
      scaledTime ((2 : NNReal) ^ N)
        ((t.1.1 : ℝ) / (((2 : NNReal) ^ N : NNReal) : ℝ)) = t.1.1 := by
  have htD : (t.1.1 : ℝ) ∈
      MathlibExt.Probability.KolmogorovContinuity.dyadicRationals := t.property
  obtain ⟨k, n, ht⟩ := htD
  have hH : (0 : ℝ) < (((2 : NNReal) ^ N : NNReal) : ℝ) := by positivity
  constructor
  · refine ⟨?_, div_nonneg (by positivity) hH.le, (div_le_one hH).2 ?_⟩
    · refine ⟨k, n + N, ?_⟩
      rw [ht, NNReal.coe_pow, NNReal.coe_ofNat, pow_add]
      field_simp
    · exact_mod_cast t.1.property.2
  · rw [scaledTime, Real.toNNReal_div (by positivity), Real.toNNReal_coe,
      Real.toNNReal_coe]
    exact mul_div_cancel₀ _ (by positivity)

private lemma holderWith_of_dist_le {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] {C r : NNReal} {f : α → β}
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist]
  have hrpow : ENNReal.ofReal (dist x y) ^ (r : ℝ) =
      ENNReal.ofReal (dist x y ^ (r : ℝ)) :=
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.property
  have hC : ENNReal.ofReal (C : ℝ) = (C : ENNReal) :=
    ENNReal.ofReal_coe_nnreal
  rw [hrpow]
  calc
    ENNReal.ofReal (dist (f x) (f y)) ≤
        ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) :=
      ENNReal.ofReal_le_ofReal (h x y)
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (dist x y ^ (r : ℝ)) :=
      ENNReal.ofReal_mul C.property
    _ = (C : ENNReal) * ENNReal.ofReal (dist x y ^ (r : ℝ)) := by rw [hC]

private lemma ae_holderEvent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (hq : 1 < q)
    (γ : NNReal) (hγ : 0 < γ) (hγlt : (γ : ℝ) < (q - 1) / p) (N : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ ⋃ C : PositiveNat, holderEvent X γ N C := by
  let H : NNReal := (2 : NNReal) ^ N
  have hscaled : ProbabilityTheory.IsKolmogorovProcess
      (fun t : ℝ => X (scaledTime H t)) P p (1 + (q - 1)) (M * H.rpow q) := by
    have hqeq : 1 + (q - 1) = q := by ring
    rw [hqeq]
    exact isKolmogorovProcess_scaled hX H
  have hae :=
    kolmogorov_ae_holder_on_dyadics_of_isKolmogorovProcess
      (X := fun t : ℝ => X (scaledTime H t)) (μ := P) (α := q - 1)
      (β := p) (M := M * H.rpow q) (by linarith) hscaled
      (γ : ℝ) hγlt (by exact_mod_cast hγ)
  filter_upwards [hae] with ω hω
  obtain ⟨C, hCpos, hC⟩ := hω
  obtain ⟨B, hCB⟩ := exists_nat_gt C
  have hBpos : 0 < B := by exact_mod_cast hCpos.trans hCB
  let Bp : PositiveNat := ⟨B, hBpos⟩
  apply Set.mem_iUnion.mpr
  refine ⟨Bp, ?_⟩
  apply holderWith_of_dist_le
  intro s t
  change dist (X s.1.1 ω) (X t.1.1 ω) ≤
    (B : ℝ) * dist s.1.1 t.1.1 ^ (γ : ℝ)
  let qs : ℝ := (s.1.1 : ℝ) / (H : ℝ)
  let qt : ℝ := (t.1.1 : ℝ) / (H : ℝ)
  have hs := normalized_compactDyadic N s
  have ht := normalized_compactDyadic N t
  have hbound := hC qs qt hs.1 ht.1
  rw [hs.2, ht.2] at hbound
  have hHpos : (0 : ℝ) < (H : ℝ) := by positivity
  have hHone : (1 : ℝ) ≤ (H : ℝ) := by
    dsimp [H]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hdist : |qs - qt| ≤ dist s.1.1 t.1.1 := by
    dsimp [qs, qt]
    rw [div_sub_div_same, abs_div, abs_of_pos hHpos]
    change dist s.1.1 t.1.1 / (H : ℝ) ≤ dist s.1.1 t.1.1
    exact div_le_self dist_nonneg hHone
  have hpow : |qs - qt| ^ (γ : ℝ) ≤ dist s.1.1 t.1.1 ^ (γ : ℝ) :=
    Real.rpow_le_rpow (abs_nonneg _) hdist γ.property
  calc
    dist (X s.1.1 ω) (X t.1.1 ω) ≤ C * |qs - qt| ^ (γ : ℝ) := by
      simpa only [Real.dist_eq] using hbound
    _ ≤ (B : ℝ) * |qs - qt| ^ (γ : ℝ) := by
      exact mul_le_mul_of_nonneg_right hCB.le (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ (B : ℝ) * dist s.1.1 t.1.1 ^ (γ : ℝ) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

private lemma ae_goodSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (hq : 1 < q)
    (γ : NNReal) (hγ : 0 < γ) (hγlt : (γ : ℝ) < (q - 1) / p) :
    ∀ᵐ ω ∂P, ω ∈ goodSet X γ := by
  simp only [goodSet, Set.mem_iInter]
  rw [ae_all_iff]
  intro N
  exact ae_holderEvent hX hq γ hγ hγlt N

private lemma continuous_pathLimit_compact {Ω : Type*} {X : NNReal → Ω → ℝ}
    {H C γ : NNReal} {ω : Ω} (hγ : 0 < γ)
    (hholder : HolderWith C γ
      (fun t : compactDyadics H => X t.1.1 ω)) :
    Continuous (fun t : Set.Icc (0 : NNReal) H => pathLimit X t ω) := by
  let D : Dense (compactDyadics H) := dense_compactDyadics H
  let f : compactDyadics H → ℝ := fun t => X t.1.1 ω
  let E : Set.Icc (0 : NNReal) H → ℝ := D.extend f
  have hf : UniformContinuous f := hholder.uniformContinuous hγ
  have hE : Continuous E := (D.uniformContinuous_extend hf).continuous
  have hpoint : ∀ t : Set.Icc (0 : NNReal) H, pathLimit X t ω = E t := by
    intro t
    let a : ℕ → Set.Icc (0 : NNReal) H := fun n =>
      ⟨dyadicApprox n t, by
        exact ⟨by positivity, (dyadicApprox_le n t).trans t.property.2⟩⟩
    let ad : ℕ → compactDyadics H := fun n => ⟨a n, dyadicApprox_mem n t⟩
    have ha : Tendsto a atTop (𝓝 t) := by
      rw [tendsto_subtype_rng]
      exact tendsto_dyadicApprox t
    have hseq : Tendsto (fun n => X (dyadicApprox n t) ω) atTop (𝓝 (E t)) := by
      convert hE.continuousAt.tendsto.comp ha using 1
      funext n
      have heq := D.extend_eq hf.continuous (ad n)
      simpa [E, f, a, ad] using heq.symm
    exact hseq.limUnder_eq
  rw [show (fun t : Set.Icc (0 : NNReal) H => pathLimit X t ω) = E from funext hpoint]
  exact hE

private lemma continuous_pathLimit_of_mem_goodSet {Ω : Type*}
    {X : NNReal → Ω → ℝ} {γ : NNReal} (hγ : 0 < γ) {ω : Ω}
    (hω : ω ∈ goodSet X γ) : Continuous (fun t => pathLimit X t ω) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨N, htN⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : NNReal) < 2)
  have hN : ω ∈ ⋃ C : PositiveNat, holderEvent X γ N C :=
    Set.mem_iInter.mp hω N
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hN
  have hrestricted := continuous_pathLimit_compact hγ hC
  have hon : ContinuousOn (fun u => pathLimit X u ω)
      (Set.Icc (0 : NNReal) ((2 : NNReal) ^ N)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hrestricted
  apply hon.continuousAt
  rw [show Set.Icc (0 : NNReal) ((2 : NNReal) ^ N) =
    Set.Iic ((2 : NNReal) ^ N) by ext u; simp]
  exact Iic_mem_nhds htN

private lemma pathLimit_zero {Ω : Type*} (X : NNReal → Ω → ℝ) (ω : Ω) :
    pathLimit X 0 ω = X 0 ω := by
  unfold pathLimit
  simp only [dyadicApprox_zero]
  exact tendsto_const_nhds.limUnder_eq

private lemma tendsto_dyadicValues_of_mem_goodSet {Ω : Type*}
    {X : NNReal → Ω → ℝ} {γ : NNReal} (hγ : 0 < γ) {ω : Ω}
    (hω : ω ∈ goodSet X γ) (t : NNReal) :
    Tendsto (fun n => X (dyadicApprox n t) ω) atTop (𝓝 (pathLimit X t ω)) := by
  obtain ⟨N, htN⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : NNReal) < 2)
  let H : NNReal := (2 : NNReal) ^ N
  have hN : ω ∈ ⋃ C : PositiveNat, holderEvent X γ N C :=
    Set.mem_iInter.mp hω N
  obtain ⟨C, hC⟩ := Set.mem_iUnion.mp hN
  let a : ℕ → Set.Icc (0 : NNReal) H := fun n =>
    ⟨dyadicApprox n t, by exact ⟨by positivity, (dyadicApprox_le n t).trans htN.le⟩⟩
  let ad : ℕ → compactDyadics H := fun n => ⟨a n, dyadicApprox_mem n t⟩
  have ha : Tendsto a atTop (𝓝 ⟨t, ⟨by positivity, htN.le⟩⟩) := by
    rw [tendsto_subtype_rng]
    exact tendsto_dyadicApprox t
  have had : CauchySeq ad := by
    have hac : CauchySeq a := ha.cauchySeq
    rw [Metric.cauchySeq_iff] at hac ⊢
    intro ε hε
    obtain ⟨K, hK⟩ := hac ε hε
    refine ⟨K, fun m hm n hn => ?_⟩
    simpa only [ad, a, Subtype.dist_eq] using hK m hm n hn
  have hout := (hC.uniformContinuous hγ).comp_cauchySeq had
  have hout' : CauchySeq (fun n => X (dyadicApprox n t) ω) := by
    simpa only [Function.comp_def, ad, a] using hout
  exact hout'.tendsto_limUnder

private lemma pathLimit_mem_closed {Ω : Type*} {X : NNReal → Ω → ℝ}
    {γ : NNReal} (hγ : 0 < γ) {ω : Ω} (hω : ω ∈ goodSet X γ)
    {S : Set ℝ} (hS : IsClosed S) (hXS : ∀ t, X t ω ∈ S) (t : NNReal) :
    pathLimit X t ω ∈ S := by
  apply hS.mem_of_tendsto (tendsto_dyadicValues_of_mem_goodSet hγ hω t)
  exact Eventually.of_forall fun n => hXS (dyadicApprox n t)

private lemma tendstoInMeasure_dyadicApprox {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (t : NNReal) :
    TendstoInMeasure P (fun n => X (dyadicApprox n t)) atTop (X t) := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε hεtop
  have hεpow0 : ε ^ p ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos_of_nonneg hε hX.p_pos.le)
  have hεpowtop : ε ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hX.p_pos.le hεtop
  have hd : Tendsto (fun n => edist (dyadicApprox n t) t) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    simpa using (tendsto_dyadicApprox t).edist hconst
  have hpow : Tendsto (fun n => edist (dyadicApprox n t) t ^ q) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := q)).continuousAt.tendsto.comp hd
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hX.q_pos] using h
  have hmul : Tendsto
      (fun n => (M : ENNReal) * edist (dyadicApprox n t) t ^ q) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (M : ENNReal)) hpow
      (Or.inr ENNReal.coe_ne_top)
    simpa using h
  have hbound : Tendsto
      (fun n => ((M : ENNReal) * edist (dyadicApprox n t) t ^ q) / ε ^ p)
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.div_const hmul (Or.inr hεpow0)
    simpa [zero_div] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun n => by
      have hmeas : AEMeasurable
          (fun ω => edist (X (dyadicApprox n t) ω) (X t ω) ^ p) P :=
        (hX.measurable_edist.pow_const p).aemeasurable
      have hmarkov := meas_ge_le_lintegral_div hmeas hεpow0 hεpowtop
      have hsubset :
          {ω | ε ≤ edist (X (dyadicApprox n t) ω) (X t ω)} ⊆
            {ω | ε ^ p ≤ edist (X (dyadicApprox n t) ω) (X t ω) ^ p} := by
        intro ω hω
        exact ENNReal.rpow_le_rpow hω hX.p_pos.le
      calc
        P {ω | ε ≤ edist (X (dyadicApprox n t) ω) (X t ω)}
            ≤ P {ω | ε ^ p ≤ edist (X (dyadicApprox n t) ω) (X t ω) ^ p} :=
          measure_mono hsubset
        _ ≤ (∫⁻ ω, edist (X (dyadicApprox n t) ω) (X t ω) ^ p ∂P) / ε ^ p :=
          hmarkov
        _ ≤ ((M : ENNReal) * edist (dyadicApprox n t) t ^ q) / ε ^ p :=
          ENNReal.div_le_div_right (hX.kolmogorovCondition _ _) _

private lemma ae_pathLimit_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : NNReal → Ω → ℝ} {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (hq : 1 < q)
    (γ : NNReal) (hγ : 0 < γ) (hγlt : (γ : ℝ) < (q - 1) / p) (t : NNReal) :
    pathLimit X t =ᵐ[P] X t := by
  obtain ⟨ns, hns, hsub⟩ := (tendstoInMeasure_dyadicApprox hX t).exists_seq_tendsto_ae
  have hgood := ae_goodSet hX hq γ hγ hγlt
  filter_upwards [hsub, hgood] with ω hsubω hgoodω
  have hfull := tendsto_dyadicValues_of_mem_goodSet hγ hgoodω t
  have hsubPath := hfull.comp hns.tendsto_atTop
  exact tendsto_nhds_unique hsubPath hsubω

private noncomputable def modification {Ω : Type*} (X : NNReal → Ω → ℝ) (γ : NNReal) :
    NNReal → Ω → ℝ := by
  classical
  exact fun t => (goodSet X γ).piecewise (pathLimit X t) (X 0)

/-- **Kolmogorov continuous-modification theorem for real-valued processes.**

A real-valued Kolmogorov process on `NNReal` whose time exponent is greater
than one has one modification with measurable coordinates and continuous paths
on every sample. The same modification agrees exactly at time zero and
preserves every closed set containing an original sample path. Fixed-time
almost-everywhere equality is asserted separately at each time; no
indistinguishability claim is made for the raw process. -/
theorem exists_continuous_modification {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : NNReal → Ω → ℝ}
    {p q : ℝ} {M : NNReal}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : NNReal → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous fun t => Y t ω) ∧
      (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ ω, Y 0 ω = X 0 ω) ∧
      (∀ S : Set ℝ, IsClosed S → ∀ ω, (∀ s, X s ω ∈ S) → ∀ t, Y t ω ∈ S) := by
  have hγr : 0 < (q - 1) / (2 * p) :=
    div_pos (sub_pos.mpr hq) (mul_pos (by norm_num) hX.p_pos)
  let γ : NNReal := ⟨(q - 1) / (2 * p), hγr.le⟩
  have hγ : 0 < γ := by exact_mod_cast hγr
  have hγlt : (γ : ℝ) < (q - 1) / p := by
    change (q - 1) / (2 * p) < (q - 1) / p
    exact div_lt_div_of_pos_left (sub_pos.mpr hq) hX.p_pos (by
      nlinarith [hX.p_pos])
  refine ⟨modification X γ, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa only [modification] using
      (Measurable.piecewise (measurableSet_goodSet hX γ) (measurable_pathLimit hX t)
        (hX.measurable 0))
  · intro ω
    by_cases hω : ω ∈ goodSet X γ
    · simpa [modification, hω] using continuous_pathLimit_of_mem_goodSet hγ hω
    · simpa [modification, hω] using
        (continuous_const : Continuous fun _ : NNReal => X 0 ω)
  · intro t
    have hgood := ae_goodSet hX hq γ hγ hγlt
    have heq := ae_pathLimit_eq hX hq γ hγ hγlt t
    filter_upwards [hgood, heq] with ω hgoodω heqω
    simpa [modification, hgoodω] using heqω
  · intro ω
    by_cases hω : ω ∈ goodSet X γ <;> simp [modification, hω, pathLimit_zero]
  · intro S hS ω hXS t
    by_cases hω : ω ∈ goodSet X γ
    · simpa [modification, hω] using pathLimit_mem_closed hγ hω hS hXS t
    · simpa [modification, hω] using hXS 0

end MathlibExt.Probability.KolmogorovContinuousModification
