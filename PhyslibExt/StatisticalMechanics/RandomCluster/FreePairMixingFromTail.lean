/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTailTriviality
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKTwoBoxDecoupling
public import MathlibExt.Dynamics.Ergodic.BirkhoffErgodic

/-!
# Pair mixing of the free FK–Ising measure from tail triviality

The free infinite-volume random-cluster measure at `q = 2` is ergodic under a single axis
translation and satisfies the pair-mixing property for multi-edge open events.

## i. Overview

Translating finitely many edges far along the first coordinate axis moves them outside any finite
window. Combined with tail triviality of the free measure, this shows that every event invariant
under the unit axis translation is trivial, so that translation is ergodic. By the Birkhoff
ergodic theorem and dominated convergence, the Cesàro averages of the correlations
`μ(T open ∩ shift_k⁻¹(U open))` converge to `μ(T open) μ(U open)`. By the FKG inequality each
correlation gap is nonnegative, so a small average forces some translation with all gaps below a
given `δ`, which is the pair-mixing property. `freeInfiniteVolume_axisShift_ergodic` and
`freeInfiniteVolume_pairMixing_all_parameters` are proved unconditionally (only `1 ≤ d` and
`0 < p < 1`, at `q = 2`).

## ii. Key results

- `freeInfiniteVolume_axisShift_ergodic` : the unit axis translation is ergodic for the free
  measure.
- `freeInfiniteVolume_pairCorrelationAverage_tendsto` : Cesàro averages of translated
  correlations converge to the product of the probabilities.
- `freeInfiniteVolume_pairMixing_all_parameters` : the free measure satisfies pair mixing.

## iii. Table of contents

- A. Axis translations
- B. Ergodicity of the axis translation
- C. Averaged correlations
- D. Pair mixing

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}

/-! ## A. Axis translations -/

/-- The unit translation of `ℤ^d` along the first coordinate axis. -/
noncomputable def freeAxisTranslation (hd : 1 ≤ d) :
    Multiplicative (Site d) :=
  Multiplicative.ofAdd fun i => if i = ⟨0, hd⟩ then 1 else 0

/-- The translation of `ℤ^d` by `n` along the first coordinate axis. -/
noncomputable def freeAxisTranslationPower (hd : 1 ≤ d) (n : ℕ) :
    Multiplicative (Site d) :=
  Multiplicative.ofAdd fun i => if i = ⟨0, hd⟩ then (n : ℤ) else 0

/-- The translation by `n` is the `n`-th power of the unit axis translation. -/
lemma freeAxisTranslationPower_eq_pow (hd : 1 ≤ d) (n : ℕ) :
    freeAxisTranslationPower hd n = (freeAxisTranslation hd) ^ n := by
  unfold freeAxisTranslationPower freeAxisTranslation
  rw [← ofAdd_nsmul]
  congr 1
  funext i
  simp only [Pi.smul_apply]
  by_cases hi : i = ⟨0, hd⟩ <;> simp [hi]

/-- Shifting by `n` along the axis is the `n`-th iterate of the unit shift. -/
lemma shift_freeAxisTranslationPower (hd : 1 ≤ d) (n : ℕ) :
    (shift (freeAxisTranslationPower hd n) :
      ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) =
      (shift (freeAxisTranslation hd))^[n] := by
  rw [freeAxisTranslationPower_eq_pow]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, shift_mul, ih, Function.iterate_succ]

/-- The set of endpoints of the edges in `F`. -/
private noncomputable def freeAxisVertexSupport
    (F : Finset (Sym2 (Site d))) : Finset (Site d) :=
  F.biUnion fun e => {e.out.1, e.out.2}

/-- An endpoint of an edge of `F` lies in the endpoint set of `F`. -/
private lemma mem_freeAxisVertexSupport_of_mem
    {F : Finset (Sym2 (Site d))} {e : Sym2 (Site d)} (he : e ∈ F)
    {x : Site d} (hx : x ∈ e) : x ∈ freeAxisVertexSupport F := by
  rw [freeAxisVertexSupport, Finset.mem_biUnion]
  refine ⟨e, he, ?_⟩
  have hout : s(e.out.1, e.out.2) = e := e.out_eq
  have hx' : x ∈ s(e.out.1, e.out.2) := by
    rw [hout]
    exact hx
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    (Sym2.mem_iff.mp hx')

/-- A finite edge set translated far enough along the axis lies outside any given window. -/
lemma freeAxisTranslationPower_escape (hd : 1 ≤ d)
    (F : Finset (Sym2 (Site d))) (k : ℕ) :
    ∃ n : ℕ,
      (↑(F.image (fun e => (freeAxisTranslationPower hd n)⁻¹ • e)) :
          Set (Sym2 (Site d))) ⊆ (fkTailEdgeWindow d k)ᶜ := by
  let V := freeAxisVertexSupport F
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ x ∈ V, (x ⟨0, hd⟩).natAbs ≤ M :=
    ⟨V.sup fun x => (x ⟨0, hd⟩).natAbs,
      fun x hx => Finset.le_sup (f := fun x => (x ⟨0, hd⟩).natAbs) hx⟩
  refine ⟨M + k + 1, ?_⟩
  intro z hz
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
  obtain ⟨e, he, rfl⟩ := hz
  rw [Set.mem_compl_iff]
  intro hwindow
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxV : x ∈ V :=
        mem_freeAxisVertexSupport_of_mem he (Sym2.mem_mk_left x y)
      have hxBound : x ⟨0, hd⟩ ≤ (M : ℤ) := by
        have hnat := hM x hxV
        have habs := Int.le_natAbs (a := x ⟨0, hd⟩)
        omega
      have hxval :
          ((freeAxisTranslationPower hd (M + k + 1))⁻¹ • x) ⟨0, hd⟩ =
            x ⟨0, hd⟩ - (M + k + 1 : ℤ) := by
        change (-(Multiplicative.toAdd
          (freeAxisTranslationPower hd (M + k + 1))) + x) ⟨0, hd⟩ = _
        simp [freeAxisTranslationPower]
        ring
      have hxOutside :
          (freeAxisTranslationPower hd (M + k + 1))⁻¹ • x ∉ box d k := by
        rw [box, Set.mem_ofPred_eq]
        intro hall
        have hcoord := hall ⟨0, hd⟩
        rw [hxval] at hcoord
        have hneg : x ⟨0, hd⟩ - (M + k + 1 : ℤ) ≤ -(k + 1 : ℤ) := by
          omega
        have hcast :
            ((x ⟨0, hd⟩ - (M + k + 1 : ℤ)).natAbs : ℤ) =
              -(x ⟨0, hd⟩ - (M + k + 1 : ℤ)) := by
          rw [← Int.natAbs_neg, Int.natAbs_of_nonneg]
          omega
        have hcoord' :
            ((x ⟨0, hd⟩ - (M + k + 1 : ℤ)).natAbs : ℤ) ≤ k := by
          exact_mod_cast hcoord
        rw [hcast] at hcoord'
        omega
      apply hxOutside
      apply hwindow ((freeAxisTranslationPower hd (M + k + 1))⁻¹ • x)
      rw [Percolation.smul_sym2_mk]
      exact Sym2.mem_mk_left _ _

/-! ## B. Ergodicity of the axis translation -/

/-- At `q = 2`, the unit axis translation is ergodic for the free infinite-volume measure. -/
theorem freeInfiniteVolume_axisShift_ergodic
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    _root_.Ergodic
      (shift (freeAxisTranslation hd) :
        ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) := by
  let mu := (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    bdp_freeIV_isTranslationInvariant hp hp1
  refine Ergodic.of_preimage_eq (hti (freeAxisTranslation hd)) ?_
  intro s hs hinv
  have hinvPow : ∀ n : ℕ,
      shift (freeAxisTranslationPower hd n) ⁻¹' s = s := by
    intro n
    rw [shift_freeAxisTranslationPower]
    exact Function.IsFixedPt.preimage_iterate hinv n
  obtain ⟨t, ht, hae⟩ :=
    ati_sequenceInvariant_aeTail (fkTailEdgeWindow d)
      fkTailEdgeWindow_mono (freeAxisTranslationPower hd)
      (freeAxisTranslationPower_escape hd) hti s hs hinvPow
  rw [eventuallyEmptyOrUniv_iff']
  rcases freeInfiniteVolume_tail_trivial hp hp1 t ht with ht0 | ht1
  · exact Or.inl (hae.trans (ae_eq_empty.mpr ht0))
  · right
    apply hae.trans
    rw [ae_eq_univ]
    rw [measure_compl ht.measurableSet (measure_ne_top mu t), ht1,
      measure_univ]
    simp

/-! ## C. Averaged correlations -/

/-- The indicator of a multi-edge open event takes values in `[0, 1]`. -/
private lemma free_moInd_mem_Icc (T : Finset (Sym2 (Site d)))
    (omega : ConfigSpace (Sym2 (Site d))) :
    fmu_moInd T omega ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fmu_moInd_eq_indicator]
  by_cases h : omega ∈ fmu_multiOpen T <;> simp [h]

/-- Birkhoff averages of the indicator of a multi-edge open event take values in `[0, 1]`. -/
private lemma free_birkhoffAverage_moInd_mem_Icc
    (Tmap : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
    (T : Finset (Sym2 (Site d))) (n : ℕ)
    (omega : ConfigSpace (Sym2 (Site d))) :
    birkhoffAverage ℝ Tmap (fmu_moInd T) n omega ∈ Set.Icc (0 : ℝ) 1 := by
  rcases n with _ | n
  · simp [birkhoffAverage]
  · have hterm : ∀ k ∈ Finset.range (n + 1),
        fmu_moInd T (Tmap^[k] omega) ∈ Set.Icc (0 : ℝ) 1 :=
      fun k _ => free_moInd_mem_Icc T _
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range (n + 1),
        fmu_moInd T (Tmap^[k] omega) :=
      Finset.sum_nonneg fun k hk => (hterm k hk).1
    have hsum1 : (∑ k ∈ Finset.range (n + 1),
        fmu_moInd T (Tmap^[k] omega)) ≤ (n + 1 : ℝ) := by
      calc
        (∑ k ∈ Finset.range (n + 1),
            fmu_moInd T (Tmap^[k] omega))
            ≤ ∑ _k ∈ Finset.range (n + 1), (1 : ℝ) :=
              Finset.sum_le_sum fun k hk => (hterm k hk).2
        _ = (n + 1 : ℝ) := by simp
    simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
    norm_num [Nat.cast_add, Nat.cast_one] at hsum1 ⊢
    constructor
    · exact mul_nonneg (inv_nonneg.mpr (by positivity)) hsum0
    · calc
        (n + 1 : ℝ)⁻¹ *
            (∑ k ∈ Finset.range (n + 1), fmu_moInd T (Tmap^[k] omega))
            ≤ (n + 1 : ℝ)⁻¹ * (n + 1 : ℝ) :=
              mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr (by positivity))
        _ = 1 := inv_mul_cancel₀ (by positivity)

/-- The integral of an indicator times a Birkhoff average of another indicator is the Cesàro
average of the translated joint probabilities. -/
private lemma freeAxis_integral_mul_birkhoffAverage
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) (n : ℕ) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    ∫ omega, fmu_moInd T omega *
        birkhoffAverage ℝ (shift (freeAxisTranslation hd))
          (fmu_moInd U) n omega ∂mu =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (fmu_multiOpen T ∩
          shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  have hpoint : (fun omega => fmu_moInd T omega *
      birkhoffAverage ℝ (shift (freeAxisTranslation hd))
        (fmu_moInd U) n omega) =
      fun omega => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        fmu_moInd T omega *
          fmu_moInd U (shift (freeAxisTranslationPower hd k) omega) := by
    funext omega
    simp only [birkhoffAverage, birkhoffSum, smul_eq_mul,
      shift_freeAxisTranslationPower]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hpoint, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [fmu_moInd_mul_shift_eq,
      MeasureTheory.integral_indicator_const (1 : ℝ)]
    · simp
    · exact (fmu_multiOpen_measurable T).inter
        ((fmu_multiOpen_measurable U).preimage
          (measurable_shift (freeAxisTranslationPower hd k)))
  · intro k hk
    exact fmu_integrable_moInd_mul_shift
      (μ := mu) (freeAxisTranslationPower hd k) T U

/-- Cesàro averages of the translated joint probabilities of two multi-edge open events converge
to the product of their probabilities. -/
lemma freeInfiniteVolume_pairCorrelationAverage_tendsto
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (fmu_multiOpen T ∩
          shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U))
      atTop (𝓝 (mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U))) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  let Tmap := (shift (freeAxisTranslation hd) :
    ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
  have herg : _root_.Ergodic Tmap mu :=
    freeInfiniteVolume_axisShift_ergodic hd hp hp1
  have hbirk := MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic
    herg (fmu_integrable_moInd (μ := mu) U)
  let F : ℕ → ConfigSpace (Sym2 (Site d)) → ℝ := fun n omega =>
    fmu_moInd T omega * birkhoffAverage ℝ Tmap (fmu_moInd U) n omega
  have hlim : ∀ᵐ omega ∂mu, Tendsto (fun n => F n omega) atTop
      (𝓝 (fmu_moInd T omega * mu.real (fmu_multiOpen U))) := by
    filter_upwards [hbirk] with omega homega
    have hmass : (∫ x, fmu_moInd U x ∂mu) =
        mu.real (fmu_multiOpen U) := fmu_integral_moInd U
    rw [hmass] at homega
    exact tendsto_const_nhds.mul homega
  have hmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact MeasureTheory.AEStronglyMeasurable.mul
      (fmu_integrable_moInd (μ := mu) T).aestronglyMeasurable
      (MathlibExt.Probability.BirkhoffErgodicL1.integrable_birkhoffAverage_of_measurePreserving
        herg.toMeasurePreserving (fmu_integrable_moInd (μ := mu) U) n).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ omega ∂mu, ‖F n omega‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with omega
    have hT := free_moInd_mem_Icc T omega
    have hU := free_birkhoffAverage_moInd_mem_Icc Tmap U n omega
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hT.1 hU.1)]
    exact (mul_le_mul hT.2 hU.2 hU.1 zero_le_one).trans_eq (mul_one 1)
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := mu) (fun _ => (1 : ℝ)) hmeas (by fun_prop) hbound hlim
  have hlimitIntegral :
      (∫ omega, fmu_moInd T omega * mu.real (fmu_multiOpen U) ∂mu) =
        mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U) := by
    rw [MeasureTheory.integral_mul_const, fmu_integral_moInd]
  rw [hlimitIntegral] at hdct
  simpa only [F, Tmap, mu, freeAxis_integral_mul_birkhoffAverage hd hp hp1 T U]
    using hdct

/-! ## D. Pair mixing -/

/-- The correlation gap between a multi-edge open event and the translate by `k` of another. -/
private noncomputable def freePairGap
    (hd : 1 ≤ d) (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (T U : Finset (Sym2 (Site d))) (k : ℕ) : ℝ :=
  mu.real (fmu_multiOpen T ∩
      shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U) -
    mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U)

/-- The correlation gap is nonnegative, by the FKG inequality. -/
private lemma freePairGap_nonneg
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) (k : ℕ) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    0 ≤ freePairGap hd mu T U k := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    bdp_freeIV_isTranslationInvariant hp hp1
  have hfkg := ftb_freeIV_fkg_multiOpen hp hp1 T
    (U.image (fun e => (freeAxisTranslationPower hd k)⁻¹ • e))
  have htrans :
      mu.real (fmu_multiOpen
          (U.image (fun e => (freeAxisTranslationPower hd k)⁻¹ • e))) =
        mu.real (fmu_multiOpen U) := by
    rw [← fmu_shift_multiOpen (freeAxisTranslationPower hd k) U]
    exact fmc_real_preimage_shift hti (freeAxisTranslationPower hd k)
      (fmu_multiOpen_measurable U)
  rw [htrans] at hfkg
  unfold freePairGap
  rw [fmu_shift_multiOpen (freeAxisTranslationPower hd k) U]
  exact sub_nonneg.mpr hfkg

/-- Cesàro averages of the correlation gaps tend to zero. -/
private lemma freePairGapAverage_tendsto
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        freePairGap hd mu T U k) atTop (𝓝 0) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  let c := mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U)
  have hcorr := freeInfiniteVolume_pairCorrelationAverage_tendsto
    hd hp hp1 T U
  have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hsub : Tendsto (fun n : ℕ =>
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (fmu_multiOpen T ∩
          shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U) - c)
      atTop (𝓝 0) := by
    simpa only [mu, c, sub_self] using hcorr.sub hc
  apply hsub.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  dsimp only [c, mu]
  simp only [freePairGap, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- At `q = 2`, the free infinite-volume measure satisfies pair mixing: for every finite family of
multi-edge open events and every `δ > 0` some translation makes all correlation gaps below `δ`. -/
theorem freeInfiniteVolume_pairMixing_all_parameters
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    fmu_PairMixing (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  intro P delta hdelta
  have htotal : Tendsto (fun n : ℕ =>
      ∑ T ∈ P, ∑ U ∈ P, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        freePairGap hd mu T U k) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum P (fun T hT =>
      tendsto_finsetSum P (fun U hU =>
        freePairGapAverage_tendsto hd hp hp1 T U))
  have hevent : ∀ᶠ (n : ℕ) in atTop,
      (∑ T ∈ P, ∑ U ∈ P, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        freePairGap hd mu T U k) < delta :=
    htotal.eventually (eventually_lt_nhds hdelta)
  obtain ⟨n, hn, havg⟩ := ((eventually_ge_atTop 1).and hevent).exists
  have havg' : (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k < delta := by
    calc
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k =
          ∑ T ∈ P, ∑ U ∈ P, (n : ℝ)⁻¹ *
            ∑ k ∈ Finset.range n, freePairGap hd mu T U k := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro T hT
              rw [Finset.sum_comm]
      _ < delta := havg
  have hnR : (0 : ℝ) < n := by positivity
  have hsumlt :
      (∑ k ∈ Finset.range n,
        ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k) <
      ∑ _k ∈ Finset.range n, delta := by
    calc
      (∑ k ∈ Finset.range n,
          ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k) =
          (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k) := by
              field_simp
      _ < (n : ℝ) * delta := mul_lt_mul_of_pos_left havg' hnR
      _ = ∑ _k ∈ Finset.range n, delta := by simp
  obtain ⟨k, hk, hkdelta⟩ := Finset.exists_lt_of_sum_lt hsumlt
  refine ⟨freeAxisTranslationPower hd k, ?_⟩
  intro T hT U hU
  have hinner : freePairGap hd mu T U k ≤
      ∑ U' ∈ P, freePairGap hd mu T U' k := by
    exact Finset.single_le_sum
      (fun U' hU' => freePairGap_nonneg hd hp hp1 T U' k) hU
  have houter : (∑ U' ∈ P, freePairGap hd mu T U' k) ≤
      ∑ T' ∈ P, ∑ U' ∈ P, freePairGap hd mu T' U' k := by
    exact Finset.single_le_sum
      (fun T' hT' => Finset.sum_nonneg fun U' hU' =>
        freePairGap_nonneg hd hp hp1 T' U' k) hT
  have hgaplt : freePairGap hd mu T U k < delta :=
    lt_of_le_of_lt (hinner.trans houter) hkdelta
  change abs (freePairGap hd mu T U k) < delta
  rw [abs_of_nonneg (freePairGap_nonneg hd hp hp1 T U k)]
  exact hgaplt

end FK

end StatMech
