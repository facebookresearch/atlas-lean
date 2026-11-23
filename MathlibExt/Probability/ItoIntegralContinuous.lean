/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegral
public import MathlibExt.Probability.ItoDensity
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Data.Finset.Sort

/-!
# Continuous modification of the Itô integral

A progressively measurable process that is locally square integrable has an Itô integral with a
continuous modification. The construction chooses one rapidly convergent sequence of elementary
integrands on expanding compact horizons. A maximal inequality and Borel–Cantelli give locally
uniform convergence on one full-measure set; outside that set the modification is the zero path,
so every sample path is continuous.

## Main result

* `ProbabilityTheory.itoIntegral_continuous_modification`: an all-sample continuous process agreeing
  almost surely with the selected Itô-integral representative at each fixed time.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Section 3.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

private theorem elementary_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {F : Filtration ℝ≥0 mΩ} (K : ElementaryIntegrand F) {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hB : Continuous fun t ↦ B t ω) : Continuous fun t ↦ K.itoIntegral B t ω := by
  unfold ElementaryIntegrand.itoIntegral
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul
    ((hB.comp (continuous_const.min continuous_id)).sub
      (hB.comp (continuous_const.min continuous_id)))

private theorem integrandDist_mono {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t) :
    integrandDist P X Y s ≤ integrandDist P X Y t :=
  lintegral_mono fun _ ↦ lintegral_mono_set
    (Set.Ioc_subset_Ioc_right (by exact_mod_cast hst))

private theorem approximation_smaller {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}
    {K : ℕ → ElementaryIntegrand F} {s t : ℝ≥0} (hst : s ≤ t)
    (hK : Tendsto (fun n ↦ integrandDist P (K n).toProcess H t) atTop (𝓝 0)) :
    Tendsto (fun n ↦ integrandDist P (K n).toProcess H s) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK (fun _ ↦ bot_le)
    fun _ ↦ integrandDist_mono hst

private theorem path_limit_ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B H : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    {t : ℝ≥0} (hH : Measurable fun p : ℝ × Ω ↦ restrictIoc H t p.1.toNNReal p.2)
    {K : ℕ → ElementaryIntegrand F}
    (hK : Tendsto (fun n ↦ integrandDist P (K n).toProcess H t) atTop (𝓝 0))
    {g : Ω → ℝ} (hg : ∀ᵐ ω ∂P,
      Tendsto (fun n ↦ (K n).itoIntegral B t ω) atTop (𝓝 (g ω))) :
    g =ᵐ[P] itoIntegral P F B H t := by
  have hlim := tendsto_toL2_itoIntegral hB hBF hInd hH hK
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ n, (toL2 P ((K n).itoIntegral B t) : Ω → ℝ)
      =ᵐ[P] (K n).itoIntegral B t := fun n ↦ by
    have hm := (K n).memLp_itoIntegral hB t
    simp only [toL2, hm, ↓reduceDIte]
    exact hm.coeFn_toLp
  filter_upwards [hg, hae, ae_all_iff.2 hrep, itoIntegral_ae_eq P F B H t]
    with ω hω hω' hr hi
  rw [hi]
  exact tendsto_nhds_unique (hω.comp hns.tendsto_atTop)
    (hω'.congr fun n ↦ hr (ns n))

private noncomputable def fallback {Ω : Type*} (G : Set Ω) (X : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if ω ∈ G then X t ω else 0

private theorem fallback_continuous {Ω : Type*} {G : Set Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ ω ∈ G, Continuous fun t ↦ X t ω) (ω : Ω) :
    Continuous fun t ↦ fallback G X t ω := by
  classical
  by_cases hω : ω ∈ G
  · simpa only [fallback, ite_eq_left hω] using hX ω hω
  · simpa only [fallback, ite_eq_right hω] using (continuous_const : Continuous fun _ : ℝ≥0 ↦
      (0 : ℝ))

private theorem fallback_ae_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {G : Set Ω} (hG : ∀ᵐ ω ∂P, ω ∈ G) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    fallback G X t =ᵐ[P] X t := by
  filter_upwards [hG] with ω hω
  simp only [fallback, ite_eq_left hω]

private theorem limit_continuous {X : ℕ → ℝ≥0 → ℝ}
    (hX : ∀ n, Continuous (X n))
    (hc : ∀ m : ℕ, UniformCauchySeqOn X atTop (Set.Iic (m : ℝ≥0))) :
    Continuous fun t ↦ limUnder atTop (fun n ↦ X n t) := by
  have hp : ∀ t, Tendsto (fun n ↦ X n t) atTop
      (𝓝 (limUnder atTop (fun n ↦ X n t))) := by
    intro t
    obtain ⟨m, hm⟩ := exists_nat_ge t
    exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ((hc m).cauchySeq hm))
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨m, hm⟩ := exists_nat_gt t
  have hu := (hc m).tendstoUniformlyOn_of_tendsto fun u _ ↦ hp u
  have hcont := hu.continuousOn
    (Eventually.of_forall fun n ↦ (hX n).continuousOn).frequently
  exact hcont.continuousAt (Iic_mem_nhds hm)

private theorem finite_maximal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X F P) (T : ℝ≥0)
    (s : Finset ℝ≥0) (hT : T ∈ s) (hs : ∀ t ∈ s, t ≤ T) (ε : ℝ≥0) :
    ε * P {ω | ∃ t ∈ s, (ε : ℝ) ≤ |X t ω|} ≤ ENNReal.ofReal (∫ ω, |X T ω| ∂P) := by
  classical
  have hc : 0 < s.card := Finset.card_pos.mpr ⟨T, hT⟩
  let e := s.orderEmbOfFin rfl
  let τ : ℕ → ℝ≥0 := fun k ↦ if hk : k < s.card then e ⟨k, hk⟩ else T
  have hτ : Monotone τ := by
    intro i j hij
    dsimp [τ]
    split_ifs with hi hj hj
    · exact e.monotone hij
    · exact hs _ (s.orderEmbOfFin_mem rfl _)
    · omega
    · rfl
  let Fs : Filtration ℕ mΩ :=
    { seq := fun k ↦ F (τ k)
      mono' := fun _ _ h ↦ F.mono (hτ h)
      le' := fun k ↦ F.le (τ k) }
  have hm : Martingale (fun k ↦ X (τ k)) Fs P :=
    ⟨fun k ↦ hX.stronglyMeasurable (τ k), fun i j hij ↦ hX.condExp_ae_eq (hτ hij)⟩
  have ha : Submartingale (fun k ω ↦ |X (τ k) ω|) Fs P := by
    refine ⟨fun k ↦ ?_, fun i j hij ↦ ?_, fun k ↦ (hm.integrable k).abs⟩
    · simpa only [Real.norm_eq_abs] using (hm.stronglyMeasurable k).norm
    · filter_upwards [hm.condExp_ae_eq hij,
        norm_condExp_le (μ := P) (m := Fs i) (f := X (τ j))] with ω hω hω'
      rw [← hω]
      simpa only [Real.norm_eq_abs] using hω'
  have hend : τ (s.card - 1) = T := by
    dsimp [τ]
    rw [dite_eq_left (by omega)]
    have he := s.orderEmbOfFin_last rfl hc
    change e _ = T
    rw [show e _ = s.max' ⟨T, hT⟩ from he]
    exact le_antisymm (hs _ (Finset.max'_mem _ _)) (Finset.le_max' _ _ hT)
  have hevent : {ω | ∃ t ∈ s, (ε : ℝ) ≤ |X t ω|} =
      {ω | (ε : ℝ) ≤ (Finset.range (s.card - 1 + 1)).sup'
        Finset.nonempty_range_add_one (fun k ↦ |X (τ k) ω|)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, hε⟩
      let k := (s.orderIsoOfFin rfl).symm ⟨t, ht⟩
      have hk : (k : ℕ) ∈ Finset.range (s.card - 1 + 1) := by
        simp only [Finset.mem_range]
        have := k.isLt
        omega
      have hkt : τ k = t := by
        simp only [τ, dite_eq_left k.isLt, e, ← Finset.coe_orderIsoOfFin_apply]
        simp [k]
      exact hε.trans (hkt ▸ Finset.le_sup' (fun k ↦ |X (τ k) ω|) hk)
    · intro hε
      obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup'
        (show (Finset.range (s.card - 1 + 1)).Nonempty from
          Finset.nonempty_range_add_one) (fun k ↦ |X (τ k) ω|)
      have hk' : k < s.card := by
        have := Finset.mem_range.mp hk
        omega
      refine ⟨τ k, ?_, ?_⟩
      · dsimp [τ]
        rw [dite_eq_left hk']
        exact s.orderEmbOfFin_mem rfl _
      · rwa [heq] at hε
  rw [hevent]
  have h := maximal_ineq ha (fun _ _ ↦ abs_nonneg _) (ε := ε) (s.card - 1)
  refine h.trans ?_
  rw [hend]
  exact ENNReal.ofReal_le_ofReal
    (setIntegral_le_integral (hX.integrable T).abs (Eventually.of_forall fun _ ↦ abs_nonneg _))

private theorem integral_abs_le_L2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ENNReal.ofReal (∫ ω, |f ω| ∂P) ≤ eLpNorm f 2 P := by
  have h1 : ENNReal.ofReal (∫ ω, |f ω| ∂P) = eLpNorm f 1 P := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    simp only [Real.enorm_eq_ofReal_abs]
    exact ofReal_integral_eq_lintegral_ofReal (hf.integrable (by norm_num)).abs
      (Eventually.of_forall fun _ ↦ abs_nonneg _)
  rw [h1]
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

private theorem countable_maximal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X F P) (T : ℝ≥0)
    (q : ℕ → ℝ≥0) (hq : ∀ n, q n ≤ T) (ε : ℝ≥0) :
    ε * P {ω | ∃ n, (ε : ℝ) ≤ |X (q n) ω|} ≤
      ENNReal.ofReal (∫ ω, |X T ω| ∂P) := by
  classical
  let A : ℕ → Set Ω := fun n ↦ {ω | ∃ k < n, (ε : ℝ) ≤ |X (q k) ω|}
  have hA : Monotone A := by
    intro i j hij ω hω
    rcases hω with ⟨k, hk, hε⟩
    exact ⟨k, hk.trans_le hij, hε⟩
  have heq : {ω | ∃ n, (ε : ℝ) ≤ |X (q n) ω|} = ⋃ n, A n := by
    ext ω
    simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n + 1, n, Nat.lt_succ_self n, hn⟩
    · rintro ⟨_, k, _, hk⟩
      exact ⟨k, hk⟩
  rw [heq, hA.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  let s := insert T ((Finset.range n).image q)
  have hs : ∀ t ∈ s, t ≤ T := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · rfl
    · rcases Finset.mem_image.mp ht with ⟨k, _, rfl⟩
      exact hq k
  refine le_trans (mul_le_mul_of_nonneg_left (measure_mono ?_) (bot_le : 0 ≤ (ε : ℝ≥0∞)))
    (finite_maximal hX T s (Finset.mem_insert_self _ _) hs ε)
  rintro ω ⟨k, hk, hε⟩
  exact ⟨q k, Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨k, Finset.mem_range.mpr hk, rfl⟩), hε⟩

private theorem dense_grid_bound {X : ℝ≥0 → ℝ} (hX : Continuous X) (T : ℝ≥0)
    (ε : ℝ) (hgrid : ∀ n, |X (min (TopologicalSpace.denseSeq ℝ≥0 n) T)| ≤ ε) :
    ∀ t ≤ T, |X t| ≤ ε := by
  let g : ℝ≥0 → Set.Iic T := fun t ↦ ⟨min t T, min_le_right _ _⟩
  have hg : Function.Surjective g := fun t ↦ ⟨t, by
    apply Subtype.ext
    exact min_eq_left t.property⟩
  have hgc : Continuous g := (continuous_id.min continuous_const).subtype_mk _
  have hd := hg.denseRange.comp (TopologicalSpace.denseRange_denseSeq ℝ≥0) hgc
  intro t ht
  exact hd.induction_on (p := fun x : Set.Iic T ↦ |X x| ≤ ε) ⟨t, ht⟩
    (isClosed_le ((hX.comp continuous_subtype_val).abs) continuous_const)
    hgrid

private theorem increments_uniformCauchy {X : ℕ → ℝ≥0 → ℝ} {s : Set ℝ≥0}
    (hb : ∀ᶠ n in atTop, ∀ t ∈ s, |X (n + 1) t - X n t| ≤ (1 / 2 : ℝ) ^ n) :
    UniformCauchySeqOn X atTop s := by
  have hu := tendstoUniformlyOn_tsum_nat_eventually summable_geometric_two
    (f := fun n t ↦ X (n + 1) t - X n t)
    (hb.mono fun n hn t ht ↦ by simpa only [Real.norm_eq_abs] using hn t ht)
  have hconst : TendstoUniformlyOn (fun _ : ℕ ↦ X 0) (X 0) atTop s :=
    by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Eventually.of_forall fun _ _ _ ↦ by simpa using hε
  have hv := hu.add hconst
  have heq : (fun N t ↦ (∑ n ∈ Finset.range N, (X (n + 1) t - X n t)) + X 0 t) = X := by
    funext N t
    rw [Finset.sum_range_sub (fun n ↦ X n t)]
    ring
  change TendstoUniformlyOn
    (fun N t ↦ (∑ n ∈ Finset.range N, (X (n + 1) t - X n t)) + X 0 t) _ atTop s at hv
  rw [heq] at hv
  exact hv.uniformCauchySeqOn

private theorem ae_uniformCauchy {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {X : ℕ → ℝ≥0 → Ω → ℝ}
    (hm : ∀ n, Martingale (X n) F P) (h2 : ∀ n t, MemLp (X n t) 2 P)
    (hc : ∀ᵐ ω ∂P, ∀ n, Continuous fun t ↦ X n t ω) (m : ℕ)
    (hb : ∀ n ≥ m, eLpNorm (X (n + 1) m - X n m) 2 P ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n)) :
    ∀ᵐ ω ∂P, UniformCauchySeqOn (fun n t ↦ X n t ω) atTop (Set.Iic (m : ℝ≥0)) := by
  let q : ℕ → ℝ≥0 := fun k ↦ min (TopologicalSpace.denseSeq ℝ≥0 k) m
  let ε : ℕ → ℝ≥0 := fun n ↦ NNReal.mk ((1 / 2 : ℝ) ^ n) (by positivity)
  let A : ℕ → Set Ω := fun n ↦ {ω | ∃ k,
    (ε n : ℝ) ≤ |X (n + 1) (q k) ω - X n (q k) ω|}
  have hbound : ∀ n ≥ m, P (A n) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
    intro n hn
    have hmax := countable_maximal ((hm (n + 1)).sub (hm n)) (m : ℝ≥0) q
      (fun _ ↦ min_le_right _ _) (ε n)
    have hε : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (ε n : ℝ≥0∞) :=
      by simpa only [ε, NNReal.coe_mk] using (ENNReal.ofReal_coe_nnreal (p := ε n))
    have h := hmax.trans ((integral_abs_le_L2 ((h2 (n + 1) m).sub (h2 n m))).trans
      (hb n hn))
    change (ε n : ℝ≥0∞) * P (A n) ≤ _ at h
    rw [hε] at h
    have h0 : (ε n : ℝ≥0∞) ≠ 0 := by
      have hp : 0 < ε n := by
        change 0 < (1 / 2 : ℝ) ^ n
        positivity
      exact_mod_cast hp.ne'
    have htop : (ε n : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
    apply (ENNReal.mul_le_mul_iff_left h0 htop).mp
    simpa only [mul_comm] using h
  have hsum : ∑' n, P (A n) ≠ ∞ := by
    have hr : Summable (fun n ↦ ((P (A n)).toNNReal : ℝ)) :=
      (summable_geometric_two.mul_left 2).of_norm_bounded_eventually_nat
        ((eventually_ge_atTop m).mono fun n hn ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
          have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound n hn)
          rw [ENNReal.toReal_ofReal
            (show 0 ≤ 2 * (1 / 2 : ℝ) ^ n by positivity)] at h
          simpa only [ENNReal.toReal] using h)
    have h := ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hr
    simpa only [ENNReal.coe_toNNReal (measure_ne_top P _)] using h
  filter_upwards [ae_eventually_notMem hsum, hc] with ω hω hcont
  apply increments_uniformCauchy
  refine hω.mono fun n hn ↦ ?_
  exact dense_grid_bound ((hcont (n + 1)).sub (hcont n)) m ((1 / 2 : ℝ) ^ n)
    (fun k ↦ le_of_lt (lt_of_not_ge (fun hk ↦ hn ⟨k, hk⟩)))

private theorem rapid_approximants {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B H : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance) (F s) P)
    (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∃ K : ℕ → ElementaryIntegrand F, ∀ n,
      integrandDist P (K n).toProcess H n ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∧
      ∀ m : ℕ, m ≤ n → dist (toL2 P ((K n).itoIntegral B m))
        (itoIntegralL2 P F B H m) ≤ (1 / 2 : ℝ) ^ (2 * n) := by
  classical
  have := hB.isGaussianProcess.isProbabilityMeasure
  have happ : ∀ n : ℕ, IsItoApproximable P F H n := fun n ↦
    isItoApproximable_of_isProgressive hH n (hH2 n)
  have hex : ∀ n : ℕ, ∃ K : ElementaryIntegrand F,
      integrandDist P K.toProcess H n ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ∧
      ∀ m : ℕ, m ≤ n → dist (toL2 P (K.itoIntegral B m))
        (itoIntegralL2 P F B H m) ≤ (1 / 2 : ℝ) ^ (2 * n) := by
    intro n
    obtain ⟨hHm, A, hA⟩ := happ n
    have hfinite : ∀ᶠ k in atTop, ∀ m ∈ Finset.range (n + 1),
        dist (toL2 P ((A k).itoIntegral B m)) (itoIntegralL2 P F B H m) <
          (1 / 2 : ℝ) ^ (2 * n) := by
      apply (eventually_all_finset _).mpr
      intro m hm
      have hmn : (m : ℝ≥0) ≤ n := by
        exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
      have ht := tendsto_toL2_itoIntegral hB hBF hInd (happ m).1
        (approximation_smaller hmn hA)
      have hd : Tendsto (fun k ↦ dist (toL2 P ((A k).itoIntegral B m))
          (itoIntegralL2 P F B H m)) atTop (𝓝 0) := by
        simpa only [dist_self] using ht.dist (tendsto_const_nhds (x := itoIntegralL2 P F B H m))
      exact hd.eventually (gt_mem_nhds (by positivity))
    have herr := hA.eventually (gt_mem_nhds
      (ENNReal.ofReal_pos.mpr (show 0 < (1 / 2 : ℝ) ^ n by positivity)))
    obtain ⟨k, hk, hk'⟩ := (herr.and hfinite).exists
    refine ⟨A k, hk.le, fun m hm ↦ (hk' m ?_).le⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  choose K hK using hex
  exact ⟨K, hK⟩

private theorem rapid_tendsto {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ} {K : ℕ → ElementaryIntegrand F}
    (hK : ∀ n, integrandDist P (K n).toProcess H n ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) (t : ℝ≥0) :
    Tendsto (fun n ↦ integrandDist P (K n).toProcess H t) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp summable_geometric_two.tendsto_atTop_zero
  obtain ⟨m, hm⟩ := exists_nat_ge t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  refine (eventually_ge_atTop m).mono fun n hn ↦ ?_
  exact (integrandDist_mono (hm.trans (by exact_mod_cast hn))).trans (hK n)

private theorem terminal_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {B H : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {K : ℕ → ElementaryIntegrand F}
    (hK : ∀ n, ∀ m : ℕ, m ≤ n → dist (toL2 P ((K n).itoIntegral B m))
      (itoIntegralL2 P F B H m) ≤ (1 / 2 : ℝ) ^ (2 * n)) (m n : ℕ) (hmn : m ≤ n) :
    eLpNorm ((K (n + 1)).itoIntegral B m - (K n).itoIntegral B m) 2 P ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n) := by
  have ha := (K (n + 1)).memLp_itoIntegral hB m
  have hb := (K n).memLp_itoIntegral hB m
  have he : eLpNorm ((K (n + 1)).itoIntegral B m - (K n).itoIntegral B m) 2 P =
      ENNReal.ofReal (dist (toL2 P ((K (n + 1)).itoIntegral B m))
        (toL2 P ((K n).itoIntegral B m))) := by
    simp only [toL2, ha, hb, ↓reduceDIte]
    exact (Lp.edist_toLp_toLp _ _ ha hb).symm.trans (Lp.edist_dist _ _)
  rw [he]
  have hd : dist (toL2 P ((K (n + 1)).itoIntegral B m)) (toL2 P ((K n).itoIntegral B m)) ≤
      2 * (1 / 2 : ℝ) ^ (2 * n) := by
    have ht := dist_triangle (toL2 P ((K (n + 1)).itoIntegral B m))
      (itoIntegralL2 P F B H m) (toL2 P ((K n).itoIntegral B m))
    rw [dist_comm (itoIntegralL2 P F B H m)] at ht
    have hp : (1 / 2 : ℝ) ^ (2 * (n + 1)) ≤ (1 / 2 : ℝ) ^ (2 * n) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact ht.trans ((add_le_add (hK (n + 1) m (by omega)) (hK n m hmn)).trans (by linarith))
  calc _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (2 * n)) := ENNReal.ofReal_le_ofReal hd
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (2 * (1 / 2 : ℝ) ^ n)) := by
      congr 1
      rw [Nat.mul_comm 2 n, pow_mul, pow_two]
      ring
    _ = _ := ENNReal.ofReal_mul (by positivity)

/-- **Continuous modification.** The Itô integral admits a modification with continuous paths:
there is a process `J` with continuous paths such that `J t = ∫_0^t H dB` almost surely for each
`t` (Karatzas–Shreve 1991, Section 3.2). `ProbabilityTheory.itoIntegral` chooses its version
separately at each time, so it is only determined up to a null set that may depend on `t`; the
statement therefore asks for a modification rather than for a process indistinguishable from
this particular choice. Any two continuous modifications are indistinguishable. -/
public theorem itoIntegral_continuous_modification {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBF : Adapted F B)
    (hInd : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω ↦ B t ω - B s ω) inferInstance)
      (F s) P)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsProgressive F H)
    (hH2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖H u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞) :
    ∃ J : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t ↦ J t ω) ∧
      ∀ t, J t =ᵐ[P] itoIntegral P F B H t := by
  classical
  have hpre := hB.toIsPreBrownianReal
  have := hpre.isGaussianProcess.isProbabilityMeasure
  obtain ⟨K, hK⟩ := rapid_approximants hpre hBF hInd hH hH2
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous fun t ↦ (K n).itoIntegral B t ω :=
    hB.cont.mono fun ω hω n ↦ elementary_continuous (K n) hω
  have hu : ∀ m : ℕ, ∀ᵐ ω ∂P, UniformCauchySeqOn
      (fun n t ↦ (K n).itoIntegral B t ω) atTop (Set.Iic (m : ℝ≥0)) := fun m ↦
    ae_uniformCauchy (fun n ↦ (K n).martingale_itoIntegral hpre hBF hInd)
      (fun n t ↦ (K n).memLp_itoIntegral hpre t) hc m
      (fun n hn ↦ terminal_bound hpre (fun n ↦ (hK n).2) m n hn)
  let G : Set Ω := {ω | (∀ n, Continuous fun t ↦ (K n).itoIntegral B t ω) ∧
    ∀ m : ℕ, UniformCauchySeqOn (fun n t ↦ (K n).itoIntegral B t ω) atTop (Set.Iic (m : ℝ≥0))}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := hc.and (ae_all_iff.mpr hu)
  let X : ℝ≥0 → Ω → ℝ := fun t ω ↦ limUnder atTop (fun n ↦ (K n).itoIntegral B t ω)
  have hX : ∀ ω ∈ G, Continuous fun t ↦ X t ω := fun ω hω ↦
    limit_continuous hω.1 hω.2
  refine ⟨fallback G X, fallback_continuous hX, fun t ↦ ?_⟩
  refine (fallback_ae_eq hG X t).trans (path_limit_ae_eq hpre hBF hInd
    (measurable_restrictIoc (IsProgressive.measurable_toNNReal hH) t)
    (rapid_tendsto (fun n ↦ (hK n).1) t) ?_)
  filter_upwards [hG] with ω hω
  obtain ⟨m, hm⟩ := exists_nat_ge t
  exact tendsto_nhds_limUnder
    (cauchySeq_tendsto_of_complete ((hω.2 m).cauchySeq hm))

end ProbabilityTheory
