/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.Occam
public import Cslib.MachineLearning.PACLearning.VCDimension
import CSLibExt.MachineLearning.PACLearning.Growth
import CSLibExt.MachineLearning.PACLearning.RiskBridge
import MathlibExt.Probability.UniformLaws
import MathlibExt.Probability.Statistics.Learning.Rademacher
import MathlibExt.Probability.LearningTheory.NoFreeLunch
import Mathlib.Probability.UniformOn
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The fundamental theorem of PAC learning

Valiant's model asks for a learner that, for every distribution and every target realizable by
the class, outputs with probability at least `1 - δ` a hypothesis of error at most `ε` from
polynomially many examples (L. G. Valiant, *A theory of the learnable*, Comm. ACM 27 (1984)).
Blumer, Ehrenfeucht, Haussler and Warmuth (1989) characterized the classes of binary hypotheses
that are learnable from finitely many examples, regardless of computation, as those of finite
Vapnik-Chervonenkis dimension. In the form of Shalev-Shwartz and Ben-David (Theorem 6.7, the
equivalence of items 4 and 6), a class `H` of functions `X → {0, 1}` is PAC learnable under the
0-1 loss if and only if it has finite VC dimension.

The statement uses CSLib's notions: `IsPACLearnable` over the realizable family
`realizableFamily H` (the joint distributions under which some concept of `H` has error `0`, so
the optimal error is `0`), and `HasFiniteVCDim` built on `SetShatters`. The instance space is
countable with measurable singletons, so every set of instances and of samples is measurable; the
textbook leaves measurability implicit.

For the upper bound, index the outputs of a consistent learner by its possible samples. This
gives a countable class to which the uniform deviation inequality applies. On each sample the
loss vectors are determined by the traces of `H`, so Sauer–Shelah and Massart bound their
Rademacher complexity. For the converse, average over all labellings of a finite shattered set
and all samples drawn uniformly from it.

## Sources

A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, "Learnability and the
Vapnik-Chervonenkis dimension", Journal of the ACM 36 (1989), 929-965; S. Shalev-Shwartz and
S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University
Press (2014), Definition 3.1 and Theorem 6.7.
-/

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MathlibExt.Probability.UniformLawsWanted

namespace isPACLearnable_realizableFamily_iff_hasFiniteVCDim

variable {X : Type*}

private theorem trace_bound {H : ConceptClass X Bool} (hH : HasFiniteVCDim H)
    (s : Finset X) {n : ℕ} (hs : s.card ≤ n) (hn : 1 ≤ n) :
    (traceFamily H s).card ≤ (vcDim H + 1) * n ^ vcDim H := by
  refine (card_traceFamily_le_sum_vcDim hH s).trans ?_
  rw [← Nat.range_succ_eq_Iic]
  calc ∑ k ∈ Finset.range (vcDim H + 1), s.card.choose k
      ≤ ∑ _k ∈ Finset.range (vcDim H + 1), n ^ vcDim H := by
        refine Finset.sum_le_sum fun k hk => (Nat.choose_le_pow _ _).trans ?_
        exact (Nat.pow_le_pow_left hs _).trans (Nat.pow_le_pow_right hn (by simpa using hk))
    _ = _ := by simp

/-- An upper bound on the Rademacher complexity at sample size `n`. -/
private noncomputable def bound (d n : ℕ) : ℝ :=
  Real.sqrt (2 * (Real.log (2 * (d + 1 : ℝ)) + d * Real.log n) / n)

private theorem empirical_bound {H : ConceptClass X Bool} (hH : HasFiniteVCDim H)
    {ι : Type*} [Nonempty ι] (h : ι → X → Bool) (hh : ∀ i, h i ∈ H)
    {n : ℕ} (hn : 1 ≤ n) (S : LabeledSample X Bool n) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
      ⨆ i, |(1 / (n : ℝ)) * ∑ k, (if σ k then (1 : ℝ) else -1) * zeroOneLoss (h i) (S k)|
      ≤ bound (vcDim H) n := by
  classical
  let s := Finset.univ.image (fun k => (S k).1)
  let x (k : Fin n) : s := ⟨(S k).1, Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩
  let loss (t : Finset s) (k : Fin n) : ℝ := if decide (x k ∈ t) = (S k).2 then 0 else 1
  let V := (traceFamily H s).image loss
  -- Include both signs to bound the absolute correlation by a one-sided maximum.
  let T := V ∪ V.image (fun v => -v)
  have hmem (i : ι) : (fun k => zeroOneLoss (h i) (S k)) ∈ V := by
    let t := Finset.univ.filter (fun a : s => h i a = true)
    have ht (a : s) : a ∈ t ↔ h i a = true := by simp [t]
    refine Finset.mem_image.mpr ⟨t, mem_traceFamily.mpr ⟨_, hh i, ht⟩, ?_⟩
    funext k
    have he : decide (x k ∈ t) = h i (S k).1 := by simp [ht, x]
    simp [loss, he, zeroOneLoss, Set.indicator_apply]
  have hT : T.Nonempty := ⟨_, Finset.mem_union_left _ (hmem (Classical.arbitrary ι))⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : T.sup' hT (fun v => Real.sqrt (∑ i, v i ^ 2)) ≤ Real.sqrt n := by
    refine Finset.sup'_le _ _ fun v hv => Real.sqrt_le_sqrt ?_
    have hv' : ∀ v ∈ V, ∀ k, (v k) ^ 2 ≤ 1 := by
      rintro _ hv k
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
      simp only [loss]; split <;> norm_num
    have hsq (k : Fin n) : (v k) ^ 2 ≤ 1 := by
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hv' v hv k
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        simpa only [Pi.neg_apply, neg_sq] using hv' w hw k
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun k _ => hsq k)
  have hcard : T.card ≤ 2 * (vcDim H + 1) * n ^ vcDim H := by
    have hs : s.card ≤ n := by
      simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := fun k => (S k).1))
    have hV := Finset.card_image_le (s := traceFamily H s) (f := loss)
    have hnV := Finset.card_image_le (s := V) (f := fun v => -v)
    have hu := Finset.card_union_le V (V.image (fun v => -v))
    have ht := trace_bound hH s hs hn
    dsimp only [T]
    change V.card ≤ _ at hV
    rw [mul_assoc]
    omega
  have hlog : Real.log T.card ≤ Real.log (2 * (vcDim H + 1 : ℝ)) + vcDim H * Real.log n := by
    have hx := Real.log_le_log (Nat.cast_pos.mpr (Finset.card_pos.mpr hT))
      (show (T.card : ℝ) ≤ (2 * (vcDim H + 1 : ℝ)) * n ^ vcDim H by exact_mod_cast hcard)
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hx
  have hrad : ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
        ⨆ i, |(1 / (n : ℝ)) * ∑ k, (if σ k then (1 : ℝ) else -1) * zeroOneLoss (h i) (S k)|
      ≤ empiricalRademacher T := by
    rw [empiricalRademacher_eq_sup' hT, ← div_eq_inv_mul]
    gcongr with σ
    apply ciSup_le
    intro i
    let v := fun k => zeroOneLoss (h i) (S k)
    let corr := fun v : Fin n → ℝ => (n : ℝ)⁻¹ * ∑ k, (if σ k then (1 : ℝ) else -1) * v k
    have hp := Finset.le_sup' corr (Finset.mem_union_left (V.image (fun v => -v)) (hmem i))
    have hm := Finset.le_sup' corr (s := T) (b := -v)
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hmem i)))
    change |1 / (n : ℝ) * _| ≤ T.sup' hT corr
    rw [one_div, abs_le]
    have hneg : corr (-v) = -corr v := by
      simp only [corr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [hneg] at hm
    exact ⟨by change -_ ≤ corr v; linarith, hp⟩
  refine hrad.trans ((empiricalRademacher_le_massart hT).trans ?_)
  calc T.sup' hT (fun v => Real.sqrt (∑ i, v i ^ 2)) * Real.sqrt (2 * Real.log T.card) / n
      ≤ Real.sqrt n * Real.sqrt (2 * (Real.log (2 * (vcDim H + 1 : ℝ)) +
          vcDim H * Real.log n)) / n := by gcongr
    _ = _ := by
      dsimp [bound]
      rw [Real.sqrt_div (by
        have := Real.log_nonneg (show 1 ≤ (T.card : ℝ) by exact_mod_cast hT.card_pos)
        linarith)]
      have hs := Real.sq_sqrt hn'.le
      have hp := Real.sqrt_pos.mpr hn'
      field_simp
      linear_combination (norm := ring) (Real.sqrt (2 * (Real.log (2 * (vcDim H + 1 : ℝ)) +
        vcDim H * Real.log n))) * hs

open Filter Topology in
private theorem exists_sample_size (d : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ n : ℕ, 1 ≤ n ∧ 2 * bound d n + ε / 2 ≤ ε ∧
      Real.exp (-(n : ℝ) * (ε / 2) ^ 2 / 2) ≤ δ := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hn
  have hc := (tendsto_const_nhds (x := Real.log (2 * (d + 1 : ℝ)))).div_atTop hn
  have hb : Tendsto (bound d) atTop (𝓝 0) := by
    unfold bound
    simpa only [mul_add, add_div, mul_div_assoc, mul_zero, add_zero, Real.sqrt_zero] using
      (((hc.add (hl.const_mul (d : ℝ))).const_mul 2).sqrt)
  have hex : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * (ε / 2) ^ 2 / 2)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (hn.atTop_mul_const_of_neg (neg_lt_zero.mpr (show 0 < (ε / 2) ^ 2 / 2 by positivity)))
    convert h using 2 with n
    simp only [Function.comp_apply]
    congr 1
    ring
  apply Filter.Eventually.exists (f := atTop)
  filter_upwards [eventually_ge_atTop 1, hb.eventually_lt_const (show 0 < ε / 4 by positivity),
    hex.eventually_lt_const hδ] with n hn he hd using ⟨hn, by linarith, hd.le⟩

variable [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]

private theorem pac_of_finite_vc {H : ConceptClass X Bool} (hH : HasFiniteVCDim H) :
    IsPACLearnable H (realizableFamily H) := by
  classical
  intro ε δ
  obtain ⟨n, hn, hsize, htail⟩ := exists_sample_size (vcDim H)
    (ε := (ε.val : ℝ)) (δ := (δ.val : ℝ)) (by exact_mod_cast ε.2.1) (by exact_mod_cast δ.2.1)
  rcases H.eq_empty_or_nonempty with rfl | ⟨h₀, hh₀⟩
  · exact ⟨0, fun _ _ => false, fun _ _ ⟨_, h, _⟩ => h.elim⟩
  let A : Learner X Bool n := fun S => if h : Realizable H S then h.choose else h₀
  have hA (S) : A S ∈ H := by
    dsimp [A]
    split <;> rename_i h
    · exact h.choose_spec.1
    · exact hh₀
  refine ⟨n, A, fun D _ hD => ?_⟩
  rw [optimalError_eq_zero_of_mem_realizableFamily hD, zero_add]
  obtain ⟨h, hh, he⟩ := hD
  let F (S : LabeledSample X Bool n) := zeroOneLoss (A S)
  let μ := Measure.pi (fun _ : Fin n => D)
  have hF (S) (z) : |F S z| ≤ 1 := by
    simp only [F, zeroOneLoss, Set.indicator_apply]; split <;> norm_num
  have hR : rademacherComplexity D F hn ≤ bound (vcDim H) n := by
    apply le_trans (integral_mono_of_nonneg (g := fun _ => bound (vcDim H) n) ?_
      (integrable_const _) ?_)
    · simp
    · apply Filter.Eventually.of_forall
      intro S
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun σ _ => Real.iSup_nonneg fun i => abs_nonneg _
    · apply Filter.Eventually.of_forall
      intro S
      have : Nonempty (LabeledSample X Bool n) := ⟨S⟩
      exact empirical_bound hH A hA hn S
  let good := {S | uniformDeviation D F hn S ≤
    2 * rademacherComplexity D F hn + (ε.val : ℝ) / 2}
  have hgood : 1 - Real.exp (-(n : ℝ) * ((ε.val : ℝ) / 2) ^ 2 / 2) ≤ μ.real good := by
    simpa [good, μ] using uniformDeviation_le_two_mul_rademacherComplexity_add D F
      (fun _ => .of_discrete) (b := 1) zero_lt_one hF hn
      (δ := (ε.val : ℝ) / 2) (by positivity)
  have hsub : {S | (ε.val : ℝ≥0∞) < error D (A S)} ≤ᵐ[μ] goodᶜ := by
    filter_upwards [ae_realizable_of_error_eq_zero D hh (.of_discrete) he n] with S hr herr
    intro hg
    have hfit (k) : F S (S k) = 0 := by
      have hk := hr.choose_spec.2 k
      simp [F, A, hr, zeroOneLoss, hk]
    have hi (T) : (∫ z, F T z ∂D) = (error D (A T)).toReal :=
      risk_zeroOneLoss_eq_toReal_error D _ .of_discrete
    have hbd : BddAbove (Set.range fun T =>
        |1 / (n : ℝ) * ∑ k, F T (S k) - ∫ z, F T z ∂D|) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨T, rfl⟩
      dsimp only
      rw [hi]
      have hp : (error D (A T)).toReal ≤ 1 := by
        exact (ENNReal.toReal_mono ENNReal.one_ne_top
          (show error D (A T) ≤ 1 from prob_le_one)).trans_eq ENNReal.toReal_one
      have hz (k) : 0 ≤ F T (S k) := by
        simp only [F, zeroOneLoss, Set.indicator_apply]; split <;> norm_num
      have hs : ∑ k, F T (S k) ≤ n := by
        simpa using Finset.sum_le_sum (s := Finset.univ)
          (fun k _ => (le_abs_self _).trans (hF T (S k)))
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [one_div, ← div_eq_inv_mul, abs_le]
      have hlo := div_nonneg (Finset.sum_nonneg (s := Finset.univ) fun k _ => hz k) hn'.le
      have hup := (div_le_one hn').mpr hs
      constructor <;> linarith [ENNReal.toReal_nonneg (a := error D (A T))]
    have hdev := le_ciSup hbd S
    change _ ≤ uniformDeviation D F hn S at hdev
    simp only [hfit, Finset.sum_const_zero, mul_zero, zero_sub, abs_neg, hi,
      abs_of_nonneg ENNReal.toReal_nonneg] at hdev
    change uniformDeviation D F hn S ≤ _ at hg
    have her := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (measure_ne_top D _)).2 herr
    simp only [ENNReal.coe_toReal] at her
    change (ε.val : ℝ) < (error D (A S)).toReal at her
    linarith
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.coe_ne_top).mp
  change μ.real _ ≤ (δ.val : ℝ)
  refine (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)).trans ?_
  change μ.real goodᶜ ≤ _
  rw [probReal_compl_eq_one_sub .of_discrete]
  linarith

/-- Enlarge the distinct points of a possibly repeating sample to a list of distinct points.
A learner can recover its original input by reading the designated positions of this list. -/
private theorem many_bad_targets {W : Type*} [Fintype W] [DecidableEq W] {m : ℕ}
    (hW : Fintype.card W = 2 * (m + 1)) (A : Learner W Bool m) (x : Fin m → W) :
    (Fintype.card (W → Bool) : ℝ) / 7 ≤
      ∑ f : W → Bool, if (1 / 8 : ℝ) <
        ((Finset.univ.filter fun w => A (sampleOf x f) w ≠ f w).card : ℝ) / Fintype.card W
        then (1 : ℝ) else 0 := by
  classical
  let s := Finset.univ.image x
  have hs : s.card ≤ m := by simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := x))
  obtain ⟨t, hst, _, ht⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ s)
    (show s.card ≤ m + 1 by omega) (show m + 1 ≤ Finset.univ.card (α := W) by
      rw [Finset.card_univ, hW]; omega)
  let e := (Finset.equivFinOfCardEq ht).symm
  let y (i : Fin (m + 1)) : W := e i
  let j (k : Fin m) := e.symm ⟨x k, hst (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  have hj (k) : y (j k) = x k := by simp [y, j]
  let B : Learner W Bool (m + 1) := fun S => A (S ∘ j)
  have hB (f : W → Bool) : B (sampleOf y f) = A (sampleOf x f) := by
    unfold B
    congr 1
    funext k
    simp [sampleOf, hj]
  have hl := nfl_tail B y (Subtype.val_injective.comp e.injective) hW (Nat.succ_pos m)
  rw [Finset.sum_boole]
  have hc : Fintype.card (W → Bool) = 2 ^ Fintype.card W := by simp [Fintype.card_pi]
  rw [hc, Nat.cast_pow, Nat.cast_ofNat, div_eq_inv_mul]
  refine le_trans (by simpa only [one_div] using hl) (Nat.cast_le.mpr (Finset.card_le_card ?_))
  intro f hf
  have herr := (Finset.mem_filter.mp hf).2
  rw [hB] at herr
  simp only [one_div]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, herr.trans_le ?_⟩
  gcongr
  exact Finset.card_le_card (fun w hw => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2.2⟩)

private theorem uniform_real {W : Type*} [MeasurableSpace W] [Fintype W]
    [MeasurableSingletonClass W] (p : W → Prop) [DecidablePred p] :
    (uniformOn Set.univ).real {w | p w} =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card W := by
  have hs : {w | p w} = (Finset.univ.filter p : Finset W) := by ext; simp
  rw [measureReal_def, uniformOn_univ, hs, Measure.count_apply_finset]
  simp

private theorem finite_vc_of_pac {H : ConceptClass X Bool}
    (hH : IsPACLearnable H (realizableFamily H)) : HasFiniteVCDim H := by
  classical
  let q : Set.Ioo (0 : NNReal) 1 := ⟨1 / 8, by constructor <;> norm_num⟩
  obtain ⟨m, A, hA⟩ := hH q q
  apply hasFiniteVCDim_iff.mpr
  refine ⟨2 * (m + 1), fun U hU => ?_⟩
  by_contra! hsize
  obtain ⟨W, hWU, hW⟩ := Finset.exists_subset_card_eq hsize.le
  have hsh := hU.subset (Finset.coe_subset.mpr hWU)
  have hcard : Fintype.card W = 2 * (m + 1) := by simpa using hW
  have : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let μ : Measure W := uniformOn Set.univ
  let L : Learner W Bool m := fun S w => A (fun k => ((S k).1.val, (S k).2)) w.val
  let bad (f : W → Bool) (x : Fin m → W) : Prop :=
    (1 / 8 : ℝ) < ((Finset.univ.filter fun w => L (sampleOf x f) w ≠ f w).card : ℝ) /
      Fintype.card W
  have hupper (f : W → Bool) : (∑ x : Fin m → W, if bad f x then (1 : ℝ) else 0) ≤
      Fintype.card (Fin m → W) / 8 := by
    let label (w : W) : X × Bool := (w.val, f w)
    let D := μ.map label
    have hmap : MeasurePreserving label μ D := ⟨.of_discrete, rfl⟩
    have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (uniformOn Set.univ))
    have : IsProbabilityMeasure D := inferInstanceAs (IsProbabilityMeasure (μ.map label))
    have hrisk (h : X → Bool) : (error D h).toReal =
        ((Finset.univ.filter fun w : W => h w ≠ f w).card : ℝ) / Fintype.card W := by
      change (D {p | h p.1 ≠ p.2}).toReal = _
      rw [← hmap.measure_preimage (MeasurableSet.of_discrete.nullMeasurableSet)]
      exact uniform_real _
    have hreal : D ∈ realizableFamily H := by
      obtain ⟨c, hc, hp⟩ := hsh (Subtype.val '' {w | f w = true})
        (fun z ⟨w, _, hw⟩ => hw ▸ w.property)
      have hcf (w : W) : c w = f w := by
        have he := Set.ext_iff.mp hp w.val
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro hc
          obtain ⟨z, hz, heq⟩ := he.mp ⟨hc, w.property⟩
          exact Subtype.val_injective heq ▸ hz
        · exact fun hf => (he.mpr ⟨w, hf, rfl⟩).1
      refine ⟨c, hc, ?_⟩
      change D {p | c p.1 ≠ p.2} = 0
      rw [← hmap.measure_preimage MeasurableSet.of_discrete.nullMeasurableSet]
      simp [label, Set.preimage, hcf]
    let B := {S : LabeledSample X Bool m | (q.val : ℝ≥0∞) < error D (A S)}
    have hp := hA D hreal
    rw [optimalError_eq_zero_of_mem_realizableFamily hreal, zero_add] at hp
    have hpi := measurePreserving_pi (fun _ : Fin m => μ) (fun _ => D) (fun _ => hmap)
    have hpre : (fun (x : Fin m → W) i => label (x i)) ⁻¹' B = {x | bad f x} := by
      ext x
      change (q.val : ℝ≥0∞) < error D _ ↔ _
      have ht : error D (A (fun i => label (x i))) ≠ ⊤ := measure_ne_top D _
      rw [← ENNReal.toReal_lt_toReal ENNReal.coe_ne_top ht, hrisk]
      change (q.val : ℝ≥0∞).toReal < _ ↔ (1 / 8 : ℝ) < _
      rw [show (q.val : ℝ≥0∞).toReal = 1 / 8 by norm_num [q]]
      congr!
    change (Measure.pi fun _ : Fin m => D) B ≤ _ at hp
    rw [← hpi.measure_preimage MeasurableSet.of_discrete.nullMeasurableSet] at hp
    change (Measure.pi fun _ : Fin m => μ) ((fun x i => label (x i)) ⁻¹' B) ≤ _ at hp
    rw [hpre] at hp
    have hprod : (Measure.pi fun _ : Fin m => μ) = uniformOn Set.univ := by
      simpa [μ] using (uniformOn_pi (f := fun _ : Fin m => (Set.univ : Set W))).symm
    rw [hprod] at hp
    have hpr := ENNReal.toReal_mono ENNReal.coe_ne_top hp
    change (uniformOn Set.univ).real {x | bad f x} ≤ (q.val : ℝ) at hpr
    rw [uniform_real] at hpr
    rw [Finset.sum_boole]
    have hp' := (div_le_iff₀ (show (0 : ℝ) < Fintype.card (Fin m → W) by positivity)).mp hpr
    simpa [q, div_eq_mul_inv, mul_comm] using hp'
  have hlower (x : Fin m → W) : (Fintype.card (W → Bool) : ℝ) / 7 ≤
      ∑ f : W → Bool, if bad f x then (1 : ℝ) else 0 := many_bad_targets hcard L x
  have ht := (Finset.sum_le_sum (s := Finset.univ) (fun x _ => hlower x)).trans
    ((Finset.sum_comm ..).le.trans (Finset.sum_le_sum (s := Finset.univ) (fun f _ => hupper f)))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  have hpos : 0 < (Fintype.card (Fin m → W) : ℝ) * (Fintype.card (W → Bool) : ℝ) := by
    positivity
  linarith

end isPACLearnable_realizableFamily_iff_hasFiniteVCDim

/-- **The fundamental theorem of PAC learning.** On a countable instance space with measurable
singletons, a class `H` of binary hypotheses is PAC learnable over its realizable distributions
(CSLib's `IsPACLearnable H (realizableFamily H)`) if and only if it has finite VC dimension
(CSLib's `HasFiniteVCDim H`) (Blumer, Ehrenfeucht, Haussler and Warmuth, *Learnability and the
Vapnik-Chervonenkis dimension*, J. ACM 36 (1989), 929-965; Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, 2014, Theorem 6.7, equivalence of items 4 and 6). -/
public theorem isPACLearnable_realizableFamily_iff_hasFiniteVCDim {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] (H : ConceptClass X Bool) :
    IsPACLearnable H (realizableFamily H) ↔ HasFiniteVCDim H :=
  ⟨isPACLearnable_realizableFamily_iff_hasFiniteVCDim.finite_vc_of_pac,
    isPACLearnable_realizableFamily_iff_hasFiniteVCDim.pac_of_finite_vc⟩

end Cslib.MachineLearning.PACLearning
