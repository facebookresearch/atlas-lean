/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalMutualInformation
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import MathlibExt.InformationTheory.GallagerExponent

/-!
# Strong converse for discrete memoryless channels

`channelCoding_strong_converse` shows that above capacity the average decoding error
tends to one uniformly over codes. We maximize a smoothed entropy on the input simplex
to find a single output reference for all channel rows. An exponential moment bound then
tensorizes over the letters of each codeword.
-/

namespace MathlibExt.InformationTheory.ChannelCodingWanted

open MeasureTheory Filter Topology Real Convexity _root_.InformationTheory
open MathlibExt.InformationTheory.GallagerExponent

section

variable {α β : Type*} [Fintype α] [Fintype β]

private def average (p k : α → ℝ) : ℝ := ∑ a, p a * k a

private lemma average_mix (p k : α → ℝ) (a : α) (t : ℝ) [DecidableEq α] :
    average (fun i => (1 - t) * p i + t * (if i = a then 1 else 0)) k =
      average p k + t * (k a - average p k) := by
  simp only [average, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

-- At a maximizer of the smoothed entropy, moving towards any vertex has
-- nonpositive right derivative. The resulting inequality holds for every row.
private lemma exists_reference [Nonempty α] (w : α → β → ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (hs : ∀ a, ∑ b, w a b = 1) (u : α → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (p : α → ℝ), (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧
      ∀ a, u a - ∑ b, w a b * log (average p (w · b) + δ) ≤
        average p u - ∑ b, average p (w · b) * log (average p (w · b) + δ) := by
  classical
  let S : Set (α → ℝ) := {p | (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1}
  have hS : IsCompact S := by
    have h := isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ α).continuous
    rwa [StdSimplex.range_toFun_comp_weights, show
      (⋂ i : α, {s : α → ℝ | 0 ≤ s i}) ∩ {s | ∑ i, s i = 1} = S by ext; simp [S]] at h
  let F (p : α → ℝ) := average p u + ∑ b, negMulLog (average p (w · b) + δ)
  have hc : Continuous F := by unfold F average; fun_prop
  obtain ⟨p, ⟨hp, hp1⟩, hmax⟩ := hS.exists_isMaxOn (by
    refine ⟨fun i => if i = Classical.arbitrary α then 1 else 0, ?_, by simp⟩
    intro i; dsimp only; split <;> norm_num) hc.continuousOn
  refine ⟨p, hp, hp1, fun a => ?_⟩
  let v (b : β) := average p (w · b)
  have hv b : 0 ≤ v b := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hw i b)
  have hv1 : ∑ b, v b = 1 := by
    simp only [v, average]
    rw [Finset.sum_comm]
    simpa only [← Finset.mul_sum, hs, mul_one] using hp1
  let G (t : ℝ) := (average p u + t * (u a - average p u)) +
    ∑ b, negMulLog (v b + δ + t * (w a b - v b))
  have hG : HasDerivAt G ((u a - average p u) +
      ∑ b, (-log (v b + δ) - 1) * (w a b - v b)) 0 := by
    have affine (l k : ℝ) : HasDerivAt (fun t : ℝ => l + t * k) k 0 := by
      simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const k).const_add l)
    apply (affine _ _).add (HasDerivAt.fun_sum _)
    intro b _
    have hb := affine (v b + δ) (w a b - v b)
    have hd := (hasDerivAt_negMulLog (x := v b + δ + 0 * (w a b - v b))
      (by simpa using (add_pos_of_nonneg_of_pos (hv b) hδ).ne')).comp 0 hb
    simpa [Function.comp_def] using hd
  have hle : (u a - average p u) + ∑ b, (-log (v b + δ) - 1) * (w a b - v b) ≤ 0 := by
    apply le_of_tendsto hG.tendsto_slope_zero_right
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    simp only [zero_add, smul_eq_mul]
    apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.1.le)
    apply sub_nonpos.mpr
    let r (i : α) := (1 - t) * p i + t * (if i = a then 1 else 0)
    have hr : r ∈ S := by
      refine ⟨fun i => add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hp i))
        (mul_nonneg ht.1.le (by split <;> norm_num)), ?_⟩
      simp [r, Finset.sum_add_distrib, ← Finset.mul_sum, hp1]
    have he : G t = F r := by
      simp only [G, F, r, average_mix, v]
      congr 1
      exact Finset.sum_congr rfl fun b _ => congrArg negMulLog (by ring)
    simpa [he, G, F, v] using (isMaxOn_iff.mp hmax r hr)
  change u a - ∑ b, w a b * log (v b + δ) ≤ average p u - ∑ b, v b * log (v b + δ)
  have he : ∀ b, (-log (v b + δ) - 1) * (w a b - v b) =
      v b * log (v b + δ) - w a b * log (v b + δ) + (v b - w a b) := fun b => by ring
  simp only [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, hv1, hs] at hle
  linarith

private noncomputable abbrev row (W : α → PMF β) (a : α) (b : β) := ((W a) b).toReal

private lemma entropy_bound {γ : Type*} [Fintype γ] (q : PMF γ) :
    shannonEntropy q ≤ Fintype.card γ / log 2 := by
  apply div_le_div_of_nonneg_right _ (log_nonneg one_le_two)
  calc ∑ b, negMulLog (q b).toReal ≤ ∑ _ : γ, (1 : ℝ) :=
         Finset.sum_le_sum fun b _ => (negMulLog_le_one_sub_self ENNReal.toReal_nonneg).trans
           (sub_le_self _ ENNReal.toReal_nonneg)
       _ = _ := by simp

omit [Fintype α] [Fintype β] in
private lemma information_bddAbove [Finite α] [Finite β] (W : α → PMF β) :
    BddAbove (Set.range fun p : PMF α =>
      finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  refine ⟨Fintype.card α / log 2 + Fintype.card β / log 2, ?_⟩
  rintro _ ⟨p, rfl⟩
  dsimp only
  rw [finiteMutualInformation_eq]
  exact (sub_le_self _ (shannonEntropy_nonneg _)).trans
    (add_le_add (entropy_bound _) (entropy_bound _))

-- Scale the smoothed output reference so its mass is below the code growth
-- factor and its expected log likelihood ratio is negative for every input.
omit [Fintype α] in
private lemma exists_output_weight [Finite α] [Nonempty α] (W : α → PMF β) {R : ℝ}
    (hR : (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) < R) :
    ∃ q : β → ℝ, (∀ b, 0 < q b) ∧ (∑ b, q b) < exp (R * log 2) ∧
      ∀ a, ∑ b, row W a b * (log (row W a b) - log (q b)) < 0 := by
  let := Fintype.ofFinite α
  let C := ⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))
  obtain ⟨s, hCs, hsR⟩ := exists_between (mul_lt_mul_of_pos_right hR (log_pos one_lt_two))
  change C * log 2 < s at hCs
  have hev : ∀ᶠ δ : ℝ in 𝓝 0, exp s * (1 + Fintype.card β * δ) < exp (R * log 2) := by
    have hc : Continuous (fun δ : ℝ => exp s * (1 + Fintype.card β * δ)) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using exp_lt_exp.mpr hsR))
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hδR⟩ := (hpos.and (hev.filter_mono nhdsWithin_le_nhds)).exists
  let u a := ∑ b, row W a b * log (row W a b)
  obtain ⟨p, hp, hp1, hrow⟩ := exists_reference (row W) (fun _ _ => ENNReal.toReal_nonneg)
    (fun a => sum_toReal_eq_one (W a)) u hδ
  let v b := average p (row W · b)
  have hv b : 0 ≤ v b := Finset.sum_nonneg fun a _ => mul_nonneg (hp a) ENNReal.toReal_nonneg
  have hvδ b : 0 < v b + δ := add_pos_of_nonneg_of_pos (hv b) hδ
  have hv1 : ∑ b, v b = 1 := by
    simp only [v, average]
    rw [Finset.sum_comm]
    simpa only [← Finset.mul_sum, row, sum_toReal_eq_one, mul_one] using hp1
  let P : PMF α := PMF.ofFintype (fun a => ENNReal.ofReal (p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hp a), hp1, ENNReal.ofReal_one])
  have hP a : (P a).toReal = p a := ENNReal.toReal_ofReal (hp a)
  -- The two formulas for the derivative of Gallager's exponent identify the finite
  -- entropy expression with mutual information in nats.
  have hI := (hasDerivAt_gallagerE0_zero_nats P W).unique (hasDerivAt_gallagerE0_zero P W)
  simp only [hP, ← Finset.mul_sum] at hI
  have hcap : average p u - ∑ b, v b * log (v b) ≤ C * log 2 := by
    rw [show average p u - ∑ b, v b * log (v b) = _ from hI]
    exact mul_le_mul_of_nonneg_right (le_ciSup (information_bddAbove W) P) (log_nonneg one_le_two)
  have hmono : ∑ b, v b * log (v b) ≤ ∑ b, v b * log (v b + δ) := by
    apply Finset.sum_le_sum
    intro b _
    rcases (hv b).eq_or_lt with hb | hb
    · simp [← hb]
    · exact mul_le_mul_of_nonneg_left (log_le_log hb (le_add_of_nonneg_right hδ.le)) hb.le
  refine ⟨fun b => exp s * (v b + δ), fun b => mul_pos (exp_pos _) (hvδ b), ?_, fun a => ?_⟩
  · simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hv1, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] using hδR
  · have hlog b : log (exp s * (v b + δ)) = s + log (v b + δ) := by
      rw [log_mul (exp_pos _).ne' (hvδ b).ne', log_exp]
    dsimp only
    simp only [hlog]
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, row, sum_toReal_eq_one, one_mul]
    change u a - (s + ∑ b, row W a b * log (v b + δ)) < 0
    have ha := hrow a
    change u a - ∑ b, row W a b * log (v b + δ) ≤
      average p u - ∑ b, v b * log (v b + δ) at ha
    linarith

private noncomputable def tilt (w q t : ℝ) := w * exp (t * (log w - log q))

-- A single positive tilt makes the exponential moment strictly less than one
-- for every row, since at zero all moments equal one and their slopes are negative.
omit [Fintype α] in
private lemma exists_tilt [Finite α] [Nonempty α] (W : α → PMF β) (q : β → ℝ)
    (h : ∀ a, ∑ b, row W a b * (log (row W a b) - log (q b)) < 0) :
    ∃ t > 0, ∃ c ∈ Set.Ico (0 : ℝ) 1, ∀ a, ∑ b, tilt (row W a b) (q b) t ≤ c := by
  classical
  let := Fintype.ofFinite α
  let K a t := ∑ b, tilt (row W a b) (q b) t
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hev (a : α) : ∀ᶠ t in 𝓝[>] (0 : ℝ), K a t < 1 := by
    have hd : HasDerivAt (K a) (∑ b, row W a b * (log (row W a b) - log (q b))) 0 := by
      apply HasDerivAt.fun_sum
      intro b _
      unfold tilt
      simpa using ((((hasDerivAt_id' (0 : ℝ)).mul_const
        (log (row W a b) - log (q b))).exp).const_mul (row W a b))
    have h0 : K a 0 = 1 := by simp [K, tilt, row, sum_toReal_eq_one]
    filter_upwards [hd.tendsto_slope_zero_right.eventually (gt_mem_nhds (h a)), hpos] with t ht ht0
    simp only [zero_add, smul_eq_mul, h0] at ht
    by_contra! hle
    exact ht.not_ge (mul_nonneg (inv_nonneg.mpr ht0.le) (sub_nonneg.mpr hle))
  obtain ⟨t, ht, hK⟩ := (hpos.and (eventually_all.mpr hev)).exists
  obtain ⟨a, _, ha⟩ := Finset.univ.exists_max_image (K · t) Finset.univ_nonempty
  refine ⟨t, ht, K a t, ⟨?_, hK a⟩, fun i => ha i (Finset.mem_univ _)⟩
  exact Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (exp_pos _).le

private lemma product_le_reference_add_tilt {n : ℕ} (w q : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hq : ∀ i, 0 < q i) {t : ℝ} (ht : 0 < t) :
    ∏ i, w i ≤ (∏ i, q i) + ∏ i, tilt (w i) (q i) t := by
  have hqprod := Finset.prod_pos (s := Finset.univ) fun i _ => hq i
  by_cases h : ∏ i, w i ≤ ∏ i, q i
  · exact h.trans (le_add_of_nonneg_right (Finset.prod_nonneg fun i _ =>
      mul_nonneg (hw i) (exp_pos _).le))
  have hprod := hqprod.trans (lt_of_not_ge h)
  have hw' i : w i ≠ 0 := fun hi => hprod.ne' (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hlog := log_lt_log hqprod (lt_of_not_ge h)
  rw [log_prod (fun i _ => (hq i).ne'), log_prod (fun i _ => hw' i)] at hlog
  have hexp : 1 ≤ exp (∑ i, t * (log (w i) - log (q i))) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, one_le_exp_iff]
    exact mul_nonneg ht.le (sub_nonneg.mpr hlog.le)
  simp only [tilt, Finset.prod_mul_distrib, ← exp_sum]
  exact (le_mul_of_one_le_right hprod.le hexp).trans (le_add_of_nonneg_left hqprod.le)

omit [Fintype α] in
private lemma sum_error_eq [MeasurableSpace β] [DiscreteMeasurableSpace β] (W : α → PMF β)
    {n M : ℕ} (f : Fin M → Fin n → α) (g : (Fin n → β) → Fin M) :
    (∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m}) =
      M - ∑ y, ∏ i, row W (f (g y) i) (y i) := by
  classical
  let D (m : Fin M) := Finset.univ.filter fun y => g y = m
  have hm (m : Fin M) : (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m} =
      1 - ∑ y ∈ D m, ∏ i, row W (f m i) (y i) := by
    have hD : {y | g y ≠ m} = (D m : Set (Fin n → β))ᶜ := by ext; simp [D]
    rw [hD, probReal_compl_eq_one_sub (D m).measurableSet, ← sum_measureReal_singleton]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    rw [measureReal_def, ← Set.univ_pi_singleton, Measure.pi_pi, ENNReal.toReal_prod]
    simp only [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete, row]
  simp_rw [hm, D, Finset.sum_filter]
  rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun m y =>
    if g y = m then ∏ i, row W (f m i) (y i) else 0)]
  simp

-- In the reference term, disjoint decoding regions cost only one output sum.
-- In the tilted term we can sum over all outputs separately for each message.
omit [Fintype α] in
private lemma success_bound (W : α → PMF β) {q : β → ℝ} (hq : ∀ b, 0 < q b)
    {t c : ℝ} (ht : 0 < t) (hc : ∀ a, ∑ b, tilt (row W a b) (q b) t ≤ c)
    {n M : ℕ} (f : Fin M → Fin n → α) (g : (Fin n → β) → Fin M) :
    ∑ y, ∏ i, row W (f (g y) i) (y i) ≤ (∑ b, q b) ^ n + M * c ^ n := by
  classical
  let T a b := tilt (row W a b) (q b) t
  have hT a b : 0 ≤ T a b := mul_nonneg ENNReal.toReal_nonneg (exp_pos _).le
  have hblock (m : Fin M) : (∑ y : Fin n → β, ∏ i, T (f m i) (y i)) ≤ c ^ n := by
    rw [← Fintype.prod_sum (fun i b => T (f m i) b)]
    simpa using Finset.prod_le_prod₀ (s := Finset.univ)
      (fun i _ => Finset.sum_nonneg fun b _ => hT (f m i) b) (fun i _ => hc (f m i))
  calc
    _ ≤ ∑ y : Fin n → β, ((∏ i, q (y i)) + ∑ m, ∏ i, T (f m i) (y i)) := by
      apply Finset.sum_le_sum
      intro y _
      refine (product_le_reference_add_tilt _ _ (fun _ => ENNReal.toReal_nonneg)
        (fun i => hq (y i)) ht).trans (add_le_add le_rfl ?_)
      exact Finset.single_le_sum (f := fun m => ∏ i, T (f m i) (y i))
        (fun m _ => Finset.prod_nonneg fun i _ => hT _ _) (Finset.mem_univ (g y))
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Fintype.prod_sum (fun (_ : Fin n) b => q b),
        Finset.sum_comm (f := fun (y : Fin n → β) (m : Fin M) => ∏ i, T (f m i) (y i))]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      apply add_le_add le_rfl
      simpa using Finset.sum_le_sum fun m (_ : m ∈ Finset.univ) => hblock m

end

set_option linter.unusedFintypeInType false in
/-- **Strong converse** (Wolfowitz). For a discrete memoryless channel `W` on finite alphabets,
every rate `R > C(W)` and every `ε < 1`, for all large blocklengths `n` every code with
`M ≥ 2^{nR}` codewords has average error probability greater than `ε`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 22.1 (`C_ε = C` for `0 < ε < 1`, finite alphabets);
J. Wolfowitz (1957). -/
public theorem channelCoding_strong_converse {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [MeasurableSpace β] [DiscreteMeasurableSpace β] (W : α → PMF β) {R : ℝ}
    (hR : (⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))) < R)
    {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ n in Filter.atTop, ∀ (M : ℕ) (f : Fin M → Fin n → α) (g : (Fin n → β) → Fin M),
      (2 : ℝ) ^ ((n : ℝ) * R) ≤ M →
        ε < (∑ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m}) / M := by
  obtain ⟨q, hq, hsum, hlog⟩ := exists_output_weight W hR
  obtain ⟨t, ht, c, hc, htilt⟩ := exists_tilt W q hlog
  let A := exp (R * log 2)
  let B := ∑ b, q b
  have hA : 0 < A := exp_pos _
  have hB : 0 ≤ B := Finset.sum_nonneg fun b _ => (hq b).le
  have hratio : B / A < 1 := (div_lt_one hA).mpr hsum
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hB hA.le) hratio).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.1 hc.2)
  have hev : ∀ᶠ n : ℕ in atTop, (B / A) ^ n + c ^ n < 1 - ε :=
    hlim.eventually (gt_mem_nhds (by simpa using sub_pos.mpr hε))
  filter_upwards [hev] with n hn
  intro M f g hM
  have hsize : A ^ n ≤ M := by
    rw [mul_comm (n : ℝ), rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (log 2)] at hM
    exact hM
  have hMpos := (pow_pos hA n).trans_le hsize
  have href : B ^ n ≤ (B / A) ^ n * M := by
    calc B ^ n = (B / A) ^ n * A ^ n := by rw [div_pow, div_mul_cancel₀ _ (pow_pos hA n).ne']
         _ ≤ _ := mul_le_mul_of_nonneg_left hsize (pow_nonneg (div_nonneg hB hA.le) _)
  have hsuccess := success_bound W hq ht htilt f g
  rw [sum_error_eq, lt_div_iff₀ hMpos]
  have h := mul_lt_mul_of_pos_right hn hMpos
  change _ ≤ B ^ n + M * c ^ n at hsuccess
  linarith only [href, hsuccess, h]

end MathlibExt.InformationTheory.ChannelCodingWanted
