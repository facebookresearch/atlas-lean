/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-!
# Vector-valued dyadic maximal inequality

The scalar weak type (1,1) and `L^p` bounds for the dyadic maximal function are proved in
`MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal`. This module proves the vector-valued
extension of C. Fefferman and E. M. Stein in the normalisation of that module: dyadic intervals
`[m 2^{-k}, (m + 1) 2^{-k})` of `ℝ` with Lebesgue measure, and averages of `‖f‖ₑ`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExt.Analysis.HarmonicAnalysis.VectorValuedMaximalWanted

open MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

-- First-crossing intervals for levels at or above a fixed bottom level.
private theorem weak_above (f w : ℝ → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞) (a : ℤ) :
    c * (∫⁻ x in {x | ∃ n : ℕ, c < dyadicAverage (a + n) f x}, w x) ≤
      ∫⁻ x, f x * dyadicMaximalFunction w x := by
  classical
  let first (x : ℝ) (n : ℕ) := c < dyadicAverage (a + n) f x ∧
    ∀ j < n, dyadicAverage (a + (j : ℕ)) f x ≤ c
  let T := {i : ℕ × ℤ | ∃ x, first x i.1 ∧ dyadicIndex (a + i.1) x = i.2}
  let Q (i : T) := dyadicInterval (a + i.val.1) i.val.2
  have hfirst (i : T) {x} (hx : x ∈ Q i) : first x i.val.1 := by
    obtain ⟨y, hy, hi⟩ := i.property
    have he := (mem_dyadicInterval_iff.mp hx).trans hi.symm
    refine ⟨(dyadicAverage_congr f he).symm ▸ hy.1, fun j hj => ?_⟩
    rw [dyadicAverage_congr f (dyadicIndex_eq_of_le (show a + j ≤ a + i.val.1 by omega) he)]
    exact hy.2 j hj
  have hd : Pairwise (Function.onFun Disjoint Q) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hi hj
    obtain ⟨hi₁, hi₂⟩ := hfirst i hi
    obtain ⟨hj₁, hj₂⟩ := hfirst j hj
    rcases lt_trichotomy i.val.1 j.val.1 with h | h | h
    · exact hi₁.not_ge (hj₂ _ h)
    · apply hij
      apply Subtype.ext
      exact Prod.ext h ((mem_dyadicInterval_iff.mp hi).symm.trans
        (h ▸ mem_dyadicInterval_iff.mp hj))
    · exact hj₁.not_ge (hi₂ _ h)
  have hcover : {x | ∃ n : ℕ, c < dyadicAverage (a + n) f x} = ⋃ i, Q i := by
    ext x
    constructor
    · intro hx
      let n := Nat.find hx
      refine mem_iUnion.mpr ⟨⟨(n, dyadicIndex (a + n) x), x, ⟨Nat.find_spec hx, ?_⟩, rfl⟩,
        mem_dyadicInterval_iff.mpr rfl⟩
      exact fun j hj => not_lt.mp (Nat.find_min hx hj)
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨_, (hfirst i hi).1⟩
  have hm (i : T) : MeasurableSet (Q i) := measurableSet_dyadicInterval _ _
  rw [hcover, lintegral_iUnion hm hd, ← ENNReal.tsum_mul_left]
  refine (tsum_le_tsum (g := fun i : T => ∫⁻ x in Q i, f x * dyadicMaximalFunction w x)
    fun i => ?_).trans ((lintegral_iUnion hm hd _).ge.trans (setLIntegral_le_lintegral _ _))
  obtain ⟨x, hx, hi⟩ := i.property
  have hav := hx.1.le
  simp only [dyadicAverage, hi, eNorm_eq_self] at hav
  have hfin : volume (Q i) ≠ ∞ := volume_dyadicInterval_ne_top _ _
  calc
    _ = (c * volume (Q i)) * (⨍⁻ z in Q i, w z) := by
      rw [mul_assoc, measure_mul_setLAverage _ hfin]
    _ ≤ (∫⁻ z in Q i, f z) * (⨍⁻ z in Q i, w z) := by
      rw [mul_comm c, ← measure_mul_setLAverage f hfin]
      gcongr
    _ = ∫⁻ z in Q i, f z * (⨍⁻ y in Q i, w y) := (lintegral_mul_const _ hf).symm
    _ ≤ _ := by
      apply setLIntegral_mono' (hm i)
      intro z hz
      refine mul_le_mul_of_nonneg_left ?_ zero_le
      refine le_trans ?_ (le_iSup (fun k => dyadicAverage k w z) (a + i.val.1))
      simp only [dyadicAverage, mem_dyadicInterval_iff.mp hz, eNorm_eq_self, Q, le_refl]

private theorem weighted_weak (f w : ℝ → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞) :
    c * (∫⁻ x in {x | c < dyadicMaximalFunction f x}, w x) ≤
      ∫⁻ x, f x * dyadicMaximalFunction w x := by
  let W (N : ℕ) := {x | ∃ n : ℕ, c < dyadicAverage (-(N : ℤ) + n) f x}
  have hmono : Monotone W := by
    intro N M h x
    rintro ⟨n, hn⟩
    refine ⟨M - N + n, ?_⟩
    rwa [show -(M : ℤ) + (↑(M - N + n) : ℤ) = -N + n by omega]
  have hU : {x | c < dyadicMaximalFunction f x} = ⋃ N, W N := by
    ext x
    simp only [mem_ofPred_eq, dyadicMaximalFunction, lt_iSup_iff, W, mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k.natAbs, (k + k.natAbs).toNat, by rwa [show -(k.natAbs : ℤ) +
        ↑(k + ↑k.natAbs).toNat = k by omega]⟩
    · rintro ⟨N, n, h⟩
      exact ⟨_, h⟩
  have hm (N) : MeasurableSet (W N) := by
    simp only [W, ofPred_exists]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_lt measurable_const (measurable_dyadicAverage _ _)
  rw [hU, ← withDensity_apply _ (MeasurableSet.iUnion hm), hmono.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro N
  rw [withDensity_apply _ (hm N)]
  exact weak_above f w hf c (-N)

private noncomputable abbrev kernel (r t : ℝ) := ENNReal.ofReal (r * t ^ (r - 1))

private theorem weighted_layers {f w : ℝ → ℝ≥0∞} (hf : Measurable f) (hw : Measurable w)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, f x ^ r * w x = ∫⁻ t in Ioi (0 : ℝ),
      kernel r t * ∫⁻ x in {x | ENNReal.ofReal t < f x}, w x := by
  classical
  have hK : Measurable (kernel r) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  let F (x t : ℝ) := if ENNReal.ofReal t < f x then kernel r t * w x else 0
  have hF : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      (hf.comp measurable_fst)) ((hK.comp measurable_snd).mul (hw.comp measurable_fst))
      measurable_const
  calc
    _ = ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), F x t := by
      refine lintegral_congr fun x => ?_
      rw [rpow_eq_lintegral _ hr, ← lintegral_mul_const (w x) (hK.indicator
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const))]
      refine lintegral_congr fun t => ?_
      simp [F, indicator_apply, ite_mul]
    _ = _ := by
      rw [lintegral_lintegral_swap hF.aemeasurable]
      refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [← lintegral_indicator (measurableSet_lt measurable_const hf),
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      simp [F, indicator_apply, mul_ite]

private theorem weak_tail (f w : ℝ → ℝ≥0∞) (hf : Measurable f) (s : ℝ≥0∞) :
    s * (∫⁻ x in {x | s < dyadicMaximalFunction f x / 2}, w x) ≤
      ∫⁻ x in {x | s < f x}, f x * dyadicMaximalFunction w x := by
  let g := {x | s < f x}.indicator f
  have hs := measurableSet_lt (measurable_const (a := s)) hf
  have sub : {x | s < dyadicMaximalFunction f x / 2} ⊆ {x | s < dyadicMaximalFunction g x} := by
    intro x hx
    have h : s * 2 < dyadicMaximalFunction f x :=
      (ENNReal.lt_div_iff_mul_lt (by simp) (by simp)).mp hx
    obtain ⟨k, hk⟩ := lt_iSup_iff.mp h
    change s < ⨆ j, dyadicAverage j g x
    refine lt_iSup_iff.mpr ⟨k, ?_⟩
    by_contra! hle
    have ha := dyadicAverage_le_indicator_add k f s x
    simp only [eNorm_eq_self] at ha
    exact hk.not_ge (ha.trans ((add_le_add_left hle s).trans_eq (mul_two s).symm))
  refine (mul_le_mul_of_nonneg_left (lintegral_mono_set sub) zero_le).trans
    ((weighted_weak g w (hf.indicator hs) s).trans_eq ?_)
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  simp [g, indicator_apply, ite_mul]

private noncomputable abbrev weightedConst (q : ℝ) :=
  (2 : ℝ≥0∞) ^ q * ENNReal.ofReal (q / (q - 1))

-- Integrate the weighted weak estimate against the derivative of t ↦ t^q.
private theorem weighted_strong {f w : ℝ → ℝ≥0∞} (hf : Measurable f) (hw : Measurable w)
    {q : ℝ} (hq : 1 < q) :
    ∫⁻ x, dyadicMaximalFunction f x ^ q * w x ≤
      weightedConst q * ∫⁻ x, f x ^ q * dyadicMaximalFunction w x := by
  have hq₁ : 0 < q - 1 := by linarith
  have hq₀ : 0 < q := by linarith
  let B := ENNReal.ofReal (q / (q - 1))
  have hK {t : ℝ} (ht : 0 < t) : kernel q t = B * kernel (q - 1) t * ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_mul (show 0 ≤ q / (q - 1) by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    rw [Real.rpow_sub_one ht.ne']
    field_simp
  have half_bound :
      (∫⁻ x, (dyadicMaximalFunction f x / 2) ^ q * w x) ≤
      B * ∫⁻ x, f x ^ (q - 1) * (f x * dyadicMaximalFunction w x) := by
    rw [weighted_layers ((measurable_dyadicMaximalFunction f).div_const _) hw hq₀,
      weighted_layers (w := fun x => f x * dyadicMaximalFunction w x) hf
        (hf.mul (measurable_dyadicMaximalFunction w)) hq₁,
      ← lintegral_const_mul' B _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    rw [hK ht, mul_assoc, ← mul_assoc B]
    exact mul_le_mul_of_nonneg_left (weak_tail f w hf _) zero_le
  calc
    _ = 2 ^ q * ∫⁻ x, (dyadicMaximalFunction f x / 2) ^ q * w x := by
      rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq₀.le (by norm_num))]
      apply lintegral_congr
      intro x
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hq₀.le, mul_comm 2,
        ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    _ ≤ _ := (mul_le_mul_of_nonneg_left half_bound zero_le).trans_eq (by
      rw [← mul_assoc]
      congr 1
      refine lintegral_congr fun x => ?_
      rw [← mul_assoc]
      congr 1
      simpa only [ENNReal.rpow_one, sub_add_cancel] using
        (ENNReal.rpow_add_of_nonneg (x := f x) (q - 1) 1 hq₁.le zero_le_one).symm)

local notation "M" => dyadicMaximalFunction

private noncomputable abbrev scalarConst (p : ℝ) := ENNReal.ofReal ((p / (p - 1)) ^ p)

private theorem scalar {f : ℝ → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, M f x ^ p ≤ scalarConst p * ∫⁻ x, f x ^ p := by
  simpa only [eNorm_eq_self] using lintegral_rpow_dyadicMaximalFunction_le
    (f := f) (by simpa only [eNorm_eq_self] using hf.aemeasurable) hp

private noncomputable abbrev powerSum (s : Finset ℕ) (f : ℕ → ℝ → ℝ≥0∞) (q : ℝ) (x : ℝ) :=
  ∑ i ∈ s, f i x ^ q

private theorem measurable_powerSum (s : Finset ℕ) {f : ℕ → ℝ → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) (q : ℝ) : Measurable (powerSum s f q) :=
  Finset.measurable_fun_sum s fun i _ => (hf i).pow_const _

private theorem weighted_sum (s : Finset ℕ) {f : ℕ → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) {q : ℝ} (hq : 1 < q) :
    ∫⁻ x, powerSum s (fun i => M (f i)) q x * w x ≤
      weightedConst q * ∫⁻ x, powerSum s f q x * M w x := by
  simp only [powerSum, Finset.sum_mul]
  rw [lintegral_finsetSum, lintegral_finsetSum, Finset.mul_sum]
  · exact Finset.sum_le_sum fun i _ => weighted_strong (hf i) hw hq
  · exact fun i _ => ((hf i).pow_const q).mul (measurable_dyadicMaximalFunction w)
  · exact fun i _ => ((measurable_dyadicMaximalFunction _).pow_const q).mul hw

private theorem diagonal (s : Finset ℕ) {f : ℕ → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    {p : ℝ} (hp : 1 < p) :
    ∫⁻ x, powerSum s (fun i => M (f i)) p x ≤ scalarConst p * ∫⁻ x, powerSum s f p x := by
  unfold powerSum
  rw [lintegral_finsetSum, lintegral_finsetSum, Finset.mul_sum]
  · exact Finset.sum_le_sum fun i _ => scalar (hf i) hp
  · exact fun i _ => (hf i).pow_const p
  · exact fun i _ => (measurable_dyadicMaximalFunction _).pow_const p

private theorem sum_energy_finite {r : ℝ} (hr : 1 < r) (s : Finset ℕ) {g : ℕ → ℝ → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) (hfin : ∀ i ∈ s, (∫⁻ x, g i x ^ r) < ∞) :
    (∫⁻ x, (∑ i ∈ s, g i x) ^ r) < ∞ := by
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos (zero_lt_one.trans hr)]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
      (hg i).aemeasurable (hfin i (Finset.mem_insert_self _ _))
      (ih fun j hj => hfin j (Finset.mem_insert_of_mem hj)) hr.le

private theorem cancel_energy {X K : ℝ≥0∞} {r u : ℝ} (hru : r.HolderConjugate u) (hX : X ≠ ∞)
    (h : X ≤ K * X ^ u⁻¹) : X ≤ K ^ r := by
  rcases eq_or_ne X 0 with rfl | h₀
  · exact zero_le
  apply (ENNReal.rpow_inv_le_iff hru.pos).mp
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 h₀) hX).ne'
    (ENNReal.rpow_ne_top_of_nonneg hru.symm.inv_nonneg hX)).mp
  rwa [← ENNReal.rpow_add _ _ h₀ hX, hru.inv_add_inv_eq_one, ENNReal.rpow_one]

-- When p/q > 1, test the finite sum against its (p/q - 1)-st power.
private theorem outer_large {p q : ℝ} (hq : 1 < q) (hpq : q < p) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
      (∫⁻ x, powerSum s f q x ^ (p / q)) < ∞ →
      ∫⁻ x, powerSum s (fun i => M (f i)) q x ^ (p / q) ≤
        C * ∫⁻ x, powerSum s f q x ^ (p / q) := by
  let r := p / q
  let u := Real.conjExponent r
  have hq₀ := zero_lt_one.trans hq
  have hr : 1 < r := (one_lt_div hq₀).mpr hpq
  have hru : r.HolderConjugate u := .conjExponent hr
  have hqr : q * r = p := by dsimp [r]; field_simp
  let K := weightedConst q * scalarConst u ^ u⁻¹
  refine ⟨K ^ r, ENNReal.rpow_ne_top_of_nonneg hru.nonneg (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq₀.le (by norm_num)) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg hru.symm.inv_nonneg ENNReal.ofReal_ne_top)), ?_⟩
  intro s f hf hfin
  let F := powerSum s f q
  let H := powerSum s (fun i => M (f i)) q
  let X := ∫⁻ x, H x ^ r
  let Y := ∫⁻ x, F x ^ r
  have hH := measurable_powerSum s (fun i => measurable_dyadicMaximalFunction (f i)) q
  have hF := measurable_powerSum s hf q
  -- Scalar boundedness makes the finite sum integrable to the power r before cancellation.
  have hX : X < ∞ := by
    refine sum_energy_finite hr s (fun i => (measurable_dyadicMaximalFunction (f i)).pow_const q)
      fun i hi => ?_
    simp_rw [← ENNReal.rpow_mul, hqr]
    refine (scalar (hf i) (hq.trans hpq)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
    change f i x ^ p ≤ F x ^ r
    rw [← hqr, ENNReal.rpow_mul]
    exact ENNReal.rpow_le_rpow (Finset.single_le_sum_of_canonicallyOrdered (f := fun j => f j x ^ q)
      hi) hru.nonneg
  let w := fun x => H x ^ (r - 1)
  have hw : Measurable w := hH.pow_const _
  have hMw : ∫⁻ x, M w x ^ u ≤ scalarConst u * X := by
    simpa only [w, ← ENNReal.rpow_mul, hru.sub_one_mul_conj] using scalar hw hru.symm.lt
  have hXw : X = ∫⁻ x, H x * w x := by
    apply lintegral_congr
    intro x
    simpa only [ENNReal.rpow_one, add_sub_cancel] using
      (ENNReal.rpow_add_of_nonneg (x := H x) 1 (r - 1) zero_le_one hru.sub_one_pos.le)
  have hpair : (∫⁻ x, F x * M w x) ≤ Y ^ r⁻¹ * (scalarConst u * X) ^ u⁻¹ := by
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hru hF.aemeasurable
      (measurable_dyadicMaximalFunction w).aemeasurable
    simp only [Pi.mul_apply, one_div] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hMw hru.symm.inv_nonneg)
      zero_le)
  have h := hXw.le.trans ((weighted_sum s hf hw hq).trans
    (mul_le_mul_of_nonneg_left hpair zero_le))
  rw [ENNReal.mul_rpow_of_nonneg _ _ hru.symm.inv_nonneg] at h
  have hcancel := cancel_energy hru hX.ne (K := K * Y ^ r⁻¹) (h.trans_eq (by dsimp [K]; ac_rfl))
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hru.nonneg, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ hru.ne_zero, ENNReal.rpow_one] using hcancel

private theorem maximal_factor {f g h : ℝ → ℝ≥0∞} (hg : Measurable g) (hh : Measurable h)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hfac : ∀ y, f y ≤ g y ^ a * h y ^ b) (x : ℝ) :
    M f x ≤ M g x ^ a * M h x ^ b := by
  refine iSup_le fun k => ?_
  calc
    dyadicAverage k f x ≤ dyadicAverage k g x ^ a * dyadicAverage k h x ^ b := by
      simp only [dyadicAverage, eNorm_eq_self, laverage]
      exact (lintegral_mono hfac).trans
        (ENNReal.lintegral_mul_norm_pow_le hg.aemeasurable hh.aemeasurable ha hb hab)
    _ ≤ _ := by
      apply mul_le_mul' (ENNReal.rpow_le_rpow (le_iSup (fun j => dyadicAverage j g x) k) ha)
        (ENNReal.rpow_le_rpow (le_iSup (fun j => dyadicAverage j h x) k) hb)

-- Interpolate the diagonal bound and the pointwise supremum bound by factoring the input.
private theorem outer_small {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) (s : Finset ℕ)
    {f : ℕ → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) (hft : ∀ i x, f i x ≠ ∞) :
    ∫⁻ x, powerSum s (fun i => M (f i)) q x ^ (p / q) ≤
      scalarConst p * ∫⁻ x, powerSum s f q x ^ (p / q) := by
  let a := p / q
  let b := 1 - a
  have hp₀ := zero_lt_one.trans hp
  have hq₀ := hp₀.trans_le hpq
  have ha : 0 < a := div_pos hp₀ hq₀
  have hb : 0 ≤ b := sub_nonneg.mpr ((div_le_one hq₀).mpr hpq)
  have hab : a + b = 1 := by dsimp [b]; ring
  have haq : a * q = p := div_mul_cancel₀ _ hq₀.ne'
  have hpa : p⁻¹ * a = q⁻¹ := by dsimp [a]; field_simp
  have hqp : q⁻¹ * p = a := by dsimp [a]; ring
  -- Write each coordinate as gᵢᵃ Hᵇ, with H the pointwise ℓ^q norm. Both Hᵖ and
  -- the sum of the gᵢᵖ equal Fᵃ, so the two scalar bounds have the same right-hand side.
  let F := powerSum s f q
  let H := fun x => F x ^ q⁻¹
  let g := fun i x => (f i x ^ q / F x ^ b) ^ p⁻¹
  have hF := measurable_powerSum s hf q
  have hH : Measurable H := hF.pow_const _
  have hg (i) : Measurable (g i) := (((hf i).pow_const q).div (hF.pow_const b)).pow_const _
  have hFt (x) : F x ≠ ∞ := ENNReal.sum_ne_top.mpr fun i _ =>
    ENNReal.rpow_ne_top_of_nonneg hq₀.le (hft i x)
  have hg_sum (x) : powerSum s g p x = F x ^ a := by
    simp only [powerSum, g, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp₀.ne', ENNReal.rpow_one,
      div_eq_mul_inv, ← Finset.sum_mul]
    change F x / F x ^ b = F x ^ a
    rcases eq_or_ne (F x) 0 with hz | hz
    · simp [hz, ENNReal.zero_rpow_of_pos ha]
    · calc
        _ = F x ^ (1 - b) := by
          rw [ENNReal.rpow_sub 1 b hz (hFt x), ENNReal.rpow_one]
        _ = _ := by rw [show 1 - b = a by dsimp [b]; ring]
  have hfac (i) (hi : i ∈ s) (x) : f i x ≤ g i x ^ a * H x ^ b := by
    rcases eq_or_ne (F x) 0 with hz | hz
    · have hi₀ : f i x ^ q = 0 := nonpos_iff_eq_zero.mp <| hz ▸
        (Finset.single_le_sum_of_canonicallyOrdered (f := fun j => f j x ^ q) hi : _ ≤ F x)
      have : f i x = 0 := (ENNReal.rpow_eq_zero_iff.mp hi₀).elim And.left
        (fun h => (hq₀.not_gt h.2).elim)
      simp [this]
    · have hden₀ := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hz) (hFt x) (p := b * q⁻¹)).ne'
      have hdent := ENNReal.rpow_ne_top_of_nonneg (mul_nonneg hb (inv_nonneg.mpr hq₀.le)) (hFt x)
      simp only [g, H, ← ENNReal.rpow_mul, hpa, ENNReal.div_rpow_of_nonneg _ _ (inv_nonneg.mpr
        hq₀.le), mul_inv_cancel₀ hq₀.ne', ENNReal.rpow_one, mul_comm q⁻¹ b,
        ENNReal.div_mul_cancel hden₀ hdent, le_refl]
  let G := powerSum s (fun i => M (g i)) p
  let V := fun x => M H x ^ p
  have hpoint (x) : powerSum s (fun i => M (f i)) q x ^ a ≤ G x ^ a * V x ^ b := by
    have hsum : powerSum s (fun i => M (f i)) q x ≤ G x * (M H x ^ (b * q)) := by
      unfold G powerSum
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have h := ENNReal.rpow_le_rpow (maximal_factor (hg i) hH ha.le hb hab (hfac i hi) x) hq₀.le
      simpa only [ENNReal.mul_rpow_of_nonneg _ _ hq₀.le, ← ENNReal.rpow_mul, haq] using h
    refine (ENNReal.rpow_le_rpow hsum ha.le).trans_eq ?_
    simp only [V, ENNReal.mul_rpow_of_nonneg _ _ ha.le, ← ENNReal.rpow_mul,
      show b * q * a = p * b by rw [mul_comm a q] at haq; rw [← haq]; ring]
  let Z := scalarConst p * ∫⁻ x, F x ^ a
  have hG : ∫⁻ x, G x ≤ Z := by
    simpa only [hg_sum] using diagonal s hg hp
  have hV : ∫⁻ x, V x ≤ Z := by
    simpa only [H, ← ENNReal.rpow_mul, hqp] using scalar hH hp
  calc
    _ ≤ ∫⁻ x, G x ^ a * V x ^ b := lintegral_mono hpoint
    _ ≤ (∫⁻ x, G x) ^ a * (∫⁻ x, V x) ^ b := ENNReal.lintegral_mul_norm_pow_le
      (measurable_powerSum s (fun i => measurable_dyadicMaximalFunction (g i)) p).aemeasurable
      ((measurable_dyadicMaximalFunction H).pow_const p).aemeasurable ha.le hb hab
    _ ≤ Z ^ a * Z ^ b := mul_le_mul' (ENNReal.rpow_le_rpow hG ha.le) (ENNReal.rpow_le_rpow hV hb)
    _ = Z := by rw [← ENNReal.rpow_add_of_nonneg _ _ ha.le hb, hab, ENNReal.rpow_one]

/-- **Dyadic Fefferman–Stein vector-valued maximal inequality.** For `1 < p, q < ∞` there is a
finite constant `C` such that for every sequence of measurable functions `f_i : ℝ → ℝ`,
`∫ (∑_i (M_d f_i)^q)^{p/q} ≤ C ∫ (∑_i |f_i|^q)^{p/q}`, that is
`‖(M_d f_i)_i‖_{L^p(ℓ^q)} ≤ C^{1/p} ‖(f_i)_i‖_{L^p(ℓ^q)}` (T. Hytönen, *Dyadic analysis and
weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 4.9 with `μ`
the Lebesgue measure on `ℝ`; C. Fefferman and E. M. Stein, *Some maximal inequalities*,
Amer. J. Math. 93 (1971), 107–115, for the Hardy–Littlewood maximal function on `ℝ^n`). -/
public theorem exists_lintegral_tsum_rpow_dyadicMaximalFunction_le {p q : ℝ}
    (_hp : 1 < p) (_hq : 1 < q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : ℕ → ℝ → ℝ, (∀ i, Measurable (f i)) →
      ∫⁻ x, (∑' i, dyadicMaximalFunction (f i) x ^ q) ^ (p / q) ≤
        C * ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ q) ^ (p / q) := by
  have hq := zero_lt_one.trans _hq
  have hr := div_pos (zero_lt_one.trans _hp) hq
  have finite_bound : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℝ≥0∞),
      (∀ i, Measurable (f i)) → (∀ i x, f i x ≠ ∞) → (∫⁻ x, powerSum s f q x ^ (p / q)) < ∞ →
      ∫⁻ x, powerSum s (fun i => M (f i)) q x ^ (p / q) ≤
        C * ∫⁻ x, powerSum s f q x ^ (p / q) := by
    rcases le_or_gt p q with hpq | hpq
    · exact ⟨_, ENNReal.ofReal_ne_top, fun s _ hf ht _ => outer_small _hp hpq s hf ht⟩
    · obtain ⟨C, hC, h⟩ := outer_large _hq hpq
      exact ⟨C, hC, fun s f hf _ => h s f hf⟩
  obtain ⟨C, hC, h⟩ := finite_bound
  refine ⟨C + 1, ENNReal.add_ne_top.mpr ⟨hC, ENNReal.one_ne_top⟩, ?_⟩
  intro f hf
  let g := fun i x => ‖f i x‖ₑ
  have hg (i) : Measurable (g i) := (hf i).eNorm
  let Y := ∫⁻ x, (∑' i, g i x ^ q) ^ (p / q)
  change (∫⁻ x, (∑' i, M (g i) x ^ q) ^ (p / q)) ≤ (C + 1) * Y
  rcases eq_or_ne Y ∞ with hY | hY
  · simp [hY]
  have hle (n) : (∫⁻ x, powerSum (Finset.range n) g q x ^ (p / q)) ≤ Y :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (sum_le_tsum (Finset.range n)) hr.le
  simp_rw [ENNReal.tsum_eq_iSup_nat, ENNReal.iSup_rpow_of_pos hr]
  rw [lintegral_iSup]
  · refine iSup_le fun n => (h _ g hg (fun i x => eNorm_ne_top) ((hle n).trans_lt hY.lt_top)).trans
      (mul_le_mul' le_self_add (hle n))
  · exact fun n => (measurable_powerSum (Finset.range n) (fun i =>
      measurable_dyadicMaximalFunction (g i)) q).pow_const _
  · intro n m hnm x
    exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hnm)) hr.le

end MathlibExt.Analysis.HarmonicAnalysis.VectorValuedMaximalWanted
