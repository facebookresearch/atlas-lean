/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-!
# The John–Nirenberg inequality on the real line

The measure of the set where a function of bounded mean oscillation deviates from its
interval average decays exponentially. The proof iterates the dyadic Calderón–Zygmund
decomposition after an affine change of variables.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted

open DyadicMaximal

private noncomputable abbrev mean (f : ℝ → ℝ) (s : Set ℝ) := ⨍ x in s, f x

private def tail (f : ℝ → ℝ) (s : Set ℝ) (t : ℝ) :=
  {x | x ∈ s ∧ t < |f x - mean f s|}

private theorem ofReal_mean_abs (f : ℝ → ℝ) {s : Set ℝ} (hf : IntegrableOn f s) :
    ENNReal.ofReal (⨍ x in s, |f x|) = ⨍⁻ x in s, ‖f x‖ₑ := by
  rw [setLAverage_eq, ofReal_setAverage hf.abs (ae_of_all _ fun x => abs_nonneg (f x))]
  simp only [Real.eNorm_eq_ofReal_abs]

private theorem abs_mean_sub_le (f : ℝ → ℝ) {s : Set ℝ} (hf : IntegrableOn f s)
    (h₀ : volume s ≠ 0) (hfin : volume s ≠ ∞) (u : ℝ) :
    |mean f s - u| ≤ ⨍ x in s, |f x - u| := by
  have hc : IntegrableOn (fun _ : ℝ => u) s := integrableOn_const hfin
  have h := norm_integral_le_integral_norm (μ := ((volume.restrict s) univ)⁻¹ • volume.restrict s)
    (fun x => f x - u)
  change ‖⨍ x in s, f x - u‖ ≤ ⨍ x in s, ‖f x - u‖ at h
  simpa only [setAverage_fun_sub hf hc, setAverage_const h₀ hfin, Real.norm_eq_abs] using h

-- On each selected interval the mean moves by at most 4B. Their union takes up at most
-- half of the parent and contains almost every point with deviation greater than 2B.
private theorem stopping_intervals {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B) (k m : ℤ)
    (hf : IntegrableOn f (dyadicInterval k m))
    (hosc : (⨍ x in dyadicInterval k m, |f x - mean f (dyadicInterval k m)|) ≤ B) :
    ∃ T : Set (ℤ × ℤ), let Q := fun i : T => dyadicInterval i.val.1 i.val.2
      Pairwise (Function.onFun Disjoint Q) ∧
      volume (⋃ i, Q i) ≤ (2 : ℝ≥0∞)⁻¹ * volume (dyadicInterval k m) ∧
      (∀ i, |mean f (Q i) - mean f (dyadicInterval k m)| ≤ 4 * B) ∧
      tail f (dyadicInterval k m) (2 * B) ≤ᵐ[volume] ⋃ i, Q i := by
  classical
  let I := dyadicInterval k m
  let d := fun x => f x - mean f I
  let g := I.indicator d
  let c := ENNReal.ofReal (2 * B)
  let Ω := {x | c < dyadicMaximalFunction g x}
  have hI : MeasurableSet I := measurableSet_dyadicInterval k m
  have hd : IntegrableOn d I := hf.sub (integrableOn_const (volume_dyadicInterval_ne_top k m))
  have hg : Integrable g := hd.integrable_indicator hI
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  obtain ⟨hweak, hgood, hstop⟩ := calderon_zygmund hg.aestronglyMeasurable.eNorm
    hg.hasFiniteIntegral.ne hc
  have hmass : ∫⁻ x, ‖g x‖ₑ ≤ ENNReal.ofReal B * volume I := by
    simp only [g, eNorm_indicator_eq_indicator_eNorm, lintegral_indicator hI]
    rw [← measure_mul_setLAverage _ (volume_dyadicInterval_ne_top k m),
      ← ofReal_mean_abs d hd, mul_comm]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hosc) (by positivity)
  have hhalf : volume Ω ≤ (2 : ℝ≥0∞)⁻¹ * volume I := by
    apply (ENNReal.mul_le_mul_iff_right hc ENNReal.ofReal_ne_top).mp
    refine hweak.trans (hmass.trans_eq ?_)
    rw [show c = ENNReal.ofReal B * 2 by simp [c, ENNReal.ofReal_mul, mul_comm]]
    rw [mul_assoc, ← mul_assoc (2 : ℝ≥0∞), ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
      one_mul]
  have hsmall : volume Ω < volume I := by
    refine hhalf.trans_lt ?_
    calc
      _ < 1 * volume I := ENNReal.mul_lt_mul_left (volume_dyadicInterval_pos k m).ne'
        (volume_dyadicInterval_ne_top k m) (by norm_num)
      _ = _ := one_mul _
  let T : Set (ℤ × ℤ) := {i | ∃ x ∈ I, IsStoppingLevel g c x i.1 ∧ dyadicIndex i.1 x = i.2}
  let Q := fun i : T => dyadicInterval i.val.1 i.val.2
  have hlevel (i : T) {y : ℝ} (hy : y ∈ Q i) : IsStoppingLevel g c y i.val.1 := by
    obtain ⟨x, _, hx, hi⟩ := i.property
    exact hx.of_mem (hi ▸ hy)
  have hΩ (i : T) : Q i ⊆ Ω := fun _ hy => (hlevel i hy).lt_dyadicMaximalFunction
  have hsub (i : T) : Q i ⊆ I := by
    obtain ⟨x, hx, _, hi⟩ := i.property
    have hxi := mem_dyadicInterval_iff.mp hx
    have hki : k ≤ i.val.1 := by
      by_contra! hlt
      refine hsmall.not_ge (measure_mono (Subset.trans ?_ (hΩ i)))
      intro y hy
      exact mem_dyadicInterval_iff.mpr ((dyadicIndex_eq_of_le hlt.le
        ((mem_dyadicInterval_iff.mp hy).trans hxi.symm)).trans hi)
    intro y hy
    exact mem_dyadicInterval_iff.mpr ((dyadicIndex_eq_of_le hki
      ((mem_dyadicInterval_iff.mp hy).trans hi.symm)).trans hxi)
  refine ⟨T, ?_, (measure_mono (iUnion_subset hΩ)).trans hhalf, ?_, ?_⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    have h := (hlevel i hxi).unique (hlevel j hxj)
    apply hij
    apply Subtype.ext
    apply Prod.ext h
    exact (mem_dyadicInterval_iff.mp hxi).symm.trans
      (h ▸ mem_dyadicInterval_iff.mp hxj)
  · intro i
    obtain ⟨x, _, hs, hi⟩ := i.property
    have havg := hs.dyadicAverage_le_two_mul
    rw [dyadicAverage, hi] at havg
    have heq : (⨍⁻ y in Q i, ‖g y‖ₑ) = ⨍⁻ y in Q i, ‖d y‖ₑ :=
      setLAverage_congr_fun (measurableSet_dyadicInterval _ _) fun y hy => by
        simp [g, indicator_of_mem (hsub i hy)]
    rw [heq, ← ofReal_mean_abs d (hd.mono_set (hsub i))] at havg
    have hfour : 2 * c = ENNReal.ofReal (4 * B) := by
      rw [show 4 * B = 2 * (2 * B) by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp [c]
    rw [hfour, ENNReal.ofReal_le_ofReal_iff (by positivity)] at havg
    exact (abs_mean_sub_le f (hf.mono_set (hsub i)) (volume_dyadicInterval_pos _ _).ne'
      (volume_dyadicInterval_ne_top _ _) _).trans havg
  · filter_upwards [hgood] with x hx
    rintro ⟨hxI, hgt⟩
    have hxΩ : x ∈ Ω := by
      by_contra h
      have hle := hx (not_lt.mp h)
      rw [show g x = d x from indicator_of_mem hxI _, Real.eNorm_eq_ofReal_abs,
        ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2 * B)] at hle
      exact hgt.not_ge hle
    obtain ⟨j, hj, _⟩ := hstop x hxΩ
    exact mem_iUnion.mpr ⟨⟨(j, dyadicIndex j x), x, hxI, hj, rfl⟩, mem_dyadicInterval_iff.mpr rfl⟩

private theorem dyadic_tail {f : ℝ → ℝ} {B : ℝ} (hB : 0 < B)
    (hf : ∀ k m, IntegrableOn f (dyadicInterval k m))
    (hosc : ∀ k m, (⨍ x in dyadicInterval k m, |f x - mean f (dyadicInterval k m)|) ≤ B)
    (n : ℕ) (k m : ℤ) :
    volume (tail f (dyadicInterval k m) (n * (4 * B))) ≤
      (2 : ℝ≥0∞)⁻¹ ^ n * volume (dyadicInterval k m) := by
  induction n generalizing k m with
  | zero => simpa using measure_mono (fun _ hx => hx.1 : tail f (dyadicInterval k m) _ ⊆ _)
  | succ n ih =>
    let I := dyadicInterval k m
    obtain ⟨T, hdisj, hhalf, hmean, hcover⟩ := stopping_intervals hB k m (hf k m) (hosc k m)
    let Q := fun i : T => dyadicInterval i.val.1 i.val.2
    have hstep : tail f I ((n + 1 : ℕ) * (4 * B)) ≤ᵐ[volume]
        ⋃ i : T, tail f (Q i) (n * (4 * B)) := by
      filter_upwards [hcover] with x hx
      rintro ⟨hxI, hxgt⟩
      push_cast at hxgt
      have hpos : (0 : ℝ) ≤ n * (4 * B) := by positivity
      have hgt : 2 * B < |f x - mean f I| := by nlinarith
      obtain ⟨i, hxi⟩ := mem_iUnion.mp (hx ⟨hxI, hgt⟩)
      refine mem_iUnion.mpr ⟨i, hxi, ?_⟩
      have := abs_sub_le (f x) (mean f (Q i)) (mean f I)
      have hi : |mean f (Q i) - mean f I| ≤ 4 * B := hmean i
      nlinarith
    calc
      _ ≤ volume (⋃ i : T, tail f (Q i) (n * (4 * B))) := measure_mono_ae hstep
      _ ≤ ∑' i : T, volume (tail f (Q i) (n * (4 * B))) := measure_iUnion_le _
      _ ≤ ∑' i : T, (2 : ℝ≥0∞)⁻¹ ^ n * volume (Q i) :=
        tsum_le_tsum fun i => ih i.val.1 i.val.2
      _ = (2 : ℝ≥0∞)⁻¹ ^ n * volume (⋃ i, Q i) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj (fun _ => measurableSet_dyadicInterval _ _)]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (2⁻¹ * volume I) := by gcongr
      _ = _ := by rw [pow_succ, mul_assoc]

-- An increasing affine change of variables preserves interval averages.
private theorem mean_affine (f : ℝ → ℝ) {u v L : ℝ} (huv : u < v) (hL : 0 < L) (a : ℝ) :
    mean (fun x => f (L * x + a)) (Ico u v) = mean f (Icc (L * u + a) (L * v + a)) := by
  have huv' : L * u + a < L * v + a := by gcongr
  change (⨍ x in Ico u v, f (L * x + a)) = _
  rw [setAverage_congr Ico_ae_eq_Icc]
  simp only [mean, setAverage_eq, Real.volume_real_Icc_of_le huv.le,
    Real.volume_real_Icc_of_le huv'.le, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le huv.le, ← intervalIntegral.integral_of_le huv'.le,
    intervalIntegral.integral_comp_mul_add _ hL.ne', smul_eq_mul]
  rw [show L * v + a - (L * u + a) = L * (v - u) by ring, mul_inv_rev, mul_assoc]

private theorem integrableOn_affine (f : ℝ → ℝ) (hf : LocallyIntegrable f) {u v L : ℝ}
    (huv : u < v) (hL : 0 < L) (a : ℝ) :
    IntegrableOn (fun x => f (L * x + a)) (Ico u v) := by
  have hi : IntervalIntegrable f volume (L * u + a) (L * v + a) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by gcongr)).mpr
      (hf.integrableOn_isCompact isCompact_Icc)
  have hj := (IntervalIntegrable.comp_add_right_iff (c := a)).mpr hi
  have hh := hj.comp_mul_left (c := L)
  simp only [mul_div_cancel_left₀ _ hL.ne'] at hh
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le huv.le).mp hh).mono_set Ico_subset_Icc_self

private theorem geometric_le_exp {α B : ℝ} (hB : 0 < B) :
    (2 : ℝ)⁻¹ ^ ⌊α / (4 * B)⌋₊ ≤ 2 * Real.exp (-α / ((4 / Real.log 2) * B)) := by
  let n := ⌊α / (4 * B)⌋₊
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hceil : α / (4 * B) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  calc
    _ = Real.exp (-(n : ℝ) * Real.log 2) := by
      rw [neg_mul, Real.exp_neg, mul_comm (n : ℝ), Real.exp_mul, Real.exp_log (by norm_num),
        Real.rpow_natCast, inv_pow]
    _ ≤ Real.exp (Real.log 2 - (α / (4 * B)) * Real.log 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_lt_mul_of_pos_right hceil hlog]
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
      congr 2
      field

/-- **John–Nirenberg inequality.** There is an absolute constant `c > 0` such that for every
locally integrable `f : ℝ → ℝ` whose mean oscillation over every bounded interval is at most
`B > 0`, every interval `I = [a, b]` with `a < b` and every `α > 0`,
`|{x ∈ I : |f(x) - f_I| > α}| ≤ 2 |I| exp(-α / (c B))`
(F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
14 (1961), 415–426; statement as in A. K. Lerner, *A "local mean oscillation" decomposition and
some its applications*, lecture notes, inequality (2.1), with `n = 1`). -/
public theorem exists_volume_abs_sub_average_gt_le :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ, LocallyIntegrable f → ∀ B : ℝ, 0 < B →
      (∀ a b : ℝ, a < b → ⨍ x in Icc a b, |f x - ⨍ y in Icc a b, f y| ≤ B) →
      ∀ a b : ℝ, a < b → ∀ α : ℝ, 0 < α →
        volume {x | x ∈ Icc a b ∧ α < |f x - ⨍ y in Icc a b, f y|} ≤
          ENNReal.ofReal (2 * (b - a) * Real.exp (-α / (c * B))) := by
  refine ⟨4 / Real.log 2, by positivity, ?_⟩
  intro f hf B hB hosc a b hab α hα
  let L := b - a
  have hL : 0 < L := sub_pos.mpr hab
  let g := fun x => f (L * x + a)
  have hends (k m : ℤ) : (m : ℝ) / 2 ^ k < ((m : ℝ) + 1) / 2 ^ k := by
    apply div_lt_div_of_pos_right (by linarith) (by positivity)
  have hg (k m : ℤ) : IntegrableOn g (dyadicInterval k m) :=
    integrableOn_affine f hf (hends k m) hL a
  have hgosc (k m : ℤ) : (⨍ x in dyadicInterval k m, |g x - mean g (dyadicInterval k m)|) ≤ B := by
    let u := (m : ℝ) / 2 ^ k
    let v := ((m : ℝ) + 1) / 2 ^ k
    have huv : u < v := hends k m
    change mean (fun x => |f (L * x + a) - mean g (Ico u v)|) (Ico u v) ≤ B
    rw [mean_affine f huv hL a]
    exact (mean_affine (fun y => |f y - mean f (Icc (L * u + a) (L * v + a))|)
      huv hL a).le.trans (hosc _ _ (by gcongr))
  let n := ⌊α / (4 * B)⌋₊
  have hn : (n : ℝ) * (4 * B) ≤ α :=
    (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have hunit : dyadicInterval 0 0 = Ico (0 : ℝ) 1 := by norm_num [dyadicInterval]
  have htail := dyadic_tail hB hg hgosc n 0 0
  rw [hunit, Real.volume_Ico] at htail
  norm_num at htail
  have hunitTail : volume (tail g (Ico 0 1) α) ≤
      ENNReal.ofReal (2 * Real.exp (-α / ((4 / Real.log 2) * B))) := by
    calc
      volume (tail g (Ico 0 1) α) ≤ volume (tail g (Ico 0 1) (n * (4 * B))) := by
        apply measure_mono
        intro x hx
        exact ⟨hx.1, hn.trans_lt hx.2⟩
      _ ≤ _ := htail
      _ ≤ _ := by
        simpa [n, ENNReal.inv_pow, inv_pow, ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos] using
          ENNReal.ofReal_le_ofReal (geometric_le_exp (α := α) hB)
  have hmean : mean g (Ico 0 1) = mean f (Icc a b) := by
    simpa [L, g] using mean_affine f zero_lt_one hL a
  let A := tail f (Icc a b) α
  have hpre : (fun x => L * x + a) ⁻¹' A =ᵐ[volume] tail g (Ico 0 1) α := by
    filter_upwards [Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)] with x hx
    change (L * x + a ∈ Icc a b ∧ _) ↔ (x ∈ Ico 0 1 ∧ _)
    rw [show x ∈ Ico 0 1 ↔ x ∈ Icc 0 1 from hx, hmean]
    have hφ : StrictMono (fun y : ℝ => L * y + a) := fun y z hyz => by dsimp; gcongr
    have hmem := and_congr (hφ.le_iff_le (a := 0) (b := x)) (hφ.le_iff_le (a := x) (b := 1))
    exact and_congr (by simpa [L] using hmem) Iff.rfl
  have hscale := measure_congr hpre
  change volume ((fun x => L * x) ⁻¹' ((fun y => y + a) ⁻¹' A)) = _ at hscale
  rw [Real.volume_preimage_mul_left hL.ne', measure_preimage_add_right, abs_of_pos (inv_pos.mpr hL),
    ENNReal.ofReal_inv_of_pos hL] at hscale
  calc
    volume A = ENNReal.ofReal L * volume (tail g (Ico 0 1) α) := by
      rw [← hscale, ← mul_assoc, ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,
        one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hunitTail (by positivity : 0 ≤ ENNReal.ofReal L)
    _ = _ := by rw [← ENNReal.ofReal_mul hL.le]; congr 1; dsimp [L]; ring

end MathlibExt.Analysis.HarmonicAnalysis.BoundedMeanOscillationWanted
