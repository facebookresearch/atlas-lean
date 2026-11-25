/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GlivenkoCantelli
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import MathlibExt.InformationTheory.Pinsker
import MathlibExt.MeasureTheory.Measure.PiWithDensity
import MathlibExt.Probability.Statistics.Nonparametric.EmpiricalCDFSup

/-!
# The Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant

For an i.i.d. sample of size `N` from a distribution function `F` on `ℝ`, with empirical
distribution function `F_N`, the Dvoretzky–Kiefer–Wolfowitz inequality bounds the probability
that `F_N` is uniformly `ε`-far from `F`:

`P(sup_x |F_N(x) - F(x)| > ε) ≤ C exp(-2 N ε²)` for every `ε > 0`.

Dvoretzky, Kiefer and Wolfowitz (Ann. Math. Statist. 27 (1956) 642–669) proved it with an
unspecified constant `C`. Massart (Ann. Probab. 18 (1990) 1269–1283), Theorem 1, as stated on
p. 3 of Reeve, arXiv:2403.16651v1 (the source read for this entry; Massart's paper was not),
gives the one-sided bound `P(sup_x √N (F_N(x) - F(x)) > λ) ≤ exp(-2 λ²)` for
`λ ≥ min {√(log 2 / 2), 1.0841 N^(-1/6)}`. Reeve's Corollary 2 gives the one-sided bound
`exp(-2 λ²)` for every `λ ≥ 0`, for independent observations with an arbitrary distribution
function `F`.

The two-sided bound `2 exp(-2 N ε²)` stated here follows by a union bound. The upper deviation is
the bound above with `λ = √N ε`. The lower deviation `sup_x (F(x) - F_N(x))` is at most the upper
deviation of the sample `-X_i` (compare left limits), so it obeys the same bound. When
`√N ε < √(log 2 / 2)` the right-hand side exceeds `1` and there is nothing to prove, so
Massart's Theorem 1 alone already covers every `ε > 0`. The inequality is used in this form,
`2 exp(-2 n ε²)`, in the proof of Theorem 2.4 of Lei, G'Sell, Rinaldo, Tibshirani and Wasserman,
arXiv:1604.04173v2, Appendix A.1.

The empirical count is the one of the Glivenko–Cantelli theorem in this library
(`MathlibExt.Probability.Statistics.GlivenkoCantelliWanted.empiricalCount`), which counts the
indices `0, …, n`; the sample size is therefore `N = n + 1`, which also excludes the empty
sample.

The proof uses Reeve's likelihood factors on a finite family of nested sets. Censoring at the
largest crossing threshold identifies the likelihood there with that of a common tilted law.
Binary Pinsker bounds the likelihood at the stationary point for a fixed deviation level.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GlivenkoCantelliWanted

namespace MathlibExt.Probability.Statistics.DKWInequalityWanted

open Set Filter Topology
open scoped ENNReal

private lemma two_mul_div_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  let f := fun z : ℝ => Real.log z - 2 * (z - 1) / (z + 1)
  have hd (z : ℝ) (hz : 1 ≤ z) :
      HasDerivAt f ((z - 1)^2 / (z * (z + 1)^2)) z := by
    have hz₀ : 0 < z := by linarith
    have hz₁ : 0 < z + 1 := by linarith
    have h₁ := ((hasDerivAt_id z).sub_const 1).const_mul 2
    have h₂ := (hasDerivAt_id z).add_const 1
    convert (Real.hasDerivAt_log hz₀.ne').sub (h₁.div h₂ hz₁.ne') using 1
    · rfl
    · dsimp [id, Pi.mul_apply]
      field_simp
      ring
  have hm : MonotoneOn f (Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · rw [interior_Ici]
      exact fun z hz => (hd z hz.le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro z hz
      rw [(hd z hz.le).deriv]
      have : 0 < z := by linarith [mem_Ioi.mp hz]
      positivity
  have h := hm (show (1 : ℝ) ∈ Ici 1 from le_rfl) hx hx
  simpa [f, sub_nonneg] using h

private lemma log_le_sub_inv_div_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let f := fun z : ℝ => (z - z⁻¹) / 2 - Real.log z
  have hd (z : ℝ) (hz : 1 ≤ z) : HasDerivAt f ((z - 1)^2 / (2 * z^2)) z := by
    have hz₀ : 0 < z := by linarith
    have h₁ := (hasDerivAt_id z).sub ((hasDerivAt_id z).inv hz₀.ne')
    convert (h₁.div_const 2).sub (Real.hasDerivAt_log hz₀.ne') using 1
    · rfl
    · dsimp [id, Pi.mul_apply]
      field_simp
      ring
  have hm : MonotoneOn f (Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · rw [interior_Ici]
      exact fun z hz => (hd z hz.le).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro z hz
      rw [(hd z hz.le).deriv]
      positivity
  have h := hm (show (1 : ℝ) ∈ Ici 1 from le_rfl) hx hx
  simpa [f, sub_nonneg] using h

private noncomputable def logTilt (a p : ℝ) : ℝ := Real.log ((p + a) / p)

private lemma hasDerivAt_logTilt {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    HasDerivAt (logTilt a) (-a / (p * (p + a))) p := by
  have hpa : 0 < p + a := by positivity
  have hd := (((hasDerivAt_id p).add_const a).div (hasDerivAt_id p) hp.ne')
  have hl := hd.log (show (p + a) / p ≠ 0 from (div_pos hpa hp).ne')
  convert hl using 1
  · rfl
  · dsimp [id, Pi.div_apply]
    field_simp
    ring

private noncomputable def tiltSlope (a p : ℝ) : ℝ :=
  p * (p + a) / a * logTilt a p - p

private lemma monotoneOn_tiltSlope {a : ℝ} (ha : 0 < a) : MonotoneOn (tiltSlope a) (Ioi 0) := by
  have hd (p : ℝ) (hp : 0 < p) :
      HasDerivAt (tiltSlope a) ((2 * p + a) / a * logTilt a p - 2) p := by
    have hpa : 0 < p + a := by positivity
    have h := (((hasDerivAt_id p).mul ((hasDerivAt_id p).add_const a)).div_const a).mul
      (hasDerivAt_logTilt ha hp)
    convert h.sub (hasDerivAt_id p) using 1
    · rfl
    · dsimp [id, Pi.mul_apply]
      field_simp
      ring
  refine monotoneOn_of_deriv_nonneg (convex_Ioi _) ?_ ?_ ?_
  · exact fun p hp => (hd p hp).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun p hp => (hd p hp).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro p hp
    have hp' : 0 < p := hp
    have hpa : 0 < p + a := by positivity
    have hle : 1 ≤ (p + a) / p := (le_div_iff₀ hp').2 (by linarith)
    have hlog := two_mul_div_le_log hle
    rw [(hd p hp').deriv, sub_nonneg]
    have heq : 2 * ((p + a) / p - 1) / ((p + a) / p + 1) = 2 * a / (2 * p + a) := by
      field_simp
      ring
    rw [heq] at hlog
    have hc : 0 < (2 * p + a) / a := by positivity
    have h := mul_le_mul_of_nonneg_left hlog hc.le
    convert h using 1
    · field_simp
    · rfl

private noncomputable def tiltObjective (ε a p : ℝ) : ℝ :=
  (p + ε) * logTilt a p - Real.log (1 + a)

private lemma tiltObjective_minimum {ε a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hs : tiltSlope a r = ε) {p : ℝ} (hp : 0 < p) :
    tiltObjective ε a r ≤ tiltObjective ε a p := by
  have hd (z : ℝ) (hz : 0 < z) :
      HasDerivAt (tiltObjective ε a) (a / (z * (z + a)) * (tiltSlope a z - ε)) z := by
    have hza : 0 < z + a := by positivity
    have h := (((hasDerivAt_id z).add_const ε).mul (hasDerivAt_logTilt ha hz)).sub_const
      (Real.log (1 + a))
    convert h using 1
    · rfl
    · dsimp [tiltSlope, id, Pi.mul_apply]
      field_simp
      ring
  rcases le_total p r with hpr | hrp
  · have hm : AntitoneOn (tiltObjective ε a) (Ioc 0 r) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _) ?_ ?_ ?_
      · exact fun z hz => (hd z hz.1).continuousAt.continuousWithinAt
      · rw [interior_Ioc]
        exact fun z hz => (hd z hz.1).differentiableAt.differentiableWithinAt
      · rw [interior_Ioc]
        intro z hz
        rw [(hd z hz.1).deriv]
        have h := monotoneOn_tiltSlope ha hz.1 hr hz.2.le
        rw [hs] at h
        have : 0 < z := hz.1
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h)
    exact hm ⟨hp, hpr⟩ ⟨hr, le_rfl⟩ hpr
  · have hm : MonotoneOn (tiltObjective ε a) (Ici r) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
      · exact fun z hz => (hd z (hr.trans_le hz)).continuousAt.continuousWithinAt
      · rw [interior_Ici]
        exact fun z hz => (hd z (hr.trans hz)).differentiableAt.differentiableWithinAt
      · rw [interior_Ici]
        intro z hz
        have hz₀ : 0 < z := hr.trans hz
        rw [(hd z hz₀).deriv]
        have h := monotoneOn_tiltSlope ha hr hz₀ hz.le
        rw [hs] at h
        exact mul_nonneg (by positivity) (sub_nonneg.mpr h)
    exact hm le_rfl hrp hrp

/-- At fixed deviation, choose the Bernoulli relative entropy's stationary point in the null
probability. The parameter that matches the displaced probability there gives a uniform bound. -/
private lemma exists_tilt {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ p : ℝ, 0 < p → 2 * ε^2 ≤ tiltObjective ε a p := by
  let l := (1 - ε) / 2
  have hl : 0 < l := by dsimp [l]; linarith
  have hl₁ : l < 1 := by dsimp [l]; linarith
  let C := 1 / l
  have hC : 0 < C := by positivity
  let d := l * ε^2 * Real.exp (-C)
  have hd : 0 < d := by positivity
  have hExp : Real.exp (-C) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hεsq : ε^2 < 1 := by nlinarith
  have hdₗ : d < l := by
    dsimp [d]
    calc
      l * ε ^ 2 * Real.exp (-C) ≤ l * ε ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hExp (by positivity)
      _ < l := by nlinarith
  let u := 1 - ε - d
  have hlu : l ≤ u := by dsimp [u]; dsimp [l] at *; linarith
  have hu : u < 1 - ε := by dsimp [u]; linarith
  have hu₀ : 0 < u := hl.trans_le hlu
  let R := fun p : ℝ => (p + ε) * (1 - p) / (p * (1 - p - ε))
  let f := fun p : ℝ => Real.log (R p) - ε / (p * (1 - p))
  have hR (p : ℝ) (hp : 0 < p) (hp' : p < 1 - ε) : 0 < R p := by
    have h₁ : 0 < 1 - p := by linarith
    have h₂ : 0 < 1 - p - ε := by linarith
    dsimp [R]
    positivity
  have hcont : ContinuousOn f (Icc l u) := by
    intro p hp
    have hp₀ := hl.trans_le hp.1
    have hp₁ := hp.2.trans_lt hu
    have h₁ : p ≠ 0 := hp₀.ne'
    have h₂ : 1 - p ≠ 0 := by linarith
    have h₃ : 1 - p - ε ≠ 0 := by linarith
    apply ContinuousAt.continuousWithinAt
    dsimp [f, R]
    exact (((continuousAt_id.add continuousAt_const).mul
      (continuousAt_const.sub continuousAt_id)).div
        (continuousAt_id.mul ((continuousAt_const.sub continuousAt_id).sub
          continuousAt_const)) (mul_ne_zero h₁ h₃)).log (hR p hp₀ hp₁).ne' |>.sub
      (continuousAt_const.div (continuousAt_id.mul (continuousAt_const.sub continuousAt_id))
        (mul_ne_zero h₁ h₂))
  have hleft : f l ≤ 0 := by
    let v := (1 - l) / l
    have hv : 1 ≤ v := (le_div_iff₀ hl).2 (by dsimp [l]; linarith)
    have h₁ : l + ε = 1 - l := by dsimp [l]; ring
    have h₂ : 1 - l - ε = l := by dsimp [l]; ring
    have h₃ : R l = v^2 := by
      dsimp [R, v]
      rw [h₁, h₂, div_pow]
      ring
    have h₄ : v - v⁻¹ = ε / (l * (1 - l)) := by
      dsimp [v]
      have h₅ : 1 - l ≠ 0 := by linarith
      field_simp
      dsimp [l]
      ring
    dsimp [f]
    rw [h₃, Real.log_pow, ← h₄]
    have h := log_le_sub_inv_div_two hv
    linarith
  have hright : 0 ≤ f u := by
    have hu₁ : u < 1 := by linarith
    have h₁ : ε ≤ 1 - u := by linarith
    have h₂ : ε ≤ u + ε := by linarith
    have h₃ : 1 - u - ε = d := by dsimp [u]; ring
    have hfrac : ε / (u * (1 - u)) ≤ C := by
      dsimp [C]
      apply (div_le_div_iff₀ (mul_pos hu₀ (by linarith)) hl).2
      calc
        ε * l ≤ (1 - u) * l := mul_le_mul_of_nonneg_right h₁ hl.le
        _ ≤ 1 * (u * (1 - u)) := by
          rw [one_mul, mul_comm (1 - u) l]
          exact mul_le_mul_of_nonneg_right hlu (by linarith)
    have hbig : Real.exp C ≤ R u := by
      unfold R
      rw [h₃]
      apply (le_div_iff₀ (mul_pos hu₀ hd)).2
      have he : Real.exp C * d = l * ε^2 := by
        dsimp [d]
        rw [show Real.exp C * (l * ε^2 * Real.exp (-C)) =
          l * ε^2 * (Real.exp C * Real.exp (-C)) by ring,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      calc
        Real.exp C * (u * d) ≤ Real.exp C * d := by
          gcongr
          exact mul_le_of_le_one_left hd.le hu₁.le
        _ = l * ε^2 := he
        _ ≤ ε^2 := by nlinarith
        _ ≤ (u + ε) * (1 - u) := by
          simpa [pow_two] using mul_le_mul h₂ h₁ hε.le (by positivity : 0 ≤ u + ε)
    have hlog := (Real.le_log_iff_exp_le (hR u hu₀ hu)).2 hbig
    exact sub_nonneg.mpr (hfrac.trans hlog)
  obtain ⟨r, hr, hr₀⟩ := intermediate_value_Icc hlu hcont (show 0 ∈ Icc (f l) (f u) from
    ⟨hleft, hright⟩)
  have hrp : 0 < r := hl.trans_le hr.1
  have hrq : r < 1 - ε := hr.2.trans_lt hu
  have hden : 0 < 1 - r - ε := by linarith
  have hr₁ : 0 < 1 - r := by linarith
  let a := ε / (1 - r - ε)
  have ha : 0 < a := div_pos hε hden
  have hsum : r + a = (r + ε) * (1 - r) / (1 - r - ε) := by
    dsimp [a]
    field_simp
    ring
  have htilt : logTilt a r = Real.log (R r) := by
    unfold logTilt R
    rw [hsum, div_div, mul_comm (1 - r - ε) r]
  have he : Real.log (R r) = ε / (r * (1 - r)) := sub_eq_zero.mp hr₀
  have hs : tiltSlope a r = ε := by
    rw [tiltSlope, htilt, he, hsum]
    dsimp [a]
    field_simp
    ring
  refine ⟨a, ha, fun p hp => ?_⟩
  refine le_trans ?_ (tiltObjective_minimum ha hrp hs hp)
  have heq₁ : 1 + a = (1 - r) / (1 - r - ε) := by
    dsimp [a]
    field_simp
    ring
  have heq₂ : R r = ((r + ε) / r) * (1 + a) := by
    rw [heq₁]
    dsimp [R]
    rw [div_mul_div_comm]
  have heq₃ : (1 - (r + ε)) / (1 - r) = (1 + a)⁻¹ := by
    rw [heq₁]
    field_simp
    ring
  have hq : 0 < r + ε := by positivity
  have h := MathlibExt.InformationTheory.Pinsker.binary_pinsker_of_mem_Icc hq.le
    (show r + ε ≤ 1 by linarith) hrp (show r < 1 by linarith)
  rw [heq₃, Real.log_inv] at h
  rw [tiltObjective, htilt, heq₂, Real.log_mul (div_pos hq hrp).ne'
    (by positivity : 1 + a ≠ 0)]
  convert h using 1 <;> ring_nf

section NestedSets

variable {α : Type*}

open Classical in
private noncomputable def fraction {m : ℕ} (A : Set α) (y : Fin m → α) : ℝ :=
  ((Finset.univ.filter (fun i => y i ∈ A)).card : ℝ) / m

private lemma fraction_le_one {m : ℕ} (hm : 0 < m) (A : Set α) (y : Fin m → α) :
    fraction A y ≤ 1 := by
  apply (div_le_one (Nat.cast_pos.mpr hm)).2
  classical
  exact_mod_cast (Finset.card_filter_le Finset.univ (fun i : Fin m => y i ∈ A)).trans
    (by simp)

private lemma measurable_fraction [MeasurableSpace α] {m : ℕ} {A : Set α} (hA : MeasurableSet A) :
    Measurable (fraction (m := m) A) := by
  classical
  have h (i : Fin m) :
      Measurable (fun y : Fin m → α => if y i ∈ A then (1 : ℝ) else 0) :=
    Measurable.ite ((measurable_pi_apply i) hA) measurable_const measurable_const
  convert (Finset.measurable_sum Finset.univ (fun i _ => h i)).div_const (m : ℝ) using 1
  funext y
  rw [fraction, Finset.sum_boole]

open Classical in
private noncomputable def censor (A : Set α) (b y : α) : α :=
  if y ∈ A then b else y

private lemma measurable_censor [MeasurableSpace α] {A : Set α} (hA : MeasurableSet A) (b : α) :
    Measurable (censor A b) :=
  Measurable.ite hA measurable_const measurable_id

private lemma fraction_censor {m : ℕ} {A B : Set α} (hAB : A ⊆ B) {b : α} (hb : b ∈ A)
    (y : Fin m → α) : fraction B (fun i => censor A b (y i)) = fraction B y := by
  classical
  unfold fraction
  congr 3
  apply Finset.filter_congr
  intro i _
  by_cases hi : y i ∈ A
  · simp [censor, hi, hAB hi, hAB hb]
  · simp [censor, hi]

variable [MeasurableSpace α]

private noncomputable def tiltDensity (c k : ℝ≥0∞) (μ : Measure α) (A : Set α) (y : α) :
    ℝ≥0∞ :=
  c + A.indicator (fun _ => k / μ A) y

private lemma measurable_tiltDensity (c k : ℝ≥0∞) (μ : Measure α) {A : Set α}
    (hA : MeasurableSet A) : Measurable (tiltDensity c k μ A) :=
  measurable_const.add (measurable_const.indicator hA)

private lemma withDensity_tiltDensity (c k : ℝ≥0∞) (μ : Measure α) {A : Set α}
    (hA : MeasurableSet A) :
    μ.withDensity (tiltDensity c k μ A) = c • μ + (k / μ A) • μ.restrict A := by
  unfold tiltDensity
  rw [show (fun y => c + A.indicator (fun _ => k / μ A) y) =
      (fun _ => c) + A.indicator (fun _ => k / μ A) from rfl,
    withDensity_add_right _ (measurable_const.indicator hA), withDensity_indicator hA,
    withDensity_const, withDensity_const]

private lemma map_censor_tilt {μ : Measure α} [IsProbabilityMeasure μ]
    {A : Set α} (hA : MeasurableSet A) (hpos : μ A ≠ 0) {b : α} (hb : b ∈ A)
    (c k : ℝ≥0∞) :
    (μ.withDensity (tiltDensity c k μ A)).map (censor A b) =
      (c • μ + k • Measure.dirac b).map (censor A b) := by
  have hc := measurable_censor hA b
  have hm : (μ.restrict A).map (censor A b) = μ A • Measure.dirac b := by
    rw [Measure.map_congr (g := fun _ => b) ?_, Measure.map_const, Measure.restrict_apply_univ]
    filter_upwards [ae_restrict_mem hA (μ := μ)] with y hy
    simp [censor, hy]
  rw [withDensity_tiltDensity c k μ hA, Measure.map_add _ _ hc, Measure.map_add _ _ hc,
    Measure.map_smul c hc.aemeasurable, Measure.map_smul (k / μ A) hc.aemeasurable,
    Measure.map_smul k hc.aemeasurable, Measure.map_dirac' hc, hm, smul_smul,
    ENNReal.div_mul_cancel hpos (measure_ne_top _ _)]
  simp [censor, hb]

private lemma measure_crossing_le_tilt {m : ℕ} {μ : Measure α} [IsProbabilityMeasure μ]
    {A : Set α} (hA : MeasurableSet A) (hpos : μ A ≠ 0) {b : α} (hb : b ∈ A)
    {c k L : ℝ≥0∞} (hc : c ≠ ∞) (hk : k ≠ ∞) {E : Set (Fin m → α)}
    (hE : MeasurableSet E) (hstable : (fun y i => censor A b (y i)) ⁻¹' E = E)
    (hbound : ∀ y ∈ E, L ≤ ∏ i, tiltDensity c k μ A (y i)) :
    L * (Measure.pi (fun _ : Fin m => μ)) E ≤
      (Measure.pi (fun _ : Fin m => c • μ + k • Measure.dirac b)) E := by
  let φ := censor A b
  have hφ : Measurable φ := measurable_censor hA b
  have : IsFiniteMeasure (μ.withDensity (tiltDensity c k μ A)) := by
    rw [withDensity_tiltDensity c k μ hA]
    have := Measure.smul_finite hc (μ := μ)
    have := Measure.smul_finite (ENNReal.div_ne_top hk hpos) (μ := μ.restrict A)
    infer_instance
  have : IsFiniteMeasure (c • μ + k • Measure.dirac b) := by
    have := Measure.smul_finite hc (μ := μ)
    have := Measure.smul_finite hk (μ := Measure.dirac b)
    infer_instance
  have hmap := map_censor_tilt hA hpos hb c k
  have heq : (Measure.pi (fun _ : Fin m => μ.withDensity (tiltDensity c k μ A))) E =
      (Measure.pi (fun _ : Fin m => c • μ + k • Measure.dirac b)) E := by
    have hf : Measurable (fun y : Fin m → α => fun i => φ (y i)) :=
      Measurable.of_eval fun i => hφ.comp (measurable_pi_apply i)
    have hmapPi := congrArg (fun ν : Measure α => (Measure.pi (fun _ : Fin m => ν)) E) hmap
    rw [← Measure.pi_map_pi (fun _ : Fin m => hφ.aemeasurable),
      ← Measure.pi_map_pi (fun _ : Fin m => hφ.aemeasurable),
      Measure.map_apply hf hE, Measure.map_apply hf hE, hstable] at hmapPi
    exact hmapPi
  rw [← heq, Measure.pi_withDensity (fun _ => measurable_tiltDensity c k μ hA),
    withDensity_apply _ hE, ← setLIntegral_const]
  exact lintegral_mono_ae (ae_restrict_of_forall_mem hE hbound)

private lemma tiltDensity_product {m : ℕ} (hm : 0 < m)
    {μ : Measure α} [IsProbabilityMeasure μ] {A : Set α} {a : ℝ} (ha : 0 < a)
    (hp : 0 < (μ A).toReal) (y : Fin m → α) :
    (∏ i, tiltDensity (ENNReal.ofReal ((1 + a)⁻¹)) (ENNReal.ofReal (a / (1 + a)))
      μ A (y i)) =
      ENNReal.ofReal (Real.exp ((m : ℝ) *
        (fraction A y * logTilt a (μ A).toReal - Real.log (1 + a)))) := by
  classical
  let p := (μ A).toReal
  have hμ : ENNReal.ofReal p = μ A := ENNReal.ofReal_toReal (measure_ne_top μ A)
  have hk : ENNReal.ofReal (a / (1 + a)) / μ A =
      ENNReal.ofReal (a / (1 + a) / p) := by
    rw [ENNReal.ofReal_div_of_pos hp, hμ]
  have ha₁ : 0 < 1 + a := by positivity
  have hpa : 0 < p + a := by positivity
  have hlog (z : α) :
      tiltDensity (ENNReal.ofReal ((1 + a)⁻¹)) (ENNReal.ofReal (a / (1 + a))) μ A z =
        ENNReal.ofReal (Real.exp
          ((if z ∈ A then logTilt a p else 0) - Real.log (1 + a))) := by
    by_cases hz : z ∈ A
    · rw [tiltDensity, indicator_of_mem hz, ite_eq_left hz, Real.exp_sub, logTilt,
        Real.exp_log (div_pos hpa hp), Real.exp_log ha₁, hk,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      change (1 + a)⁻¹ + a / (1 + a) / p = (p + a) / p / (1 + a)
      have hp' : p ≠ 0 := hp.ne'
      field_simp [hp']
    · simp [tiltDensity, hz, Real.exp_neg, Real.exp_log ha₁]
  simp_rw [hlog]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _), ← Real.exp_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  congr 2
  rw [fraction]
  have hm₀ : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  field_simp
  ring

private def crossing {m : ℕ} (μ : Measure α) (ε : ℝ) (A : Set α) : Set (Fin m → α) :=
  {y | ε < fraction A y - (μ A).toReal}

private lemma measurableSet_crossing {m : ℕ} (μ : Measure α) (ε : ℝ)
    {A : Set α} (hA : MeasurableSet A) : MeasurableSet (crossing (m := m) μ ε A) :=
  measurableSet_lt measurable_const ((measurable_fraction hA).sub_const _)

/-- Partition the crossing event by the largest crossing threshold. On each part, censoring
below that threshold leaves the event invariant, and the same tilted law controls every part. -/
private lemma measure_finite_crossing {τ : Type*} [LinearOrder τ] {m : ℕ} (hm : 0 < m)
    (μ : Measure α) [IsProbabilityMeasure μ] (A : τ → Set α) (hA : Monotone A)
    (hAm : ∀ t, MeasurableSet (A t)) (s : Finset τ) (hpos : ∀ t ∈ s, μ (A t) ≠ 0)
    {ε a : ℝ} (ha : 0 < a) (htilt : ∀ p : ℝ, 0 < p → 2 * ε^2 ≤ tiltObjective ε a p) :
    (Measure.pi (fun _ : Fin m => μ)) (⋃ t ∈ s, crossing μ ε (A t)) ≤
      ENNReal.ofReal (Real.exp (-2 * (m : ℝ) * ε^2)) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  let t₀ := s.min' hs
  have ht₀ : t₀ ∈ s := s.min'_mem hs
  obtain ⟨b, hb⟩ : (A t₀).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hpos t₀ ht₀ (by simp [h])
  let c := ENNReal.ofReal ((1 + a)⁻¹)
  let k := ENNReal.ofReal (a / (1 + a))
  let ν : Measure α := c • μ + k • Measure.dirac b
  have ha₁ : 0 < 1 + a := by positivity
  have hc : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hk : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hν : IsProbabilityMeasure ν := by
    constructor
    have hsum : c + k = 1 := by
      dsimp [c, k]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_one]
      congr 1
      field_simp
    simpa [ν, add_apply, smul_apply] using hsum
  let E : τ → Set (Fin m → α) := fun t =>
    crossing μ ε (A t) \ ⋃ u ∈ s.filter (t < ·), crossing μ ε (A u)
  have hEm (t : τ) : MeasurableSet (E t) :=
    (measurableSet_crossing μ ε (hAm t)).diff
      (Finset.measurableSet_biUnion _ fun u _ => measurableSet_crossing μ ε (hAm u))
  have hdisj : PairwiseDisjoint (↑s : Set τ) E := by
    intro t ht u hu htu
    apply Set.disjoint_left.mpr
    intro y hyt hyu
    rcases lt_or_gt_of_ne htu with hlt | hlt
    · exact hyt.2 (mem_iUnion₂.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hlt⟩, hyu.1⟩)
    · exact hyu.2 (mem_iUnion₂.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hlt⟩, hyt.1⟩)
  have hdecomp : (⋃ t ∈ s, crossing μ ε (A t)) = ⋃ t ∈ s, E t := by
    ext y
    constructor
    · intro hy
      obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
      let T := s.filter fun u => y ∈ crossing μ ε (A u)
      have hT : T.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨ht, hyt⟩⟩
      let u := T.max' hT
      have hu := Finset.mem_filter.mp (T.max'_mem hT)
      refine mem_iUnion₂.mpr ⟨u, hu.1, hu.2, ?_⟩
      intro h
      obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp h
      obtain ⟨hv, huv⟩ := Finset.mem_filter.mp hv
      exact huv.not_ge (T.le_max' v (Finset.mem_filter.mpr ⟨hv, hyv⟩))
    · intro hy
      obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
      exact mem_iUnion₂.mpr ⟨t, ht, hyt.1⟩
  let L := ENNReal.ofReal (Real.exp (2 * (m : ℝ) * ε^2))
  have hpart (t : τ) (ht : t ∈ s) :
      L * (Measure.pi (fun _ : Fin m => μ)) (E t) ≤
        (Measure.pi (fun _ : Fin m => ν)) (E t) := by
    have hbt : b ∈ A t := hA (s.min'_le t ht) hb
    refine measure_crossing_le_tilt (hAm t) (hpos t ht) hbt hc hk (hEm t) ?_ ?_
    · have hstable (u : τ) (htu : t ≤ u) :
          (fun (y : Fin m → α) i => censor (A t) b (y i)) ⁻¹' crossing μ ε (A u) =
            crossing μ ε (A u) := by
        ext y
        change (ε < fraction (A u) (fun i => censor (A t) b (y i)) - (μ (A u)).toReal) ↔ _
        rw [fraction_censor (hA htu) hbt]
        rfl
      simp only [E, preimage_sdiff, preimage_iUnion, hstable t le_rfl]
      congr 1
      ext y
      simp only [mem_iUnion, Finset.mem_filter]
      refine exists_congr fun u => ?_
      exact exists_congr fun hu => by rw [hstable u hu.2.le]
    · intro y hy
      have hp := ENNReal.toReal_pos (hpos t ht) (measure_ne_top μ (A t))
      have hlog : 0 ≤ logTilt a (μ (A t)).toReal :=
        Real.log_nonneg ((le_div_iff₀ hp).2 (by linarith))
      have hcross : ε < fraction (A t) y - (μ (A t)).toReal := hy.1
      rw [tiltDensity_product hm ha hp]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := htilt _ hp
      have hm₀ : 0 ≤ (m : ℝ) := by positivity
      rw [show 2 * (m : ℝ) * ε^2 = m * (2 * ε^2) by ring]
      apply mul_le_mul_of_nonneg_left (h.trans ?_) hm₀
      unfold tiltObjective
      gcongr
      linarith
  have hbound : L * (Measure.pi (fun _ : Fin m => μ)) (⋃ t ∈ s, crossing μ ε (A t)) ≤ 1 := by
    rw [hdecomp, measure_biUnion_finset hdisj (fun t _ => hEm t), Finset.mul_sum]
    refine (Finset.sum_le_sum hpart).trans ?_
    rw [← measure_biUnion_finset hdisj (fun t _ => hEm t)]
    exact prob_le_one
  have hL : L ≠ 0 := by dsimp [L]; positivity
  have hL' : L ≠ ∞ := ENNReal.ofReal_ne_top
  have heq : L * ENNReal.ofReal (Real.exp (-2 * (m : ℝ) * ε^2)) = 1 := by
    dsimp [L]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    rw [show 2 * (m : ℝ) * ε^2 + -2 * m * ε^2 = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
  rw [← heq] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ L⁻¹ from bot_le)
  rwa [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hL hL', one_mul, one_mul] at h

private lemma measure_crossing_eq_zero {m : ℕ} {μ : Measure α} [IsProbabilityMeasure μ]
    {A : Set α} (hzero : μ A = 0) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin m => μ)) (crossing μ ε A) = 0 := by
  have hnull (i : Fin m) : (Measure.pi (fun _ : Fin m => μ)) ((fun y => y i) ⁻¹' A) = 0 :=
    Measure.pi_eval_preimage_null _ hzero
  apply measure_mono_null (t := ⋃ i : Fin m, (fun y => y i) ⁻¹' A) _
    (measure_iUnion_null hnull)
  intro y hy
  by_contra hy'
  simp only [mem_iUnion, mem_preimage, not_exists] at hy'
  have hfrac : fraction A y = 0 := by
    classical
    simp [fraction, Finset.filter_false_of_mem (fun i _ => hy' i)]
  exact hε.not_gt (by simpa [crossing, hfrac, hzero] using hy)

private lemma measure_countable_crossing {τ : Type*} [LinearOrder τ] [Countable τ]
    {m : ℕ} (hm : 0 < m) (μ : Measure α) [IsProbabilityMeasure μ]
    (A : τ → Set α) (hA : Monotone A) (hAm : ∀ t, MeasurableSet (A t))
    {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin m => μ)) (⋃ t, crossing μ ε (A t)) ≤
      ENNReal.ofReal (Real.exp (-2 * (m : ℝ) * ε^2)) := by
  classical
  by_cases hε₁ : ε < 1
  · obtain ⟨a, ha, htilt⟩ := exists_tilt hε hε₁
    let positiveThresholds := {t : τ | μ (A t) ≠ 0}
    let zeroThresholds := {t : τ | μ (A t) = 0}
    have hdecomp : (⋃ t, crossing (m := m) μ ε (A t)) =
        (⋃ t : positiveThresholds, crossing μ ε (A ↑t)) ∪
          (⋃ t : zeroThresholds, crossing μ ε (A ↑t)) := by
      ext y
      simp only [mem_iUnion, mem_union, Subtype.exists, positiveThresholds, zeroThresholds,
        mem_ofPred_eq]
      constructor
      · rintro ⟨t, ht⟩
        by_cases h : μ (A t) = 0
        · exact Or.inr ⟨t, h, ht⟩
        · exact Or.inl ⟨t, h, ht⟩
      · rintro (⟨t, _, ht⟩ | ⟨t, _, ht⟩) <;> exact ⟨t, ht⟩
    have hzero :
        (Measure.pi (fun _ : Fin m => μ)) (⋃ t : zeroThresholds, crossing μ ε (A ↑t)) = 0 :=
      measure_iUnion_null fun t => measure_crossing_eq_zero t.property hε
    rw [hdecomp]
    refine (measure_union_le _ _).trans ?_
    rw [hzero, add_zero]
    let B := fun s : Finset positiveThresholds => ⋃ t ∈ s, crossing (m := m) μ ε (A ↑t)
    have hB : (⋃ t : positiveThresholds, crossing (m := m) μ ε (A ↑t)) =
        ⋃ s : Finset positiveThresholds, B s := by
      ext y
      simp only [B, mem_iUnion]
      exact ⟨fun ⟨t, ht⟩ => ⟨{t}, t, Finset.mem_singleton_self t, ht⟩,
        fun ⟨_, t, _, ht⟩ => ⟨t, ht⟩⟩
    rw [hB]
    have hdir : Directed (· ⊆ ·) B := by
      intro s t
      refine ⟨s ∪ t, ?_, ?_⟩
      · exact biUnion_mono (Finset.subset_union_left) (fun _ _ => Subset.rfl)
      · exact biUnion_mono (Finset.subset_union_right) (fun _ _ => Subset.rfl)
    rw [hdir.measure_iUnion]
    exact iSup_le fun s => measure_finite_crossing hm μ (fun t : positiveThresholds => A ↑t)
      (fun _ _ h => hA h) (fun t => hAm t) s (fun t _ => t.property) ha htilt
  · have hbound : (⋃ t, crossing (m := m) μ ε (A t)) = ∅ := by
      ext y
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      intro t ht
      have hfrac := fraction_le_one hm (A t) y
      have hnonneg := ENNReal.toReal_nonneg (a := μ (A t))
      have hc : ε < fraction (A t) y - (μ (A t)).toReal := ht
      linarith [le_of_not_gt hε₁]
    simp [hbound]

end NestedSets

private lemma exists_rat_of_gt {f : ℝ → ℝ} {ε : ℝ}
    (hf : ∀ x, ContinuousWithinAt f (Ici x) x) (h : ∃ x, ε < f x) :
    ∃ q : ℚ, ε < f q := by
  obtain ⟨x, hx⟩ := h
  have hcx := hf x
  rw [Metric.continuousWithinAt_iff] at hcx
  obtain ⟨δ, hδ, hclose⟩ := hcx (f x - ε) (sub_pos.mpr hx)
  obtain ⟨q, hxq, hqx⟩ := exists_rat_btwn (show x < x + δ by linarith)
  have hd : dist (q : ℝ) x < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxq)]
    linarith
  have hclose := hclose (mem_Ici.mpr hxq.le) hd
  rw [Real.dist_eq, abs_lt] at hclose
  exact ⟨q, by linarith [hclose.1]⟩

private lemma fraction_compl {m : ℕ} (hm : 0 < m)
    {α : Type*} (A : Set α) (y : Fin m → α) : fraction Aᶜ y = 1 - fraction A y := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin m => y i ∈ A)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have hc' : (((Finset.univ.filter (fun i => y i ∈ A)).card : ℕ) : ℝ) +
      ((Finset.univ.filter (fun i => y i ∉ A)).card : ℝ) = (m : ℝ) := by exact_mod_cast hc
  rw [fraction, fraction]
  simp only [mem_compl_iff]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hm.ne')).2
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne')]
  linarith

private lemma fraction_Iic_eq_empiricalCount {Ω : Type*} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (x : ℝ) :
    fraction (Iic x) (fun i : Fin (n + 1) => X i ω) =
      (empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  change empCDF (fun i : Fin (n + 1) => X i ω) x = _
  classical
  unfold empiricalCount
  rw [empCDF_eq_sum_div, Fin.sum_univ_eq_sum_range (fun i => if X i ω ≤ x then (1 : ℝ) else 0),
    Finset.sum_boole]

private lemma fraction_Ioi_sub {m : ℕ} (hm : 0 < m) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) (y : Fin m → ℝ) :
    fraction (Ioi x) y - (μ (Ioi x)).toReal = (μ (Iic x)).toReal - fraction (Iic x) y := by
  rw [← compl_Iic, fraction_compl hm, ← measureReal_def, measureReal_compl measurableSet_Iic,
    probReal_univ, measureReal_def]
  ring

private lemma abs_crossing_iff_rat {m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ε : ℝ) (y : Fin m → ℝ) :
    (∃ x : ℝ, ε < |fraction (Iic x) y - (μ (Iic x)).toReal|) ↔
      ∃ q : ℚ, ε < |fraction (Iic (q : ℝ)) y - (μ (Iic (q : ℝ))).toReal| := by
  have hc (t : ℝ) : (μ (Iic t)).toReal = cdf μ t := (cdf_eq_real μ t).symm
  simp only [hc]
  change (∃ x : ℝ, ε < |empCDF y x - cdf μ x|) ↔ ∃ q : ℚ, ε < |empCDF y q - cdf μ q|
  refine ⟨exists_rat_of_gt (fun x => ?_), fun ⟨q, hq⟩ => ⟨q, hq⟩⟩
  exact ((empCDF_rightContinuous (fun i (_ : Unit) => y i) () x).sub
    ((cdf μ).right_continuous x)).abs

private lemma measure_abs_crossing {m : ℕ} (hm : 0 < m) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin m => μ))
        {y | ∃ x : ℝ, ε < |fraction (Iic x) y - (μ (Iic x)).toReal|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (m : ℝ) * ε^2)) := by
  let upper := ⋃ q : ℚ, crossing (m := m) μ ε (Iic (q : ℝ))
  let lower := ⋃ q : ℚ, crossing (m := m) μ ε (Ioi (-(q : ℝ)))
  have heq : {y | ∃ x : ℝ, ε < |fraction (Iic x) y - (μ (Iic x)).toReal|} =
      upper ∪ lower := by
    ext y
    change (∃ x : ℝ, ε < |fraction (Iic x) y - (μ (Iic x)).toReal|) ↔ y ∈ upper ∪ lower
    rw [abs_crossing_iff_rat]
    simp only [upper, lower, mem_union, mem_iUnion]
    constructor
    · rintro ⟨q, hq⟩
      rcases lt_abs.mp hq with hq | hq
      · exact Or.inl ⟨q, hq⟩
      · refine Or.inr ⟨-q, ?_⟩
        simp only [crossing, mem_ofPred_eq, Rat.cast_neg, neg_neg, fraction_Ioi_sub hm]
        linarith
    · rintro (⟨q, hq⟩ | ⟨q, hq⟩)
      · exact ⟨q, lt_abs.mpr (Or.inl hq)⟩
      · refine ⟨-q, lt_abs.mpr (Or.inr ?_)⟩
        simp only [Rat.cast_neg]
        simp only [crossing, mem_ofPred_eq, fraction_Ioi_sub hm] at hq
        linarith
  have hupper : (Measure.pi (fun _ : Fin m => μ)) upper ≤
      ENNReal.ofReal (Real.exp (-2 * (m : ℝ) * ε^2)) :=
    measure_countable_crossing hm μ (fun q : ℚ => Iic (q : ℝ))
      (fun _ _ h => Iic_subset_Iic.mpr (by exact_mod_cast h)) (fun _ => measurableSet_Iic) hε
  have hlower : (Measure.pi (fun _ : Fin m => μ)) lower ≤
      ENNReal.ofReal (Real.exp (-2 * (m : ℝ) * ε^2)) :=
    measure_countable_crossing hm μ (fun q : ℚ => Ioi (-(q : ℝ)))
      (fun _ _ h => Ioi_subset_Ioi (neg_le_neg (by exact_mod_cast h)))
      (fun _ => measurableSet_Ioi) hε
  rw [heq, two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact (measure_union_le upper lower).trans (add_le_add hupper hlower)

private lemma measurableSet_abs_crossing {m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] (ε : ℝ) :
    MeasurableSet {y : Fin m → ℝ | ∃ x : ℝ, ε < |fraction (Iic x) y - (μ (Iic x)).toReal|} := by
  simp_rw [abs_crossing_iff_rat]
  have hc (t : ℝ) : (μ (Iic t)).toReal = cdf μ t := (cdf_eq_real μ t).symm
  simp only [hc]
  exact measurableSet_uniform_deviation (fun (i : Fin m) (y : Fin m → ℝ) => y i)
    (cdf μ) ε (fun i => measurable_pi_apply i)

/-- **Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant.** Let `X₀, X₁, …` be
independent real random variables on a probability space, each with the law of `X₀`, and let
`F(x) = P(X₀ ≤ x)`. For every `n` and every `ε > 0`, the empirical distribution function
`F_{n+1}(x) = #{i ≤ n : X_i ≤ x} / (n + 1)` of the first `n + 1` observations satisfies
`P(∃ x, |F_{n+1}(x) - F(x)| > ε) ≤ 2 exp(-2 (n + 1) ε²)`. This is the two-sided form of
P. Massart, *The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality*, Ann. Probab. 18
(1990) 1269–1283, Theorem 1 (a one-sided bound, as stated in H. W. J. Reeve, arXiv:2403.16651v1,
p. 3), obtained by a union bound over the two deviations. Reeve's Corollary 2 gives the one-sided
bound for an arbitrary distribution function `F` and every level. The constant is unspecified in
A. Dvoretzky, J. Kiefer and J. Wolfowitz, Ann. Math. Statist. 27 (1956) 642–669. -/
theorem measure_exists_abs_empiricalCDF_sub_gt_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X P) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    P {ω | ∃ x : ℝ, ε < |(empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ) -
        (P (X 0 ⁻¹' Set.Iic x)).toReal|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) * ε ^ 2)) := by
  let μ : Measure ℝ := P.map (X 0)
  have hμ : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff (hMeas 0).aemeasurable).mpr inferInstance
  let Y (ω : Ω) (i : Fin (n + 1)) := X i ω
  have hY : Measurable Y := Measurable.of_eval fun i => hMeas i
  have hYind : iIndepFun (fun (i : Fin (n + 1)) ω => X i ω) P :=
    iIndepFun.precomp Fin.val_injective hIndep
  have hmap : P.map Y = Measure.pi (fun _ : Fin (n + 1) => μ) := by
    have hYm (i : Fin (n + 1)) : AEMeasurable (X i) P := (hMeas i).aemeasurable
    rw [hYind.map_fun_eq_pi_map hYm]
    congr 1
    funext i
    exact (hIdent i).map_eq
  let E := {y : Fin (n + 1) → ℝ | ∃ x : ℝ,
    ε < |fraction (Iic x) y - (μ (Iic x)).toReal|}
  have hE : MeasurableSet E := measurableSet_abs_crossing μ ε
  have heq : {ω | ∃ x : ℝ, ε < |(empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ) -
        (P (X 0 ⁻¹' Iic x)).toReal|} = Y ⁻¹' E := by
    ext ω
    simp only [E, mem_preimage, mem_ofPred_eq, Y, fraction_Iic_eq_empiricalCount, μ,
      Measure.map_apply (hMeas 0) measurableSet_Iic]
  rw [heq, ← Measure.map_apply hY hE, hmap]
  exact measure_abs_crossing (Nat.succ_pos n) μ hε

end MathlibExt.Probability.Statistics.DKWInequalityWanted
