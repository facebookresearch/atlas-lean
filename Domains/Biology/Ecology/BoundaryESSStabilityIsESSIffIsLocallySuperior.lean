/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Domains.Biology.Ecology.BoundaryESSStabilityTendstoOfPos

/-!
# ESS is equivalent to local superiority

For a symmetric matrix game with payoff matrix `A`, a state `p` of the simplex
`Δ = {x | x ≥ 0, ∑ x = 1}` is an evolutionarily stable state (ESS) in the sense of Maynard
Smith and Price iff it is locally superior: `x · A x < p · A x` for all `x ≠ p` in `Δ`
near `p`.

## Definitions

* `simplex ι`: the simplex of mixed strategies.
* `IsESS A p`: `p` is an evolutionarily stable state of `A`.
* `IsLocallySuperior A p`: `p` is locally superior for `A`.

## Main results

* `isESS_iff_isLocallySuperior`: `p` is an ESS of `A` iff `p` is locally superior for `A`.

Sources: J. Hofbauer, P. Schuster and K. Sigmund, "A note on evolutionary stable strategies and
game dynamics", J. Theor. Biol. 81 (1979) 609–612; P. D. Taylor and L. B. Jonker,
"Evolutionarily stable strategies and game dynamics", Math. Biosci. 40 (1978) 145–156, §§2–4;
J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc. (N.S.) 40
(2003) 479–519, §2.6, Theorem 7.
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι]

/-- `p` is **locally superior**: `p ∈ Δ` and `x · A x < p · A x` for every `x ≠ p` in `Δ`
near `p`. -/
def IsLocallySuperior (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧ ∀ᶠ x in 𝓝 p, x ∈ simplex ι → x ≠ p → x ⬝ᵥ A *ᵥ x < p ⬝ᵥ A *ᵥ x

/-- Expansion of `(p + t • y) ⬝ᵥ A *ᵥ p`. -/
private theorem expand_left (A : Matrix ι ι ℝ) (p y : ι → ℝ) (t : ℝ) :
    (p + t • y) ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p + t * (y ⬝ᵥ A *ᵥ p) := by
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]

/-- Expansion of `p ⬝ᵥ A *ᵥ (p + t • y)`. -/
private theorem expand_right (A : Matrix ι ι ℝ) (p y : ι → ℝ) (t : ℝ) :
    p ⬝ᵥ A *ᵥ (p + t • y) = p ⬝ᵥ A *ᵥ p + t * (p ⬝ᵥ A *ᵥ y) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, smul_eq_mul]

/-- Expansion of `(p + t • y) ⬝ᵥ A *ᵥ (p + t • y)`. -/
private theorem expand_self (A : Matrix ι ι ℝ) (p y : ι → ℝ) (t : ℝ) :
    (p + t • y) ⬝ᵥ A *ᵥ (p + t • y)
      = p ⬝ᵥ A *ᵥ p + t * (y ⬝ᵥ A *ᵥ p + p ⬝ᵥ A *ᵥ y) + t ^ 2 * (y ⬝ᵥ A *ᵥ y) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Expansion of `(q - p) ⬝ᵥ A *ᵥ p`. -/
private theorem expand_diff_left (A : Matrix ι ι ℝ) (q p : ι → ℝ) :
    (q - p) ⬝ᵥ A *ᵥ p = q ⬝ᵥ A *ᵥ p - p ⬝ᵥ A *ᵥ p := by
  simp only [sub_dotProduct]

/-- Expansion of `(q - p) ⬝ᵥ A *ᵥ (q - p)`. -/
private theorem expand_diff (A : Matrix ι ι ℝ) (q p : ι → ℝ) :
    (q - p) ⬝ᵥ A *ᵥ (q - p)
      = q ⬝ᵥ A *ᵥ q - q ⬝ᵥ A *ᵥ p - p ⬝ᵥ A *ᵥ q + p ⬝ᵥ A *ᵥ p := by
  simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  ring

/-- If `t * s < 0` with `0 < t` then `s < 0`. -/
private theorem neg_of_mul_pos {t s : ℝ} (h : t * s < 0) (ht : 0 < t) : s < 0 := by
  by_contra hcon
  push Not at hcon
  exact absurd (mul_nonneg ht.le hcon) (not_le_of_gt h)

/-- If `t * s ≤ 0` with `0 < t` then `s ≤ 0`. -/
private theorem nonpos_of_mul_pos {t s : ℝ} (h : t * s ≤ 0) (ht : 0 < t) : s ≤ 0 := by
  by_contra hcon
  push Not at hcon
  exact absurd (mul_pos ht hcon) (not_lt_of_ge h)

omit [Fintype ι] in
/-- A nonzero scalar multiple vanishes only if the vector does. -/
private theorem eq_zero_of_smul_eq_zero {t : ℝ} {v : ι → ℝ} (ht : t ≠ 0) (h : t • v = 0) :
    v = 0 :=
  (smul_eq_zero.mp h).resolve_left ht

/-- The map `y ↦ A *ᵥ y` is continuous. -/
private theorem continuous_mulVec (A : Matrix ι ι ℝ) :
    Continuous fun z : ι → ℝ => A *ᵥ z :=
  (Matrix.mulVecLin A).continuous_of_finiteDimensional

/-- The payoff `y ⬝ᵥ A *ᵥ y` is continuous in `y`. -/
private theorem continuous_self (A : Matrix ι ι ℝ) :
    Continuous fun y : ι → ℝ => y ⬝ᵥ A *ᵥ y := by
  have hm := continuous_mulVec A
  simp only [dotProduct]
  fun_prop

/-- The payoff `y ⬝ᵥ A *ᵥ p` is continuous in `y`. -/
private theorem continuous_left (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    Continuous fun y : ι → ℝ => y ⬝ᵥ A *ᵥ p := by
  simp only [dotProduct]
  fun_prop

omit [Fintype ι] in
/-- The segment map `t ↦ p + t • (q - p)` is continuous. -/
private theorem continuous_seg (p q : ι → ℝ) :
    Continuous fun t : ℝ => p + t • (q - p) := by
  rw [continuous_pi_iff]
  intro i
  have hexp : (fun t : ℝ => (p + t • (q - p)) i) = fun t : ℝ => p i + t * (q i - p i) := by
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hexp]
  fun_prop

/-- The segment from `p` toward `q` stays in the simplex for `t ∈ [0, 1]`. -/
private theorem seg_mem {p q : ι → ℝ} (hp : p ∈ simplex ι) (hq : q ∈ simplex ι) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : p + t • (q - p) ∈ simplex ι := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  refine ⟨fun i => ?_, ?_⟩
  · have hexp : (p + t • (q - p)) i = (1 - t) * p i + t * q i := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hexp]
    exact add_nonneg (mul_nonneg (sub_nonneg.2 ht1) (hp0 i)) (mul_nonneg ht0 (hq0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hp1, hq1]
    ring

omit [Fintype ι] in
/-- Points of the segment `p + t • (q - p)` with `t > 0` differ from `p` when `q ≠ p`. -/
private theorem seg_ne {p q : ι → ℝ} (hqp : q ≠ p) {t : ℝ} (ht : 0 < t) :
    p + t • (q - p) ≠ p := by
  intro hcon
  apply hqp
  have h1 : t • (q - p) = 0 := by
    have h2 := congrArg (· - p) hcon
    simpa using h2
  have h0 := eq_zero_of_smul_eq_zero ht.ne' h1
  exact sub_eq_zero.1 h0

open scoped Classical in
/-- **ESS ⇔ local superiority** (Hofbauer, Schuster and Sigmund 1979). For every payoff matrix
`A` and every `p`, `p` is an ESS of `A` iff `p ∈ Δ` and `x · A x < p · A x` for all `x ≠ p` in
`Δ` near `p`.

Source: Hofbauer, Schuster and Sigmund (1979), pp. 609–611. -/
public theorem isESS_iff_isLocallySuperior (A : Matrix ι ι ℝ) (p : ι → ℝ) :
    IsESS A p ↔ IsLocallySuperior A p := by
  constructor
  · rintro ⟨hp, hESS⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [not_imp, not_lt] at hcon
    have hseq : ∀ n : ℕ, ∃ x : ι → ℝ, (x ∈ simplex ι ∧ x ≠ p ∧ p ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ A *ᵥ x) ∧
        dist x p < 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hball : ∀ᶠ x in 𝓝 p, dist x p < 1 / ((n : ℝ) + 1) :=
        Filter.eventually_of_mem (Metric.ball_mem_nhds p hpos) fun x hx => Metric.mem_ball.1 hx
      exact (hcon.and_eventually hball).exists
    choose x hx using hseq
    have hxmem : ∀ n, x n ∈ simplex ι := fun n => (hx n).1.1
    have hxne : ∀ n, x n ≠ p := fun n => (hx n).1.2.1
    have hxle : ∀ n, p ⬝ᵥ A *ᵥ x n ≤ x n ⬝ᵥ A *ᵥ x n := fun n => (hx n).1.2.2
    have hxdist : ∀ n, dist (x n) p < 1 / ((n : ℝ) + 1) := fun n => (hx n).2
    have hdist0 : Tendsto (fun n => dist (x n) p) atTop (𝓝 0) :=
      squeeze_zero (fun n => dist_nonneg) (fun n => (hxdist n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hxtend : Tendsto x atTop (𝓝 p) := tendsto_iff_dist_tendsto_zero.2 hdist0
    have hnorm_pos : ∀ n, 0 < ‖x n - p‖ := fun n => norm_pos_iff.2 (sub_ne_zero.2 (hxne n))
    set u : ℕ → ι → ℝ := fun n => (‖x n - p‖)⁻¹ • (x n - p) with hudef
    have hmem : ∀ n, u n ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      intro n
      rw [Metric.mem_sphere, dist_zero_right]
      simp only [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hnorm_pos n)]
      exact inv_mul_cancel₀ (hnorm_pos n).ne'
    have hcompact : IsCompact (Metric.sphere (0 : ι → ℝ) 1) :=
      (isCompact_closedBall _ _).of_isClosed_subset Metric.isClosed_sphere
        Metric.sphere_subset_closedBall
    obtain ⟨w, hwmem, φ, hφmono, hφtend⟩ := hcompact.tendsto_subseq hmem
    have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    set y : ℕ → ι → ℝ := fun n => x (φ n) with hydef
    set δ : ℕ → ℝ := fun n => ‖y n - p‖ with hδdef
    set v : ℕ → ι → ℝ := fun n => (δ n)⁻¹ • (y n - p) with hvdef
    have hymem : ∀ n, y n ∈ simplex ι := fun n => hxmem (φ n)
    have hyne : ∀ n, y n ≠ p := fun n => hxne (φ n)
    have hyle : ∀ n, p ⬝ᵥ A *ᵥ y n ≤ y n ⬝ᵥ A *ᵥ y n := fun n => hxle (φ n)
    have hytend : Tendsto y atTop (𝓝 p) := hxtend.comp hφtop
    have hδpos : ∀ n, 0 < δ n := fun n => hnorm_pos (φ n)
    have hδtend : Tendsto δ atTop (𝓝 0) := by
      have h := tendsto_iff_dist_tendsto_zero.1 hytend
      simpa [hδdef, dist_eq_norm] using h
    have hvtend : Tendsto v atTop (𝓝 w) := hφtend
    have hydecomp : ∀ n, y n = p + δ n • v n := by
      intro n
      simp only [hvdef]
      rw [smul_inv_smul₀ (hδpos n).ne']
      exact (add_sub_cancel p (y n)).symm
    have ha_neg : ∀ n, v n ⬝ᵥ A *ᵥ p < 0 := by
      intro n
      rcases hESS (y n) (hymem n) (hyne n) with hlt | ⟨heq, hlt2⟩
      · rw [hydecomp n, expand_left] at hlt
        have hmul : δ n * (v n ⬝ᵥ A *ᵥ p) < 0 := by linarith [hlt]
        exact neg_of_mul_pos hmul (hδpos n)
      · exact absurd hlt2 (not_lt_of_ge (hyle n))
    have hatend : Tendsto (fun n => v n ⬝ᵥ A *ᵥ p) atTop (𝓝 (w ⬝ᵥ A *ᵥ p)) :=
      ((continuous_left A p).tendsto w).comp hvtend
    have hbtend : Tendsto (fun n => v n ⬝ᵥ A *ᵥ v n) atTop (𝓝 (w ⬝ᵥ A *ᵥ w)) :=
      ((continuous_self A).tendsto w).comp hvtend
    have ha_le : w ⬝ᵥ A *ᵥ p ≤ 0 :=
      le_of_tendsto hatend (Filter.Eventually.of_forall fun n => (ha_neg n).le)
    have hf : ∀ n, p ⬝ᵥ A *ᵥ y n - y n ⬝ᵥ A *ᵥ y n
        = -(δ n * (v n ⬝ᵥ A *ᵥ p)) - (δ n) ^ 2 * (v n ⬝ᵥ A *ᵥ v n) := by
      intro n
      rw [hydecomp n, expand_right, expand_self]
      ring
    have ha_ge : 0 ≤ w ⬝ᵥ A *ᵥ p := by
      have hlim : Tendsto (fun n => -(v n ⬝ᵥ A *ᵥ p) - δ n * (v n ⬝ᵥ A *ᵥ v n)) atTop
          (𝓝 (-(w ⬝ᵥ A *ᵥ p) - 0 * (w ⬝ᵥ A *ᵥ w))) :=
        hatend.neg.sub (hδtend.mul hbtend)
      have hstep : ∀ n, -(v n ⬝ᵥ A *ᵥ p) - δ n * (v n ⬝ᵥ A *ᵥ v n) ≤ 0 := by
        intro n
        have h0' : p ⬝ᵥ A *ᵥ y n - y n ⬝ᵥ A *ᵥ y n ≤ 0 := sub_nonpos.2 (hyle n)
        rw [hf n] at h0'
        have hmul : δ n * (-(v n ⬝ᵥ A *ᵥ p) - δ n * (v n ⬝ᵥ A *ᵥ v n)) ≤ 0 := by
          have hring : δ n * (-(v n ⬝ᵥ A *ᵥ p) - δ n * (v n ⬝ᵥ A *ᵥ v n))
              = -(δ n * (v n ⬝ᵥ A *ᵥ p)) - (δ n) ^ 2 * (v n ⬝ᵥ A *ᵥ v n) := by ring
          rw [hring]
          exact h0'
        exact nonpos_of_mul_pos hmul (hδpos n)
      have hle := le_of_tendsto hlim (Filter.Eventually.of_forall hstep)
      simpa only [zero_mul, sub_zero, neg_nonpos] using hle
    have ha0 : w ⬝ᵥ A *ᵥ p = 0 := le_antisymm ha_le ha_ge
    have hsum0 : ∑ i, w i = 0 := by
      have hsumcont : Continuous fun y : ι → ℝ => ∑ i, y i :=
        continuous_finsetSum _ fun i _ => continuous_apply i
      have hsumtend : Tendsto (fun n => ∑ i, v n i) atTop (𝓝 (∑ i, w i)) :=
        (hsumcont.tendsto w).comp hvtend
      have hvn : ∀ n, ∑ i, v n i = 0 := by
        intro n
        have hym1 : ∑ i, y n i = 1 := (hymem n).2
        have hp1 : ∑ i, p i = 1 := hp.2
        simp only [hvdef, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Pi.sub_apply,
          Finset.sum_sub_distrib, hym1, hp1, sub_self, mul_zero]
      have h0 : Tendsto (fun n => ∑ i, v n i) atTop (𝓝 0) := by
        simp only [hvn]
        exact tendsto_const_nhds
      exact (tendsto_nhds_unique h0 hsumtend).symm
    have hw_nonneg : ∀ i, p i = 0 → 0 ≤ w i := by
      intro i hi
      have hcont_i : Tendsto (fun n => v n i) atTop (𝓝 (w i)) :=
        ((continuous_apply i).tendsto w).comp hvtend
      apply ge_of_tendsto hcont_i
      apply Filter.Eventually.of_forall
      intro n
      have hy0 : 0 ≤ y n i := (hymem n).1 i
      simp only [hvdef, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hi, sub_zero]
      exact mul_nonneg (inv_nonneg.2 (hδpos n).le) hy0
    have hwne : w ≠ 0 := by
      rintro rfl
      rw [Metric.mem_sphere, dist_self] at hwmem
      exact zero_ne_one hwmem
    have huniv : (Finset.univ : Finset ι).Nonempty := by
      by_contra hcon
      have hempty : (Finset.univ : Finset ι) = ∅ := by
        simpa [Finset.nonempty_iff_ne_empty] using hcon
      have hp1 : ∑ i, p i = 1 := hp.2
      rw [hempty, Finset.sum_empty] at hp1
      exact one_ne_zero hp1.symm
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
      (fun i => if p i = 0 then (1 : ℝ) else p i / (|w i| + 1)) huniv
    have hmin : ∀ i, (if p i₀ = 0 then (1 : ℝ) else p i₀ / (|w i₀| + 1))
        ≤ (if p i = 0 then (1 : ℝ) else p i / (|w i| + 1)) :=
      fun i => hi₀ i (Finset.mem_univ i)
    set t₀ : ℝ := (if p i₀ = 0 then (1 : ℝ) else p i₀ / (|w i₀| + 1)) with ht₀def
    have ht₀pos : 0 < t₀ := by
      rw [ht₀def]
      by_cases hi : p i₀ = 0
      · rw [ite_eq_left hi]
        exact one_pos
      · rw [ite_eq_right hi]
        have hpi : 0 < p i₀ := lt_of_le_of_ne (hp.1 i₀) (Ne.symm hi)
        exact div_pos hpi (by positivity)
    have hqmem : ∀ t : ℝ, 0 < t → t ≤ t₀ → p + t • w ∈ simplex ι := by
      intro t htt htle
      have hsum : ∑ i, (p + t • w) i = 1 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        rw [hsum0]
        simp [hp.2]
      have hnonneg : ∀ i, 0 ≤ (p + t • w) i := by
        intro i
        by_cases hi : p i = 0
        · have hwi := hw_nonneg i hi
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hi, zero_add]
          exact mul_nonneg htt.le hwi
        · have hpi : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hi)
          have hle : t ≤ p i / (|w i| + 1) := by
            have hmi := hmin i
            rw [ite_eq_right hi] at hmi
            exact htle.trans hmi
          have hfrac : t * |w i| < p i := by
            have hd : (0 : ℝ) < |w i| + 1 := by positivity
            have h1 : t * |w i| ≤ p i / (|w i| + 1) * |w i| :=
              mul_le_mul_of_nonneg_right hle (abs_nonneg _)
            have h2 : p i / (|w i| + 1) * |w i| < p i := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
              nlinarith [abs_nonneg (w i), hpi]
            exact h1.trans_lt h2
          have hexp : (p + t • w) i = p i + t * w i := by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hexp]
          have h3 : -(t * |w i|) ≤ t * w i := by
            have hneg := neg_abs_le (t * w i)
            rw [abs_mul, abs_of_pos htt] at hneg
            exact hneg
          linarith [hfrac]
      exact ⟨hnonneg, hsum⟩
    have hqmem0 : p + t₀ • w ∈ simplex ι := hqmem t₀ ht₀pos le_rfl
    have hqne : p + t₀ • w ≠ p := by
      intro hcon
      have h1 : t₀ • w = 0 := by
        have h2 := congrArg (· - p) hcon
        simpa using h2
      exact hwne (eq_zero_of_smul_eq_zero ht₀pos.ne' h1)
    have hqAp : (p + t₀ • w) ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p := by
      rw [expand_left, ha0, mul_zero, add_zero]
    have hb_neg : w ⬝ᵥ A *ᵥ w < 0 := by
      have hdisj := hESS _ hqmem0 hqne
      rcases hdisj with hlt | ⟨heq, hlt⟩
      · rw [hqAp] at hlt
        exact absurd hlt (lt_irrefl _)
      · rw [expand_self, expand_right, ha0] at hlt
        have hmul : t₀ ^ 2 * (w ⬝ᵥ A *ᵥ w) < 0 := by
          have hring : t₀ ^ 2 * (w ⬝ᵥ A *ᵥ w)
              = (p ⬝ᵥ A *ᵥ p + t₀ * (0 + p ⬝ᵥ A *ᵥ w) + t₀ ^ 2 * (w ⬝ᵥ A *ᵥ w))
                - (p ⬝ᵥ A *ᵥ p + t₀ * (p ⬝ᵥ A *ᵥ w)) := by ring
          rw [hring]
          linarith [hlt]
        exact neg_of_mul_pos hmul (pow_pos ht₀pos 2)
    have hev_pos : ∀ᶠ n in atTop, 0 < v n ⬝ᵥ A *ᵥ p := by
      have hb2 : w ⬝ᵥ A *ᵥ w < (w ⬝ᵥ A *ᵥ w) / 2 := by linarith [hb_neg]
      have hev := hbtend.eventually_lt_const hb2
      filter_upwards [hev] with n hn
      have h0' : p ⬝ᵥ A *ᵥ y n - y n ⬝ᵥ A *ᵥ y n ≤ 0 := sub_nonpos.2 (hyle n)
      rw [hf n] at h0'
      have hbpos : 0 < -(v n ⬝ᵥ A *ᵥ v n) := by linarith [hn, hb_neg]
      have hda : 0 < δ n * (v n ⬝ᵥ A *ᵥ p) := by
        have h2 : (0 : ℝ) < (δ n) ^ 2 * (-(v n ⬝ᵥ A *ᵥ v n)) :=
          mul_pos (pow_pos (hδpos n) 2) hbpos
        have hring : (δ n) ^ 2 * (-(v n ⬝ᵥ A *ᵥ v n))
            = δ n * (v n ⬝ᵥ A *ᵥ p)
              + (-(δ n * (v n ⬝ᵥ A *ᵥ p)) - (δ n) ^ 2 * (v n ⬝ᵥ A *ᵥ v n)) := by ring
        rw [hring] at h2
        linarith [h0']
      exact pos_of_mul_pos_right hda (hδpos n).le
    have hcontra := ((Filter.Eventually.of_forall ha_neg).and hev_pos).exists
    obtain ⟨n, hn1, hn2⟩ := hcontra
    exact absurd hn1 (not_lt_of_gt hn2)
  · rintro ⟨hp, hloc⟩
    refine ⟨hp, fun q hq hqp => ?_⟩
    have hcts : Continuous fun t : ℝ => p + t • (q - p) := continuous_seg p q
    have htend : Tendsto (fun t : ℝ => p + t • (q - p)) (𝓝[>] 0) (𝓝 p) := by
      have h : Tendsto (fun t : ℝ => p + t • (q - p)) (𝓝[>] 0)
          (𝓝 ((fun t : ℝ => p + t • (q - p)) 0)) :=
        (hcts.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (p + t • (q - p)) ∈ simplex ι →
        (p + t • (q - p)) ≠ p →
        (p + t • (q - p)) ⬝ᵥ A *ᵥ (p + t • (q - p)) < p ⬝ᵥ A *ᵥ (p + t • (q - p)) :=
      htend.eventually hloc
    have hmem0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi 0 :=
      Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => ht
    have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
    have hexpand : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (q - p) ⬝ᵥ A *ᵥ p + t * ((q - p) ⬝ᵥ A *ᵥ (q - p)) < 0 := by
      filter_upwards [hev, hmem0, hlt1] with t ht h0 h1
      have h0' : 0 < t := h0
      have hmem : p + t • (q - p) ∈ simplex ι := seg_mem hp hq h0'.le h1.le
      have hne : p + t • (q - p) ≠ p := seg_ne hqp h0'
      have hine := ht hmem hne
      rw [expand_self, expand_right] at hine
      have hmul : t * ((q - p) ⬝ᵥ A *ᵥ p + t * ((q - p) ⬝ᵥ A *ᵥ (q - p))) < 0 := by
        have hring : t * ((q - p) ⬝ᵥ A *ᵥ p + t * ((q - p) ⬝ᵥ A *ᵥ (q - p)))
            = t * ((q - p) ⬝ᵥ A *ᵥ p + p ⬝ᵥ A *ᵥ (q - p)) + t ^ 2 * ((q - p) ⬝ᵥ A *ᵥ (q - p))
              - t * (p ⬝ᵥ A *ᵥ (q - p)) := by ring
        rw [hring]
        linarith [hine]
      exact neg_of_mul_pos hmul h0'
    have hcts2 : Continuous fun t : ℝ =>
        (q - p) ⬝ᵥ A *ᵥ p + t * ((q - p) ⬝ᵥ A *ᵥ (q - p)) := by
      fun_prop
    have hlim : Tendsto (fun t : ℝ => (q - p) ⬝ᵥ A *ᵥ p + t * ((q - p) ⬝ᵥ A *ᵥ (q - p)))
        (𝓝[>] 0) (𝓝 ((q - p) ⬝ᵥ A *ᵥ p + 0 * ((q - p) ⬝ᵥ A *ᵥ (q - p)))) :=
      (hcts2.tendsto 0).mono_left nhdsWithin_le_nhds
    have hle : (q - p) ⬝ᵥ A *ᵥ p + 0 * ((q - p) ⬝ᵥ A *ᵥ (q - p)) ≤ 0 :=
      le_of_tendsto hlim (hexpand.mono fun t ht => ht.le)
    simp only [zero_mul, add_zero, expand_diff_left] at hle
    by_cases heq : q ⬝ᵥ A *ᵥ p = p ⬝ᵥ A *ᵥ p
    · refine Or.inr ⟨heq, ?_⟩
      have h0' : (q - p) ⬝ᵥ A *ᵥ p = 0 := by
        rw [expand_diff_left]
        linarith [heq]
      rw [h0'] at hexpand
      obtain ⟨t, ht⟩ := (hexpand.and hmem0).exists
      have htpos : 0 < t := ht.2
      have hneg : (q - p) ⬝ᵥ A *ᵥ (q - p) < 0 := by
        by_contra hcon
        push Not at hcon
        have hnn := mul_nonneg htpos.le hcon
        have h1 := ht.1
        simp only [zero_add] at h1
        linarith [hnn]
      rw [expand_diff, heq] at hneg
      linarith [hneg]
    · refine Or.inl ?_
      have hle' : q ⬝ᵥ A *ᵥ p ≤ p ⬝ᵥ A *ᵥ p := by linarith [hle]
      exact lt_of_le_of_ne hle' heq

end WantedExt.Biology.Ecology.BoundaryESSStabilityWanted
