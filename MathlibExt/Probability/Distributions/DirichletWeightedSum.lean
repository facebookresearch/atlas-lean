/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Dirichlet
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The distribution function of a weighted sum of a flat Dirichlet vector

Let `θ ∼ Dir(1, …, 1)` be uniform on the probability simplex in `ℝⁿ⁺¹` and let
`w₀, …, wₙ` be pairwise distinct real weights. For every real `x`,

`P(∑ⱼ wⱼ θⱼ ≤ x) = (-1)ⁿ ∑ⱼ (x - wⱼ)₊ⁿ / ∏_{m ≠ j} (wⱼ - wₘ)`  (`n ≥ 1`).

The weights may have any signs and need not be sorted. The full sum over all `n + 1` nodes is
needed: for `x` above every weight the formula equals `1` by the saturation identity
`sum_sub_pow_div_prod_erase_sub`.

* `sum_inv_prod_erase_sub_eq_zero`: `∑ᵢ 1 / ∏_{m ≠ i} (wᵢ - wₘ) = 0` for at least two distinct
  nodes (Lagrange interpolation of the constant polynomial `1`).
* `sum_sub_pow_div_prod_erase_sub`: `∑ⱼ (x - wⱼ)ⁿ / ∏_{m ≠ j} (wⱼ - wₘ) = (-1)ⁿ` for `n + 1`
  distinct nodes.
* `dirichletMeasure_one_real_weightedSum_le`: the distribution function above.

The proof is by induction on `n`, following `lintegral_dirichletDensity`: integrating out the
first coordinate `t` after rescaling the others by `1 - t` turns the event into the same event
for the remaining weights at the level `(x - t w₀) / (1 - t)`, so the induction runs over all
real levels. A one-dimensional integral of a truncated power and the identity
`sum_inv_prod_erase_sub_eq_zero` close the step. The case `n = 0` uses the Heaviside convention
for the truncated power of degree `0`; the stated theorem assumes `n ≥ 1`, where `(·)₊ⁿ` is
`max (·) 0 ^ n`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions, Vol. 1*,
  Wiley, 2000, Chapter 49 (background on the Dirichlet distribution, as cited in
  `MathlibExt.Probability.Distributions.Dirichlet`; not a source for the formula above).
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Real Set Finset Filter Topology Polynomial
open scoped ENNReal

namespace ProbabilityTheory

/-! ### Partial-fraction identities -/

/-- **Partial fractions of the constant `1`**: for at least two distinct real nodes,
`∑ᵢ 1 / ∏_{m ≠ i} (wᵢ - wₘ) = 0` (Lagrange interpolation of the constant polynomial `1`). -/
theorem sum_inv_prod_erase_sub_eq_zero {n : ℕ} {w : Fin (n + 2) → ℝ}
    (hw : Function.Injective w) :
    ∑ i, 1 / ∏ m ∈ univ.erase i, (w i - w m) = 0 := by
  have h := Lagrange.coeff_eq_sum (s := (univ : Finset (Fin (n + 2)))) (v := w)
    (P := (1 : ℝ[X])) hw.injOn (by
      simp only [degree_one, card_univ, Fintype.card_fin]
      exact_mod_cast Nat.succ_pos (n + 1))
  simp only [card_univ, Fintype.card_fin, eval_one] at h
  rw [← h]
  simp [coeff_one]

/-- **Partial fractions of `(x - X)ⁿ`**: for `n + 1` distinct real nodes and every real `x`,
`∑ⱼ (x - wⱼ)ⁿ / ∏_{m ≠ j} (wⱼ - wₘ) = (-1)ⁿ` (Lagrange interpolation of `(x - X)ⁿ`). This is
why the distribution function `dirichletMeasure_one_real_weightedSum_le` equals `1` above every
weight. -/
theorem sum_sub_pow_div_prod_erase_sub {n : ℕ} {w : Fin (n + 1) → ℝ}
    (hw : Function.Injective w) (x : ℝ) :
    ∑ j, (x - w j) ^ n / ∏ m ∈ univ.erase j, (w j - w m) = (-1) ^ n := by
  have hP : ((C x - X) ^ n : ℝ[X]) = C ((-1) ^ n) * (X - C x) ^ n := by
    rw [C_pow, ← mul_pow]
    congr 1
    simp only [map_neg, map_one]
    ring
  have hdeg : ((C x - X) ^ n : ℝ[X]).degree < #(univ : Finset (Fin (n + 1))) := by
    rw [card_univ, Fintype.card_fin, hP]
    refine (degree_mul_le _ _).trans_lt ?_
    refine (add_le_add degree_C_le (degree_pow_le _ _)).trans_lt ?_
    rw [degree_X_sub_C, zero_add, nsmul_one]
    exact_mod_cast Nat.lt_succ_self n
  have h := Lagrange.coeff_eq_sum (s := (univ : Finset (Fin (n + 1)))) (v := w)
    (P := ((C x - X) ^ n : ℝ[X])) hw.injOn hdeg
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, eval_pow, eval_sub, eval_C,
    eval_X] at h
  rw [← h, hP, coeff_C_mul]
  have hm : ((X - C x) ^ n : ℝ[X]).coeff n = 1 := by
    have := ((monic_X_sub_C x).pow n).coeff_natDegree
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at this
  rw [hm, mul_one]

/-- Removing the node `j.succ` from `Fin (n + 2)`: the product splits off the node `0`. -/
private lemma prod_erase_succ {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 2) → M)
    (j : Fin (n + 1)) :
    ∏ m ∈ univ.erase j.succ, f m = f 0 * ∏ m ∈ univ.erase j, f m.succ := by
  classical
  have h1 : ∀ {k : ℕ} (g : Fin k → M) (i : Fin k),
      ∏ m ∈ univ.erase i, g m = ∏ m, if m = i then 1 else g m := by
    intro k g i
    rw [← prod_erase (s := univ) (a := i) (f := fun m ↦ if m = i then 1 else g m) (by simp)]
    refine prod_congr rfl fun m hm ↦ ?_
    rw [ite_eq_right (ne_of_mem_erase hm)]
  rw [h1, h1, Fin.prod_univ_succ, ite_eq_right (Fin.succ_ne_zero j).symm]
  simp only [Fin.succ_inj]

/-! ### Truncated powers -/

/-- The truncated power `s₊ⁿ`, with the Heaviside convention `s₊⁰ = 𝟙[0 ≤ s]`. -/
private noncomputable def truncPow (n : ℕ) (s : ℝ) : ℝ := if 0 ≤ s then s ^ n else 0

private lemma truncPow_of_nonneg {n : ℕ} {s : ℝ} (hs : 0 ≤ s) : truncPow n s = s ^ n :=
  ite_eq_left hs

private lemma truncPow_of_neg {n : ℕ} {s : ℝ} (hs : s < 0) : truncPow n s = 0 :=
  ite_eq_right (not_le.2 hs)

private lemma truncPow_eq_max_pow {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    truncPow n s = max s 0 ^ n := by
  rcases le_or_gt 0 s with hs | hs
  · rw [truncPow_of_nonneg hs, max_eq_left hs]
  · rw [truncPow_of_neg hs, max_eq_right hs.le, zero_pow hn]

private lemma abs_truncPow_le (n : ℕ) (s : ℝ) : |truncPow n s| ≤ |s| ^ n := by
  unfold truncPow
  split_ifs with h
  · rw [abs_pow]
  · simp

private lemma truncPow_mul (n : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    truncPow n (a * s) = a ^ n * truncPow n s := by
  rcases le_or_gt 0 s with hs | hs
  · rw [truncPow_of_nonneg hs, truncPow_of_nonneg (mul_nonneg ha.le hs), mul_pow]
  · rw [truncPow_of_neg hs, truncPow_of_neg (mul_neg_of_pos_of_neg ha hs), mul_zero]

private lemma measurable_truncPow (n : ℕ) : Measurable (truncPow n) :=
  Measurable.ite measurableSet_Ici (measurable_id.pow_const n) measurable_const

private lemma continuous_truncPow_succ (n : ℕ) : Continuous (truncPow (n + 1)) := by
  have : truncPow (n + 1) = fun s ↦ max s 0 ^ (n + 1) :=
    funext (truncPow_eq_max_pow (Nat.succ_ne_zero n))
  rw [this]
  fun_prop

private lemma hasDerivAt_truncPow_succ (n : ℕ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (truncPow (n + 1)) ((n + 1 : ℝ) * truncPow n s) s := by
  rcases hs.lt_or_gt with hs | hs
  · have hev : truncPow (n + 1) =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) :=
      (eventually_lt_nhds hs).mono fun u hu ↦ truncPow_of_neg hu
    rw [truncPow_of_neg hs, mul_zero]
    exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
  · have hev : truncPow (n + 1) =ᶠ[𝓝 s] fun u ↦ u ^ (n + 1) :=
      (eventually_gt_nhds hs).mono fun u hu ↦ truncPow_of_nonneg hu.le
    rw [truncPow_of_nonneg hs.le]
    have h := hasDerivAt_pow (n + 1) s
    simp only [Nat.add_sub_cancel] at h
    push_cast at h
    exact h.congr_of_eventuallyEq hev

private lemma intervalIntegrable_truncPow_sub_mul (n : ℕ) (c d : ℝ) :
    IntervalIntegrable (fun t ↦ truncPow n (c - t * d)) volume 0 1 := by
  have hg : IntervalIntegrable (fun t : ℝ ↦ |c - t * d| ^ n) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ ↦ |c - t * d| ^ n).intervalIntegrable 0 1
  refine hg.mono_fun' ?_ ?_
  · exact ((measurable_truncPow n).comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      simpa [Real.norm_eq_abs] using abs_truncPow_le n (c - t * d)

/-- `∫₀¹ (c - t d)₊ⁿ dt = (c₊ⁿ⁺¹ - (c - d)₊ⁿ⁺¹) / ((n + 1) d)` for `d ≠ 0`. -/
private lemma integral_truncPow_sub_mul (n : ℕ) (c : ℝ) {d : ℝ} (hd : d ≠ 0) :
    ∫ t in (0 : ℝ)..1, truncPow n (c - t * d) =
      (truncPow (n + 1) c - truncPow (n + 1) (c - d)) / ((n + 1) * d) := by
  set F : ℝ → ℝ := fun t ↦ -truncPow (n + 1) (c - t * d) / ((n + 1) * d) with hF
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1 \ {c / d},
      HasDerivAt F (truncPow n (c - t * d)) t := by
    intro t ht
    have hne : c - t * d ≠ 0 := by
      intro h
      apply ht.2
      rw [mem_singleton_iff, eq_div_iff hd]
      linarith
    have h1 : HasDerivAt (fun t : ℝ ↦ c - t * d) (-d) t := by
      simpa using ((hasDerivAt_id t).mul_const d).const_sub c
    have h2 := ((hasDerivAt_truncPow_succ n hne).comp t h1).neg.div_const ((n + 1) * d)
    exact h2.congr_deriv (by field_simp)
  have hcont : Continuous F :=
    ((continuous_truncPow_succ n).comp (by fun_prop)).neg.div_const _
  rw [integral_eq_of_hasDerivAt_off_countable_of_le F (fun t ↦ truncPow n (c - t * d))
    zero_le_one (countable_singleton (c / d)) hcont.continuousOn hderiv
    (intervalIntegrable_truncPow_sub_mul n c d)]
  simp only [hF]
  ring_nf

/-! ### The induction on the dimension -/

/-- The right-hand side of the distribution function, with the Heaviside convention in
degree `0`. -/
private noncomputable def cdfSum (n : ℕ) (w : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  (-1) ^ n * ∑ j, truncPow n (x - w j) / ∏ m ∈ univ.erase j, (w j - w m)

/-- The event `∑ⱼ wⱼ θⱼ ≤ x` in the first `n` coordinates of the open simplex. -/
private def weightedSumEvent {n : ℕ} (w : Fin (n + 1) → ℝ) (x : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} ∩ {y | ∑ j, w j * simplexCompletion y j ≤ x}

private lemma measurableSet_weightedSumEvent {n : ℕ} (w : Fin (n + 1) → ℝ) (x : ℝ) :
    MeasurableSet (weightedSumEvent w x) := by
  refine (measurableSet_cornerSimplex n).inter (measurableSet_le ?_ measurable_const)
  exact Finset.measurable_sum _ fun j _ ↦
    measurable_const.mul ((measurable_pi_apply j).comp (measurable_simplexCompletion n))

private lemma simplexCompletion_cons_smul {n : ℕ} (t : ℝ) (u : Fin n → ℝ) :
    simplexCompletion (Fin.cons t ((1 - t) • u) : Fin (n + 1) → ℝ) =
      Fin.cons t ((1 - t) • simplexCompletion u) := by
  ext i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simp only [simplexCompletion, Fin.snoc_last]
    rw [← Fin.succ_last, Fin.cons_succ]
    simp only [Pi.smul_apply, smul_eq_mul, Fin.snoc_last, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, ← Finset.mul_sum]
    ring
  · simp only [simplexCompletion, Fin.snoc_castSucc]
    refine Fin.cases ?_ (fun l ↦ ?_) k
    · simp
    · rw [← Fin.succ_castSucc]
      simp [Fin.snoc_castSucc]

private lemma weightedSum_cons_smul {n : ℕ} (w : Fin (n + 2) → ℝ) (t : ℝ) (u : Fin n → ℝ) :
    ∑ j, w j * simplexCompletion (Fin.cons t ((1 - t) • u) : Fin (n + 1) → ℝ) j =
      t * w 0 + (1 - t) * ∑ j, w j.succ * simplexCompletion u j := by
  rw [simplexCompletion_cons_smul, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ ↦ by ring

private lemma mem_weightedSumEvent_cons_smul {n : ℕ} (w : Fin (n + 2) → ℝ) (x : ℝ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (u : Fin n → ℝ) :
    (Fin.cons t ((1 - t) • u) : Fin (n + 1) → ℝ) ∈ weightedSumEvent w x ↔
      u ∈ weightedSumEvent (fun j ↦ w j.succ) ((x - t * w 0) / (1 - t)) := by
  set c := 1 - t with hc_def
  have hc : 0 < c := sub_pos.mpr ht1
  have hcond : ((∀ i, 0 < (Fin.cons t (c • u) : Fin (n + 1) → ℝ) i) ∧
      ∑ i, (Fin.cons t (c • u) : Fin (n + 1) → ℝ) i < 1) ↔ ((∀ j, 0 < u j) ∧ ∑ j, u j < 1) := by
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ,
      Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have hlt : t + c * ∑ j, u j < 1 ↔ ∑ j, u j < 1 := by
      constructor
      · intro h
        by_contra h'
        push Not at h'
        nlinarith
      · intro h
        nlinarith
    rw [hlt]
    exact ⟨fun ⟨⟨_, h⟩, hs⟩ ↦ ⟨fun j ↦ pos_of_mul_pos_right (h j) hc.le, hs⟩,
      fun ⟨h, hs⟩ ↦ ⟨⟨ht0, fun j ↦ mul_pos hc (h j)⟩, hs⟩⟩
  have hsum : (∑ j, w j * simplexCompletion (Fin.cons t (c • u) : Fin (n + 1) → ℝ) j ≤ x) ↔
      ∑ j, w j.succ * simplexCompletion u j ≤ (x - t * w 0) / c := by
    rw [hc_def, weightedSum_cons_smul, ← hc_def, le_div_iff₀ hc]
    constructor <;> intro h <;> linarith
  simp only [weightedSumEvent, mem_inter_iff, mem_ofPred_eq]
  rw [hcond, hsum]

private lemma not_mem_weightedSumEvent_cons {n : ℕ} (w : Fin (n + 2) → ℝ) (x : ℝ) {t : ℝ}
    (ht : t ∉ Ioo (0 : ℝ) 1) (y : Fin n → ℝ) :
    (Fin.cons t y : Fin (n + 1) → ℝ) ∉ weightedSumEvent w x := by
  rintro ⟨⟨hpos, hsum⟩, -⟩
  refine ht ⟨by simpa using hpos 0, ?_⟩
  rw [Fin.sum_univ_succ, Fin.cons_zero] at hsum
  have : 0 ≤ ∑ j, (Fin.cons t y : Fin (n + 1) → ℝ) (Fin.succ j) :=
    Finset.sum_nonneg fun j _ ↦ (hpos j.succ).le
  linarith

/-- The algebra closing the induction step: after integrating out the first coordinate, the
missing node `0` is restored by `sum_inv_prod_erase_sub_eq_zero`. -/
private lemma cdfSum_succ_eq {n : ℕ} {w : Fin (n + 2) → ℝ} (hw : Function.Injective w)
    (x : ℝ) :
    (-1) ^ n / n.factorial * ∑ j : Fin (n + 1),
      (truncPow (n + 1) (x - w j.succ) - truncPow (n + 1) (x - w j.succ - (w 0 - w j.succ))) /
        ((n + 1) * (w 0 - w j.succ)) / ∏ m ∈ univ.erase j, (w j.succ - w m.succ) =
      cdfSum (n + 1) w x / (n + 1).factorial := by
  set P : Fin (n + 2) → ℝ := fun i ↦ ∏ m ∈ univ.erase i, (w i - w m) with hP_def
  have hPne : ∀ i, P i ≠ 0 := fun i ↦
    prod_ne_zero_iff.2 fun m hm ↦ sub_ne_zero.2 (hw.ne (ne_of_mem_erase hm).symm)
  have hPsucc : ∀ j : Fin (n + 1),
      P j.succ = (w j.succ - w 0) * ∏ m ∈ univ.erase j, (w j.succ - w m.succ) := fun j ↦
    prod_erase_succ (fun m ↦ w j.succ - w m) j
  have hL : 1 / P 0 + ∑ j : Fin (n + 1), 1 / P j.succ = 0 := by
    rw [← Fin.sum_univ_succ (f := fun i ↦ 1 / P i)]
    exact sum_inv_prod_erase_sub_eq_zero hw
  set B := truncPow (n + 1) (x - w 0) with hB
  have hterm : ∀ j : Fin (n + 1),
      (truncPow (n + 1) (x - w j.succ) - truncPow (n + 1) (x - w j.succ - (w 0 - w j.succ))) /
        ((n + 1) * (w 0 - w j.succ)) / ∏ m ∈ univ.erase j, (w j.succ - w m.succ) =
      -(truncPow (n + 1) (x - w j.succ) / P j.succ) / (n + 1) + B * (1 / P j.succ) / (n + 1) := by
    intro j
    have hd : w j.succ - w 0 ≠ 0 := sub_ne_zero.2 (hw.ne (Fin.succ_ne_zero j))
    have hQ : ∏ m ∈ univ.erase j, (w j.succ - w m.succ) ≠ 0 := by
      intro h
      apply hPne j.succ
      rw [hPsucc, h, mul_zero]
    have hx : x - w j.succ - (w 0 - w j.succ) = x - w 0 := by ring
    rw [hx, hPsucc, ← hB]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hd' : w 0 - w j.succ ≠ 0 := fun h ↦ hd (by linarith)
    field_simp
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.mul_sum, cdfSum,
    Fin.sum_univ_succ (f := fun i ↦ truncPow (n + 1) (x - w i) / ∏ m ∈ univ.erase i, (w i - w m)),
    Nat.factorial_succ]
  change _ = (-1) ^ (n + 1) * (B / P 0 + ∑ j : Fin (n + 1), truncPow (n + 1) (x - w j.succ) /
    P j.succ) / ((n + 1 : ℕ) * n.factorial : ℕ)
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination (-1) ^ n * B * hL

/-- Volume of the event `∑ⱼ wⱼ θⱼ ≤ x` in simplex coordinates, for every real level `x`. -/
private lemma volume_weightedSumEvent (n : ℕ) :
    ∀ {w : Fin (n + 1) → ℝ}, Function.Injective w → ∀ x : ℝ,
      volume (weightedSumEvent w x) = ENNReal.ofReal (cdfSum n w x / n.factorial) ∧
        0 ≤ cdfSum n w x := by
  induction n with
  | zero =>
    intro w _ x
    have hs : ∀ y : Fin 0 → ℝ, simplexCompletion y 0 = 1 := fun y ↦ by
      change Fin.snoc (α := fun _ ↦ ℝ) y (1 - ∑ i, y i) (Fin.last 0) = 1
      rw [Fin.snoc_last]
      simp
    have hc : cdfSum 0 w x = if w 0 ≤ x then 1 else 0 := by
      simp only [cdfSum, truncPow, pow_zero, one_mul, sub_nonneg]
      simp
    by_cases h : w 0 ≤ x
    · have hE : weightedSumEvent w x = Set.univ := by
        ext y
        simp [weightedSumEvent, hs, h]
      rw [hE, hc, ite_eq_left h, volume_pi, Measure.pi_of_empty]
      simp
    · have hE : weightedSumEvent w x = ∅ := by
        ext y
        simp [weightedSumEvent, hs, h]
      rw [hE, hc, ite_eq_right h]
      simp
  | succ n ih =>
    intro w hw x
    set w' : Fin (n + 1) → ℝ := fun j ↦ w j.succ with hw'
    have hw'inj : Function.Injective w' := hw.comp (Fin.succ_injective _)
    set g : ℝ → ℝ := fun t ↦ (-1) ^ n / n.factorial *
      ∑ j : Fin (n + 1), truncPow n (x - w j.succ - t * (w 0 - w j.succ)) /
        ∏ m ∈ univ.erase j, (w j.succ - w m.succ) with hg
    have hg_eq : ∀ t ∈ Ioo (0 : ℝ) 1,
        (1 - t) ^ n * (cdfSum n w' ((x - t * w 0) / (1 - t)) / n.factorial) = g t := by
      intro t ht
      have hc : 0 < 1 - t := sub_pos.mpr ht.2
      have key : ∀ j : Fin (n + 1), truncPow n (x - w j.succ - t * (w 0 - w j.succ)) =
          (1 - t) ^ n * truncPow n ((x - t * w 0) / (1 - t) - w j.succ) := fun j ↦ by
        rw [← truncPow_mul n hc]
        congr 1
        field_simp
        ring
      simp only [hg, key, cdfSum, hw', mul_div_assoc]
      rw [← Finset.mul_sum]
      ring
    have hg_nonneg : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ g t := fun t ht ↦ by
      rw [← hg_eq t ht]
      exact mul_nonneg (pow_nonneg (sub_pos.mpr ht.2).le _)
        (div_nonneg (ih hw'inj _).2 (Nat.cast_nonneg _))
    have hmeas : ∀ t, Measurable fun y : Fin n → ℝ ↦
        (weightedSumEvent w x).indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) (Fin.cons t y) :=
      fun t ↦ (measurable_one.indicator (measurableSet_weightedSumEvent w x)).comp
        (measurable_pi_iff.mpr fun i ↦ by
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp only [Fin.cons_zero]
            exact measurable_const
          · simp only [Fin.cons_succ]
            exact measurable_pi_apply j)
    have hinner : ∀ t, ∫⁻ y, (weightedSumEvent w x).indicator
        (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) (Fin.cons t y) =
        (Ioo (0 : ℝ) 1).indicator (fun t ↦ ENNReal.ofReal (g t)) t := by
      intro t
      by_cases ht : t ∈ Ioo (0 : ℝ) 1
      · have hc : 0 < 1 - t := sub_pos.mpr ht.2
        rw [indicator_of_mem ht, lintegral_comp_smul_fin (hmeas t) hc]
        have hpt : ∀ u : Fin n → ℝ, (weightedSumEvent w x).indicator
            (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) (Fin.cons t ((1 - t) • u)) =
            (weightedSumEvent w' ((x - t * w 0) / (1 - t))).indicator 1 u := fun u ↦ by
          by_cases hu : u ∈ weightedSumEvent w' ((x - t * w 0) / (1 - t))
          · rw [indicator_of_mem hu,
              indicator_of_mem ((mem_weightedSumEvent_cons_smul w x ht.1 ht.2 u).2 hu)]
            simp only [Pi.one_apply]
          · rw [indicator_of_notMem hu, indicator_of_notMem
              (fun h ↦ hu ((mem_weightedSumEvent_cons_smul w x ht.1 ht.2 u).1 h))]
        simp_rw [hpt]
        rw [lintegral_indicator_one (measurableSet_weightedSumEvent _ _), (ih hw'inj _).1,
          ← ENNReal.ofReal_mul (pow_nonneg hc.le _), hg_eq t ht]
      · rw [indicator_of_notMem ht]
        have h0 : ∀ y : Fin n → ℝ, (weightedSumEvent w x).indicator
            (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) (Fin.cons t y) = 0 := fun y ↦
          indicator_of_notMem (not_mem_weightedSumEvent_cons w x ht y) _
        simp_rw [h0]
        exact lintegral_zero
    have hgint : IntervalIntegrable g volume 0 1 := by
      have h : IntervalIntegrable (fun t ↦ ∑ j : Fin (n + 1),
          truncPow n (x - w j.succ - t * (w 0 - w j.succ)) /
            ∏ m ∈ univ.erase j, (w j.succ - w m.succ)) volume 0 1 := by
        have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1) univ
          (f := fun (j : Fin (n + 1)) (t : ℝ) ↦ truncPow n (x - w j.succ - t * (w 0 - w j.succ)) /
            ∏ m ∈ univ.erase j, (w j.succ - w m.succ))
          fun j _ ↦ (intervalIntegrable_truncPow_sub_mul n _ _).div_const _
        rwa [Finset.sum_fn] at this
      exact h.const_mul _
    have hint : ∫ t in (0 : ℝ)..1, g t = cdfSum (n + 1) w x / (n + 1).factorial := by
      simp only [hg]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
        fun j _ ↦ (intervalIntegrable_truncPow_sub_mul n _ _).div_const _]
      simp_rw [intervalIntegral.integral_div]
      rw [← cdfSum_succ_eq hw x]
      congr 1
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [integral_truncPow_sub_mul n _ (sub_ne_zero.2 (hw.ne (Fin.succ_ne_zero j).symm))]
    have hIoo : ∫ t in (0 : ℝ)..1, g t = ∫ t in Ioo (0 : ℝ) 1, g t := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have hvol : volume (weightedSumEvent w x) = ENNReal.ofReal (∫ t in (0 : ℝ)..1, g t) := by
      rw [← lintegral_indicator_one (measurableSet_weightedSumEvent w x),
        lintegral_fin_succ (measurable_one.indicator (measurableSet_weightedSumEvent w x)),
        lintegral_congr hinner, lintegral_indicator measurableSet_Ioo, hIoo,
        ofReal_integral_eq_lintegral_ofReal]
      · exact (hgint.1.mono_set Ioo_subset_Ioc_self)
      · exact (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hg_nonneg)
    refine ⟨by rw [hvol, hint], ?_⟩
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, g t := by
      rw [hIoo]
      exact setIntegral_nonneg measurableSet_Ioo hg_nonneg
    rw [hint] at h0
    have hpos : (0 : ℝ) < (n + 1).factorial := by positivity
    have := mul_nonneg h0 hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at this

/-! ### The distribution function -/

/-- **Distribution function of a weighted sum of a flat Dirichlet vector.** If `θ ∼ Dir(1, …, 1)`
on `Fin (n + 1) → ℝ` with `n ≥ 1` and the weights `w` are pairwise distinct, then for every real
`x`,
`P(∑ⱼ wⱼ θⱼ ≤ x) = (-1)ⁿ ∑ⱼ (x - wⱼ)₊ⁿ / ∏_{m ≠ j} (wⱼ - wₘ)`.
The weights may have any signs and need not be sorted; the sum runs over all `n + 1` nodes. -/
theorem dirichletMeasure_one_real_weightedSum_le {n : ℕ} (hn : 1 ≤ n) {w : Fin (n + 1) → ℝ}
    (hw : Function.Injective w) (x : ℝ) :
    (dirichletMeasure (fun _ ↦ (1 : ℝ))).real {θ | ∑ j, w j * θ j ≤ x} =
      (-1) ^ n * ∑ j, (max (x - w j) 0) ^ n / ∏ m ∈ Finset.univ.erase j, (w j - w m) := by
  have hE : MeasurableSet {θ : Fin (n + 1) → ℝ | ∑ j, w j * θ j ≤ x} :=
    measurableSet_le (by fun_prop) measurable_const
  have hdens : ∀ y : Fin n → ℝ, dirichletDensity (fun _ ↦ (1 : ℝ)) y *
      {θ : Fin (n + 1) → ℝ | ∑ j, w j * θ j ≤ x}.indicator 1 (simplexCompletion y) =
      (weightedSumEvent w x).indicator 1 y := fun y ↦ by
    by_cases hy : (∀ i, 0 < y i) ∧ ∑ i, y i < 1
    · have hd : dirichletDensity (fun _ ↦ (1 : ℝ)) y = 1 := by
        simp [dirichletDensity, hy]
      by_cases hx : ∑ j, w j * simplexCompletion y j ≤ x
      · rw [hd, indicator_of_mem (show simplexCompletion y ∈ {θ : Fin (n + 1) → ℝ |
          ∑ j, w j * θ j ≤ x} from hx), indicator_of_mem (show y ∈ weightedSumEvent w x
          from ⟨hy, hx⟩)]
        simp
      · rw [indicator_of_notMem (show simplexCompletion y ∉ {θ : Fin (n + 1) → ℝ |
          ∑ j, w j * θ j ≤ x} from hx), indicator_of_notMem (show y ∉ weightedSumEvent w x
          from fun h ↦ hx h.2), mul_zero]
    · have hd : dirichletDensity (fun _ ↦ (1 : ℝ)) y = 0 := by
        simp [dirichletDensity, hy]
      rw [hd, zero_mul, indicator_of_notMem (show y ∉ weightedSumEvent w x from fun h ↦ hy h.1)]
  have hB : multiBeta (fun _ : Fin (n + 1) ↦ (1 : ℝ)) = 1 / n.factorial := by
    rw [multiBeta]
    simp only [Gamma_one, prod_const_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring, Gamma_nat_eq_factorial]
  obtain ⟨hvol, hnn⟩ := volume_weightedSumEvent n hw x
  have hf : (0 : ℝ) < n.factorial := by positivity
  rw [measureReal_def, ← lintegral_indicator_one hE,
    lintegral_dirichletMeasure _ (measurable_one.indicator hE), lintegral_congr hdens,
    lintegral_indicator_one (measurableSet_weightedSumEvent w x), hvol, hB,
    ENNReal.toReal_div, ENNReal.toReal_ofReal (div_nonneg hnn hf.le),
    ENNReal.toReal_ofReal (by positivity), cdfSum]
  simp_rw [truncPow_eq_max_pow (by omega : n ≠ 0)]
  field_simp

end ProbabilityTheory
