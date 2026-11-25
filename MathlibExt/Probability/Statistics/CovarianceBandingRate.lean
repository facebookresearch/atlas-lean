/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.CovarianceBanding
public import MathlibExt.Probability.Statistics.PCA
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Distributions.Gaussian.Fernique
import MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation
import MathlibExt.Probability.Statistics.ANOVA.OneWay

/-!
# Operator-norm rate of the banded sample covariance (Bickel and Levina, 2008)

For `n` i.i.d. Gaussian vectors in `ℝ^p` with covariance `Σ` in the bandable class
`U(ε₀, α, C)`, banding the sample covariance at width `k_n ≍ (n⁻¹ log p)^{-1/(2(α+1))}` gives an
estimator of `Σ`, and of `Σ⁻¹` by inversion, that is consistent in operator norm at the rate
`(n⁻¹ log p)^{α/(2(α+1))}`, uniformly over the class (P. J. Bickel and E. Levina, "Regularized
estimation of large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, Theorem 1).

The deterministic half of the proof is proved in
`MathlibExt.Probability.Statistics.CovarianceBanding`; the probabilistic half is a
union bound over the `p²` entries of `Σ̂ - Σ` with Gaussian (sub-exponential) tail bounds.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped RealInnerProductSpace ENNReal Matrix.Norms.L2Operator

open MathlibExt.Probability.Statistics.CovarianceBanding

namespace MathlibExt.Probability.Statistics.CovarianceBandingWanted

-- The quadratic remainder in log(1 - 2s) controls both sides of the chi-square tail.
private lemma chiSquare_mgf_le {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : |s| ≤ 1 / 8) :
    mgf id (chiSquareMeasure d) s ≤ Real.exp (d * (s + 4 * s ^ 2)) := by
  have hu : |2 * s| ≤ 1 / 4 := by simpa [abs_mul] using (show 2 * |s| ≤ 1 / 4 by linarith)
  have h := Real.abs_log_sub_add_sum_range_le (show |2 * s| < 1 by linarith) 1
  norm_num [Finset.sum_range_succ] at h
  have hden : 0 < 1 - |2 * s| := by linarith
  have hb : |2 * s| ^ 2 / (1 - |2 * s|) ≤ 2 * (2 * s) ^ 2 := by
    rw [sq_abs, div_le_iff₀ hden]
    nlinarith [mul_nonneg (sq_nonneg (2 * s)) (show 0 ≤ 1 / 2 - |2 * s| by linarith)]
  have hl : -(2 * s + Real.log (1 - 2 * s)) ≤ 2 * (2 * s) ^ 2 :=
    (neg_le_abs _).trans (h.trans (by simpa [abs_mul] using hb))
  have hpos : 0 < 1 - 2 * s := by linarith [le_abs_self (2 * s)]
  rw [mgf_chiSquareMeasure_of_lt hd (by linarith : s < 1 / 2)]
  rw [show (1 / 2 : ℝ) / (1 / 2 - s) = (1 - 2 * s)⁻¹ by
    field_simp, Real.rpow_def_of_pos (inv_pos.mpr hpos), Real.log_inv]
  apply Real.exp_le_exp.mpr
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  nlinarith [mul_nonneg hd0 (show 0 ≤ 2 * (2 * s) ^ 2 + (2 * s + Real.log (1 - 2 * s)) by
    linarith)]

private lemma chiSquare_tail {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (chiSquareMeasure d).real {x | d * t < |x - d|} ≤
      2 * Real.exp (-(d * t ^ 2 / 16)) := by
  let μ := chiSquareMeasure d
  have : IsProbabilityMeasure μ := isProbabilityMeasure_chiSquareMeasure hd
  have bound (s a : ℝ) (hs : |s| ≤ 1 / 8) :
      Real.exp (-s * a) * mgf id μ s ≤ Real.exp (-s * a + d * (s + 4 * s ^ 2)) := by
    rw [Real.exp_add]
    gcongr
    exact chiSquare_mgf_le hd hs
  have aux (s : ℝ) (hs : s < 1 / 2) : Integrable (fun x => Real.exp (s * id x)) μ :=
    Iio_subset_integrableExpSet_chiSquareMeasure hd hs
  have up := measure_ge_le_exp_mul_mgf (d * (1 + t)) (show 0 ≤ t / 8 by positivity)
    (aux (t / 8) (by linarith))
  have lo := measure_le_le_exp_mul_mgf (d * (1 - t)) (show -(t / 8) ≤ 0 by linarith)
    (aux (-(t / 8)) (by linarith))
  have h₁ := up.trans (bound _ _ (by rw [abs_of_nonneg (by positivity)]; linarith))
  have h₂ := lo.trans (bound _ _ (by rw [abs_neg, abs_of_nonneg (by positivity)]; linarith))
  have heq₁ : -(t / 8) * (d * (1 + t)) + d * (t / 8 + 4 * (t / 8) ^ 2) =
      -(d * t ^ 2 / 16) := by ring
  have heq₂ : - -(t / 8) * (d * (1 - t)) + d * (-(t / 8) + 4 * (-(t / 8)) ^ 2) =
      -(d * t ^ 2 / 16) := by ring
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  refine (measureReal_mono (μ := μ) (s₂ := {x | d * (1 + t) ≤ id x} ∪
    {x | id x ≤ d * (1 - t)}) ?_).trans ?_
  · intro x hx
    change d * t < |x - d| at hx
    change d * (1 + t) ≤ x ∨ x ≤ d * (1 - t)
    rcases lt_abs.mp hx with h | h
    · left; linarith
    · right; linarith
  · exact (measureReal_union_le _ _).trans (by linarith [add_le_add h₁ h₂])

private lemma posDef_of_mem {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} {ε α C : ℝ}
    (hε : 0 < ε) (hS : S ∈ bandableClass ε α C) : S.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun x hx => ?_⟩
  · simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hS.1.eq
  · have hx' := dotProduct_star_self_pos_iff.mpr hx
    simp only [star_trivial] at hx' ⊢
    exact (mul_pos hε hx').trans_le (hS.2.1 x).1

private abbrev Rows (n p : ℕ) := Fin n → EuclideanSpace ℝ (Fin p)

private noncomputable def estimate {n p : ℕ} (X : Rows n p) :=
  let Y := PCA.center (Matrix.of fun i j => X i j)
  (n : ℝ)⁻¹ • (Yᵀ * Y)

-- Variance along the sum of two coordinate directions, allowing the two indices to coincide.
private def pairForm {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :=
  M i i + M i j + M j i + M j j

private lemma pair_quadratic {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    let a := Pi.single i (1 : ℝ) + Pi.single j 1
    a ⬝ᵥ M *ᵥ a = pairForm M i j := by
  simp [add_dotProduct, Matrix.mulVec_add, single_dotProduct, pairForm, add_left_comm, add_comm]

private lemma pairForm_estimate {n p : ℕ} (X : Rows n p) (i j : Fin p) :
    pairForm (estimate X) i j =
      (∑ k, ((X k i + X k j) - (∑ l, (X l i + X l j)) / n) ^ 2) / n := by
  simp only [pairForm, estimate, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply, PCA.center, PCA.colMean, Matrix.of_apply, Finset.sum_add_distrib,
    add_div]
  simp only [← mul_add, ← Finset.sum_add_distrib, div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_add_distrib]
  ring

private lemma pairForm_tail {n p : ℕ} (hn : 2 ≤ n) {ε α C : ℝ} (hε : 0 < ε)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S ∈ bandableClass ε α C) (i j : Fin p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hnt : 1 ≤ n * t) :
    (Measure.pi fun _ : Fin n => multivariateGaussian 0 S).real
      {X | 8 * ε⁻¹ * t < |pairForm (estimate X) i j - pairForm S i j|} ≤
      2 * Real.exp (-((n - 1 : ℝ) * t ^ 2 / 16)) := by
  classical
  let a : EuclideanSpace ℝ (Fin p) := EuclideanSpace.single i 1 + EuclideanSpace.single j 1
  have ha : WithLp.ofLp a = Pi.single i (1 : ℝ) + Pi.single j 1 := rfl
  have hnorm : 0 < WithLp.ofLp a ⬝ᵥ WithLp.ofLp a ∧
      WithLp.ofLp a ⬝ᵥ WithLp.ofLp a ≤ 4 := by
    rw [ha, add_dotProduct]
    by_cases hij : i = j <;> norm_num [hij]
  have hq := hS.2.1 (WithLp.ofLp a)
  rw [ha, pair_quadratic] at hq
  rw [ha] at hnorm
  let v := (pairForm S i j).toNNReal
  have hpos : 0 < pairForm S i j := (mul_pos hε hnorm.1).trans_le hq.1
  have hv : (v : ℝ) = pairForm S i j := Real.coe_toNNReal _ hpos.le
  have hvmax : pairForm S i j ≤ ε⁻¹ * 4 := hq.2.trans (by gcongr; exact hnorm.2)
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S
  have hL : μ.map (innerSL ℝ a) = gaussianReal 0 v := by
    rw [IsGaussian.map_eq_gaussianReal, ContinuousLinearMap.integral_comp_id_comm
      IsGaussian.integrable_id (innerSL ℝ a)]
    simp only [μ, integral_id_multivariateGaussian, map_zero]
    congr 1
    change Var[fun x => ⟪a, x⟫; μ].toNNReal = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian (posDef_of_mem hε hS).posSemidef, ha, pair_quadratic]
  have heval : (innerSL ℝ a : EuclideanSpace ℝ (Fin p) → ℝ) = fun x => x i + x j := by
    funext x
    simp [a, EuclideanSpace.inner_single_left]
  rw [heval] at hL
  let Y (X : Rows n p) (k : Fin n) := X k i + X k j
  have hY : HasLaw Y (Measure.pi fun _ => gaussianReal 0 v) (Measure.pi fun _ => μ) := by
    refine ⟨(by dsimp [Y]; fun_prop), ?_⟩
    exact (Measure.pi_map_pi (μ := fun _ : Fin n => μ) (f := fun _ x => x i + x j)
      (fun _ => by fun_prop)).trans (by simp only [hL])
  -- A single ANOVA group centers all n observations and costs one degree of freedom.
  have hχ := hasLaw_sumSqWithin_div (fun _ : Fin n => ())
    (fun _ => ⟨⟨0, by omega⟩, rfl⟩) (by simpa using (show 1 < n by omega))
    (v := v) (by intro h; simp [h] at hv; linarith) hY
  let d := n - 1
  have hd : 0 < d := by dsimp [d]; omega
  have hdn : (d : ℝ) = n - 1 := by dsimp [d]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have law : HasLaw (fun X => (∑ k, (Y X k - (∑ l, Y X l) / n) ^ 2) / v)
      (chiSquareMeasure d) (Measure.pi fun _ => μ) := by
    simpa [sumSqWithin, groupMean, d] using hχ
  have htail := law.measureReal_eq (p := fun x => d * t < |x - d|)
    (measurableSet_lt measurable_const (by fun_prop))
  have h := htail.le.trans (chiSquare_tail hd ht ht1)
  rw [hdn] at h
  refine (measureReal_mono (μ := Measure.pi fun _ : Fin n => μ) ?_).trans h
  intro X hx
  change 8 * ε⁻¹ * t < |pairForm (estimate X) i j - pairForm S i j| at hx
  rw [pairForm_estimate] at hx
  change (n - 1 : ℝ) * t < |(∑ k, (Y X k - (∑ l, Y X l) / n) ^ 2) / v - (n - 1)|
  set z := ∑ k, (Y X k - (∑ l, Y X l) / n) ^ 2
  change 8 * ε⁻¹ * t < |z / n - pairForm S i j| at hx
  rw [hv, lt_abs]
  rw [lt_abs] at hx
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hvt : pairForm S i j * t ≤ ε⁻¹ * 4 * t := by gcongr
  have hnvt := mul_le_mul_of_nonneg_left hvt hn'.le
  have hb := mul_le_mul_of_nonneg_left hnt hpos.le
  rcases hx with h | h
  · left
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hpos]
    have hh := (lt_div_iff₀ hn').mp (lt_sub_iff_add_lt.mp h)
    nlinarith
  · right
    rw [neg_sub, lt_sub_comm, div_lt_iff₀ hpos]
    have hh := (div_lt_iff₀ hn').mp (lt_sub_comm.mp (by simpa only [neg_sub] using h))
    nlinarith

-- Polarization recovers each entry from the three directions (i, j), (i, i), and (j, j).
private lemma entry_le_of_pairForm {n p : ℕ} (X : Rows n p) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.IsSymm) {b : ℝ} (hb : ∀ i j, |pairForm (estimate X) i j - pairForm S i j| ≤ b)
    (i j : Fin p) : |(estimate X - S) i j| ≤ b := by
  have hsymm : (estimate X).IsSymm := by
    unfold estimate Matrix.IsSymm
    simp [transpose_mul]
  have h := abs_le.mp (hb i j)
  have hi := abs_le.mp (hb i i)
  have hj := abs_le.mp (hb j j)
  simp only [pairForm, hsymm.apply i j, hS.apply i j] at h hi hj
  rw [Matrix.sub_apply, abs_le]
  constructor <;> linarith

private lemma band_error {p : ℕ} {A S : Matrix (Fin p) (Fin p) ℝ} {ε α C x D : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C) (hS : S ∈ bandableClass ε α C)
    (hx : 0 < x) (hx1 : x ≤ 1) (hD : 0 ≤ D) (he : ∀ i j, |(A - S) i j| ≤ D * √x) :
    ‖band ⌈x ^ (-1 / (2 * (α + 1)))⌉₊ A - S‖ ≤ (5 * D + C) * x ^ (α / (2 * (α + 1))) := by
  let w := x ^ (-1 / (2 * (α + 1)))
  let k := ⌈w⌉₊
  have hw : 1 ≤ w := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  have hk : w ≤ (k : ℝ) := Nat.le_ceil w
  have hk' : (k : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
  have hk0 : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
  have hα1 : α + 1 ≠ 0 := by positivity
  have hbal : w * √x = x ^ (α / (2 * (α + 1))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    congr 1
    field_simp
    ring
  have hbias : w ^ (-α) = x ^ (α / (2 * (α + 1))) := by
    dsimp [w]
    rw [← Real.rpow_mul hx.le]
    congr 1
    ring
  have herr := norm_band_le k (mul_nonneg hD (Real.sqrt_nonneg x)) he
  have hb := norm_band_sub_le_of_mem_bandableClass hC hS hk0
  have heq : band k A - S = band k (A - S) + (band k S - S) := by rw [← band_sub]; abel
  change ‖band k A - S‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖band k (A - S)‖ + ‖band k S - S‖ := norm_add_le _ _
    _ ≤ (2 * k + 1) * (D * √x) + C * (k : ℝ) ^ (-α) := add_le_add herr hb
    _ ≤ (5 * w) * (D * √x) + C * w ^ (-α) := by
      apply add_le_add (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) hk (by linarith)) hC
    _ = _ := by rw [← hbal, hbias, ← hbal]; ring

private lemma norm_inv_unit_le {p : ℕ} (U : (Matrix (Fin p) (Fin p) ℝ)ˣ) {ε α C : ℝ}
    (hε : 0 < ε) (hS : U.val ∈ bandableClass ε α C) :
    ‖(↑U⁻¹ : Matrix (Fin p) (Fin p) ℝ)‖ ≤ ε⁻¹ := by
  let Φ := toEuclideanCLM (n := Fin p) (𝕜 := ℝ)
  change ‖Φ (↑U⁻¹)‖ ≤ ε⁻¹
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hε.le)
  intro y
  let x := Φ (↑U⁻¹) y
  have heq : Φ (↑U) x = y := by
    change (Φ (↑U) * Φ (↑U⁻¹)) y = y
    rw [← map_mul, Units.mul_inv, map_one]
    rfl
  have hxx : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      real_inner_self_eq_norm_sq x
  have h := (hS.2.1 x.ofLp).1
  rw [hxx, ← inner_toEuclideanCLM] at h
  change ε * ‖x‖ ^ 2 ≤ ⟪x, Φ (↑U) x⟫ at h
  rw [heq] at h
  have hh := h.trans (real_inner_le_norm x y)
  change ‖x‖ ≤ ε⁻¹ * ‖y‖
  rw [← div_eq_inv_mul, le_div_iff₀ hε]
  rcases (norm_nonneg x).eq_or_lt with hz | hz
  · simp [← hz]
  · by_contra! hlt
    nlinarith [mul_pos hz (sub_pos.mpr hlt)]

private lemma inv_error {p : ℕ} {A S : Matrix (Fin p) (Fin p) ℝ} {ε α C : ℝ}
    (hε : 0 < ε) (hS : S ∈ bandableClass ε α C) {b : ℝ} (hb : ‖A - S‖ ≤ b)
    (hbε : b * ε⁻¹ ≤ 1 / 2) : ‖A⁻¹ - S⁻¹‖ ≤ 2 * ε⁻¹ ^ 2 * b := by
  obtain ⟨U, rfl⟩ := (posDef_of_mem hε hS).isUnit
  let E := (U : Matrix (Fin p) (Fin p) ℝ) - A
  have hE : ‖E‖ ≤ b := by simpa only [E, norm_sub_rev] using hb
  have hZ := norm_inv_unit_le U hε hS
  have hsmall : ‖E‖ * ‖(↑U⁻¹ : Matrix (Fin p) (Fin p) ℝ)‖ ≤ 1 / 2 :=
    (mul_le_mul hE hZ (norm_nonneg _) ((norm_nonneg _).trans hE)).trans hbε
  have h := MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation.norm_inverse_sub_sub_le
    U E (by linarith)
  have hid : (U : Matrix (Fin p) (Fin p) ℝ) - E = A := sub_sub_cancel _ _
  rw [hid] at h
  rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  apply h.trans
  rw [div_le_iff₀ (by linarith)]
  calc
    _ ≤ ε⁻¹ ^ 2 * b := by gcongr
    _ ≤ _ := by
      have hb0 := (norm_nonneg _).trans hE
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ε⁻¹) hb0) (sub_nonneg.mpr hsmall)]

/-- **Bickel–Levina rate for the banded sample covariance** (P. J. Bickel and E. Levina,
*Ann. Statist.* 36 (2008), Theorem 1). Let `p n ≥ 2` be dimensions with `log p_n / n → 0`, let
`ε₀, α, C > 0`, and for a sample `X₁, …, X_n` let `Σ̂ = n⁻¹ ∑_i (X_i - X̄)(X_i - X̄)ᵀ` (their
equation (1)). With `k_n = ⌈(n⁻¹ log p_n)^{-1/(2(α+1))}⌉` and
`r_n = (n⁻¹ log p_n)^{α/(2(α+1))}`, both `‖B_{k_n}(Σ̂) - Σ‖` and `‖B_{k_n}(Σ̂)⁻¹ - Σ⁻¹‖` are
`O_P(r_n)` uniformly over `Σ ∈ U(ε₀, α, C)` when `X_i` are i.i.d. `N(0, Σ)`: for every `η > 0`
there are `K` and `N` such that for all `n ≥ N` and all `Σ` in the class each of the two events
`{‖·‖ > K r_n}` has probability at most `η`. The hypothesis `log p_n / n → 0` is the regime of
the paper's abstract and of its proof (which uses tail bounds for `t ≍ (n⁻¹ log p)^{1/2}` small);
`p_n ≥ 2` keeps `log p_n > 0`. -/
theorem banded_sampleCovariance_rate (p : ℕ → ℕ) (hp : ∀ n, 2 ≤ p n)
    (hlog : Tendsto (fun n : ℕ => Real.log (p n) / n) atTop (𝓝 0))
    {ε₀ α C : ℝ} (hε₀ : 0 < ε₀) (hα : 0 < α) (hC : 0 < C) :
    ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ S ∈ bandableClass (p := p n) ε₀ α C,
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 S)
          {X | K * (Real.log (p n) / n) ^ (α / (2 * (α + 1))) <
            ‖band ⌈(Real.log (p n) / n) ^ (-1 / (2 * (α + 1)))⌉₊
                ((n : ℝ)⁻¹ • ((PCA.center (Matrix.of fun i j => X i j))ᵀ *
                  PCA.center (Matrix.of fun i j => X i j))) - S‖} ≤ ENNReal.ofReal η ∧
      (Measure.pi fun _ : Fin n => multivariateGaussian 0 S)
          {X | K * (Real.log (p n) / n) ^ (α / (2 * (α + 1))) <
            ‖(band ⌈(Real.log (p n) / n) ^ (-1 / (2 * (α + 1)))⌉₊
                ((n : ℝ)⁻¹ • ((PCA.center (Matrix.of fun i j => X i j))ᵀ *
                  PCA.center (Matrix.of fun i j => X i j))))⁻¹ - S⁻¹‖} ≤ ENNReal.ofReal η := by
  classical
  intro η hη
  -- Choose M so the union bound over p² pairs also works when p stays fixed.
  let L := max 0 (Real.log (2 / η) / Real.log 2)
  let M := √(32 * (2 + L))
  let D := 8 * ε₀⁻¹ * M
  let B := 5 * D + C
  let K := max B (2 * ε₀⁻¹ ^ 2 * B)
  let x (n : ℕ) := Real.log (p n) / n
  let t (n : ℕ) := M * √(x n)
  let r (n : ℕ) := (x n) ^ (α / (2 * (α + 1)))
  have hL : 0 ≤ L := le_max_left ..
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM₂ : M ^ 2 = 32 * (2 + L) := Real.sq_sqrt (by positivity)
  have hM : 2 ≤ M := by
    have := Real.sqrt_nonneg (32 * (2 + L))
    change 0 ≤ M at this
    nlinarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa [t, x] using hlog.sqrt.const_mul M
  have hr0 : Tendsto r atTop (𝓝 0) :=
    hlog.rpow_const_nhds_zero (by positivity)
  have hbr : Tendsto (fun n => B * r n * ε₀⁻¹) atTop (𝓝 0) := by
    simpa using (hr0.const_mul B).mul_const ε₀⁻¹
  have eventually_small : ∀ᶠ n in atTop,
      2 ≤ n ∧ x n ≤ 1 ∧ t n ≤ 1 ∧ B * r n * ε₀⁻¹ ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop 2, hlog.eventually_le_const zero_lt_one,
      ht0.eventually_le_const zero_lt_one, hbr.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)]
      with n hn hx ht hb using ⟨hn, hx, ht, hb⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_small
  refine ⟨K, N, fun n hn S hS => ?_⟩
  obtain ⟨hn2, hx1, ht1, hbε⟩ := hN n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp' : (2 : ℝ) ≤ p n := by exact_mod_cast hp n
  have hp0 : (0 : ℝ) < p n := by linarith
  have hlp : Real.log 2 ≤ Real.log (p n) := Real.log_le_log (by norm_num) hp'
  have hx : 0 < x n := div_pos (hlog₂.trans_le hlp) hn'
  have hnx : n * x n = Real.log (p n) := by dsimp [x]; field_simp
  have ht : 0 ≤ t n := by dsimp [t]; positivity
  have hnt : 1 ≤ n * t n := by
    have htwo : 1 / 2 ≤ Real.log (2 : ℝ) := by
      simpa only [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num] using
        Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    calc
      (1 : ℝ) ≤ 2 * Real.log (p n) := by linarith
      _ = n * (2 * x n) := by rw [← hnx]; ring
      _ ≤ n * t n := by dsimp [t]; gcongr; exact Real.le_sqrt_self_iff.mpr hx1
  let μ := Measure.pi fun _ : Fin n => multivariateGaussian 0 S
  let bad (ij : Fin (p n) × Fin (p n)) : Set (Rows n (p n)) :=
    {X | 8 * ε₀⁻¹ * t n < |pairForm (estimate X) ij.1 ij.2 - pairForm S ij.1 ij.2|}
  have hbad : μ.real (⋃ ij, bad ij) ≤ η := by
    have hnt₂ : n * t n ^ 2 = Real.log (p n) * (32 * (2 + L)) := by
      dsimp only [t]
      rw [mul_pow, Real.sq_sqrt hx.le, hM₂, ← hnx]
      ring
    have htail : -((n - 1 : ℝ) * t n ^ 2 / 16) ≤ -Real.log (p n) * (2 + L) := by
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      nlinarith [mul_nonneg (sub_nonneg.mpr hn2') (sq_nonneg (t n))]
    have hlogη : Real.log (2 / η) ≤ Real.log (p n) * L := by
      calc
        _ ≤ L * Real.log 2 := (div_le_iff₀ hlog₂).mp (le_max_right ..)
        _ ≤ _ := by rw [mul_comm]; gcongr
    calc
      _ ≤ ∑ ij, μ.real (bad ij) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _ : Fin (p n) × Fin (p n), 2 * Real.exp (-((n - 1 : ℝ) * t n ^ 2 / 16)) :=
        Finset.sum_le_sum fun ij _ => pairForm_tail hn2 hε₀ hS ij.1 ij.2 ht ht1 hnt
      _ = (p n : ℝ) ^ 2 * (2 * Real.exp (-((n - 1 : ℝ) * t n ^ 2 / 16))) := by
        simp [sq]
      _ ≤ (p n : ℝ) ^ 2 * (2 * Real.exp (-Real.log (p n) * (2 + L))) := by gcongr
      _ = 2 * Real.exp (-(Real.log (p n) * L)) := by
        rw [show (p n : ℝ) ^ 2 = Real.exp (Real.log (p n) + Real.log (p n)) by
          rw [Real.exp_add, Real.exp_log hp0, sq]]
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * Real.exp (-Real.log (2 / η)) := by gcongr
      _ = η := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  let k := ⌈x n ^ (-1 / (2 * (α + 1)))⌉₊
  have hgood (X : Rows n (p n)) (hX : X ∉ ⋃ ij, bad ij) :
      ‖band k (estimate X) - S‖ ≤ B * r n := by
    apply band_error hα hC.le hS hx hx1 hD
    have hpairs (i j : Fin (p n)) : |pairForm (estimate X) i j - pairForm S i j| ≤
        8 * ε₀⁻¹ * t n := le_of_not_gt fun h => hX (Set.mem_iUnion.mpr ⟨(i, j), h⟩)
    intro i j
    simpa only [D, t, mul_assoc] using entry_le_of_pairForm X hS.1 hpairs i j
  have hr : 0 ≤ r n := Real.rpow_nonneg hx.le _
  have bound (F : Rows n (p n) → ℝ)
      (hF : ∀ X, X ∉ ⋃ ij, bad ij → F X ≤ K * r n) :
      μ {X | K * r n < F X} ≤ ENNReal.ofReal η := by
    rw [← ofReal_measureReal (μ := μ) (s := {X | K * r n < F X})]
    apply ENNReal.ofReal_le_ofReal
    apply le_trans (measureReal_mono (s₂ := ⋃ ij, bad ij) ?_) hbad
    intro X hx'
    by_contra hn'
    exact (hF X hn').not_gt hx'
  constructor
  · exact bound (fun X => ‖band k (estimate X) - S‖) fun X hX =>
      (hgood X hX).trans (mul_le_mul_of_nonneg_right (le_max_left ..) hr)
  · apply bound (fun X => ‖(band k (estimate X))⁻¹ - S⁻¹‖)
    intro X hX
    exact (inv_error hε₀ hS (hgood X hX) hbε).trans (by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) hr)

end MathlibExt.Probability.Statistics.CovarianceBandingWanted
