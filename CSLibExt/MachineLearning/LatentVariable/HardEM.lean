/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.LatentVariable.GaussianMixture
public import CSLibExt.MachineLearning.KMeans
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Order.Field

/-!
# k-means is the zero-variance limit of Gaussian-mixture EM

Bishop, *Pattern Recognition and Machine Learning*, Section 9.3.2: for a Gaussian mixture whose
components share the isotropic variance `v`, the E-step responsibilities tend, as `v → 0`, to the
hard assignment of each point to its nearest mean, the assignment step of k-means
(`MachineLearning/KMeans.lean`). The M-step means then tend to the cluster centroids, the update
step of k-means. In this sense k-means is "hard EM".

Main results:

* `softAssign`: the responsibilities with a common variance; `resp_eq_softAssign`: they are the
  Gaussian-mixture responsibilities (`LatentVariable/GaussianMixture.lean`).
* `isoGaussPDF_div`, `softAssign_eq`: dividing by the density of a fixed component leaves
  `exp ((‖x - μ j‖² - ‖x - μ i‖²) / (2 v))`.
* `tendsto_softAssign`: **if `μ j` is the unique nearest mean, the responsibilities tend to the
  indicator of `j` as `v → 0⁺`**.
* `nearest_and_tendsto_softAssign`: for an assignment `a` of unique nearest means, `a` is a
  `KMeans.Nearest` assignment and the responsibilities tend to it.
* `softMean`, `newMean_eq_softMean`, `tendsto_softMean`: **the M-step mean of a nonempty cluster
  tends to its k-means centroid** `KMeans.centers xs a k`.

Ties between nearest means are excluded by hypothesis; the tied case is not treated.

## Cost model

None: a limit statement over the reals.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.HardEM

open Real Filter Topology
open Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.MachineLearning.LatentVariable.GaussianMixture

variable {d K : ℕ}

/-- The responsibilities of a mixture whose components share the variance `v`:
`w k N(x | μ k, v I) / ∑ i, w i N(x | μ i, v I)`. -/
noncomputable def softAssign (w : Fin K → ℝ) (μ : Fin K → EuclideanSpace ℝ (Fin d)) (v : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  w k * isoGaussPDF (μ k) v.toNNReal x / ∑ i, w i * isoGaussPDF (μ i) v.toNNReal x

/-- With a common variance, the Gaussian-mixture responsibilities are `softAssign`. -/
theorem resp_eq_softAssign (θ : ValidParams d K) {v : ℝ} (hv : ∀ k, (θ.1.var k : ℝ) = v)
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    resp θ x k = softAssign θ.1.weight θ.1.mean v x k := by
  have hv' : ∀ k, θ.1.var k = v.toNNReal := fun k => by
    rw [← hv k, Real.toNNReal_coe]
  simp only [resp, posterior, marginal, joint, softAssign, hv']

/-- Ratios of isotropic densities with a common variance: `N(x | μ, v I) / N(x | ν, v I)` is
`exp ((‖x - ν‖² - ‖x - μ‖²) / (2 v))`. -/
theorem isoGaussPDF_div (μ ν x : EuclideanSpace ℝ (Fin d)) {v : ℝ} (hv : 0 < v) :
    isoGaussPDF μ v.toNNReal x / isoGaussPDF ν v.toNNReal x =
      exp ((‖x - ν‖ ^ 2 - ‖x - μ‖ ^ 2) / (2 * v)) := by
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  rw [← exp_log (isoGaussPDF_pos μ hv0 x), ← exp_log (isoGaussPDF_pos ν hv0 x), ← exp_sub,
    log_isoGaussPDF _ hv0, log_isoGaussPDF _ hv0, Real.coe_toNNReal _ hv.le]
  congr 1
  field_simp
  ring

/-- `exp (c / (2 v)) → 0` as `v → 0⁺`, for `c < 0`. -/
theorem tendsto_exp_div_nhdsGT_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun v : ℝ => exp (c / (2 * v))) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun v : ℝ => c / 2 * v⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by linarith)
  refine tendsto_exp_atBot.comp (h.congr fun v => ?_)
  ring

/-- `softAssign` after dividing by the density of the component `j`. -/
theorem softAssign_eq (w : Fin K → ℝ) (μ : Fin K → EuclideanSpace ℝ (Fin d)) {v : ℝ} (hv : 0 < v)
    (x : EuclideanSpace ℝ (Fin d)) (j k : Fin K) :
    softAssign w μ v x k = w k * exp ((‖x - μ j‖ ^ 2 - ‖x - μ k‖ ^ 2) / (2 * v)) /
      ∑ i, w i * exp ((‖x - μ j‖ ^ 2 - ‖x - μ i‖ ^ 2) / (2 * v)) := by
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  have hN := isoGaussPDF_pos (μ j) hv0 x
  simp only [← isoGaussPDF_div _ _ x hv, softAssign, ← mul_div_assoc, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hN.ne']

/-- **The zero-variance limit**: if `μ j` is the unique nearest mean to `x`, then as the common
variance tends to `0` the responsibility of `k` tends to `1` for `k = j` and to `0` otherwise
(Bishop, Section 9.3.2). -/
theorem tendsto_softAssign {w : Fin K → ℝ} (hw : ∀ k, 0 < w k)
    (μ : Fin K → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) {j : Fin K}
    (hj : ∀ k, k ≠ j → ‖x - μ j‖ < ‖x - μ k‖) (k : Fin K) :
    Tendsto (fun v : ℝ => softAssign w μ v x k) (𝓝[>] 0) (𝓝 (if k = j then 1 else 0)) := by
  -- the scaled densities converge to the indicator of `j`
  have he : ∀ i, Tendsto (fun v : ℝ => exp ((‖x - μ j‖ ^ 2 - ‖x - μ i‖ ^ 2) / (2 * v)))
      (𝓝[>] 0) (𝓝 (if i = j then 1 else 0)) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [sub_self, zero_div, exp_zero, ↓reduceIte]
      exact tendsto_const_nhds
    · simp only [hij, ↓reduceIte]
      have := hj i hij
      exact tendsto_exp_div_nhdsGT_zero (by nlinarith [norm_nonneg (x - μ j)])
  have hnum := (he k).const_mul (w k)
  have hden : Tendsto (fun v : ℝ => ∑ i, w i * exp ((‖x - μ j‖ ^ 2 - ‖x - μ i‖ ^ 2) / (2 * v)))
      (𝓝[>] 0) (𝓝 (∑ i, w i * if i = j then 1 else 0)) :=
    tendsto_finsetSum _ fun i _ => (he i).const_mul (w i)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hden
  have hlim := hnum.div hden (hw j).ne'
  refine (hlim.congr' ?_).trans ?_
  · filter_upwards [self_mem_nhdsWithin] with v hv
    rw [softAssign_eq w μ hv x j k]
    rfl
  · by_cases hkj : k = j
    · subst hkj; simp [(hw k).ne']
    · simp [hkj]

/-- **k-means is the zero-variance limit of Gaussian-mixture EM**: if every point `xs n` has a
unique nearest mean `μ (a n)`, then `a` is a nearest-center assignment of `KMeans` and, as the
common variance tends to `0`, the responsibilities tend to the hard assignment `a`. -/
theorem nearest_and_tendsto_softAssign {N : ℕ} (xs : Fin N → EuclideanSpace ℝ (Fin d))
    {w : Fin K → ℝ} (hw : ∀ k, 0 < w k) (μ : Fin K → EuclideanSpace ℝ (Fin d)) (a : Fin N → Fin K)
    (ha : ∀ n k, k ≠ a n → ‖xs n - μ (a n)‖ < ‖xs n - μ k‖) :
    KMeans.Nearest xs μ a ∧ ∀ n k, Tendsto (fun v : ℝ => softAssign w μ v (xs n) k) (𝓝[>] 0)
      (𝓝 (if k = a n then 1 else 0)) := by
  refine ⟨fun n k => ?_, fun n k => tendsto_softAssign hw μ (xs n) (ha n) k⟩
  by_cases hk : k = a n
  · rw [hk]
  · exact (ha n k hk).le

/-! ## The M-step: the means tend to the k-means centroids -/

/-- The M-step mean of component `k` with common-variance responsibilities. -/
noncomputable def softMean {N : ℕ} (w : Fin K → ℝ) (μ : Fin K → EuclideanSpace ℝ (Fin d)) (v : ℝ)
    (xs : Fin N → EuclideanSpace ℝ (Fin d)) (k : Fin K) : EuclideanSpace ℝ (Fin d) :=
  (∑ n, softAssign w μ v (xs n) k)⁻¹ • ∑ n, softAssign w μ v (xs n) k • xs n

/-- With a common variance, the Gaussian-mixture M-step mean is `softMean`. -/
theorem newMean_eq_softMean {N : ℕ} (xs : Fin N → EuclideanSpace ℝ (Fin d)) (θ : ValidParams d K)
    {v : ℝ} (hv : ∀ k, (θ.1.var k : ℝ) = v) (k : Fin K) :
    newMean xs θ k = softMean θ.1.weight θ.1.mean v xs k := by
  simp only [newMean, mass, softMean, resp_eq_softAssign θ hv]

/-- **The M-step in the zero-variance limit**: if every point has a unique nearest mean and `a`
assigns it there, the M-step mean of a nonempty cluster `k` tends to its k-means centroid
`KMeans.centers xs a k`. -/
theorem tendsto_softMean {N : ℕ} (xs : Fin N → EuclideanSpace ℝ (Fin d)) {w : Fin K → ℝ}
    (hw : ∀ k, 0 < w k) (μ : Fin K → EuclideanSpace ℝ (Fin d)) (a : Fin N → Fin K)
    (ha : ∀ n k, k ≠ a n → ‖xs n - μ (a n)‖ < ‖xs n - μ k‖) (k : Fin K) (hk : ∃ n, a n = k) :
    Tendsto (fun v : ℝ => softMean w μ v xs k) (𝓝[>] 0) (𝓝 (KMeans.centers xs a k)) := by
  have hr : ∀ n, Tendsto (fun v : ℝ => softAssign w μ v (xs n) k) (𝓝[>] 0)
      (𝓝 (if a n = k then 1 else 0)) := fun n => by
    simpa only [eq_comm] using tendsto_softAssign hw μ (xs n) (ha n) k
  have hmass : Tendsto (fun v : ℝ => ∑ n, softAssign w μ v (xs n) k) (𝓝[>] 0)
      (𝓝 ((Finset.univ.filter fun n => a n = k).card : ℝ)) := by
    rw [← Finset.sum_boole]
    exact tendsto_finsetSum _ fun n _ => hr n
  have hsum : Tendsto (fun v : ℝ => ∑ n, softAssign w μ v (xs n) k • xs n) (𝓝[>] 0)
      (𝓝 (∑ n ∈ Finset.univ.filter fun n => a n = k, xs n)) := by
    rw [Finset.sum_filter]
    refine tendsto_finsetSum _ fun n _ => ?_
    have := (hr n).smul_const (xs n)
    simpa only [ite_smul, one_smul, zero_smul] using this
  have hcard : ((Finset.univ.filter fun n => a n = k).card : ℝ) ≠ 0 := by
    obtain ⟨n, hn⟩ := hk
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨n, by simp [hn]⟩)
  exact (hmass.inv₀ hcard).smul hsum

end Cslib.MachineLearning.LatentVariable.HardEM
