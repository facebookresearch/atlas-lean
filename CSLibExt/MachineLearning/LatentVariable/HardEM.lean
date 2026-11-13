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

/-- **Responsibilities with a common variance.** Given weights $w_1, \dots, w_K \in \mathbb{R}$,
means $\mu_1, \dots, \mu_K \in \mathbb{R}^d$ and a real $v$, the common-variance responsibility
of component $k$ at a point $x \in \mathbb{R}^d$ is
$$
r_v(x, k) = \frac{w_k \, \mathcal{N}(x \mid \mu_k, vI)}
{\sum_i w_i \, \mathcal{N}(x \mid \mu_i, vI)},
$$
where, for $v > 0$, $\mathcal{N}(x \mid \mu, vI)$ is the isotropic Gaussian density with mean
$\mu$ and covariance $vI$, and for $v \le 0$ it is $1$ if $d = 0$ and $0$ if $d \ge 1$. A quotient
with denominator $0$ is $0$. -/
noncomputable def softAssign (w : Fin K → ℝ) (μ : Fin K → EuclideanSpace ℝ (Fin d)) (v : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) : ℝ :=
  w k * isoGaussPDF (μ k) v.toNNReal x / ∑ i, w i * isoGaussPDF (μ i) v.toNNReal x

/-- **The Gaussian-mixture responsibilities are the common-variance responsibilities.** Let
$\theta$ be valid parameters of an isotropic Gaussian mixture with $K$ components on
$\mathbb{R}^d$, with weights $w_k$, means $\mu_k$ and variances all equal to a real number $v$.
Then for every point $x \in \mathbb{R}^d$ and every component $k$, the responsibility of $k$ at
$x$ under $\theta$ equals the common-variance responsibility $r_v(x, k)$ for the weights $w$ and
means $\mu$. -/
theorem resp_eq_softAssign (θ : ValidParams d K) {v : ℝ} (hv : ∀ k, (θ.1.var k : ℝ) = v)
    (x : EuclideanSpace ℝ (Fin d)) (k : Fin K) :
    resp θ x k = softAssign θ.1.weight θ.1.mean v x k := by
  have hv' : ∀ k, θ.1.var k = v.toNNReal := fun k => by
    rw [← hv k, Real.toNNReal_coe]
  simp only [resp, posterior, marginal, joint, softAssign, hv']

/-- **Ratio of isotropic Gaussian densities with a common variance.** For all points
$\mu, \nu, x \in \mathbb{R}^d$ and every real $v > 0$, writing $\mathcal{N}(x \mid \mu, vI)$ for
the isotropic Gaussian density with mean $\mu$ and covariance $vI$,
$$
\frac{\mathcal{N}(x \mid \mu, vI)}{\mathcal{N}(x \mid \nu, vI)}
= \exp\left(\frac{\|x - \nu\|^2 - \|x - \mu\|^2}{2v}\right).
$$
-/
theorem isoGaussPDF_div (μ ν x : EuclideanSpace ℝ (Fin d)) {v : ℝ} (hv : 0 < v) :
    isoGaussPDF μ v.toNNReal x / isoGaussPDF ν v.toNNReal x =
      exp ((‖x - ν‖ ^ 2 - ‖x - μ‖ ^ 2) / (2 * v)) := by
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  rw [← exp_log (isoGaussPDF_pos μ hv0 x), ← exp_log (isoGaussPDF_pos ν hv0 x), ← exp_sub,
    log_isoGaussPDF _ hv0, log_isoGaussPDF _ hv0, Real.coe_toNNReal _ hv.le]
  congr 1
  field_simp
  ring

/-- **Exponential decay as the variance tends to zero.** For every real $c < 0$,
$\exp(c / (2v)) \to 0$ as $v \to 0^+$. -/
theorem tendsto_exp_div_nhdsGT_zero {c : ℝ} (hc : c < 0) :
    Tendsto (fun v : ℝ => exp (c / (2 * v))) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun v : ℝ => c / 2 * v⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by linarith)
  refine tendsto_exp_atBot.comp (h.congr fun v => ?_)
  ring

/-- **Common-variance responsibilities relative to a fixed component.** For weights
$w_1, \dots, w_K \in \mathbb{R}$, means $\mu_1, \dots, \mu_K \in \mathbb{R}^d$, a real $v > 0$,
a point $x \in \mathbb{R}^d$ and components $j$ and $k$, the common-variance responsibility
$r_v(x, k)$ of component $k$ at $x$ for these weights and means satisfies
$$
r_v(x, k) = \frac{w_k \exp\bigl((\|x - \mu_j\|^2 - \|x - \mu_k\|^2) / (2v)\bigr)}
{\sum_i w_i \exp\bigl((\|x - \mu_j\|^2 - \|x - \mu_i\|^2) / (2v)\bigr)}.
$$
-/
theorem softAssign_eq (w : Fin K → ℝ) (μ : Fin K → EuclideanSpace ℝ (Fin d)) {v : ℝ} (hv : 0 < v)
    (x : EuclideanSpace ℝ (Fin d)) (j k : Fin K) :
    softAssign w μ v x k = w k * exp ((‖x - μ j‖ ^ 2 - ‖x - μ k‖ ^ 2) / (2 * v)) /
      ∑ i, w i * exp ((‖x - μ j‖ ^ 2 - ‖x - μ i‖ ^ 2) / (2 * v)) := by
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  have hN := isoGaussPDF_pos (μ j) hv0 x
  simp only [← isoGaussPDF_div _ _ x hv, softAssign, ← mul_div_assoc, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hN.ne']

/-- **Responsibilities in the zero-variance limit.** Let $w_1, \dots, w_K$ be positive weights,
$\mu_1, \dots, \mu_K \in \mathbb{R}^d$ means and $x \in \mathbb{R}^d$ a point, and suppose that
$\mu_j$ is the unique nearest mean to $x$: $\|x - \mu_j\| < \|x - \mu_k\|$ for every $k \ne j$.
Then for every component $k$, the common-variance responsibility $r_v(x, k)$ of $k$ at $x$ for
these weights and means tends to $1$ if $k = j$ and to $0$ otherwise as $v \to 0^+$.

Source: Bishop, *Pattern Recognition and Machine Learning*, Section 9.3.2. -/
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

/-- **The k-means assignment step is the zero-variance limit of the E-step.** Let
$x_1, \dots, x_N$ be points of $\mathbb{R}^d$, let $\mu_1, \dots, \mu_K \in \mathbb{R}^d$ be means
with positive weights $w_1, \dots, w_K$, and let $a$ assign to each $n$ a component $a(n)$ such
that $\|x_n - \mu_{a(n)}\| < \|x_n - \mu_k\|$ for every $k \ne a(n)$. Then $a$ is a nearest-center
assignment, that is, $\|x_n - \mu_{a(n)}\| \le \|x_n - \mu_k\|$ for all $n$ and $k$, and for all
$n$ and $k$ the common-variance responsibility $r_v(x_n, k)$ of component $k$ at $x_n$ for these
weights and means tends to $1$ if $k = a(n)$ and to $0$ otherwise as $v \to 0^+$. -/
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

/-- **Common-variance M-step mean.** Given weights $w_1, \dots, w_K \in \mathbb{R}$, means
$\mu_1, \dots, \mu_K \in \mathbb{R}^d$, a real $v$ and data $x_1, \dots, x_N \in \mathbb{R}^d$,
the common-variance M-step mean of component $k$ is
$$
\Bigl(\sum_n r_v(x_n, k)\Bigr)^{-1} \sum_n r_v(x_n, k) \, x_n,
$$
where $r_v(x, k)$ is the common-variance responsibility of component $k$ at $x$ for these
weights and means, and $0^{-1} = 0$. -/
noncomputable def softMean {N : ℕ} (w : Fin K → ℝ) (μ : Fin K → EuclideanSpace ℝ (Fin d)) (v : ℝ)
    (xs : Fin N → EuclideanSpace ℝ (Fin d)) (k : Fin K) : EuclideanSpace ℝ (Fin d) :=
  (∑ n, softAssign w μ v (xs n) k)⁻¹ • ∑ n, softAssign w μ v (xs n) k • xs n

/-- **The Gaussian-mixture M-step mean is the common-variance M-step mean.** Let $\theta$ be valid
parameters of an isotropic Gaussian mixture with $K$ components on $\mathbb{R}^d$, with weights
$w_k$, means $\mu_k$ and variances all equal to a real number $v$. Then for data
$x_1, \dots, x_N \in \mathbb{R}^d$ and every component $k$, the M-step mean of component $k$ under
$\theta$ equals the common-variance M-step mean of component $k$ for the weights $w$, means $\mu$,
variance $v$ and data $x_1, \dots, x_N$. -/
theorem newMean_eq_softMean {N : ℕ} (xs : Fin N → EuclideanSpace ℝ (Fin d)) (θ : ValidParams d K)
    {v : ℝ} (hv : ∀ k, (θ.1.var k : ℝ) = v) (k : Fin K) :
    newMean xs θ k = softMean θ.1.weight θ.1.mean v xs k := by
  simp only [newMean, mass, softMean, resp_eq_softAssign θ hv]

/-- **The M-step in the zero-variance limit.** Let $x_1, \dots, x_N \in \mathbb{R}^d$ be data, let
$\mu_1, \dots, \mu_K \in \mathbb{R}^d$ be means with positive weights $w_1, \dots, w_K$, and let
$a$ assign to each $n$ a component $a(n)$ with $\|x_n - \mu_{a(n)}\| < \|x_n - \mu_k\|$ for
every $k \ne a(n)$. Then for every component $k$ such that $a(n) = k$ for some $n$, the
common-variance M-step mean of component $k$ for these weights, means and data tends, as
$v \to 0^+$, to the k-means centroid of cluster $k$ under $a$, the mean of the points $x_n$ with
$a(n) = k$. -/
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
