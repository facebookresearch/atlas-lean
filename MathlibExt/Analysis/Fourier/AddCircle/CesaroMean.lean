/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.AddCircle.FejerKernel
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Cesàro–Fourier means as convolutions with the Fejér kernel

For a period `T > 0`, the `N`-th partial Fourier sum of `f : AddCircle T → ℂ` is
`S_N f(x) = ∑_{n = -N}^{N} ĉ_n(f) · fourier n x`, and the `N`-th Cesàro–Fourier mean is
`σ_N f(x) = (N+1)⁻¹ • ∑_{k=0}^{N} S_k f(x)`.

The main result is `AddCircle.cesaroMean_eq_fejer_convolution`:
`σ_N f(x) = ∫_{AddCircle T} K_N(t) • f (x - t) dt`, the bridge from the abstract
definition of `σ_N f` to the kernel-theoretic analysis underlying Fejér's theorem.
Also proved: since `K_N ≥ 0` and `∫ K_N = 1`, its `L¹` norm is `1`
(`AddCircle.integral_norm_fejerKernel`).

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(targets: Definition of the `N`-th Cesàro–Fourier mean, April 13, 2021;
Proposition on the Fejér kernel, April 15, 2021). The v1 file used the namespace
`FourierSeries`; here the definitions live in Mathlib's `AddCircle` namespace.
-/

@[expose] public section

variable {T : ℝ} [hT : Fact (0 < T)]

open MeasureTheory AddCircle Finset Filter Complex

namespace AddCircle

/-- **Partial Fourier sums.** Let $T > 0$ and $f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$. For
$N \in \mathbb{N}$, the $N$-th partial Fourier sum of $f$ is the function
$$S_N f(x) = \sum_{n=-N}^{N} \hat f(n)\, e_n(x),$$
where $e_n(x) = e^{2\pi i n x / T}$ is the $n$-th Fourier character and
$\hat f(n) = \int_{\mathbb{R}/T\mathbb{Z}} e_{-n}(t)\, f(t)\, dt$ is the $n$-th Fourier coefficient,
the integral taken against the Haar probability measure on the circle. -/
noncomputable def partialFourierSum (f : AddCircle T → ℂ) (N : ℕ) :
    AddCircle T → ℂ :=
  fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n • fourier n x

/-- **Cesàro–Fourier means.** Let $T > 0$ and $f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$. For
$N \in \mathbb{N}$, the $N$-th Cesàro–Fourier mean of $f$ is the average of its first $N + 1$
partial Fourier sums,
$$\sigma_N f(x) = \frac{1}{N+1} \sum_{k=0}^{N} S_k f(x),$$
where $S_k f$ is the $k$-th partial Fourier sum of $f$. -/
noncomputable def cesaroFourierMean (f : AddCircle T → ℂ) (N : ℕ) :
    AddCircle T → ℂ :=
  fun x => ((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1), partialFourierSum f k x

set_option linter.unusedSectionVars false in
/-- **Fourier characters at a difference.** Let $T > 0$ and for $n \in \mathbb{Z}$ let
$e_n(x) = e^{2\pi i n x / T}$ be the $n$-th Fourier character on $\mathbb{R}/T\mathbb{Z}$. Then
for every $n \in \mathbb{Z}$ and all $x, t \in \mathbb{R}/T\mathbb{Z}$,
$e_n(x - t) = e_{-n}(t)\, e_n(x)$. -/
lemma fourier_sub_eq (n : ℤ) (x t : AddCircle T) :
    (fourier n (x - t) : ℂ) = (fourier (-n) t : ℂ) * (fourier n x : ℂ) :=
  (fourier_neg_mul_fourier_eq n x t).symm

/-- **Integrability of a function twisted by a Fourier character.** Let $T > 0$ and let
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ be integrable with respect to the Haar probability
measure on the circle. Then for every $n \in \mathbb{Z}$ and every $x \in \mathbb{R}/T\mathbb{Z}$,
the function $t \mapsto e^{2\pi i n t / T} f(x - t)$ is integrable with respect to the same
measure.

This is used to interchange sums and integrals in the convolution computation. -/
lemma fourier_smul_integrable (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (n : ℤ) (x : AddCircle T) :
    Integrable (fun t => (fourier n t : ℂ) • f (x - t)) haarAddCircle := by
  simp only [smul_eq_mul]
  exact (hf.comp_sub_left x).bdd_mul (map_continuous (fourier n)).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [fourier_apply, Circle.norm_coe])

/-- **Convolution of a function with a Fourier character.** Let $T > 0$, let
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ be integrable with respect to the Haar probability
measure $dt$ on the circle, for $n \in \mathbb{Z}$ let $e_n(x) = e^{2\pi i n x / T}$ be the
$n$-th Fourier character, and let $\hat f(n) = \int_{\mathbb{R}/T\mathbb{Z}} e_{-n}(t)\, f(t)\, dt$
be the $n$-th Fourier coefficient of $f$. Then for every $n \in \mathbb{Z}$ and every
$x \in \mathbb{R}/T\mathbb{Z}$,
$$\int_{\mathbb{R}/T\mathbb{Z}} e_n(t)\, f(x - t)\, dt = \hat f(n)\, e_n(x).$$

Thus the $n$-th term of the partial Fourier sum of $f$ at $x$ is the convolution of $f$ with
the Fourier character $e_n$. -/
theorem fourier_integral_convolution (f : AddCircle T → ℂ)
    (_hf : Integrable f haarAddCircle) (n : ℤ) (x : AddCircle T) :
    ∫ t : AddCircle T, (fourier n t : ℂ) • f (x - t) ∂haarAddCircle =
    fourierCoeff f n • (fourier n x : ℂ) := by
  have h1 : ∫ t : AddCircle T, (fourier n t : ℂ) • f (x - t) ∂haarAddCircle =
      ∫ t : AddCircle T, (fourier n (x - t) : ℂ) • f t ∂haarAddCircle := by
    have key : (fun t => (fourier n t : ℂ) • f (x - t)) =
        (fun t => (fourier n (x - t) : ℂ) • f t) ∘ (x - ·) := by
      ext t; simp only [Function.comp, sub_sub_cancel]
    rw [key]
    exact integral_sub_left_eq_self (fun s => (fourier n (x - s) : ℂ) • f s) haarAddCircle x
  rw [h1]
  simp_rw [fourier_sub_eq n x, smul_eq_mul, mul_assoc]
  simp_rw [show ∀ t, (fourier (-n) t : ℂ) * ((fourier n x : ℂ) * f t) =
    ((fourier (-n) t : ℂ) * f t) * (fourier n x : ℂ) from fun t => by ring]
  rw [show (fun t => ((fourier (-n) t : ℂ) * f t) * (fourier n x : ℂ)) =
    (fun t => ((fourier (-n) t : ℂ) * f t) • (fourier n x : ℂ)) from by
    ext t; simp [smul_eq_mul]]
  rw [integral_smul_const]
  rfl

/-- **Cesàro–Fourier means are convolutions with the Fejér kernel.** Let $T > 0$ and let
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ be integrable with respect to the Haar probability
measure $dt$ on the circle. Then for every $N \in \mathbb{N}$ and every
$x \in \mathbb{R}/T\mathbb{Z}$, the $N$-th Cesàro–Fourier mean of $f$ satisfies
$$\sigma_N f(x) = \int_{\mathbb{R}/T\mathbb{Z}} K_N(t)\, f(x - t)\, dt,$$
where $K_N$ is the $N$-th Fejér kernel.

This is the bridge from the definition of $\sigma_N f$ to the kernel-theoretic analysis
underlying Fejér's theorem. -/
theorem cesaroMean_eq_fejer_convolution (f : AddCircle T → ℂ)
    (hf : Integrable f haarAddCircle) (N : ℕ) (x : AddCircle T) :
    cesaroFourierMean f N x =
    ∫ t : AddCircle T, fejerKernel N t • f (x - t) ∂haarAddCircle := by
  unfold cesaroFourierMean fejerKernel
  rw [show (fun t => (((N : ℂ) + 1)⁻¹ • ∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n t : ℂ)) • f (x - t)) =
    (fun t => ((N : ℂ) + 1)⁻¹ • ((∑ k ∈ range (N + 1),
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n t : ℂ)) • f (x - t))) from by
    ext t; rw [smul_assoc]]
  rw [integral_smul]
  congr 1
  have h_rw : (fun t => (∑ k ∈ range (N + 1), ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (fourier n t : ℂ)) • f (x - t)) = (fun t => ∑ k ∈ range (N + 1),
      (∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), (fourier n t : ℂ)) • f (x - t)) := by
    ext t; exact Finset.sum_smul
  rw [h_rw]
  have h_int_outer : ∀ k, k ∈ range (N + 1) →
      Integrable (fun t => (∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
        (fourier n t : ℂ)) • f (x - t)) haarAddCircle := by
    intro k _
    simp_rw [smul_eq_mul, Finset.sum_mul]
    apply integrable_finsetSum
    intro n _
    have := fourier_smul_integrable f hf n x
    simp only [smul_eq_mul] at this
    exact this
  rw [integral_finsetSum _ h_int_outer]
  congr 1; ext k
  have h_rw2 : (fun t => (∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (fourier n t : ℂ)) • f (x - t)) = (fun t => ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
      (fourier n t : ℂ) • f (x - t)) := by
    ext t; exact Finset.sum_smul
  rw [h_rw2]
  rw [integral_finsetSum _ (fun n _ => fourier_smul_integrable f hf n x)]
  unfold partialFourierSum
  congr 1; ext n
  exact (fourier_integral_convolution f hf n x).symm

/-- **The Fejér kernel has $L^1$ norm one.** Let $T > 0$. For every $N \in \mathbb{N}$, the
$N$-th Fejér kernel $K_N$ on $\mathbb{R}/T\mathbb{Z}$ satisfies
$$\int_{\mathbb{R}/T\mathbb{Z}} |K_N(t)|\, dt = 1,$$
where $dt$ is the Haar probability measure on the circle.

Since $K_N \ge 0$, this is the normalization $\int K_N = 1$; it is used to control
convolutions with $K_N$ in the proof of Fejér's theorem. -/
theorem integral_norm_fejerKernel (N : ℕ) :
    ∫ t : AddCircle T, ‖fejerKernel N t‖ ∂haarAddCircle = 1 := by
  have h_eq : ∀ t : AddCircle T, ‖fejerKernel N t‖ = (fejerKernel N t).re := by
    intro t
    rw [fejerKernel_eq_ofReal]
    simp only [Complex.ofReal_re, Complex.norm_real]
    exact abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1))
      (normSq_nonneg _))
  simp_rw [h_eq]
  have h_re : (fun t : AddCircle T => (fejerKernel N t).re) =
      fun t => RCLike.re (fejerKernel N t) := rfl
  rw [h_re, integral_re (fejerKernel_integrable N)]
  have h1 := integral_fejerKernel (T := T) N
  exact_mod_cast congrArg Complex.re h1

end AddCircle
