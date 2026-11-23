/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

open scoped FourierTransform
open MeasureTheory

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Fourier transform of a dilation.** Let $E$ be a complex normed space, and write
$\hat g(y) = \int_{\mathbb{R}} e^{-2\pi i x y} g(x)\,dx$ for the Fourier transform of a
function $g : \mathbb{R} \to E$. For every $f : \mathbb{R} \to E$, every real $a \ne 0$ and
every real $y$, the Fourier transform of $x \mapsto f(ax)$ at $y$ equals $|a|^{-1} \hat f(y/a)$.

No integrability hypothesis is needed because Mathlib's Bochner integral is
totalized, so the identity also uses that convention for nonintegrable
functions. -/
theorem fourier_comp_mul_left (f : ℝ → E) {a : ℝ} (ha : a ≠ 0) (y : ℝ) :
    𝓕 (fun x => f (a * x)) y = (|a|⁻¹ : ℝ) • 𝓕 f (y / a) := by
  simp only [Real.fourier_real_eq]
  let g : ℝ → E := fun v => (𝐞 (-(v * (y / a)))) • f v
  have hg : ∀ v, g (a * v) = (𝐞 (-(v * y))) • f (a * v) := by
    intro v
    simp only [g]
    congr 1
    congr 1
    field_simp
  simp_rw [← hg]
  rw [Measure.integral_comp_mul_left g a, abs_inv]

/-- **Fourier transform of a dilation by a positive factor.** Write
$\hat g(y) = \int_{\mathbb{R}} e^{-2\pi i x y} g(x)\,dx$ for the Fourier transform of a
function $g : \mathbb{R} \to \mathbb{C}$. For every $f : \mathbb{R} \to \mathbb{C}$, every real
$a > 0$ and every real $y$, the Fourier transform of $x \mapsto f(ax)$ at $y$ equals
$a^{-1} \hat f(y/a)$.

No integrability hypothesis is needed because Mathlib's Bochner integral is
totalized, so the identity also uses that convention for nonintegrable
functions. -/
theorem fourier_comp_mul_left_of_pos (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    𝓕 (fun x => f (a * x)) y = ((a : ℂ)⁻¹) • 𝓕 f (y / a) := by
  rw [fourier_comp_mul_left f (ne_of_gt ha) y, abs_of_pos ha]
  change (a⁻¹ : ℝ) • 𝓕 f (y / a) = ((a : ℂ)⁻¹) • 𝓕 f (y / a)
  simp only [Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]

end Real

namespace SchwartzMap

/-- **Fourier transform of a dilated Schwartz function.** Write
$\hat g(y) = \int_{\mathbb{R}} e^{-2\pi i x y} g(x)\,dx$ for the Fourier transform of a
function $g : \mathbb{R} \to \mathbb{C}$. For every Schwartz function
$f : \mathbb{R} \to \mathbb{C}$, every real $a > 0$ and every real $y$, the Fourier transform of
$x \mapsto f(ax)$ at $y$ equals $a^{-1} \hat f(y/a)$. -/
theorem fourier_coe_comp_mul_left_of_pos (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : 0 < a)
    (y : ℝ) :
    𝓕 (fun x => (f : ℝ → ℂ) (a * x)) y
      = ((a : ℂ)⁻¹) • 𝓕 (f : ℝ → ℂ) (y / a) :=
  Real.fourier_comp_mul_left_of_pos (f : ℝ → ℂ) ha y

end SchwartzMap
