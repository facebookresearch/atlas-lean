/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Basic

@[expose] public section

noncomputable section

namespace TorusSobolev

open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **Fourier coefficients of a Fourier monomial on the 2-torus.** For frequencies
$m, n \in \mathbb{Z}^2$, the $n$-th Fourier coefficient, taken with respect to normalized Haar
measure on $(\mathbb{R}/\mathbb{Z})^2$, of the monomial $e_m(x) = e^{2\pi i\, m \cdot x}$ is $1$ if
$n = m$ and $0$ otherwise. -/
theorem mFourierCoeff_monomial (m n : Frequency) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier m) n = if n = m then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) n m
  simpa only [MeasureTheory.ContinuousMap.inner_toLp, UnitAddTorus.mFourierCoeff,
    UnitAddTorus.mFourier_neg, smul_eq_mul, mul_comm] using h

/-- **Integrability of Fourier integrands on the 2-torus.** For every continuous function
$f : (\mathbb{R}/\mathbb{Z})^2 \to \mathbb{C}$ and every frequency $n \in \mathbb{Z}^2$, the
function $x \mapsto e^{-2\pi i\, n \cdot x} f(x)$ is integrable with respect to normalized Haar
measure. -/
theorem mFourierCoeff_integrable (f : C(UnitAddTorus (Fin 2), ℂ)) (n : Frequency) :
    Integrable (fun x ↦ UnitAddTorus.mFourier (-n) x * f x) :=
  ((UnitAddTorus.mFourier (-n)).continuous.mul f.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Additivity of Fourier coefficients on the 2-torus.** For continuous functions
$f, g : (\mathbb{R}/\mathbb{Z})^2 \to \mathbb{C}$ and every frequency $n \in \mathbb{Z}^2$, the
$n$-th Fourier coefficient $\hat h(n) = \int e^{-2\pi i\, n \cdot x} h(x)\,dx$ (normalized Haar
measure) satisfies $\widehat{f + g}(n) = \hat f(n) + \hat g(n)$. -/
theorem mFourierCoeff_add (f g : C(UnitAddTorus (Fin 2), ℂ)) (n : Frequency) :
    UnitAddTorus.mFourierCoeff (f + g) n =
      UnitAddTorus.mFourierCoeff f n + UnitAddTorus.mFourierCoeff g n := by
  simpa only [UnitAddTorus.mFourierCoeff, ContinuousMap.add_apply, smul_eq_mul, mul_add] using
    integral_add (mFourierCoeff_integrable f n) (mFourierCoeff_integrable g n)

/-- **Homogeneity of Fourier coefficients on the 2-torus.** For every $c \in \mathbb{C}$, every
continuous function $f : (\mathbb{R}/\mathbb{Z})^2 \to \mathbb{C}$ and every frequency
$n \in \mathbb{Z}^2$, the $n$-th Fourier coefficient (normalized Haar measure) satisfies
$\widehat{c f}(n) = c\, \hat f(n)$. -/
theorem mFourierCoeff_smul (c : ℂ) (f : C(UnitAddTorus (Fin 2), ℂ)) (n : Frequency) :
    UnitAddTorus.mFourierCoeff (c • f) n = c * UnitAddTorus.mFourierCoeff f n := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (UnitAddTorus.mFourier (-n) _) c]
  exact integral_const_mul _ _

/-- **Axis frequency.** For $i \in \{0, 1\}$, the axis frequency $e_i$ is the frequency in
$\mathbb{Z}^2$ whose $i$-th coordinate is $1$ and whose other coordinate is $0$. -/
def axisFrequency (i : Fin 2) : Frequency := Pi.single i 1

/-- The four lowest nonzero lattice modes, with the primary's normalization. -/
def lowestShellUnit : C(UnitAddTorus (Fin 2), ℂ) :=
  (((4 * Real.pi)⁻¹ : ℝ) : ℂ) •
    ((UnitAddTorus.mFourier (axisFrequency 0) + UnitAddTorus.mFourier (-axisFrequency 0)) +
      (UnitAddTorus.mFourier (axisFrequency 1) + UnitAddTorus.mFourier (-axisFrequency 1)))

/-- **Lowest-shell witness.** The lowest-shell witness is the continuous real function $u$ on the
torus $(\mathbb{R}/2\pi\mathbb{Z})^2$ given by
$u(x_1, x_2) = \frac{1}{4\pi}(e^{i x_1} + e^{-i x_1} + e^{i x_2} + e^{-i x_2})
= \frac{\cos x_1 + \cos x_2}{2\pi}$,
the normalized sum of the four lowest nonzero Fourier modes. -/
def lowestShellWitness : C(Torus, ℝ) where
  toFun x := (lowestShellUnit (unitRescaling x)).re
  continuous_toFun := Complex.continuous_re.comp
    (lowestShellUnit.continuous.comp unitRescaling.continuous)

/-- **The lowest-shell unit polynomial is real-valued.** For every point $y$ of the unit torus
$(\mathbb{R}/\mathbb{Z})^2$, the lowest-shell unit polynomial $P$ satisfies
$\operatorname{Im} P(y) = 0$.

Its Fourier modes come in opposite pairs $\pm k$ with equal coefficients. -/
theorem lowestShellUnit_im_zero (x : UnitAddTorus (Fin 2)) : (lowestShellUnit x).im = 0 := by
  simp [lowestShellUnit, ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul,
    UnitAddTorus.mFourier_neg, Complex.mul_im]

/-- **Unit representative of the lowest-shell witness.** The unit representative of the
lowest-shell witness is the lowest-shell polynomial
$(4\pi)^{-1}\bigl(e_{(1,0)} + e_{(-1,0)} + e_{(0,1)} + e_{(0,-1)}\bigr)$ on the unit torus
$(\mathbb{R}/\mathbb{Z})^2$, where $e_n(y) = e^{2\pi i\, n \cdot y}$ for $n \in \mathbb{Z}^2$. -/
theorem unitRepresentative_lowestShellWitness :
    unitRepresentative lowestShellWitness = lowestShellUnit := by
  ext x
  change (((lowestShellUnit (unitRescaling (unitRescaling.symm x))).re : ℝ) : ℂ) =
    lowestShellUnit x
  simp only [Homeomorph.apply_symm_apply]
  apply Complex.ext <;> simp [lowestShellUnit_im_zero]

/-- **Lowest frequency shell.** The lowest shell is the set $\{e_1, -e_1, e_2, -e_2\}$ of
frequencies in $\mathbb{Z}^2$, where $e_1 = (1, 0)$ and $e_2 = (0, 1)$; these are the four nonzero
frequencies of smallest length. -/
def lowestShell : Finset Frequency := by
  classical
  exact {axisFrequency 0, -axisFrequency 0, axisFrequency 1, -axisFrequency 1}

theorem lowestShell_card : lowestShell.card = 4 := by
  norm_num [lowestShell, axisFrequency, funext_iff, Fin.forall_fin_two]

/-- **Fourier coefficients of the lowest-shell witness.** For every frequency $k \in \mathbb{Z}^2$,
the Fourier coefficient of the lowest-shell witness at $k$ equals $1/2$ if $k$ lies in the
lowest shell, that is, $k$ is one of $(1, 0)$, $(-1, 0)$, $(0, 1)$, $(0, -1)$, and equals $0$
otherwise. -/
theorem fourierCoefficient_lowestShellWitness (k : Frequency) :
    fourierCoefficient lowestShellWitness k = if k ∈ lowestShell then (1 / 2 : ℂ) else 0 := by
  classical
  rw [fourierCoefficient, unitRepresentative_lowestShellWitness]
  unfold lowestShellUnit
  rw [mFourierCoeff_smul]
  simp only [mFourierCoeff_add, mFourierCoeff_monomial]
  have hπ : (2 * Real.pi : ℂ) * (((4 * Real.pi)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    push_cast
    field_simp
    ring
  rw [← mul_assoc, hπ]
  simp only [lowestShell, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> simp_all [axisFrequency, funext_iff, Fin.forall_fin_two]
  aesop

theorem frequencyWeight_lowestShell {k : Frequency} (hk : k ∈ lowestShell) :
    frequencyWeight k = 1 := by
  simp only [lowestShell, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    norm_num [frequencyWeight, axisFrequency, Fin.sum_univ_two]

/-- **The lowest-shell witness is in $H^2$.** The lowest-shell witness $u$ belongs to the spectral
Sobolev space $H^2$: if $a_k(u)$ denotes its Fourier coefficients, the series
$\sum_{k \in \mathbb{Z}^2} (1 + |k|^2)^2 |a_k(u)|^2$ converges. -/
theorem lowestShellWitness_isH2 : IsH2 lowestShellWitness := by
  classical
  apply summable_of_ne_finset_zero (s := lowestShell)
  intro k hk
  simp [fourierCoefficient_lowestShellWitness, hk]

/-- **Gradient energy of the lowest-shell witness.** The gradient energy of the lowest-shell
witness equals $1$. -/
theorem gradientEnergy_lowestShellWitness : gradientEnergy lowestShellWitness = 1 := by
  classical
  unfold gradientEnergy
  rw [tsum_eq_sum (s := lowestShell)
    (fun k hk ↦ by simp [fourierCoefficient_lowestShellWitness, hk])]
  calc
    _ = ∑ _k ∈ lowestShell, (1 / 4 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [frequencyWeight_lowestShell hk, fourierCoefficient_lowestShellWitness, ite_eq_left hk]
      norm_num [Complex.norm_div]
    _ = 1 := by simp [lowestShell_card]

/-- **Laplacian energy of the lowest-shell witness.** The Laplacian energy of the lowest-shell
witness equals $1$. -/
theorem laplaceEnergy_lowestShellWitness : laplaceEnergy lowestShellWitness = 1 := by
  classical
  unfold laplaceEnergy
  rw [tsum_eq_sum (s := lowestShell)
    (fun k hk ↦ by simp [fourierCoefficient_lowestShellWitness, hk])]
  calc
    _ = ∑ _k ∈ lowestShell, (1 / 4 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [frequencyWeight_lowestShell hk, fourierCoefficient_lowestShellWitness, ite_eq_left hk]
      norm_num [Complex.norm_div]
    _ = 1 := by simp [lowestShell_card]

/-- **The mean is the real part of the zeroth Fourier coefficient.** For every continuous
function $u : \mathbb{T} \to \mathbb{R}$ on the torus $\mathbb{T} = (\mathbb{R}/2\pi\mathbb{Z})^2$,
the mean of $u$ equals the real part of the zeroth Fourier coefficient
$\int_{(\mathbb{R}/\mathbb{Z})^2} \tilde u(y)\,dy$, taken with respect to normalized Haar measure,
of the unit representative $\tilde u$ of $u$ (the function $u$, viewed as complex-valued and
transported to the unit-period torus $(\mathbb{R}/\mathbb{Z})^2$). -/
theorem mean_eq_mFourierCoeff_zero_re (u : C(Torus, ℝ)) :
    mean u = (UnitAddTorus.mFourierCoeff (unitRepresentative u) 0).re := by
  have hμ : (volume : Measure (UnitAddTorus (Fin 2))) = unitHaar := rfl
  have h : Integrable (unitRepresentative u) := by
    simpa [UnitAddTorus.mFourier_zero] using mFourierCoeff_integrable (unitRepresentative u) 0
  simp only [mean, ← hμ, UnitAddTorus.mFourierCoeff, neg_zero,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
  simpa only [RCLike.re_to_complex, unitRepresentative, ContinuousMap.coe_mk,
    Complex.ofReal_re] using integral_re h

/-- **The lowest-shell witness has mean zero.** The lowest-shell witness, the function
$w(x_1, x_2) = (\cos x_1 + \cos x_2)/(2\pi)$ on the torus $(\mathbb{R}/2\pi\mathbb{Z})^2$, has
mean $0$. -/
theorem mean_lowestShellWitness : mean lowestShellWitness = 0 := by
  rw [mean_eq_mFourierCoeff_zero_re, unitRepresentative_lowestShellWitness]
  unfold lowestShellUnit
  rw [mFourierCoeff_smul]
  simp only [mFourierCoeff_add, mFourierCoeff_monomial]
  norm_num [axisFrequency, funext_iff, Fin.forall_fin_two]

/-- **The unit rescaling fixes the origin.** The coordinate rescaling from the torus
$(\mathbb{R}/2\pi\mathbb{Z})^2$ to the unit torus $(\mathbb{R}/\mathbb{Z})^2$ maps $0$ to $0$. -/
theorem unitRescaling_zero : unitRescaling (0 : Torus) = 0 := by
  ext i
  exact (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).map_zero

theorem mFourier_eval_zero (k : Frequency) : UnitAddTorus.mFourier k 0 = 1 := by
  simp [UnitAddTorus.mFourier]

/-- **Value of the lowest-shell witness at the origin.** The lowest-shell witness $u$ takes the
value $u(0) = 1/\pi$ at the origin of the torus. -/
theorem lowestShellWitness_at_zero : lowestShellWitness 0 = 1 / Real.pi := by
  change (lowestShellUnit (unitRescaling 0)).re = 1 / Real.pi
  rw [unitRescaling_zero]
  simp [lowestShellUnit, mFourier_eval_zero, smul_eq_mul]
  field_simp
  ring

/-- **The lowest-shell witness is a zero-mean $H^2$ function.** The lowest-shell witness $u$
belongs to the spectral Sobolev space $H^2$ and has mean $0$. -/
theorem lowestShellWitness_isZeroMeanH2 : IsZeroMeanH2 lowestShellWitness :=
  ⟨lowestShellWitness_isH2, mean_lowestShellWitness⟩

/-- **The lowest-shell witness is admissible at $\delta = 1$.** The lowest-shell witness $u$
satisfies the conditional constraints with $\delta = 1$: it is a zero-mean $H^2$ function on the
torus, its gradient energy is $1$, and its Laplacian energy is $1$. -/
theorem lowestShellWitness_admissible : ConditionalAdmissible lowestShellWitness 1 :=
  ⟨lowestShellWitness_isZeroMeanH2, gradientEnergy_lowestShellWitness,
    laplaceEnergy_lowestShellWitness⟩

/-- **Upper bounds for the conditional supremum.** Let $\mathbb{T} = (\mathbb{R}/2\pi\mathbb{Z})^2$.
For every real $\delta$, let $\theta(\delta)$, the conditional supremum, be the supremum in the
extended reals of $u(0)^2$ over all continuous functions $u : \mathbb{T} \to \mathbb{R}$ that are
conditionally admissible at $\delta$, that is, zero-mean $H^2$ functions with gradient energy $1$
and Laplacian energy $\delta$. Then for every extended real number $b$, $\theta(\delta) \le b$ if
and only if $u(0)^2 \le b$ for every such $u$. -/
theorem theta_le_iff (δ : ℝ) (b : EReal) :
    theta δ ≤ b ↔ ∀ u : C(Torus, ℝ), ConditionalAdmissible u δ → ((u 0) ^ 2 : ℝ) ≤ b := by
  simp [theta, conditionalPointValues, sSup_le_iff]

/-- **Upper bounds for the sharp remainder.** Let $\mathbb{T} = (\mathbb{R}/2\pi\mathbb{Z})^2$. For
real $\delta$, let $\theta(\delta)$ be the supremum in the extended reals of $u(0)^2$ over all
continuous functions $u : \mathbb{T} \to \mathbb{R}$ that are zero-mean $H^2$ functions with
gradient energy $1$ and Laplacian energy $\delta$, and let
$R(\delta) = 4\pi\,\theta(\delta) - \log\delta - \log(1 + \log\delta)$, computed in the extended
reals. For every extended real number $b$, the sharp remainder value
$\sup_{\delta \ge 1} R(\delta)$, a supremum in the extended reals, is at most $b$ if and only if
$R(\delta) \le b$ for every real $\delta \ge 1$. -/
theorem sharpRemainderValue_le_iff (b : EReal) :
    sharpRemainderValue ≤ b ↔ ∀ δ : ℝ, 1 ≤ δ → remainder δ ≤ b := by
  simp [sharpRemainderValue, sharpRemainderValues, sSup_le_iff]

/-- **Frequency weights are nonnegative.** For every frequency $k = (k_0, k_1) \in \mathbb{Z}^2$,
the frequency weight $k_0^2 + k_1^2$ is nonnegative. -/
theorem frequencyWeight_nonneg (k : Frequency) : 0 ≤ frequencyWeight k :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- **$H^2$ functions have a summable gradient energy series.** If $u$ is a continuous real
function on the torus of period $2\pi$ that lies in $H^2$, with Fourier coefficients $a_k$, then
the family $\left((k_0^2 + k_1^2) \, |a_k|^2\right)_{k \in \mathbb{Z}^2}$ is summable. -/
theorem IsH2.gradient_summable {u : C(Torus, ℝ)} (h : IsH2 u) :
    Summable fun k ↦ frequencyWeight k * ‖fourierCoefficient u k‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (frequencyWeight_nonneg k) (sq_nonneg _)) _ h
  intro k
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have := frequencyWeight_nonneg k
  nlinarith

/-- **$H^2$ functions have a summable Laplacian energy series.** If $u$ is a continuous real
function on the torus of period $2\pi$ that lies in $H^2$, with Fourier coefficients $a_k$, then
the family $\left((k_0^2 + k_1^2)^2 \, |a_k|^2\right)_{k \in \mathbb{Z}^2}$ is summable. -/
theorem IsH2.laplace_summable {u : C(Torus, ℝ)} (h : IsH2 u) :
    Summable fun k ↦ frequencyWeight k ^ 2 * ‖fourierCoefficient u k‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ h
  intro k
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have := frequencyWeight_nonneg k
  nlinarith

/-- **Fourier reconstruction.** Let $u$ be a continuous real function on the torus of period
$2\pi$ in each coordinate, let $a_k$ ($k \in \mathbb{Z}^2$) be its Fourier coefficients, and let
$c_k = a_k / (2\pi)$ be the Fourier coefficients, with respect to normalized Haar measure, of its
unit representative on $(\mathbb{R}/\mathbb{Z})^2$. If the family $(c_k)_{k \in \mathbb{Z}^2}$
is summable, then for every point $x$ of the torus, with unit rescaling
$y \in (\mathbb{R}/\mathbb{Z})^2$, the series
$\sum_{k \in \mathbb{Z}^2} (2\pi)^{-1} a_k \, e^{2\pi i (k_0 y_0 + k_1 y_1)}$ converges
unconditionally to $u(x)$. -/
theorem fourierReconstruction (u : C(Torus, ℝ))
    (h : Summable (UnitAddTorus.mFourierCoeff (unitRepresentative u))) (x : Torus) :
    HasSum (fun k ↦ (2 * Real.pi : ℂ)⁻¹ * fourierCoefficient u k *
      UnitAddTorus.mFourier k (unitRescaling x)) (u x : ℂ) := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  simpa [fourierCoefficient, ← mul_assoc, hπ, unitRepresentative, smul_eq_mul] using
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable h (unitRescaling x)

end TorusSobolev
