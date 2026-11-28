/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Data.ZMod.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.ZMod.Basic

/-!
# Aliasing and noninjectivity of uniform sampling

For nonzero `T`, sampling at times `n * T` identifies complex exponentials exactly when
their frequencies differ by an integer multiple of `1 / T`. It also identifies the zero
signal with the smooth, bounded sine `sin (π * t / T)`. At `T = 0` all sample times
coincide. A signal with period `N * T` gives an `N`-periodic sample sequence and hence
a signal on `ZMod N`.

## References

* M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*,
  Cambridge University Press, 2014, free version v1.1
  (<https://fourierandwavelets.org/FSP_v1.1_2014.pdf>),
  §5.4.2, pp. 460–461 (including Example 5.18) and Fig. 5.24 (p. 457), for spectral
  replicas and aliasing under uniform sampling. Their angular frequency spacing `2π / T`
  corresponds to `1 / T` in cycles per unit time. Section 5.3, Fig. 5.17 (p. 441),
  illustrates the analogous replicas for discrete decimation.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped ContDiff FourierTransform

/-- For a complex-valued signal $x : \mathbb{R} \to \mathbb{C}$ and real step $T$,
the sampling map is $S_T x : \mathbb{Z} \to \mathbb{C}$, given by $(S_T x)_n = x(nT)$.
For $T < 0$ the indices run in reverse time, and for $T = 0$ all samples are $x(0)$. -/
noncomputable def sampleSignal (T : ℝ) (x : ℝ → ℂ) (n : ℤ) : ℂ :=
  x ((n : ℝ) * T)

/-- For real $T,f$ and any integer $k$, the complex exponentials $t \mapsto e^{2\pi i(f+k/T)t}$
and $t \mapsto e^{2\pi i f t}$ agree at every sample time $nT$, $n \in \mathbb{Z}$.
Here $f$ is measured in cycles per unit time and the Fourier character has positive sign.
If $T=0$, the quotient $k/0$ is defined as zero and both sample sequences are constantly $1$. -/
theorem sampleSignal_complexExp_alias {T : ℝ} (f : ℝ) (k : ℤ) :
    sampleSignal T (fun t ↦ (𝐞 ((f + (k : ℝ) / T) * t) : ℂ)) =
      sampleSignal T (fun t ↦ (𝐞 (f * t) : ℂ)) := by
  by_cases hT : T = 0
  · simp only [hT, div_zero, add_zero]
  funext n
  have hphase : (f + (k : ℝ) / T) * ((n : ℝ) * T) =
      f * ((n : ℝ) * T) + ((k * n : ℤ) : ℝ) := by
    rw [add_mul, Int.cast_mul, mul_left_comm ((k : ℝ) / T), div_mul_cancel₀ _ hT,
      mul_comm (n : ℝ) (k : ℝ)]
  have hturn : 𝐞 ((k * n : ℤ) : ℝ) = 1 := by
    rw [Real.fourierChar_apply', Circle.exp_two_pi_mul_int]
  simp only [sampleSignal, hphase, AddChar.map_add_eq_mul, hturn, mul_one]

/-- Let $T \ne 0$ be real, and let $f,g$ be real frequencies in cycles per unit time.
The positive-sign complex exponentials $t \mapsto e^{2\pi i g t}$ and $t \mapsto e^{2\pi i f t}$
agree at all times $nT$, $n \in \mathbb{Z}$, if and only if $g = f + k/T$ for some integer $k$.
Necessity follows from the sample at $n=1$. The hypothesis excludes $T=0$, when all
frequencies have the same samples regardless of their difference. -/
theorem sampleSignal_complexExp_eq_iff {T f g : ℝ} (hT : T ≠ 0) :
    sampleSignal T (fun t ↦ (𝐞 (g * t) : ℂ)) = sampleSignal T (fun t ↦ (𝐞 (f * t) : ℂ)) ↔
      ∃ k : ℤ, g = f + (k : ℝ) / T := by
  constructor
  · intro h
    have h₁ : 𝐞 (g * T) = 𝐞 (f * T) := Circle.coe_injective (by
      simpa only [sampleSignal, Int.cast_one, one_mul] using congrFun h (1 : ℤ))
    simp only [Real.fourierChar_apply'] at h₁
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h₁
    have hscaled : g * T = f * T + (k : ℝ) := by
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      rwa [mul_add, mul_comm (2 * Real.pi) (k : ℝ)]
    refine ⟨k, mul_right_cancel₀ hT ?_⟩
    rwa [add_mul, div_mul_cancel₀ _ hT]
  · rintro ⟨k, rfl⟩
    exact sampleSignal_complexExp_alias f k

/-- For any real $T$ and signals $x,y : \mathbb{R} \to \mathbb{C}$, the sample sequences
$n \mapsto x(nT)$ and $n \mapsto y(nT)$ are equal if and only if $x(nT)-y(nT)=0$
for every integer $n$. At $T=0$ this is just equality at time zero. -/
theorem sampleSignal_eq_iff {T : ℝ} {x y : ℝ → ℂ} :
    sampleSignal T x = sampleSignal T y ↔ ∀ n : ℤ, (x - y) ((n : ℝ) * T) = 0 := by
  simp only [funext_iff, sampleSignal, Pi.sub_apply, sub_eq_zero]

/-- For real $T$, the sine signal $s_T : \mathbb{R} \to \mathbb{C}$ is
$s_T(t) = \sin(\pi t/T)$, with real sine included in $\mathbb{C}$.
At $T=0$ this is identically zero, since division by zero is defined as zero. -/
noncomputable def samplingKernelSin (T t : ℝ) : ℂ :=
  ↑(Real.sin (Real.pi * t / T))

/-- For every real $T$, the complex-valued signal $t \mapsto \sin(\pi t/T)$ on $\mathbb{R}$
is smooth (infinitely differentiable over $\mathbb{R}$). At $T=0$ it is identically zero. -/
theorem contDiff_samplingKernelSin (T : ℝ) : ContDiff ℝ ∞ (samplingKernelSin T) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const T))

/-- For all real $T$ and $t$, the complex norm of the real sine value $\sin(\pi t/T)$ is at most
$1$. This holds also at $T=0$, when the sine argument is defined as zero. -/
theorem norm_samplingKernelSin_le_one (T t : ℝ) : ‖samplingKernelSin T t‖ ≤ 1 := by
  rw [samplingKernelSin, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- For every real $T$, all the samples at $nT$, $n \in \mathbb{Z}$, of the complex-valued
signal $t \mapsto \sin(\pi t/T)$ are zero. For nonzero $T$ the sine argument at $nT$ is
$n\pi$; at $T=0$ it is defined as zero. -/
theorem sampleSignal_samplingKernelSin {T : ℝ} : sampleSignal T (samplingKernelSin T) = 0 := by
  funext n
  by_cases hT : T = 0
  · simp only [sampleSignal, samplingKernelSin, hT, div_zero, Real.sin_zero,
      Complex.ofReal_zero, Pi.zero_apply]
  have harg : Real.pi * ((n : ℝ) * T) / T = (n : ℝ) * Real.pi := by
    rw [← mul_assoc, mul_div_cancel_right₀ _ hT, mul_comm]
  simp only [sampleSignal, samplingKernelSin, harg, Real.sin_int_mul_pi,
    Complex.ofReal_zero, Pi.zero_apply]

/-- For real $T \ne 0$, the complex-valued signal $t \mapsto \sin(\pi t/T)$ takes the
value $1$ at $t=T/2$, the midpoint of the sample times $0$ and $T$ for either sign of $T$. -/
theorem samplingKernelSin_half_step {T : ℝ} (hT : T ≠ 0) : samplingKernelSin T (T / 2) = 1 := by
  have harg : Real.pi * (T / 2) / T = Real.pi / 2 := by
    rw [← mul_div_assoc, ← div_mul_eq_mul_div, mul_div_cancel_right₀ _ hT]
  simp only [samplingKernelSin, harg, Real.sin_pi_div_two, Complex.ofReal_one]

/-- For any real $T \ne 0$, the map $x \mapsto (n \mapsto x(nT))$ ($n \in \mathbb{Z}$) is
not injective on smooth signals $x : \mathbb{R} \to \mathbb{C}$ with $\|x(t)\| \le C$
for some real $C$ and every real $t$. The signals $t \mapsto \sin(\pi t/T)$ and zero
have the same samples but differ at $t=T/2$. -/
theorem sampleSignal_not_injOn_smooth_bounded {T : ℝ} (hT : T ≠ 0) :
    ¬ Set.InjOn (sampleSignal T)
      {x : ℝ → ℂ | ContDiff ℝ ∞ x ∧ ∃ C : ℝ, ∀ t, ‖x t‖ ≤ C} := by
  intro hinj
  have hzero : sampleSignal T (0 : ℝ → ℂ) = 0 := rfl
  have heq : samplingKernelSin T = (0 : ℝ → ℂ) :=
    hinj ⟨contDiff_samplingKernelSin T, ⟨1, norm_samplingKernelSin_le_one T⟩⟩
      ⟨contDiff_const, ⟨0, fun t ↦ by simp⟩⟩
      ((sampleSignal_samplingKernelSin (T := T)).trans hzero.symm)
  have hval := congrFun heq (T / 2)
  rw [samplingKernelSin_half_step hT, Pi.zero_apply] at hval
  exact one_ne_zero hval

/-- For any real $T \ne 0$, the map $x \mapsto (n \mapsto x(nT))$ ($n \in \mathbb{Z}$) is
not injective on continuous signals $x : \mathbb{R} \to \mathbb{C}$: the distinct continuous
signals $t \mapsto \sin(\pi t/T)$ and zero have the same samples. -/
theorem sampleSignal_not_injOn_continuous {T : ℝ} (hT : T ≠ 0) :
    ¬ Set.InjOn (sampleSignal T) {x : ℝ → ℂ | Continuous x} := by
  intro hinj
  exact sampleSignal_not_injOn_smooth_bounded hT (hinj.mono (fun _ hx ↦ hx.1.continuous))

/-- Let $T$ be real, $N$ a natural number, and $x : \mathbb{R} \to \mathbb{C}$ satisfy
$x(t+NT)=x(t)$ for all real $t$. Then its samples satisfy $x((n+N)T)=x(nT)$
for all integers $n$. For $N=0$ this is vacuous; for $T=0$ the sequence is constant. -/
theorem sampleSignal_periodic {T : ℝ} {N : ℕ} {x : ℝ → ℂ}
    (hx : Function.Periodic x ((N : ℝ) * T)) : Function.Periodic (sampleSignal T x) (N : ℤ) := by
  intro n
  simpa only [sampleSignal, Int.cast_add, Int.cast_natCast, add_mul] using hx ((n : ℝ) * T)

/-- Let $T$ be real, $N$ a natural number, and $x : \mathbb{R} \to \mathbb{C}$ satisfy
$x(t+NT)=x(t)$ for all real $t$. There is a unique $y : \mathrm{ZMod}\,N \to \mathbb{C}$
such that $y([n])=x(nT)$ for every integer $n$, where $[n]$ is the canonical integer cast.
For $N>0$ this is a signal on a finite cyclic group. For $N=0$, `ZMod 0` is the integers,
and for $T=0$ the descended signal is constantly $x(0)$. -/
theorem sampleSignal_factors_zmod {T : ℝ} {N : ℕ} {x : ℝ → ℂ}
    (hx : Function.Periodic x ((N : ℝ) * T)) :
    ∃! y : ZMod N → ℂ, ∀ n : ℤ, y (n : ZMod N) = sampleSignal T x n := by
  have hp := sampleSignal_periodic hx
  have hsame (a b : ℤ) (hab : (a : ZMod N) = (b : ZMod N)) :
      sampleSignal T x a = sampleSignal T x b := by
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a b N).mp hab
    have hindex : a + k * (N : ℤ) = b := by
      rw [mul_comm k, ← hk, add_comm, sub_add_cancel]
    have hshift : sampleSignal T x (a + k * (N : ℤ)) = sampleSignal T x a := hp.int_mul k a
    rw [hindex] at hshift
    exact hshift.symm
  refine ⟨fun z ↦ sampleSignal T x (z.cast : ℤ), fun n ↦ ?_, fun y hy ↦ ?_⟩
  · exact hsame _ n (ZMod.intCast_zmod_cast (n : ZMod N))
  · funext z
    rw [← hy (z.cast : ℤ), ZMod.intCast_zmod_cast]

end MetaMathlibExt
