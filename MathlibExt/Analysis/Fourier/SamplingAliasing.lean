/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Aliasing and noninjectivity of uniform sampling

Sampling at times `n * T` identifies complex exponentials whose frequencies differ by
an integer multiple of `1 / T`. It can also identify distinct smooth bounded signals:
the sine `sin (π * t / T)` vanishes on the whole sampling lattice. A signal with period
`N * T` gives an `N`-periodic sample sequence and hence a signal on `ZMod N`.

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

open scoped ContDiff

/-- Sample a complex-valued signal on the integer lattice with spacing `T`. -/
noncomputable def sampleSignal (T : ℝ) (x : ℝ → ℂ) (n : ℤ) : ℂ :=
  x ((n : ℝ) * T)

/-- The complex exponential at frequency `f` in cycles per unit time. -/
noncomputable def complexExpSignal (f t : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * f * t) : ℂ) * Complex.I)

private lemma ofReal_int_turn (k : ℤ) :
    (↑((k : ℝ) * (2 * Real.pi)) : ℂ) * Complex.I =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  push_cast
  ring

/-- Shifting a frequency by any integer multiple of `1 / T` leaves all samples unchanged. -/
theorem sampleSignal_complexExp_alias {T : ℝ} (hT : 0 < T) (f : ℝ) (k : ℤ) :
    sampleSignal T (complexExpSignal (f + (k : ℝ) / T)) =
      sampleSignal T (complexExpSignal f) := by
  funext n
  have hphase : 2 * Real.pi * (f + (k : ℝ) / T) * ((n : ℝ) * T) =
      2 * Real.pi * f * ((n : ℝ) * T) + ((k * n : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [Int.cast_mul]
    field_simp [hT.ne']
  simp only [sampleSignal, complexExpSignal, hphase, Complex.ofReal_add, add_mul,
    Complex.exp_add, ofReal_int_turn, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Two complex exponentials have the same samples exactly when their frequencies differ
by an integer multiple of `1 / T`. For necessity, the sample at index `1` suffices. -/
theorem sampleSignal_complexExp_eq_iff {T f g : ℝ} (hT : 0 < T) :
    sampleSignal T (complexExpSignal g) = sampleSignal T (complexExpSignal f) ↔
      ∃ k : ℤ, g = f + (k : ℝ) / T := by
  constructor
  · intro h
    have h₁ := congrFun h (1 : ℤ)
    simp only [sampleSignal, complexExpSignal, Int.cast_one, one_mul] at h₁
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h₁
    rw [← ofReal_int_turn, ← add_mul, ← Complex.ofReal_add] at hk
    have hphase := Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hk)
    have hscaled : g * T = f * T + (k : ℝ) := by
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      calc
        2 * Real.pi * (g * T) = 2 * Real.pi * g * T := by ring
        _ = 2 * Real.pi * f * T + (k : ℝ) * (2 * Real.pi) := hphase
        _ = 2 * Real.pi * (f * T + (k : ℝ)) := by ring
    refine ⟨k, mul_right_cancel₀ hT.ne' ?_⟩
    rwa [add_mul, div_mul_cancel₀ _ hT.ne']
  · rintro ⟨k, rfl⟩
    exact sampleSignal_complexExp_alias hT f k

/-- Two signals have the same samples exactly when their difference vanishes on the lattice. -/
theorem sampleSignal_eq_iff {T : ℝ} {x y : ℝ → ℂ} :
    sampleSignal T x = sampleSignal T y ↔ ∀ n : ℤ, (x - y) ((n : ℝ) * T) = 0 := by
  simp only [funext_iff, sampleSignal, Pi.sub_apply, sub_eq_zero]

/-- A real sine, viewed as a complex signal, with zeros at the sampling times for spacing `T`. -/
noncomputable def samplingKernelSin (T t : ℝ) : ℂ :=
  ↑(Real.sin (Real.pi * t / T))

/-- The sine witness is smooth. -/
theorem contDiff_samplingKernelSin (T : ℝ) : ContDiff ℝ ∞ (samplingKernelSin T) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const T))

/-- The sine witness is uniformly bounded by one. -/
theorem norm_samplingKernelSin_le_one (T t : ℝ) : ‖samplingKernelSin T t‖ ≤ 1 := by
  rw [samplingKernelSin, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- The sine witness has zero samples at every integer index. -/
theorem sampleSignal_samplingKernelSin {T : ℝ} (hT : 0 < T) :
    sampleSignal T (samplingKernelSin T) = 0 := by
  funext n
  have harg : Real.pi * ((n : ℝ) * T) / T = (n : ℝ) * Real.pi := by
    rw [← mul_assoc, mul_div_cancel_right₀ _ hT.ne', mul_comm]
  simp only [sampleSignal, samplingKernelSin, harg, Real.sin_int_mul_pi,
    Complex.ofReal_zero, Pi.zero_apply]

/-- The sine witness is one halfway between the samples at `0` and `T`. -/
theorem samplingKernelSin_half_step {T : ℝ} (hT : 0 < T) : samplingKernelSin T (T / 2) = 1 := by
  have harg : Real.pi * (T / 2) / T = Real.pi / 2 := by
    field_simp [hT.ne']
  simp only [samplingKernelSin, harg, Real.sin_pi_div_two, Complex.ofReal_one]

/-- Uniform sampling is not injective even on the set of smooth, uniformly bounded signals. -/
theorem sampleSignal_not_injOn_smooth_bounded {T : ℝ} (hT : 0 < T) :
    ¬ Set.InjOn (sampleSignal T)
      {x : ℝ → ℂ | ContDiff ℝ ∞ x ∧ ∃ C : ℝ, ∀ t, ‖x t‖ ≤ C} := by
  intro hinj
  have hzero : sampleSignal T (0 : ℝ → ℂ) = 0 := rfl
  have heq : samplingKernelSin T = (0 : ℝ → ℂ) :=
    hinj ⟨contDiff_samplingKernelSin T, ⟨1, norm_samplingKernelSin_le_one T⟩⟩
      ⟨contDiff_const, ⟨0, fun t ↦ by simp⟩⟩
      ((sampleSignal_samplingKernelSin hT).trans hzero.symm)
  have hval := congrFun heq (T / 2)
  rw [samplingKernelSin_half_step hT, Pi.zero_apply] at hval
  exact one_ne_zero hval

/-- Uniform sampling is not injective on continuous signals. -/
theorem sampleSignal_not_injOn_continuous {T : ℝ} (hT : 0 < T) :
    ¬ Set.InjOn (sampleSignal T) {x : ℝ → ℂ | Continuous x} := by
  intro hinj
  exact sampleSignal_not_injOn_smooth_bounded hT (hinj.mono (fun _ hx ↦ hx.1.continuous))

/-- A signal with period `N * T` has an integer-indexed sample sequence with period `N`. -/
theorem sampleSignal_periodic {T : ℝ} {N : ℕ} {x : ℝ → ℂ}
    (hx : Function.Periodic x ((N : ℝ) * T)) : Function.Periodic (sampleSignal T x) (N : ℤ) := by
  intro n
  simpa only [sampleSignal, Int.cast_add, Int.cast_natCast, add_mul] using hx ((n : ℝ) * T)

/-- The samples of a signal with period `N * T` descend uniquely along the canonical cast
`ℤ → ZMod N`. For positive `N` this gives a signal on a finite cyclic group. -/
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
