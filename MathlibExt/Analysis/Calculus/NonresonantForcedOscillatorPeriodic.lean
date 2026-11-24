/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Nonresonant forced oscillator: unique periodic solution, all bounded

The following OpenBMB notice applies to the adapted statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_39.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. The original ATLAS import converted
`theorem ma_proofbench_l2_39 … := by sorry` into the Batteries `theorem_wanted`
`existsUnique_periodic_solution_and_isBounded_of_ne_natCast`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodicWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
This change proves the theorem and moves it to the proved library.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The nonresonant forced oscillator

The complex state $u'+i\omega u$ satisfies a first-order linear equation. The integrating
factor solves it, and nonresonance determines the initial value for a periodic state.
The difference of two states rotates with constant norm, which bounds the displacement
of any solution relative to the periodic solution.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodicWanted

private def carrier (ω : ℝ) : ℂ := (ω : ℂ) * I

private def wave (ω x : ℝ) : ℂ := exp (carrier ω * (x : ℂ))

private theorem carrier_neg (ω : ℝ) : carrier (-ω) = -carrier ω := by
  simp [carrier, neg_mul]

private theorem wave_zero (ω : ℝ) : wave ω 0 = 1 := by simp [wave]

private theorem wave_add (ω x y : ℝ) : wave ω (x + y) = wave ω x * wave ω y := by
  rw [wave, ofReal_add, mul_add, exp_add]
  rfl

private theorem wave_neg_argument (ω x : ℝ) : wave (-ω) x = wave ω (-x) := by
  simp [wave, carrier_neg]

private theorem wave_inv (ω x : ℝ) : wave ω x * wave (-ω) x = 1 := by
  rw [wave_neg_argument, ← wave_add, add_neg_cancel, wave_zero]

private theorem wave_norm (ω x : ℝ) : ‖wave ω x‖ = 1 := by
  rw [wave, Complex.norm_exp]
  simp [carrier, Complex.mul_re, Complex.mul_im]

private theorem wave_hd (ω x : ℝ) : HasDerivAt (wave ω) (carrier ω * wave ω x) x := by
  have h : HasDerivAt (fun z : ℂ => exp (carrier ω * z))
      (exp (carrier ω * (x : ℂ)) * carrier ω) (x : ℂ) := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (x : ℂ)).const_mul (carrier ω)).cexp
  rw [mul_comm (carrier ω) (wave ω x)]
  exact h.comp_ofReal

private theorem wave_cont (ω : ℝ) : Continuous (wave ω) :=
  (show Differentiable ℝ (wave ω) from fun x => (wave_hd ω x).differentiableAt).continuous

private theorem wave_period_ne_one {ω : ℝ} (hω : 0 < ω) (h : ∀ n : ℕ, ω ≠ n) :
    wave ω (2 * Real.pi) ≠ 1 := by
  intro he
  have him : (carrier ω * ((2 * Real.pi : ℝ) : ℂ)).im = ω * (2 * Real.pi) := by
    simp [carrier, Complex.mul_im]
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff_of_im_nonneg (by rw [him]; positivity)).mp he
  have hn_im := congrArg Complex.im hn
  rw [him] at hn_im
  have hn_mul : ω * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
    simpa [Complex.mul_im, Complex.mul_re, mul_assoc] using hn_im
  exact h n (mul_right_cancel₀ (ne_of_gt Real.two_pi_pos) hn_mul)

-- The integrating factor turns the first-order complex equation into an integral.
private def forcedState (ω : ℝ) (g : ℝ → ℝ) (a : ℂ) (x : ℝ) : ℂ :=
  wave ω x * (a + ∫ t in 0..x, wave (-ω) t * (g t : ℂ))

private theorem forcedState_zero (ω : ℝ) (g : ℝ → ℝ) (a : ℂ) :
    forcedState ω g a 0 = a := by simp [forcedState, wave_zero]

private theorem forcedState_hd (ω : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (a : ℂ) (x : ℝ) :
    HasDerivAt (forcedState ω g a) (carrier ω * forcedState ω g a x + (g x : ℂ)) x := by
  have hcont : Continuous (fun t : ℝ => wave (-ω) t * (g t : ℂ)) :=
    (wave_cont (-ω)).mul (Complex.continuous_ofReal.comp hgc)
  have hInt := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := x)
    (hcont.intervalIntegrable 0 x) hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
    hcont.continuousAt
  have hd := (wave_hd ω x).mul (hInt.const_add a)
  have hw : wave ω x * (wave (-ω) x * (g x : ℂ)) = (g x : ℂ) := by
    rw [← mul_assoc, wave_inv, one_mul]
  rw [hw] at hd
  convert hd using 1 <;> first | rfl | simp only [forcedState, mul_assoc]

-- Two states with the same forcing differ by a rotating constant.
private theorem state_difference {ω : ℝ} {g : ℝ → ℝ} {a b : ℝ → ℂ}
    (ha : ∀ x, HasDerivAt a (carrier ω * a x + (g x : ℂ)) x)
    (hb : ∀ x, HasDerivAt b (carrier ω * b x + (g x : ℂ)) x) (x : ℝ) :
    a x - b x = wave ω x * (a 0 - b 0) := by
  let d (x : ℝ) := wave (-ω) x * (a x - b x)
  have hd (x : ℝ) : HasDerivAt d 0 x := by
    have h := (wave_hd (-ω) x).mul ((ha x).sub (hb x))
    convert h using 1
    simp only [Pi.sub_apply, carrier_neg]
    ring
  have he := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).deriv) x 0
  change wave (-ω) x * (a x - b x) = wave (-ω) 0 * (a 0 - b 0) at he
  rw [wave_zero, one_mul] at he
  calc
    a x - b x = wave ω x * (wave (-ω) x * (a x - b x)) := by rw [← mul_assoc, wave_inv, one_mul]
    _ = wave ω x * (a 0 - b 0) := by rw [he]

-- Choose the initial state by matching endpoints, then use uniqueness of the initial value.
private theorem exists_periodicState {ω : ℝ} (hω : 0 < ω) (hn : ∀ n : ℕ, ω ≠ n)
    {g : ℝ → ℝ} (hgc : Continuous g) (hper : Function.Periodic g (2 * Real.pi)) :
    ∃ z : ℝ → ℂ, (∀ x, HasDerivAt z (carrier ω * z x + (g x : ℂ)) x) ∧
      Function.Periodic z (2 * Real.pi) := by
  let T := 2 * Real.pi
  let m := wave ω T
  let J := ∫ t in 0..T, wave (-ω) t * (g t : ℂ)
  have hm : m ≠ 1 := wave_period_ne_one hω hn
  let a := m * J / (1 - m)
  let z := forcedState ω g a
  have hz (x : ℝ) : HasDerivAt z (carrier ω * z x + (g x : ℂ)) x := forcedState_hd ω hgc a x
  have hzT : z T = z 0 := by
    change forcedState ω g a T = forcedState ω g a 0
    rw [forcedState_zero]
    change m * (a + J) = a
    have hden : 1 - m ≠ 0 := sub_ne_zero.mpr hm.symm
    dsimp only [a]
    field_simp [hden]
    ring
  refine ⟨z, hz, ?_⟩
  intro x
  have hshift (y : ℝ) : HasDerivAt (fun t => z (t + T))
      (carrier ω * z (y + T) + (g y : ℂ)) y := by
    have hadd : HasDerivAt (fun t : ℝ => t + T) 1 y := (hasDerivAt_id y).add_const T
    have hg' : g (y + T) = g y := hper y
    simpa only [Function.comp_def, one_smul, hg'] using (hz (y + T)).scomp y hadd
  have hd := state_difference hshift hz x
  change z (x + T) - z x = wave ω x * (z (0 + T) - z 0) at hd
  rw [zero_add, hzT, sub_self, mul_zero] at hd
  exact sub_eq_zero.mp hd

private theorem periodicState_unique {ω : ℝ} (hω : 0 < ω) (hn : ∀ n : ℕ, ω ≠ n)
    {g : ℝ → ℝ} {a b : ℝ → ℂ}
    (ha : ∀ x, HasDerivAt a (carrier ω * a x + (g x : ℂ)) x)
    (hb : ∀ x, HasDerivAt b (carrier ω * b x + (g x : ℂ)) x)
    (hpa : Function.Periodic a (2 * Real.pi)) (hpb : Function.Periodic b (2 * Real.pi)) :
    a = b := by
  have he := state_difference ha hb (2 * Real.pi)
  have ea : a (2 * Real.pi) = a 0 := by simpa only [zero_add] using hpa 0
  have eb : b (2 * Real.pi) = b 0 := by simpa only [zero_add] using hpb 0
  rw [ea, eb] at he
  have hmul : (wave ω (2 * Real.pi) - 1) * (a 0 - b 0) = 0 := by linear_combination -he
  have hzero := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (wave_period_ne_one hω hn))
  funext x
  exact sub_eq_zero.mp (by rw [state_difference ha hb x, hzero, mul_zero])

-- Encode a real solution by its derivative and its scaled displacement.
private def phaseState (ω : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℂ :=
  ((deriv u x : ℝ) : ℂ) + carrier ω * (u x : ℂ)

private theorem carrier_sq (ω : ℝ) : carrier ω * carrier ω = -(ω : ℂ) ^ 2 := by
  calc
    _ = (ω : ℂ) ^ 2 * I ^ 2 := by unfold carrier; ring
    _ = _ := by rw [I_sq]; ring

private theorem phaseState_hd {ω : ℝ} {u g : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hode : ∀ x, deriv (deriv u) x + ω ^ 2 * u x = g x) (x : ℝ) :
    HasDerivAt (phaseState ω u) (carrier ω * phaseState ω u x + (g x : ℂ)) x := by
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdd := hu.differentiable_deriv_two
  have hd := ((hdd x).hasDerivAt.ofReal_comp).add
    (((hdu x).hasDerivAt.ofReal_comp).const_mul (carrier ω))
  have he := congrArg Complex.ofReal (hode x)
  push_cast at he
  convert hd using 1
  · rfl
  · unfold phaseState
    rw [mul_add, ← mul_assoc, carrier_sq]
    linear_combination -he

private theorem phaseState_im (ω : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    (phaseState ω u x).im = ω * u x := by
  simp [phaseState, carrier, Complex.add_im, Complex.mul_re, Complex.mul_im]

private theorem phaseState_periodic {ω T : ℝ} {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hp : Function.Periodic u T) : Function.Periodic (phaseState ω u) T := by
  intro x
  have hadd : HasDerivAt (fun y : ℝ => y + T) 1 x := (hasDerivAt_id x).add_const T
  have hd : HasDerivAt (fun y => u (y + T)) (deriv u (x + T)) x := by
    simpa only [Function.comp_def, mul_one] using (hu (x + T)).hasDerivAt.comp x hadd
  have huShift : (fun y => u (y + T)) = u := funext hp
  rw [huShift] at hd
  change phaseState ω u (x + T) = phaseState ω u x
  rw [phaseState, phaseState, ← hd.deriv, hp x]

private def realSolution (ω : ℝ) (z : ℝ → ℂ) (x : ℝ) : ℝ := (z x).im / ω

private theorem realSolution_ode {ω : ℝ} (hω : 0 < ω) {g : ℝ → ℝ} (hgc : Continuous g)
    {z : ℝ → ℂ} (hz : ∀ x, HasDerivAt z (carrier ω * z x + (g x : ℂ)) x) :
    ContDiff ℝ 2 (realSolution ω z) ∧
      ∀ x, deriv (deriv (realSolution ω z)) x + ω ^ 2 * realSolution ω z x = g x := by
  have hzd : Differentiable ℝ z := fun x => (hz x).differentiableAt
  have hi (x : ℝ) : HasDerivAt (realSolution ω z) (z x).re x := by
    have hd := (imCLM.hasFDerivAt.comp_hasDerivAt x (hz x)).div_const ω
    convert hd using 1
    · rfl
    · simp [carrier, Complex.add_im, Complex.mul_re, Complex.mul_im, hω.ne']
  have hr (x : ℝ) : HasDerivAt (fun t => (z t).re) (g x - ω * (z x).im) x := by
    have hd := reCLM.hasFDerivAt.comp_hasDerivAt x (hz x)
    convert hd using 1
    · rfl
    · simp [carrier, Complex.add_re, Complex.mul_re, Complex.mul_im]
      ring
  have hid : deriv (realSolution ω z) = fun x => (z x).re := funext fun x => (hi x).deriv
  have hrd : deriv (fun x => (z x).re) = fun x => g x - ω * (z x).im :=
    funext fun x => (hr x).deriv
  constructor
  · change ContDiff ℝ (1 + 1) (realSolution ω z)
    refine contDiff_succ_iff_deriv.mpr ⟨fun x => (hi x).differentiableAt, by simp, ?_⟩
    rw [hid]
    refine contDiff_one_iff_deriv.mpr ⟨fun x => (hr x).differentiableAt, ?_⟩
    rw [hrd]
    exact hgc.sub (continuous_const.mul (Complex.continuous_im.comp hzd.continuous))
  · intro x
    rw [hid, hrd, realSolution]
    field_simp [hω.ne']
    ring

private theorem forced_oscillator {ω : ℝ} (hω : 0 < ω) (hn : ∀ n : ℕ, ω ≠ n)
    {g : ℝ → ℝ} (hgc : Continuous g) (hp : Function.Periodic g (2 * Real.pi)) :
    (∃! u : ℝ → ℝ, ContDiff ℝ 2 u ∧
      (∀ x : ℝ, deriv (deriv u) x + ω ^ 2 * u x = g x) ∧ Function.Periodic u (2 * Real.pi)) ∧
    (∀ u : ℝ → ℝ, ContDiff ℝ 2 u →
      (∀ x : ℝ, deriv (deriv u) x + ω ^ 2 * u x = g x) → Bornology.IsBounded (Set.range u)) := by
  obtain ⟨z, hz, hzper⟩ := exists_periodicState hω hn hgc hp
  let v := realSolution ω z
  obtain ⟨hv, hvode⟩ := realSolution_ode hω hgc hz
  have hvper : Function.Periodic v (2 * Real.pi) := by
    intro x
    change (z (x + 2 * Real.pi)).im / ω = (z x).im / ω
    rw [hzper x]
  have hphaseV := phaseState_hd hv hvode
  constructor
  · refine ⟨v, ⟨hv, hvode, hvper⟩, ?_⟩
    rintro u ⟨hu, huode, huper⟩
    have he := periodicState_unique hω hn (phaseState_hd hu huode) hphaseV
      (phaseState_periodic (hu.differentiable (by norm_num)) huper)
      (phaseState_periodic (hv.differentiable (by norm_num)) hvper)
    funext x
    have hi := congrArg (fun a : ℝ → ℂ => (a x).im) he
    simp only [phaseState_im] at hi
    exact mul_left_cancel₀ hω.ne' hi
  · intro u hu huode
    have hphaseU := phaseState_hd hu huode
    have hvb : Bornology.IsBounded (range v) := by
      rw [← hvper.image_Icc (by positivity : 0 < 2 * Real.pi) 0]
      exact (isCompact_Icc.image hv.continuous).isBounded
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hvb
    let C := ‖phaseState ω u 0 - phaseState ω v 0‖
    refine isBounded_iff_forall_norm_le.mpr ⟨B + C / ω, ?_⟩
    rintro _ ⟨x, rfl⟩
    have habs := abs_im_le_norm (phaseState ω u x - phaseState ω v x)
    rw [Complex.sub_im, phaseState_im, phaseState_im, ← mul_sub, abs_mul, abs_of_pos hω,
      state_difference hphaseU hphaseV x, norm_mul, wave_norm, one_mul] at habs
    have hd : ‖u x - v x‖ ≤ C / ω := by
      rw [Real.norm_eq_abs, le_div_iff₀ hω, mul_comm]
      exact habs
    calc
      ‖u x‖ = ‖v x + (u x - v x)‖ := by rw [add_comm (v x), sub_add_cancel]
      _ ≤ ‖v x‖ + ‖u x - v x‖ := norm_add_le _ _
      _ ≤ B + C / ω := add_le_add (hB _ (mem_range_self x)) hd

/-- **Nonresonant forced oscillator.** Let $\omega > 0$ be a real number that is not an integer,
and let $g : \mathbb{R} \to \mathbb{R}$ be continuous and $2\pi$-periodic. Then the equation
$u'' + \omega^2 u = g$ has exactly one twice continuously differentiable solution
$u : \mathbb{R} \to \mathbb{R}$ that is $2\pi$-periodic, and every twice continuously
differentiable solution $u : \mathbb{R} \to \mathbb{R}$ of this equation is bounded.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Ordinary
differential operators), `benchmark/level2/ma_proofbench_l2_39.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem existsUnique_periodic_solution_and_isBounded_of_ne_natCast
  (ω : ℝ) (hωpos : 0 < ω) (hω_nonint : ∀ n : ℕ, ω ≠ n)
  (g : ℝ → ℝ) (hg_cont : Continuous g)
  (hper : Function.Periodic g (2 * Real.pi)) :
  (∃! u : ℝ → ℝ, ContDiff ℝ 2 u ∧
  (∀ x : ℝ, deriv (deriv u) x + ω ^ 2 * u x = g x) ∧
  Function.Periodic u (2 * Real.pi)) ∧
  (∀ u : ℝ → ℝ, ContDiff ℝ 2 u →
  (∀ x : ℝ, deriv (deriv u) x + ω ^ 2 * u x = g x) →
  Bornology.IsBounded (Set.range u)) := by
  exact forced_oscillator hωpos hω_nonint hg_cont hper

end MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodicWanted
