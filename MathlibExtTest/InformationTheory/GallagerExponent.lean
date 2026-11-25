/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.RandomCodingBound

@[expose] public section

/-!
# Tests for Gallager's function `E₀` and the random coding bound

The running example is the noiseless binary channel `W a = δ_a` with the uniform input law. Then
`E₀(ρ, p) = ρ ln 2` for every `ρ > -1`, so `E₀(0) = 0`, `∂E₀/∂ρ (0) = ln 2` (one bit of mutual
information, in nats) and `E₀` is linear, hence concave. The hypotheses of the random coding
bound and of the coding theorem are jointly satisfiable (non-vacuity): they are instantiated with
`N = 3`, `M = 4` and `ρ = 1/2`.
-/

open Real InformationTheory MathlibExt.InformationTheory.GallagerExponent
  MathlibExt.InformationTheory.RandomCodingBound
open scoped ENNReal

namespace MathlibExtTest.InformationTheory.GallagerExponent

/-- The uniform law on `Bool`. -/
noncomputable def unif : PMF Bool :=
  PMF.ofFintype (fun _ => 2⁻¹) (by simp; exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- The noiseless binary channel. -/
noncomputable def noiseless : Bool → PMF Bool := fun a => PMF.pure a

theorem gallagerInner_noiseless {ρ : ℝ} (hρ : -1 < ρ) (b : Bool) :
    gallagerInner unif noiseless ρ b = 1 / 2 := by
  have hs : (0 : ℝ) < 1 / (1 + ρ) := by
    have : 0 < 1 + ρ := by linarith
    positivity
  have hs' : (1 + ρ)⁻¹ ≠ 0 := by simpa using hs.ne'
  cases b <;> simp [gallagerInner, unif, noiseless, PMF.pure_apply, Real.zero_rpow hs']

/-- For the noiseless binary channel and the uniform input, `E₀(ρ) = ρ ln 2`. -/
theorem gallagerE0_noiseless {ρ : ℝ} (hρ : -1 < ρ) :
    gallagerE0 unif noiseless ρ = ρ * Real.log 2 := by
  rw [gallagerE0, Fintype.sum_bool, gallagerInner_noiseless hρ, gallagerInner_noiseless hρ,
    ← two_mul, Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by norm_num),
    one_div, Real.log_inv]
  ring

example : gallagerE0 unif noiseless 0 = 0 := gallagerE0_zero unif noiseless

/-- The derivative at `0` is the mutual information in nats, here `ln 2`. -/
example : HasDerivAt (gallagerE0 unif noiseless)
    (finiteMutualInformation (unif.bind fun a => (noiseless a).map (Prod.mk a)) * Real.log 2) 0 :=
  hasDerivAt_gallagerE0_zero unif noiseless

/-- The explicit value `ln 2` agrees with the derivative of `ρ ↦ ρ ln 2`. -/
example : HasDerivAt (gallagerE0 unif noiseless) (Real.log 2) 0 := by
  have h : HasDerivAt (fun ρ : ℝ => ρ * Real.log 2) (Real.log 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (Real.log 2)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with ρ hρ
  exact gallagerE0_noiseless hρ

example : ConcaveOn ℝ (Set.Ioi (-1)) (gallagerE0 unif noiseless) :=
  concaveOn_gallagerE0 unif noiseless

/-- Non-vacuity of Corollary 2 (maximal error): `N = 3`, `M = 4`, `ρ = 1/2`. -/
example : ∃ C : Fin 4 → Fin 3 → Bool, ∀ m, mlErrorProb noiseless C m ≤
    4 * (4 : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(3 * gallagerE0 unif noiseless (1 / 2))) := by
  simpa using exists_code_mlErrorProb_le unif noiseless 3 4 (by norm_num) (ρ := 1 / 2)
    (by norm_num) (by norm_num)

/-- Non-vacuity of the random coding bound: `N = 3`, `M = 4`, `ρ = 1/2`. -/
example : randomCodingAvgError unif noiseless 3 4 0 ≤
    ((4 : ℝ) - 1) ^ (1 / 2 : ℝ) * Real.exp (-(3 * gallagerE0 unif noiseless (1 / 2))) := by
  simpa using randomCodingAvgError_le unif noiseless 3 4 0 (by norm_num) (by norm_num)

/-- Non-vacuity of Gallager's coding theorem: `N = 3`, `M = 4`, `ρ = 1/2`. -/
example : ∃ C : Fin 4 → Fin 3 → Bool, (∑ m, mlErrorProb noiseless C m) / 4 ≤
    (4 : ℝ) ^ (1 / 2 : ℝ) * Real.exp (-(3 * gallagerE0 unif noiseless (1 / 2))) := by
  simpa using exists_code_avgError_le unif noiseless 3 4 (by norm_num) (ρ := 1 / 2)
    (by norm_num) (by norm_num)

/-- The exponential achievability theorem applies below `I = ln 2` nats, for instance at
`R = (ln 2) / 2`. -/
example : ∃ E > 0, ∀ N M : ℕ, 0 < M → (M : ℝ) ≤ Real.exp (N * (Real.log 2 / 2)) →
    ∃ C : Fin M → Fin N → Bool, (∑ m, mlErrorProb noiseless C m) / M ≤ Real.exp (-(N * E)) := by
  refine exists_pos_exponent_avgError_le unif noiseless ?_
  have h := (hasDerivAt_gallagerE0_zero unif noiseless).unique (by
    have h : HasDerivAt (fun ρ : ℝ => ρ * Real.log 2) (Real.log 2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (Real.log 2)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with ρ hρ
    exact gallagerE0_noiseless hρ)
  rw [h]
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- Gallager's bound (6): the error indicator is dominated, for a code with two equal code
words (a tie, counted as an error). -/
example (y : Fin 1 → Bool) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    blockTransition noiseless ((fun _ _ => true : Fin 2 → Fin 1 → Bool) 0) y *
        (if ∃ m', m' ≠ (0 : Fin 2) ∧
            blockTransition noiseless ((fun _ _ => true : Fin 2 → Fin 1 → Bool) 0) y ≤
              blockTransition noiseless ((fun _ _ => true : Fin 2 → Fin 1 → Bool) m') y
          then 1 else 0) ≤
      blockTransition noiseless ((fun _ _ => true : Fin 2 → Fin 1 → Bool) 0) y ^ (1 / (1 + ρ)) *
        (∑ j : {j : Fin 2 // j ≠ 0},
          blockTransition noiseless ((fun _ _ => true : Fin 2 → Fin 1 → Bool) j) y ^
            (1 / (1 + ρ))) ^ ρ := by
  classical
  convert mul_indicator_le noiseless (fun _ _ => true) 0 y hρ

end MathlibExtTest.InformationTheory.GallagerExponent
