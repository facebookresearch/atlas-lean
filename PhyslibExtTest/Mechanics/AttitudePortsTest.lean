/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.AttitudePorts
public import PhyslibExt.Units.EngineeringFrames
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Mechanics.AttitudePorts`

* The unit-rate spin about the third axis, `q(t) = cos(t/2) + sin(t/2) k`, obeys the body-rate
  kinematics with `ω_B = e₃`, stays unit, has the rotation matrix `rotZ t` of the frame
  dictionary, and has `R' = rotZ t [e₃]ₓ`, a nonzero fixed-axis rotation.
* The vee of `Rᵀ R'` returns `ω_B = e₃` for the spin, and norm preservation applies to it.
* Swapping the multiplication order changes the result: at the quarter turn about the first axis
  and `ω = e₃`, `R [ω]ₓ ≠ [ω]ₓ R`.
-/

@[expose] public section

open Quaternion
open scoped Matrix

namespace PhyslibExtTest.Mechanics.AttitudePorts

open QuaternionRotation Matrix Units.EngineeringFrames _root_.Mechanics.AttitudePorts

/-- The unit-rate spin about the third axis: `q(t) = cos(t/2) + sin(t/2) k`. -/
noncomputable def zSpin (t : ℝ) : ℍ := ⟨Real.cos (t / 2), 0, 0, Real.sin (t / 2)⟩

/-- The spin as a real combination of `1` and `k`. -/
private lemma zSpin_eq (s : ℝ) :
    zSpin s = Real.cos (s / 2) • (1 : ℍ) + Real.sin (s / 2) • (⟨0, 0, 0, 1⟩ : ℍ) := by
  ext <;> simp [zSpin]

/-- A nonzero fixed-axis rotation: the spin obeys `q' = (1/2) q (0, e₃)`, stays unit, its rotation
matrix is the frame dictionary's `rotZ t`, and `R' = rotZ t [e₃]ₓ`. -/
lemma zSpin_fixture (t : ℝ) :
    HasDerivAt zSpin ((1 / 2 : ℝ) • (zSpin t * pureQuat ![0, 0, 1])) t ∧ ‖zSpin t‖ = 1 ∧
      rotMatrix (zSpin t) = rotZ t ∧
      HasDerivAt (fun s => rotMatrix (zSpin s)) (rotZ t * crossProductMatrix ![0, 0, 1]) t := by
  have hc := ((hasDerivAt_id t).div_const 2).cos
  have hs := ((hasDerivAt_id t).div_const 2).sin
  have hz : HasDerivAt zSpin ((1 / 2 : ℝ) • (zSpin t * pureQuat ![0, 0, 1])) t := by
    have h := (hc.smul_const (1 : ℍ)).add (hs.smul_const (⟨0, 0, 0, 1⟩ : ℍ))
    have hfun : zSpin = fun s => Real.cos (id s / 2) • (1 : ℍ) +
        Real.sin (id s / 2) • (⟨0, 0, 0, 1⟩ : ℍ) := by
      funext s
      exact zSpin_eq s
    rw [hfun]
    convert h using 1
    ext <;> simp [pureQuat] <;> ring
  have hnorm : ‖zSpin t‖ = 1 := by
    have hN : normSq (zSpin t) = 1 := by
      rw [Quaternion.normSq_def']
      simp [zSpin]
    have hmul : ‖zSpin t‖ * ‖zSpin t‖ = 1 := by
      rw [← Quaternion.normSq_eq_norm_mul_self, hN]
    nlinarith [norm_nonneg (zSpin t)]
  have hR : ∀ s, rotMatrix (zSpin s) = rotZ s := by
    intro s
    obtain ⟨θ, rfl⟩ : ∃ θ, s = 2 * θ := ⟨s / 2, by ring⟩
    have hcs := Real.cos_sq_add_sin_sq θ
    have hθ : 2 * θ / 2 = θ := by ring
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [rotMatrix, imCoords, imBasis, zSpin, rotZ, hθ, Real.cos_two_mul, Real.sin_two_mul] <;>
      first
        | ring1
        | linear_combination hcs
        | linear_combination -hcs
  refine ⟨hz, hnorm, hR t, ?_⟩
  have h := hasDerivAt_rotMatrix (ω := fun _ => ![0, 0, 1]) hz
  rw [hR t] at h
  have hfun : (fun s => rotMatrix (zSpin s)) = rotZ := funext hR
  rw [hfun] at h ⊢
  exact h

-- The vee of `Rᵀ R'` returns the body rate `e₃` of the spin.
example (t : ℝ) :
    crossProductVee ((rotMatrix (zSpin t))ᵀ * deriv (fun s => rotMatrix (zSpin s)) t) =
      ![0, 0, 1] :=
  crossProductVee_transpose_mul_deriv_rotMatrix (ω := fun _ => ![0, 0, 1]) (zSpin_fixture t).1
    (zSpin_fixture t).2.1

-- Norm preservation applies to the spin: a unit start gives a unit quaternion at every time.
example (t : ℝ) : ‖zSpin t‖ = 1 :=
  norm_eq_one_of_hasDerivAt (ω := fun _ => ![0, 0, 1]) (fun s => (zSpin_fixture s).1)
    (zSpin_fixture 0).2.1 t

-- Swapping the multiplication order changes the result: at the quarter turn about the first
-- axis and `ω = e₃`, `R [ω]ₓ ≠ [ω]ₓ R`.
example :
    rotMatrix ⟨√2 / 2, √2 / 2, 0, 0⟩ * crossProductMatrix ![0, 0, 1] ≠
      crossProductMatrix ![0, 0, 1] * rotMatrix ⟨√2 / 2, √2 / 2, 0, 0⟩ := by
  have hmulhalf : √2 / 2 * (√2 / 2) = (1 / 2 : ℝ) := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
    norm_num
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [rotMatrix, imCoords, imBasis, crossProductMatrix, Matrix.mul_apply, Fin.sum_univ_three,
    hmulhalf] at h01

end PhyslibExtTest.Mechanics.AttitudePorts
