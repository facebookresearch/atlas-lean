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
* A reaction wheel with the locked inertia `J = 2`, no external torque and the command `u = 1`
  spins up from `h = 0` while the body rate falls from `1`; the total momentum `J ω + h` stays `2`.
* The command `u = 1` meets the command limit `1` at every time, but from `h(0) = 0` it is
  admissible for the momentum limit `1/4` exactly on horizons `T ≤ 1/4`; the reserve condition is
  sharp there, and the momentum limit is reached at `T_sat = 1/4` whatever the command limit.
* A negative horizon is admissible for no command, even with impossible limits.
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

open Set

/-- Nonzero internal exchange conserves the total momentum: the locked inertia `J = 2`,
`τ_ext = 0`, the command `u = 1`, the body rate `ω(t) = 1 - t / 2` and the relative wheel momentum
`h(t) = t` satisfy the model (`ω' = -1/2`, `h' = 1`, `2 · (-1/2) = 0 - 1`); the total `J ω + h`
stays `2` on `[0, 4]` while the body rate falls from `1` to `-1`. -/
lemma wheel_exchange_fixture :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => 1 - s / 2) (-1 / 2) t ∧ HasDerivAt (fun s : ℝ => s) 1 t ∧
        2 * (-1 / 2 : ℝ) = 0 - 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 4, 2 * (1 - t / 2) + t = 2 * (1 - 0 / 2) + 0) ∧
      (1 - 4 / 2 : ℝ) ≠ 1 - 0 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    refine ⟨?_, hasDerivAt_id' t, by norm_num⟩
    have h1 := (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id' t).div_const (2 : ℝ))
    have heq : (0 : ℝ) - 1 / 2 = -1 / 2 := by ring
    rw [heq] at h1
    exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => rfl)
  · intro t _
    ring
  · norm_num

/-- Ignoring the momentum limit: the command `u = 1` meets the command limit `umax = 1` at every
time, but from `h(0) = 0` the wheel momentum `h(t) = t` reaches `hmax = 1/4` at `t = 1/4`, so the
command is admissible on `[0, T]`, `T ≥ 0`, exactly when `T ≤ 1/4`, and not on `[0, 1]`. The
reserve `|h(0)| + umax T ≤ hmax` holds with equality at `T = 1/4`, where every command with
`|u| ≤ 1` from `h(0) = 0` is admissible. -/
lemma constCommand_fixture :
    (∀ T : ℝ, 0 ≤ T → (WheelAdmissible 1 (1 / 4) T (fun _ => 1) (fun s => s) ↔ T ≤ 1 / 4)) ∧
      ¬ WheelAdmissible 1 (1 / 4) 1 (fun _ => 1) (fun s => s) ∧
      ∀ u h : ℝ → ℝ, (∀ t ∈ Icc (0 : ℝ) (1 / 4), HasDerivAt h (u t) t) →
        (∀ t ∈ Icc (0 : ℝ) (1 / 4), |u t| ≤ 1) → h 0 = 0 →
          WheelAdmissible 1 (1 / 4) (1 / 4) u h := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    constructor
    · rintro ⟨-, hadm⟩
      have hmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_refl T⟩
      obtain ⟨-, hhT⟩ := hadm T hmem
      have h2 : |T| ≤ 1 / 4 := hhT
      rwa [abs_of_nonneg hT] at h2
    · intro hle
      refine ⟨hT, fun t ht => ⟨?_, ?_⟩⟩
      · show |(1 : ℝ)| ≤ 1
        norm_num
      · have h2 : |t| ≤ 1 / 4 := by
          rw [abs_of_nonneg ht.1]
          exact le_trans ht.2 hle
        exact h2
  · rintro ⟨-, hadm⟩
    have hmem : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_refl 1⟩
    obtain ⟨-, hh1⟩ := hadm 1 hmem
    have h2 : |(1 : ℝ)| ≤ 1 / 4 := hh1
    norm_num at h2
  · intro u h hh hu h0
    have hres : |h 0| + 1 * (1 / 4 : ℝ) ≤ 1 / 4 := by
      rw [h0]
      norm_num
    exact wheelAdmissible_of_reserve (by norm_num) hh hu hres

-- The total momentum of the exchange fixture has rate `τ_ext = 0`: `J = 2`, `ω = 1 - t / 2` and
-- `h = t` obey `J ω' = 0 - u` and `h' = u` for `u = 1`.
example (t : ℝ) : HasDerivAt (fun s => 2 * (1 - s / 2) + s) 0 t :=
  hasDerivAt_wheel_totalMomentum (J := 2) (ω' := fun _ => -1 / 2) (u := fun _ => 1)
    (τ := fun _ => 0) (wheel_exchange_fixture.1 t).1 (wheel_exchange_fixture.1 t).2.1
    (wheel_exchange_fixture.1 t).2.2

-- The exchange lemma on the fixture: on `[0, 4]` the total momentum stays `2`, and at `t = 4` the
-- body rate has changed by `-(h(4) - h(0)) / J = -2`.
example : 2 * (1 - 4 / 2 : ℝ) + 4 = 2 * (1 - 0 / 2) + 0 ∧
    (1 - 4 / 2 : ℝ) - (1 - 0 / 2) = -(4 - 0) / 2 :=
  wheel_momentum_exchange (J := 2) (T := 4) (ω := fun s => 1 - s / 2) (ω' := fun _ => -1 / 2)
    (h := fun s => s) (u := fun _ => 1) (τ := fun _ => 0) (by norm_num)
    (fun s _ => (wheel_exchange_fixture.1 s).1) (fun s _ => (wheel_exchange_fixture.1 s).2.1)
    (fun s _ => (wheel_exchange_fixture.1 s).2.2) (fun _ _ => rfl) 4 ⟨by norm_num, le_rfl⟩

-- The input form of the momentum limit for the command `u = 1` from `h(0) = 0`: the momentum is
-- `∫₀ᵗ 1 = t`, so the command is admissible on `[0, 1/4]` for the limits `1` and `1/4`.
example : WheelAdmissible 1 (1 / 4) (1 / 4) (fun _ => 1) (fun s => s) := by
  rw [wheelAdmissible_iff_integral (fun t _ => hasDerivAt_id' t) intervalIntegrable_const]
  refine ⟨by norm_num, fun t ht => ⟨by norm_num, ?_⟩⟩
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, zero_add,
    abs_of_nonneg ht.1]
  exact ht.2

-- The constant-command criterion: the command `-1/2` from `h(0) = 1/8` is admissible on `[0, 3/4]`
-- for the limits `1` and `1/4`, since both endpoint momenta `1/8` and `-1/4` are within the limit.
example : WheelAdmissible 1 (1 / 4) (3 / 4) (fun _ => -1 / 2) (fun s => 1 / 8 - s / 2) := by
  have hh : ∀ t ∈ Set.Icc (0 : ℝ) (3 / 4), HasDerivAt (fun s : ℝ => 1 / 8 - s / 2) (-1 / 2) t :=
    fun t _ => by
      have h1 := ((hasDerivAt_id' t).div_const 2).const_sub (1 / 8 : ℝ)
      convert h1 using 1
      norm_num
  rw [constCommand_admissible_iff (by norm_num) hh]
  norm_num [abs_le]

-- A nonzero constant command reaches the momentum limit whatever the command limit: with the
-- command limit `5`, the command `1` from `h(0) = 0` reaches `|h| = 1/4` at a finite time and is
-- inadmissible on every longer horizon.
example : ∃ Tsat, 0 ≤ Tsat ∧ |Tsat| = 1 / 4 ∧
    ∀ T, Tsat < T → ¬ WheelAdmissible 5 (1 / 4) T (fun _ => 1) (fun s => s) :=
  constCommand_momentum_limit one_ne_zero (fun t _ => hasDerivAt_id' t) (by norm_num)

-- A negative horizon is not a duration: no command is admissible on it, even with the impossible
-- limits `-1`, so admissibility cannot be certified by a negative `T`.
example (u h : ℝ → ℝ) : ¬ WheelAdmissible (-1) (-1) (-1) u h :=
  fun hadm => absurd hadm.1 (by norm_num)

end PhyslibExtTest.Mechanics.AttitudePorts
