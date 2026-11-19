/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.OrbitalPorts

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Mechanics.OrbitalPorts`

Nondimensional states with exact values, center `μ`, position `(1, 0, 0)`:

* a circular state has `a = r` and `|x ⨯₃ v|² = μ r`; a radial state at the same circular speed
  also has `a = r`, but `x ⨯₃ v = 0`;
* a parabolic state has `E = 0`, and the semi-major-axis formula returns the junk value `0`;
* a radial state has `E < 0` and `a > 0` with zero specific angular momentum, so negative energy
  alone does not give an ellipse of nonzero specific angular momentum;
* a prograde tangential impulse on the circular state raises the semi-major axis;
* an impulse with `Δv = -|v|` brings the body to rest, so no orbital plane remains.

Circular-orbit premises for a low Earth orbit in kilometres and seconds,
`μ = 398600.4418 km³/s²`, `R = 6778 km` (about 400 km altitude); the examples hold for every
position and velocity that satisfy the premises:

* the speed lies between `7.66` and `7.67 km/s` and the period between `5550` and `5560 s`;
* the same orbit in metres satisfies the premises with `μ` and `R` rescaled, while time in hours
  with `μ` left in `km³/s²` does not;
* the state at rest at the center meets the trajectory clauses at `R = 0`, and only the
  positivity clause rejects it.

Spatial frame map with the quarter turn about the third axis, `quarterTurnZ`:

* the planar point `1 + 2 i` has body components `(1, 2, 0)` and inertial components
  `(-2, 1, 0)`; its squared length stays `5`, and it is orthogonal to the plane normal, which
  the quarter turn leaves at `(0, 0, 1)`;
* the planar path `s ↦ s (1 + 2 i)` has inertial velocity `(-2, 1, 0)`;
* for every orbit that satisfies the premises with `μ = 4` and `R = 1`, the spatial position
  stays at distance `1` from the center and the spatial velocity has derivative `-4 X`.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.OrbitalPorts

open _root_.OrbitalPorts Matrix

-- A nonzero circular state: `μ = 4`, `x = (1, 0, 0)`, `v = (0, 2, 0)` has `r = 1` and
-- `a = r = 1`.
example :
    radius ![1, 0, 0] = 1 ∧ semiMajorAxis 4 ![1, 0, 0] ![0, 2, 0] = 1 := by
  have hr : radius ![1, 0, 0] = 1 := by
    unfold radius
    norm_num [dotProduct, Fin.sum_univ_three]
  have ha : semiMajorAxis 4 ![1, 0, 0] ![0, 2, 0] = 1 := by
    unfold semiMajorAxis specificEnergy speedSq radius
    norm_num [dotProduct, Fin.sum_univ_three]
  exact ⟨hr, ha⟩

-- The parabolic state `μ = 2`, `x = (1, 0, 0)`, `v = (0, 2, 0)` has `E = 0`, and the
-- semi-major-axis formula returns the junk value `0`.
example :
    specificEnergy 2 ![1, 0, 0] ![0, 2, 0] = 0 ∧ semiMajorAxis 2 ![1, 0, 0] ![0, 2, 0] = 0 := by
  have hE : specificEnergy 2 ![1, 0, 0] ![0, 2, 0] = 0 := by
    unfold specificEnergy speedSq radius
    norm_num [dotProduct, Fin.sum_univ_three]
  have ha : semiMajorAxis 2 ![1, 0, 0] ![0, 2, 0] = 0 := by
    unfold semiMajorAxis specificEnergy speedSq radius
    norm_num [dotProduct, Fin.sum_univ_three]
  exact ⟨hE, ha⟩

-- Negative energy without an ellipse of nonzero specific angular momentum: the radial state
-- `μ = 1`, `x = (1, 0, 0)`, `v = (1/2, 0, 0)` has `E = -7/8`, `a = 4/7` and `x ⨯₃ v = 0`.
example :
    specificEnergy 1 ![1, 0, 0] ![1 / 2, 0, 0] = -7 / 8 ∧
      semiMajorAxis 1 ![1, 0, 0] ![1 / 2, 0, 0] = 4 / 7 ∧
      ![1, 0, 0] ⨯₃ ![1 / 2, 0, 0] = (0 : Fin 3 → ℝ) := by
  have hE : specificEnergy 1 ![1, 0, 0] ![1 / 2, 0, 0] = -7 / 8 := by
    unfold specificEnergy speedSq radius
    norm_num [dotProduct, Fin.sum_univ_three]
  have ha : semiMajorAxis 1 ![1, 0, 0] ![1 / 2, 0, 0] = 4 / 7 := by
    unfold semiMajorAxis specificEnergy speedSq radius
    norm_num [dotProduct, Fin.sum_univ_three]
  have hc : (![1, 0, 0] : Fin 3 → ℝ) ⨯₃ ![1 / 2, 0, 0] = (0 : Fin 3 → ℝ) := by
    simp [cross_apply]
  exact ⟨hE, ha, hc⟩

-- A prograde tangential impulse `Δv = 1/2` on the circular fixture: speed `5/2` and
-- `a' = 16/7 > r = 1`.
example :
    speedSq (tangentialImpulse ![0, 2, 0] (1 / 2)) = 25 / 4 ∧
      semiMajorAxis 4 ![1, 0, 0] (tangentialImpulse ![0, 2, 0] (1 / 2)) = 16 / 7 := by
  have hv_ne : (![0, 2, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have hc := congrFun h 1
    simp at hc
  have hs4 : speedSq ![0, 2, 0] = 4 := by
    unfold speedSq
    norm_num [dotProduct, Fin.sum_univ_three]
  have hsqrt : Real.sqrt (speedSq ![0, 2, 0]) = 2 := by
    rw [hs4, show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hS := speedSq_tangentialImpulse hv_ne (1 / 2)
  rw [hsqrt] at hS
  have hs_imp : speedSq (tangentialImpulse ![0, 2, 0] (1 / 2)) = 25 / 4 := by
    calc speedSq (tangentialImpulse ![0, 2, 0] (1 / 2)) = (2 + 1 / 2 : ℝ) ^ 2 := hS
      _ = 25 / 4 := by norm_num
  have hr1 : radius ![1, 0, 0] = 1 := by
    unfold radius
    norm_num [dotProduct, Fin.sum_univ_three]
  have ha : semiMajorAxis 4 ![1, 0, 0] (tangentialImpulse ![0, 2, 0] (1 / 2)) = 16 / 7 := by
    unfold semiMajorAxis specificEnergy
    rw [hs_imp, hr1]
    norm_num
  exact ⟨hs_imp, ha⟩

-- The circular fixture is transverse, `x ⬝ᵥ v = 0`, so `semiMajorAxis_of_circular` applies and
-- gives the circular specific angular momentum `|x ⨯₃ v|² = μ r = 4`.
example : (![1, 0, 0] ⨯₃ ![0, 2, 0]) ⬝ᵥ (![1, 0, 0] ⨯₃ ![0, 2, 0] : Fin 3 → ℝ) = 4 := by
  have hr : radius ![1, 0, 0] = 1 := by
    unfold radius
    norm_num [dotProduct, Fin.sum_univ_three]
  have hv : speedSq ![0, 2, 0] = 4 / radius ![1, 0, 0] := by
    rw [hr]
    unfold speedSq
    norm_num [dotProduct, Fin.sum_univ_three]
  have hperp : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 2, 0] = 0 := by
    norm_num [dotProduct, Fin.sum_univ_three]
  have h := (semiMajorAxis_of_circular (by norm_num) (by rw [hr]; norm_num) hv hperp).2.2
  rw [h, hr]
  norm_num

-- Circular speed alone does not make a state circular: `μ = 1`, `x = (1, 0, 0)` and
-- `v = (1, 0, 0)` have `|v|² = μ / r` and `a = r = 1`, but `x ⨯₃ v = 0`, a radial state.
example :
    speedSq ![1, 0, 0] = 1 / radius ![1, 0, 0] ∧ semiMajorAxis 1 ![1, 0, 0] ![1, 0, 0] = 1 ∧
      ![1, 0, 0] ⨯₃ ![1, 0, 0] = (0 : Fin 3 → ℝ) := by
  have hr : radius ![1, 0, 0] = 1 := by
    unfold radius
    norm_num [dotProduct, Fin.sum_univ_three]
  have hv : speedSq ![1, 0, 0] = 1 / radius ![1, 0, 0] := by
    rw [hr]
    unfold speedSq
    norm_num [dotProduct, Fin.sum_univ_three]
  refine ⟨hv, ?_, cross_self _⟩
  rw [(semiMajorAxis_of_circularSpeed one_pos (by rw [hr]; exact one_pos) hv).2, hr]

-- An impulse can leave no orbital plane: for `x = (1, 0, 0)`, `v = (0, 1, 0)` and `Δv = -1`
-- the specific angular momentum `x ⨯₃ v` is nonzero, but the factor `1 + Δv / |v|` is `0`, so
-- the body is at rest after the impulse.
example :
    (![1, 0, 0] ⨯₃ ![0, 1, 0] : Fin 3 → ℝ) ≠ 0 ∧ tangentialImpulse ![0, 1, 0] (-1) = 0 := by
  have hs : Real.sqrt (speedSq ![0, 1, 0]) = 1 := by
    unfold speedSq
    norm_num [dotProduct, Fin.sum_univ_three]
  refine ⟨?_, ?_⟩
  · intro h
    have h2 := congrFun h 2
    simp [cross_apply] at h2
  · unfold tangentialImpulse
    rw [hs]
    ext i
    fin_cases i <;> simp

-- A nonzero circle: the speed lies between `7.66` and `7.67 km/s` and the period between
-- `5550` and `5560 s` (about 92.6 min).
example {r v : ℝ → ℂ} (h : IsCircularOrbit 398600.4418 6778 r v) (t : ℝ) :
    7.66 < ‖v t‖ ∧ ‖v t‖ < 7.67 ∧
      5550 < 2 * Real.pi * 6778 / ‖v t‖ ∧ 2 * Real.pi * 6778 / ‖v t‖ < 5560 := by
  have hv_eq := h.norm_vel_eq t
  have hlo : 7.66 < Real.sqrt (398600.4418 / 6778) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hhi : Real.sqrt (398600.4418 / 6778) < 7.67 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  rw [hv_eq]
  have hvpos : (0 : ℝ) < Real.sqrt (398600.4418 / 6778) :=
    lt_trans (by norm_num) hlo
  refine ⟨hlo, hhi, ?_, ?_⟩
  · rw [lt_div_iff₀ hvpos]
    have e1 : 5550 * Real.sqrt (398600.4418 / 6778) < 5550 * 7.67 :=
      mul_lt_mul_of_pos_left hhi (by norm_num)
    have e2 : (5550 : ℝ) * 7.67 < 2 * 3.1415 * 6778 := by norm_num
    have e3 : 2 * 3.1415 * 6778 < 2 * Real.pi * 6778 := by
      have hmul : 3.1415 * 6778 < Real.pi * 6778 :=
        mul_lt_mul_of_pos_right Real.pi_gt_d4 (by norm_num)
      linarith
    linarith
  · rw [div_lt_iff₀ hvpos]
    have e1 : 2 * Real.pi * 6778 < 2 * 3.1416 * 6778 := by
      have hmul : Real.pi * 6778 < 3.1416 * 6778 :=
        mul_lt_mul_of_pos_right Real.pi_lt_d4 (by norm_num)
      linarith
    have e2 : (2 : ℝ) * 3.1416 * 6778 < 5560 * 7.66 := by norm_num
    have e3 : 5560 * 7.66 < 5560 * Real.sqrt (398600.4418 / 6778) :=
      mul_lt_mul_of_pos_left hlo (by norm_num)
    linarith

-- Consistent units: the same orbit in metres is a circular orbit with
-- `μ = 398600441800000 m³/s²` and `R = 6778000 m`.
example {r v : ℝ → ℂ} (h : IsCircularOrbit 398600.4418 6778 r v) :
    IsCircularOrbit 398600441800000 6778000 (fun τ => (1000 : ℝ) • r τ)
      (fun τ => (1000 : ℝ) • v τ) := by
  have hU := h.unitChange (l := 1000) (s := 1) (by norm_num) (by norm_num)
  simp only [div_one] at hU
  convert hU using 2 <;> norm_num

-- Wrong time units: the same orbit with time in hours but `μ` left in `km³/s²` is rejected.
example {r v : ℝ → ℂ} (h : IsCircularOrbit 398600.4418 6778 r v) :
    ¬ IsCircularOrbit 398600.4418 6778 (fun τ => r (3600 * τ))
      (fun τ => (3600 : ℝ) • v (3600 * τ)) := by
  have hN := h.not_wrong_time_unit (l := 1) (s := 1 / 3600) (by norm_num) (by norm_num)
    (by norm_num)
  have e1 : (1 : ℝ) ^ 3 * 398600.4418 = 398600.4418 := by norm_num
  have e2 : (1 : ℝ) * 6778 = 6778 := by norm_num
  have e3 : (fun τ : ℝ => (1 : ℝ) • r (τ / (1 / 3600))) = (fun τ => r (3600 * τ)) := by
    funext τ
    rw [one_smul]
    congr 1
    field_simp
  have e4 : (fun τ : ℝ => ((1 : ℝ) / (1 / 3600)) • v (τ / (1 / 3600)))
      = (fun τ => (3600 : ℝ) • v (3600 * τ)) := by
    funext τ
    rw [show (1 : ℝ) / (1 / 3600) = 3600 by norm_num]
    congr 1
    field_simp
  rw [e1, e2, e3, e4] at hN
  exact hN

-- Collision radius zero: the state at rest at the center satisfies the trajectory clauses with
-- `R = 0` (Lean's `μ / 0 = 0` makes the acceleration vanish), so the positivity clause is what
-- rejects it.
example (μ : ℝ) :
    (∀ t : ℝ, ‖(0 : ℂ)‖ = 0 ∧ HasDerivAt (fun _ : ℝ => (0 : ℂ)) 0 t ∧
      HasDerivAt (fun _ : ℝ => (0 : ℂ)) (-(μ / ‖(0 : ℂ)‖ ^ 3) • (0 : ℂ)) t) ∧
      ¬ IsCircularOrbit μ 0 (fun _ => 0) (fun _ => 0) := by
  refine ⟨?_, not_isCircularOrbit_zero_radius μ _ _⟩
  intro t
  refine ⟨norm_zero, hasDerivAt_const t 0, ?_⟩
  simp only [smul_zero]
  exact hasDerivAt_const t 0


open _root_.Units.EngineeringFrames (bodyToInertialVec quarterTurnZ rotZ_degToRad_ninety)

-- Mapped components: the planar point `1 + 2 i` has body components `(1, 2, 0)`, and the quarter
-- turn about the third axis maps it to the inertial components `(-2, 1, 0)`.
example (t : ℝ) :
    planarToBody (1 + 2 * Complex.I) = ![1, 2, 0] ∧
      spatialState quarterTurnZ (fun _ => 1 + 2 * Complex.I) t = ![-2, 1, 0] := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  have hp : planarToBody (1 + 2 * Complex.I) = ![1, 2, 0] := by
    ext i
    fin_cases i <;> simp [planarToBody]
  refine ⟨hp, ?_⟩
  simp only [spatialState, bodyToInertialVec, hp, hq]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

-- Length and plane: the mapped point keeps the squared length `‖1 + 2 i‖ ^ 2 = 5`, the quarter
-- turn leaves the plane normal at `(0, 0, 1)`, and the mapped point is orthogonal to it.
example (t : ℝ) :
    spatialState quarterTurnZ (fun _ => 1 + 2 * Complex.I) t ⬝ᵥ
        spatialState quarterTurnZ (fun _ => 1 + 2 * Complex.I) t = 5 ∧
      bodyToInertialVec quarterTurnZ ![0, 0, 1] = ![0, 0, 1] ∧
      spatialState quarterTurnZ (fun _ => 1 + 2 * Complex.I) t ⬝ᵥ ![0, 0, 1] = 0 := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  have hn : bodyToInertialVec quarterTurnZ ![0, 0, 1] = ![0, 0, 1] := by
    simp only [bodyToInertialVec, hq]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨?_, hn, ?_⟩
  · rw [dotProduct_spatialState, Complex.sq_norm, Complex.normSq_apply]
    norm_num
  · rw [← hn]
    exact spatialState_dotProduct_normal quarterTurnZ _ t

-- Velocity: the planar path `s ↦ s (1 + 2 i)` has velocity `1 + 2 i`, so its image under the
-- quarter turn has velocity `(-2, 1, 0)` at every time.
example (t : ℝ) :
    HasDerivAt (spatialState quarterTurnZ fun s => (s : ℂ) * (1 + 2 * Complex.I)) ![-2, 1, 0]
      t := by
  have hq : (quarterTurnZ : Matrix (Fin 3) (Fin 3) ℝ) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    rotZ_degToRad_ninety
  have hz : HasDerivAt (fun s : ℝ => (s : ℂ) * (1 + 2 * Complex.I)) (1 + 2 * Complex.I) t := by
    simpa using (hasDerivAt_id t).ofReal_comp.mul_const (1 + 2 * Complex.I)
  have hw : bodyToInertialVec quarterTurnZ (planarToBody (1 + 2 * Complex.I)) = ![-2, 1, 0] := by
    simp only [bodyToInertialVec, planarToBody, hq]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [← hw]
  exact hasDerivAt_spatialState quarterTurnZ hz

-- Inverse-square law in inertial components: for every orbit that satisfies the premises with
-- `μ = 4` and `R = 1`, the spatial position in the quarter-turn frame stays at distance `1` from
-- the center, and the spatial velocity has derivative `-4 X`.
example {r v : ℝ → ℂ} (h : IsCircularOrbit 4 1 r v) (t : ℝ) :
    spatialState quarterTurnZ r t ⬝ᵥ spatialState quarterTurnZ r t = 1 ∧
      HasDerivAt (spatialState quarterTurnZ v) ((-4 : ℝ) • spatialState quarterTurnZ r t) t := by
  have hd : spatialState quarterTurnZ r t ⬝ᵥ spatialState quarterTurnZ r t = 1 := by
    rw [h.dotProduct_spatialState]
    norm_num
  refine ⟨hd, ?_⟩
  have hv := h.hasDerivAt_spatialVelocity quarterTurnZ t
  rw [hd, Real.sqrt_one] at hv
  simpa using hv

end PhyslibExtTest.Mechanics.OrbitalPorts
