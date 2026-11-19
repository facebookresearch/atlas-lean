/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.OrbitalPorts

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

end PhyslibExtTest.Mechanics.OrbitalPorts
