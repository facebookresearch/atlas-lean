/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Signals.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.NormNum

open ControlTheory

-- The identity system is causal: agreement on `s ≤ t` includes `s = t`.
example : IsCausal (LinearMap.id : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ)) := by
  intro t x y h
  exact h t le_rfl

-- Scalar gain is causal.
example : IsCausal ((3 : ℝ) • (LinearMap.id : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ))) := by
  intro t x y h
  simp [h t le_rfl]

-- The identity system is time invariant.
example : IsTimeInvariant (LinearMap.id : (ℤ → ℝ) →ₗ[ℝ] (ℤ → ℝ)) := by
  intro a
  ext x t
  simp

-- The unit delay on `ℤ` is causal: its output at `t` reads the input at
-- `t - 1 ≤ t`.
example : IsCausal (shiftₗ ℝ ℝ (1 : ℤ)) := by
  intro t x y h
  simp only [shiftₗ_apply]
  exact h (t - 1) (by omega)

-- Every fixed delay on `ℤ` is time invariant, by the shift group law.
example (a : ℤ) : IsTimeInvariant (shiftₗ ℝ ℝ a) := by
  intro b
  rw [shiftₗ_comp, shiftₗ_comp, add_comm]

-- The advance `shiftₗ ℝ ℝ (-1)` on `ℤ` is not causal: it reads `x 1` at
-- time `0`, so two inputs agreeing up to time `0` but differing at `1` get
-- different outputs at `0`.
example : ¬ IsCausal (shiftₗ ℝ ℝ (-1 : ℤ)) := by
  intro h
  have h01 := h 0 (fun _ => (0 : ℝ)) (fun t => if t = (1 : ℤ) then (1 : ℝ) else 0)
    (by
      intro s hs
      have hs1 : s ≠ (1 : ℤ) := by omega
      simp [hs1])
  simp only [shiftₗ_apply] at h01
  norm_num at h01

-- A series of two delays is the delay by the sum.
example : ((shiftₗ ℝ ℝ (1 : ℤ)).comp (shiftₗ ℝ ℝ (2 : ℤ))) = shiftₗ ℝ ℝ (3 : ℤ) := by
  rw [shiftₗ_comp]
  norm_num

-- Shifting by zero is the identity system (application form).
example (x : ℤ → ℝ) (t : ℤ) : shiftₗ ℝ ℝ (0 : ℤ) x t = x t := by
  simp

-- `shiftₗ_zero` needs no commutativity: it holds with time domain the
-- noncommutative additive group of permutations of `Fin 3` (where the
-- composition law `shiftₗ_comp` fails). Regression case for the
-- `AddGroup` generality of `shiftₗ_zero`.
example : shiftₗ ℝ ℝ (0 : Additive (Equiv.Perm (Fin 3))) = LinearMap.id :=
  shiftₗ_zero

-- The reversed-order composition law at the same noncommutative time
-- group: composing the shift by `b` with the shift by `a` is the shift
-- by `b + a` (the `a + b` order would be false here).
example (a b : Additive (Equiv.Perm (Fin 3))) :
    (shiftₗ ℝ ℝ a).comp (shiftₗ ℝ ℝ b) = shiftₗ ℝ ℝ (b + a) :=
  shiftₗ_comp' a b

#print axioms shiftₗ_apply
#print axioms shiftₗ_zero
#print axioms shiftₗ_comp'
#print axioms shiftₗ_comp
#print axioms IsCausal.comp
#print axioms IsCausal.add
#print axioms IsTimeInvariant.comp
#print axioms IsTimeInvariant.add
