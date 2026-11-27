/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.Signals.NatTime
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

open ControlTheory

/-- A finite two-tap pulse used in the examples below. -/
def pulseSignal : ℕ → ℝ := fun n => if n = 0 then 3 else if n = 1 then -2 else 0

-- Zero extension of the pulse: `0` before time `0`, the pulse values
-- at nonnegative times.
example : zeroExt ℝ ℝ pulseSignal (-1) = 0 := by norm_num [pulseSignal]
example : zeroExt ℝ ℝ pulseSignal 0 = 3 := by norm_num [pulseSignal]
example : zeroExt ℝ ℝ pulseSignal 1 = -2 := by norm_num [pulseSignal]
example : zeroExt ℝ ℝ pulseSignal 2 = 0 := by norm_num [pulseSignal]

-- Restriction after zero extension recovers the pulse.
example : restrNat ℝ ℝ (zeroExt ℝ ℝ pulseSignal) = pulseSignal := by
  have h := LinearMap.congr_fun (restrNat_comp_zeroExt (𝕜 := ℝ) (E := ℝ)) pulseSignal
  simpa using h

-- The zero-padded right shift of the pulse.
example : rshiftNat ℝ ℝ pulseSignal 0 = 0 := by simp
example : rshiftNat ℝ ℝ pulseSignal 1 = 3 := by simp [pulseSignal]
example : rshiftNat ℝ ℝ pulseSignal 2 = -2 := by simp [pulseSignal]
example : rshiftNat ℝ ℝ pulseSignal 3 = 0 := by simp [pulseSignal]

-- `rshiftNat` is not the integer-time shift specialized to `ℕ`:
-- truncated subtraction there gives `pulseSignal 0 = 3` at time `0`, where
-- the zero-padded shift gives `0`.
example : rshiftNat ℝ ℝ ≠ shiftₗ ℝ ℝ (1 : ℕ) := by
  intro h
  have h0 : rshiftNat ℝ ℝ pulseSignal 0 = 0 := by simp
  have h1 : shiftₗ ℝ ℝ (1 : ℕ) pulseSignal 0 = 3 := by
    show pulseSignal (0 - 1) = 3
    simp [pulseSignal]
  have h2 := congr_fun (LinearMap.congr_fun h pulseSignal) 0
  rw [h0, h1] at h2
  norm_num at h2

-- Zero signal boundaries.
example : zeroExt ℝ ℝ 0 = 0 := map_zero _
example : rshiftNat ℝ ℝ 0 = 0 := map_zero _

-- The nontriviality hypothesis in `not_surjective_rshiftNat` is
-- necessary: over a subsingleton value type the right shift is
-- surjective.
example {E : Type*} [AddCommMonoid E] [Module ℝ E] [Subsingleton E] :
    Function.Surjective (rshiftNat ℝ E) :=
  fun y => ⟨y, Subsingleton.elim _ _⟩

#print axioms zeroExt_apply
#print axioms zeroExt_apply_natCast
#print axioms zeroExt_injective
#print axioms rshiftNat_apply
#print axioms restrNat_apply
#print axioms restrNat_comp_zeroExt
#print axioms zeroExt_comp_rshiftNat
#print axioms not_surjective_rshiftNat
#print axioms IsCausal.zeroExt_restrNat
