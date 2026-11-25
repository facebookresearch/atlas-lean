/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.ClassicalMechanics.RelativeOscillatorPlant
import PhyslibExt.ClassicalMechanics.RelativeOscillator
import PhyslibExt.Mechanics.ModalResponse
import PhyslibExt.Mechanics.OscillatorResponse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Base-excited plant checks

Concrete consumers of `PhyslibExt.ClassicalMechanics.RelativeOscillatorPlant`: the public
trajectory correspondence in matrix and owner-record form, the displacement output, the
`toMatrix` round trip, both directions of the bridge to the relative-oscillator equation,
the opposite signs of the force and base-acceleration channels with a wrong-sign control,
agreement with the phase operator on `ℝ × ℝ`, a free oscillation with nonzero initial
velocity, and the failure of the correspondence at `m = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Plant, owner record and trajectory correspondence
- B. Signs, phase-space agreement, witnesses and controls

## iv. References

- `PhyslibExt.ClassicalMechanics.RelativeOscillatorPlant`
-/

open RelativeOscillator
open Matrix

/-! ## A. Plant, owner record and trajectory correspondence -/

/-- The public statement shape of the trajectory correspondence. -/
example {m c k : ℝ} (hm : 0 < m) (u v pf ya : ℝ → ℝ) :
    (∀ t, HasDerivAt (fun s => ![u s, v s])
        (baseExcitedA m c k *ᵥ ![u t, v t] + baseExcitedB m *ᵥ ![pf t, ya t]) t) ↔
      ∀ t, HasDerivAt u (v t) t ∧
        ∃ a, HasDerivAt v a t ∧ m * a + c * v t + k * u t = pf t - m * ya t :=
  baseExcited_trajectory_iff hm u v pf ya

/-- Owner-record form: the inline trajectory condition on `baseExcitedPlant` is the
trajectory correspondence. -/
example {m c k : ℝ} (hm : 0 < m) (u v pf ya : ℝ → ℝ) :
    (∀ t, HasDerivAt (fun s => ![u s, v s])
        ((baseExcitedPlant m c k).A ![u t, v t] +
          (baseExcitedPlant m c k).B ![pf t, ya t]) t) ↔
      ∀ t, HasDerivAt u (v t) t ∧
        ∃ a, HasDerivAt v a t ∧ m * a + c * v t + k * u t = pf t - m * ya t := by
  simp only [baseExcitedPlant, ControlTheory.StateSpaceCoeffs.ofMatrix_A_apply,
    ControlTheory.StateSpaceCoeffs.ofMatrix_B_apply]
  exact baseExcited_trajectory_iff hm u v pf ya

/-- Owner-record output: the output is the relative displacement, with no feedthrough. -/
example {m c k u v p a : ℝ} :
    (baseExcitedPlant m c k).C ![u, v] + (baseExcitedPlant m c k).D ![p, a] = ![u] := by
  funext i
  fin_cases i
  simp [baseExcitedPlant, ControlTheory.StateSpaceCoeffs.ofMatrix_C_apply,
    ControlTheory.StateSpaceCoeffs.ofMatrix_D_apply, baseExcitedC, baseExcitedD,
    Matrix.mulVec, dotProduct]

/-- The `toMatrix` round trip recovers the four plant matrices. -/
example {m c k : ℝ} :
    ControlTheory.StateSpaceCoeffs.toMatrix (baseExcitedPlant m c k) =
      (baseExcitedA m c k, baseExcitedB m, baseExcitedC, baseExcitedD) := by
  simp [baseExcitedPlant, ControlTheory.StateSpaceCoeffs.toMatrix_ofMatrix]

/-- Relative-oscillator contract, forward: absolute-coordinate data satisfying the balance
at every time give a plant trajectory in relative coordinates. -/
example {m c k : ℝ} (hm : 0 < m) {x y u xv yv xa ya pf : ℝ → ℝ}
    (hu : ∀ t, u t = x t - y t)
    (hx : ∀ t, HasDerivAt x (xv t) t) (hy : ∀ t, HasDerivAt y (yv t) t)
    (hxv : ∀ t, HasDerivAt xv (xa t) t) (hyv : ∀ t, HasDerivAt yv (ya t) t)
    (habs : ∀ t, m * xa t + c * (xv t - yv t) + k * (x t - y t) = pf t) :
    ∀ t, HasDerivAt (fun s => ![u s, xv s - yv s])
      (baseExcitedA m c k *ᵥ ![u t, xv t - yv t] + baseExcitedB m *ᵥ ![pf t, ya t]) t :=
  (baseExcited_trajectory_iff hm u (fun s => xv s - yv s) pf ya).mpr fun t =>
    let h := relative_equation_and_energy x y u xv yv xa ya pf hu t (hx t) (hy t) (hxv t)
      (hyv t) (habs t)
    ⟨h.1, xa t - ya t, h.2.1, h.2.2.1⟩

/-- Relative-oscillator contract, reverse: a plant trajectory in relative coordinates gives
back the relative equation with acceleration `xa - ya`. -/
example {m c k : ℝ} (hm : 0 < m) {u xv yv xa ya pf : ℝ → ℝ} {t : ℝ}
    (hplant : ∀ s, HasDerivAt (fun r => ![u r, xv r - yv r])
      (baseExcitedA m c k *ᵥ ![u s, xv s - yv s] + baseExcitedB m *ᵥ ![pf s, ya s]) s)
    (hxv : HasDerivAt xv (xa t) t) (hyv : HasDerivAt yv (ya t) t) :
    HasDerivAt u (xv t - yv t) t ∧
      m * (xa t - ya t) + c * (xv t - yv t) + k * u t = pf t - m * ya t := by
  have hrel := (baseExcited_trajectory_iff hm u (fun s => xv s - yv s) pf ya).mp hplant t
  obtain ⟨hu, a, hv, heq⟩ := hrel
  have ha : a = xa t - ya t := hv.unique (by simpa only [Pi.sub_def] using hxv.sub hyv)
  rw [ha] at heq
  exact ⟨hu, heq⟩

/-! ## B. Signs, phase-space agreement, witnesses and controls -/

/-- Channel signs: the force channel enters with `+1 / m`, the base-acceleration channel
with `-1`, so `B *ᵥ (m a_g, a_g) = 0`; the wrong sign on the base channel breaks the
cancellation. -/
example {m : ℝ} (hm : 0 < m) :
    0 < baseExcitedB m 1 0 ∧ baseExcitedB m 1 1 < 0 ∧
      (∀ ag : ℝ, baseExcitedB m *ᵥ ![m * ag, ag] = 0) ∧
      !![0, 0; 1 / m, 1] *ᵥ ![m * 1, (1 : ℝ)] ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h10 : baseExcitedB m 1 0 = 1 / m := by simp [baseExcitedB]
    rw [h10]
    exact div_pos one_pos hm
  · simp [baseExcitedB]
  · intro ag
    funext i
    fin_cases i <;> simp [baseExcitedB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp [hm.ne'] <;> ring
  · intro h
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
    rw [inv_mul_cancel₀ hm.ne'] at h1
    norm_num at h1

/-- The plant matrix `A` is the phase operator on `ℝ × ℝ`, read componentwise. -/
example (m c k x v : ℝ) :
    PhyslibExt.Mechanics.OscillatorResponse.phaseOperator m c k (x, v) =
      ((baseExcitedA m c k *ᵥ ![x, v]) 0, (baseExcitedA m c k *ᵥ ![x, v]) 1) := by
  refine Prod.ext ?_ ?_ <;>
    simp [PhyslibExt.Mechanics.OscillatorResponse.phaseOperator, baseExcitedA, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

/-- The force column of `B` is the phase forcing on `ℝ × ℝ`, read componentwise. -/
example (m F Ω t : ℝ) :
    PhyslibExt.Mechanics.OscillatorResponse.phaseForcing m F Ω t =
      ((baseExcitedB m *ᵥ ![F * Real.cos (Ω * t), 0]) 0,
        (baseExcitedB m *ᵥ ![F * Real.cos (Ω * t), 0]) 1) := by
  refine Prod.ext ?_ ?_ <;>
    simp [PhyslibExt.Mechanics.OscillatorResponse.phaseForcing, baseExcitedB, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] <;> ring

/-- Nonzero initial velocity: the undamped free oscillation with `q (0) = q₀` and
`q' (0) = v₀` is a plant trajectory from the initial state `(q₀, v₀)`. -/
example {m k q₀ v₀ : ℝ} (hm : 0 < m) (hk : 0 < k) :
    (∀ t, HasDerivAt
        (fun s => ![PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀ s,
          deriv (PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀) s])
        (baseExcitedA m 0 k *ᵥ
            ![PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀ t,
              deriv (PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀) t] +
          baseExcitedB m *ᵥ ![0, 0]) t) ∧
      ![PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀ 0,
          deriv (PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀) 0] =
        ![q₀, v₀] := by
  obtain ⟨hC, heq, hq0, hv0⟩ :=
    PhyslibExt.Mechanics.ModalResponse.modalCoordinate_solves
      (div_nonneg hk.le hm.le) q₀ v₀
  have hm' : m ≠ 0 := ne_of_gt hm
  have h1 : ∀ t, HasDerivAt (PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀)
      (deriv (PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀) t) t :=
    fun t => DifferentiableAt.hasDerivAt (ContDiff.differentiable hC (by norm_num) t)
  have h2 : ∀ t, HasDerivAt
      (deriv (PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀))
      (deriv (deriv (PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀)) t) t :=
    fun t => DifferentiableAt.hasDerivAt (ContDiff.differentiable_deriv_two hC t)
  refine ⟨?_, ?_⟩
  · refine (baseExcited_trajectory_iff hm _ _ 0 0).mpr fun t => ⟨h1 t, _, h2 t, ?_⟩
    have h := heq t
    have hmk : m * (k / m) = k := mul_div_cancel₀ k hm'
    simp only [Pi.zero_apply, mul_zero, sub_zero, zero_mul, add_zero]
    linear_combination m * h -
      PhyslibExt.Mechanics.ModalResponse.modalCoordinate (k / m) q₀ v₀ t * hmk
  · rw [hq0, hv0]

/-- Invalid control at `m = 0`: for the zero state with unit base acceleration the
relative-equation side holds (everything is `0 = 0`) but the plant side demands the
constant zero curve to have derivative `(0, -1)`, so the correspondence fails. -/
example : ¬ ((∀ t, HasDerivAt (fun _ : ℝ => ![0, 0])
        (baseExcitedA 0 0 0 *ᵥ ![0, 0] + baseExcitedB 0 *ᵥ ![0, 1]) t) ↔
      ∀ t, HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t ∧
        ∃ a, HasDerivAt (fun _ : ℝ => (0 : ℝ)) a t ∧ (0 : ℝ) * a + 0 * 0 + 0 * 0 = 0 - 0 * 1) := by
  intro h
  have hR : ∀ t, HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t ∧
      ∃ a, HasDerivAt (fun _ : ℝ => (0 : ℝ)) a t ∧ (0 : ℝ) * a + 0 * 0 + 0 * 0 = 0 - 0 * 1 :=
    fun t => ⟨hasDerivAt_const t 0, 0, hasDerivAt_const t 0, by norm_num⟩
  have hL := h.mpr hR 0
  have hc : HasDerivAt (fun _ : ℝ => ![(0 : ℝ), 0]) 0 0 := hasDerivAt_const 0 _
  have hun := hL.unique hc
  have h1 := congrFun hun 1
  simp [baseExcitedA, baseExcitedB] at h1
