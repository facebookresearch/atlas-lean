/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.LinearAlgebra.Matrix.Notation
public import MathlibExt.ControlTheory.StateSpace.Coefficients

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Base-excited oscillator as a state-space plant

For a base-excited oscillator in relative coordinates, the curve `(u, u')` is a trajectory
of the linear plant with matrices `A = !![0, 1; -(k / m), -(c / m)]` and
`B = !![0, 0; 1 / m, -1]` exactly when `u` solves the relative equation
`m u'' + c u' + k u = p - m a_g`.

## i. Overview

One relative translational degree of freedom with constant mass `m`, viscous damping `c`
and stiffness `k`. The base moves with a prescribed acceleration `ya t` (the ground
acceleration `a_g`), and an applied force `pf t` acts on the mass. `u = x - y` is the
displacement of the mass relative to the base, `v` the relative velocity and `a` the
relative acceleration. The relative equation is the merged shape of
`RelativeOscillator.relative_equation_and_energy`
(`PhyslibExt/ClassicalMechanics/RelativeOscillator.lean`):
`m * a + c * v + k * u = pf - m * ya`, with `v = u'` and `a = u''`.

State `(u, u')` in `Fin 2 → ℝ`, written `![u t, v t]` (index 0 the relative displacement,
index 1 the relative velocity). Input `(p, a_g)` in `Fin 2 → ℝ`, written `![pf t, ya t]`
(index 0 the applied force, index 1 the base acceleration). Output `u` in `Fin 1 → ℝ`.
Dividing the relative equation by the fixed positive mass `m` gives the two first-order
rows `u' = v` and `v' = -(k / m) u - (c / m) v + (1 / m) p - a_g`. The plant matrices are
`A = !![0, 1; -(k / m), -(c / m)]`, `B = !![0, 0; 1 / m, -1]`, `C = !![1, 0]` and `D = 0`.

Signs: the forcing channel enters the velocity row with `+1 / m` and the base channel
with `-1`; a positive base acceleration acts on the relative coordinate as the effective
force `-m * a_g`. Units (any consistent set, e.g. SI): `pf` a force, `ya` an acceleration,
`k / m` a squared angular frequency, `c / m` a rate, `1 / m` an inverse mass. Physical
domain `m > 0`, `c ≥ 0`, `k > 0`. Only `0 < m` is a premise; the identities hold for all
real `c` and `k`.

Trajectory semantics (API lock): the owner record is `ControlTheory.StateSpaceCoeffs`,
built from matrices by `StateSpaceCoeffs.ofMatrix A B C D`
(`MathlibExt/ControlTheory/StateSpace/Coefficients.lean`), whose maps act by
`ofMatrix_A_apply : (ofMatrix A B C D).A x = A *ᵥ x` and
`ofMatrix_B_apply : (ofMatrix A B C D).B u = B *ᵥ u` (likewise `C` and `D`). The owner has
no continuous-time trajectory predicate, so the trajectory condition is stated inline as
in `MathlibExt.Analysis.Control.IsControllableOn`:
`∀ t, HasDerivAt z (S.A (z t) + S.B (w t)) t`. It appears here in its matrix-vector form
`∀ t, HasDerivAt z (A *ᵥ z t + B *ᵥ w t) t`, for all real times `t`.

Totalized division: `k / m`, `c / m` and `1 / m` are `0` at `m = 0`, where the
correspondence fails; every target that uses them assumes `0 < m`. Classical solutions:
each side asks for `HasDerivAt` at every time and nothing more; no continuity of `pf`,
`ya` or `u''` is assumed or concluded.

The scope is the state-space form of the relative equation with its trajectory
correspondence. The focused checks (opposite channel signs, nonzero initial velocity)
and the output map are integration tests. Excluded: a new state-space type or trajectory
predicate, stability or control theorems, numerical integration, existence or uniqueness
of solutions, absolute coordinates, and the producer's energy identity.

## ii. Key results

- `RelativeOscillator.baseExcitedA`, `baseExcitedB`, `baseExcitedC`, `baseExcitedD`,
  `baseExcitedPlant`: the plant matrices and the owner record built from them.
- `RelativeOscillator.baseExcited_trajectory_iff`: plant trajectories are exactly the
  solutions of the relative equation.

## iii. Table of contents

- A. The base-excited plant and its trajectory correspondence

## iv. References

- A. K. Chopra, *Dynamics of Structures: Theory and Applications to Earthquake
  Engineering*, 5th edition, Pearson, 2017, Chapter 6: earthquake excitation in relative
  coordinates.
- `RelativeOscillator.relative_equation_and_energy`
  (`PhyslibExt/ClassicalMechanics/RelativeOscillator.lean`): the relative equation in
  absolute-coordinate form.
- `ControlTheory.StateSpaceCoeffs`
  (`MathlibExt/ControlTheory/StateSpace/Coefficients.lean`): the owner coefficient record.

## A. The base-excited plant and its trajectory correspondence
-/

@[expose] public section

namespace RelativeOscillator

open Matrix

/-- State matrix `!![0, 1; -(k / m), -(c / m)]` of the base-excited oscillator in
the state `(u, u')`: row 0 is `u' = v`, row 1 is the relative equation divided by
`m`. Meaningful for `m > 0`; at `m = 0` the totalized divisions give `0`. On `ℝ × ℝ` this is
the operator of `OscillatorResponse.phaseOperator`. -/
noncomputable def baseExcitedA (m c k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -(k / m), -(c / m)]

/-- Input matrix `!![0, 0; 1 / m, -1]` for the input `(p, a_g)`: the applied force
`p` enters the velocity row with gain `1 / m`, the base acceleration `a_g` with
gain `-1`, and neither enters the displacement row. Meaningful for `m > 0`; with `u / 0 = 0`
the force gain is `0` at `m = 0`. The force channel is the `OscillatorResponse.phaseForcing`
channel on `ℝ × ℝ`. -/
noncomputable def baseExcitedB (m : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 1 / m, -1]

/-- Output matrix `!![1, 0]`: the output is the relative displacement `u`. -/
def baseExcitedC : Matrix (Fin 1) (Fin 2) ℝ :=
  !![1, 0]

/-- Feedthrough matrix `0`: the input does not reach the output directly. -/
def baseExcitedD : Matrix (Fin 1) (Fin 2) ℝ :=
  0


/-- The base-excited oscillator as an owner state-space record: the pinned matrices
assembled by `ControlTheory.StateSpaceCoeffs.ofMatrix`, with state `(u, u')`, input
`(p, a_g)` and output `u`. With `u / 0 = 0`, the entries `k / m`, `c / m` and `1 / m` are `0` at
`m = 0`. -/
noncomputable def baseExcitedPlant (m c k : ℝ) :
    ControlTheory.StateSpaceCoeffs ℝ (Fin 2 → ℝ) (Fin 2 → ℝ) (Fin 1 → ℝ) :=
  ControlTheory.StateSpaceCoeffs.ofMatrix (baseExcitedA m c k) (baseExcitedB m) baseExcitedC
    baseExcitedD

/-- **State-space form of the base-excited oscillator** (trajectory correspondence,
and the physical-to-canonical bridge). Let `m > 0`. The curve `s ↦ (u s, v s)` is a
trajectory of the plant `(baseExcitedA m c k, baseExcitedB m)` driven by the input
`s ↦ (pf s, ya s)` if and only if, at every time `t`, `u` has derivative `v t` and
`v` has a derivative `a` with `m * a + c * v t + k * u t = pf t - m * ya t`. Then
`v = u'` everywhere and `a = u''(t)`, so the right side says that `u` solves the
relative equation `m u'' + c u' + k u = p - m a_g`. For the owner record `S` that
`StateSpaceCoeffs.ofMatrix` builds from the four pinned matrices, the inline
trajectory condition on the owner record (the convention of
`MathlibExt.Analysis.Control.IsControllableOn`; the record itself carries no
trajectory semantics), `∀ t, HasDerivAt z (S.A (z t) + S.B (w t)) t` for
`z = (u, v)` and `w = (pf, ya)`, reduces to the left side by
`simp only [ofMatrix_A_apply, ofMatrix_B_apply]`. Physical domain `m > 0`, `c ≥ 0`,
`k > 0`; the equivalence holds for all real `c` and `k`. -/
theorem baseExcited_trajectory_iff {m c k : ℝ} (hm : 0 < m) (u v pf ya : ℝ → ℝ) :
    (∀ t, HasDerivAt (fun s => ![u s, v s])
        (baseExcitedA m c k *ᵥ ![u t, v t] + baseExcitedB m *ᵥ ![pf t, ya t]) t) ↔
      ∀ t, HasDerivAt u (v t) t ∧
        ∃ a, HasDerivAt v a t ∧ m * a + c * v t + k * u t = pf t - m * ya t := by
  have hm' : m ≠ 0 := ne_of_gt hm
  have h0 : ∀ t, (baseExcitedA m c k *ᵥ ![u t, v t] + baseExcitedB m *ᵥ ![pf t, ya t]) 0
      = v t := by
    intro t
    simp [baseExcitedA, baseExcitedB]
  constructor
  · intro h t
    have hpi := hasDerivAt_pi.mp (h t)
    have hu := hpi 0
    have hv := hpi 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    rw [h0 t] at hu
    refine ⟨hu, (baseExcitedA m c k *ᵥ ![u t, v t] + baseExcitedB m *ᵥ ![pf t, ya t]) 1,
      hv, ?_⟩
    simp only [Pi.add_apply, baseExcitedA, baseExcitedB, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
    field_simp
    ring
  · intro h t
    obtain ⟨hu, a, hv, heq⟩ := h t
    rw [hasDerivAt_pi, Fin.forall_fin_two]
    constructor
    · simp only [Matrix.cons_val_zero, h0 t]
      exact hu
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hFwd : m * (baseExcitedA m c k *ᵥ ![u t, v t]
          + baseExcitedB m *ᵥ ![pf t, ya t]) 1
          + c * v t + k * u t = pf t - m * ya t := by
        simp only [Pi.add_apply, baseExcitedA, baseExcitedB, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
        field_simp
        ring
      have hma : m * a = m * (baseExcitedA m c k *ᵥ ![u t, v t]
          + baseExcitedB m *ᵥ ![pf t, ya t]) 1 := by
        linear_combination heq - hFwd
      have ha : a = (baseExcitedA m c k *ᵥ ![u t, v t]
          + baseExcitedB m *ᵥ ![pf t, ya t]) 1 :=
        mul_left_cancel₀ hm' hma
      rw [← ha]
      exact hv

end RelativeOscillator
