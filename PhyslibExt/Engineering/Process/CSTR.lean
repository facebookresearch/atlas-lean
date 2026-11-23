/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Reactors

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Continuous stirred-tank reactor: explicit solution

## i. Overview

For the well-mixed reactor balance `V * c' = Q * (cin - c) - k * V * c`
with volume `V > 0`, volumetric flow `Q > 0`, and first-order rate constant
`k ≥ 0`, the steady concentration is `css = Q * cin / (Q + k * V)` and the
explicit solution from initial concentration `c0` is
`c(t) = css + (c0 - css) * exp (-(Q / V + k) * t)`. That this profile
satisfies the ODE is `EarthScience.cstr_hasDerivAt`, imported here; this
module adds the named steady value and solution, the exponential error
identity, nonnegativity, and the separated zero-flow cases. The `Q = 0`
batch case and the `Q = k = 0` constant case are separate lemmas, not
divisions by a zero rate.

## ii. Key results

- `CSTR.abs_sub_steady_eq`: the deviation from steady state decays by the
  factor `exp (-(Q / V + k) * t)`.
- `CSTR.solution_nonneg`: nonnegative inlet and initial concentrations give
  a nonnegative solution for `t ≥ 0`.
- `CSTR.solution_hasDerivAt`: the imported ODE statement for `solution`.
- `CSTR.solution_zero_flow` and `CSTR.solution_zero_flow_zero_rate`: the
  separated batch and constant branches.

## iii. Table of contents

- A. Steady state and explicit solution
- B. Error identity and nonnegativity
- C. Zero-flow branches

## iv. References

- O. Levenspiel, *Chemical Reaction Engineering*, 3rd ed., Wiley (1999),
  Chapter 5 (ideal stirred-tank reactor design equation).
- `PhyslibExt/EarthScience/Reactors.lean`: `EarthScience.cstr_hasDerivAt`
  and `EarthScience.cstr_steady_state`, imported here.
-/

@[expose] public section

namespace Engineering.Process.CSTR

/-- Steady concentration `css = Q * cin / (Q + k * V)` for the well-mixed
reactor with volume `V`, volumetric flow `Q`, first-order rate constant `k`,
and inlet concentration `cin`. -/
noncomputable def steady (V Q k cin : ℝ) : ℝ :=
  Q * cin / (Q + k * V)

/-- Explicit solution `c(t) = css + (c0 - css) * exp (-(Q / V + k) * t)` of
`V * c' = Q * (cin - c) - k * V * c` with initial concentration `c0`. -/
noncomputable def solution (V Q k cin c0 : ℝ) (t : ℝ) : ℝ :=
  steady V Q k cin + (c0 - steady V Q k cin) * Real.exp (-(Q / V + k) * t)

/-- The solution is the steady value plus the exponentially decaying
initial deviation, in the same form as the imported reactor theorem. -/
lemma solution_eq (V Q k cin c0 t : ℝ) :
    solution V Q k cin c0 t =
      Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t) := by
  rfl

/-- **Exponential error identity.** The deviation from steady state is the
initial deviation scaled by `exp (-(Q / V + k) * t)`, in absolute value. -/
lemma abs_sub_steady_eq (V Q k cin c0 t : ℝ) :
    |solution V Q k cin c0 t - steady V Q k cin| =
      |c0 - steady V Q k cin| * Real.exp (-(Q / V + k) * t) := by
  have hsub : solution V Q k cin c0 t - steady V Q k cin =
      (c0 - steady V Q k cin) * Real.exp (-(Q / V + k) * t) := by
    unfold solution
    ring
  have hexp : |Real.exp (-(Q / V + k) * t)| = Real.exp (-(Q / V + k) * t) :=
    abs_of_pos (Real.exp_pos _)
  rw [hsub, abs_mul, hexp]

/-- The solution starts at the initial concentration. -/
lemma solution_initial (V Q k cin c0 : ℝ) :
    solution V Q k cin c0 0 = c0 := by
  simp [solution]

/-- The steady concentration is nonnegative for nonnegative inlet
concentration. -/
lemma steady_nonneg {V Q k cin : ℝ} (hV : 0 < V) (hQ : 0 < Q) (hk : 0 ≤ k)
    (hcin : 0 ≤ cin) : 0 ≤ steady V Q k cin := by
  have hpos : 0 < Q + k * V :=
    lt_of_lt_of_le hQ (le_add_of_nonneg_right (mul_nonneg hk hV.le))
  unfold steady
  exact div_nonneg (mul_nonneg hQ.le hcin) hpos.le

/-- Nonnegativity: with `cin, c0 ≥ 0`, the solution stays nonnegative for
`t ≥ 0`; it is a convex combination of `css` and `c0`. -/
lemma solution_nonneg {V Q k cin c0 t : ℝ} (hV : 0 < V) (hQ : 0 < Q)
    (hk : 0 ≤ k) (hcin : 0 ≤ cin) (hc0 : 0 ≤ c0) (ht : 0 ≤ t) :
    0 ≤ solution V Q k cin c0 t := by
  have hcss : 0 ≤ steady V Q k cin := steady_nonneg hV hQ hk hcin
  have hlam : 0 ≤ Q / V + k := add_nonneg (div_pos hQ hV).le hk
  have hexp_pos : 0 < Real.exp (-(Q / V + k) * t) := Real.exp_pos _
  have hexp_le : Real.exp (-(Q / V + k) * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnn : 0 ≤ (Q / V + k) * t := mul_nonneg hlam ht
    have heq : -(Q / V + k) * t = -((Q / V + k) * t) := by ring
    rw [heq]
    exact neg_nonpos.mpr hnn
  have hdecomp : solution V Q k cin c0 t =
      steady V Q k cin * (1 - Real.exp (-(Q / V + k) * t)) +
        c0 * Real.exp (-(Q / V + k) * t) := by
    unfold solution
    ring
  rw [hdecomp]
  exact add_nonneg (mul_nonneg hcss (sub_nonneg.mpr hexp_le))
    (mul_nonneg hc0 hexp_pos.le)

/-- The explicit solution satisfies the reactor ODE; this is the imported
`EarthScience.cstr_hasDerivAt` restated for `solution`. -/
lemma solution_hasDerivAt (V Q k cin c0 t : ℝ) (hV : 0 < V) (hQ : 0 < Q)
    (hk : 0 ≤ k) :
    HasDerivAt (solution V Q k cin c0)
      ((Q / V) * (cin - solution V Q k cin c0 t) -
        k * solution V Q k cin c0 t) t := by
  have h := EarthScience.cstr_hasDerivAt V Q k cin c0 t hV hQ hk
  have hfun : solution V Q k cin c0 = fun t => Q * cin / (Q + k * V) +
      (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t) := by
    funext s
    exact solution_eq V Q k cin c0 s
  have hval : (Q / V) * (cin - solution V Q k cin c0 t) -
      k * solution V Q k cin c0 t =
      (Q / V) * (cin - (Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t))) -
        k * (Q * cin / (Q + k * V) +
        (c0 - Q * cin / (Q + k * V)) * Real.exp (-(Q / V + k) * t)) := by
    rw [solution_eq]
  rw [hval, hfun]
  exact h

set_option linter.unusedVariables false in
/-- Zero-flow case, kept separate from the `Q > 0` formulas: with `Q = 0`
and `k > 0` the reactor is a batch decay `c0 * exp (-k * t)`, for every
inlet value. -/
lemma solution_zero_flow {V k cin c0 t : ℝ} (hV : 0 < V) (hk : 0 < k) :
    solution V 0 k cin c0 t = c0 * Real.exp (-k * t) := by
  have hsteady : steady V 0 k cin = 0 := by
    unfold steady
    simp
  unfold solution
  rw [hsteady]
  simp

/-- No flow and no reaction, kept separate so no decay rate is divided by:
the concentration is constant at `c0`. -/
lemma solution_zero_flow_zero_rate (V cin c0 t : ℝ) :
    solution V 0 0 cin c0 t = c0 := by
  have hsteady : steady V 0 0 cin = 0 := by
    unfold steady
    simp
  unfold solution
  rw [hsteady]
  simp

end Engineering.Process.CSTR
