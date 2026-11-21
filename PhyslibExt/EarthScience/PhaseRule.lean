/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.RankNullity

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Gibbs phase rule: the counting identity and an abstract dimension count

The phase-rule count `F = C - P + 2` as an identity and as an abstract rank-nullity count.

## i. Overview

For `C` independent components and `P` phases in a nonreacting regular
equilibrium system with pressure and temperature free, the Gibbs phase rule
gives the freedom count `F = C - P + 2`.

Counting variables against constraints gives the rule: each phase has
`C` mole fractions summing to `1`, so `C - 1` independent compositions
per phase, plus `2` for temperature and pressure, for
`P * (C - 1) + 2` variables. For each of the `C` components, equality of
chemical potential across the `P` phases gives `P - 1` independent
equalities, for `C * (P - 1)` constraints. Subtracting gives
`C - P + 2`.

Counts alone are not a theorem of existence. The dimension form is an
abstract linearized count only: for any surjective linear map `f` from the
`P * (C - 1) + 2`-dimensional variable space onto the `C * (P - 1)`-dimensional
constraint space, the kernel of `f` has dimension `C + 2 - P` by
rank-nullity. Nothing here identifies `f` with the derivative of the
chemical-potential equalities at an equilibrium point, or its kernel with
the tangent space of an equilibrium manifold; such an identification (an
equilibrium constraint map, a point, and its Jacobian) is not formalized.
No equilibrium existence, no empirical validation, and no new framework is
claimed.

## ii. Key results

- `EarthScience.phase_rule_variable_count`: the integer counting identity.
- `EarthScience.phase_rule_finrank`: the abstract linearized count via
  rank-nullity.

## iii. Table of contents

- A. Counting identity
- B. Dimension form

## iv. References

- J. Willard Gibbs, *On the Equilibrium of Heterogeneous Substances*,
  Transactions of the Connecticut Academy of Arts and Sciences 3 (1876),
  108-248, section "On Coexistent Phases of Matter", pp. 152-153: a system of
  `r` coexistent phases, each of which has the same `n` independently variable
  components, "is capable of n + 2 - r variations of phase". Gibbs counts the
  temperature, the pressure, and the `n` component potentials, which take the
  same values in all the phases, subject to one relation (his equation (97))
  per phase. Here `C = n` and `P = r`: the components are independent (no
  reactions among them), temperature and pressure are free, and the
  composition count in the overview gives the same `C - P + 2`.
- `LinearMap.finrank_range_add_finrank_ker` in Mathlib (rank-nullity).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Counting identity -/

/-- Gibbs phase-rule count: with `P` phases and `C` independent components,
there are `P * (C - 1) + 2` variables (compositions plus temperature and
pressure) and `C * (P - 1)` independent chemical-potential equalities, so
the freedom count is `C - P + 2`. -/
theorem phase_rule_variable_count (C P : ℤ) :
    (P * (C - 1) + 2) - (C * (P - 1)) = C - P + 2 := by
  ring

/-! ## B. Dimension form -/

/-- Gibbs phase rule as an abstract linearized count: for any surjective linear
map `f` from the `P * (C - 1) + 2`-dimensional variable space onto the
`C * (P - 1)`-dimensional constraint space, `ker f` has dimension `C + 2 - P`.
This is rank-nullity only: `f` is an arbitrary surjective linear map, not
identified with the derivative of the chemical-potential equalities at an
equilibrium point, and `ker f` is not identified with the tangent space of an
equilibrium manifold. -/
theorem phase_rule_finrank (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P) (hF : P ≤ C + 2)
    (f : (Fin (P * (C - 1) + 2) → ℝ) →ₗ[ℝ] (Fin (C * (P - 1)) → ℝ))
    (hf : Function.Surjective f) :
    Module.finrank ℝ (LinearMap.ker f) = C + 2 - P := by
  have hrr := LinearMap.finrank_range_add_finrank_ker f
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hf
  rw [hrange, Submodule.topEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Fintype.card_fin] at hrr
  have h2 : (Module.finrank ℝ (LinearMap.ker f) : ℤ) = (C : ℤ) + 2 - P := by
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hrr
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hP, Nat.cast_sub hC] at hcast
    linear_combination hcast
  have h3 : ((C + 2 - P : ℕ) : ℤ) = (C : ℤ) + 2 - P := by
    rw [Nat.cast_sub hF]
    push_cast
    ring
  have h4 : (Module.finrank ℝ (LinearMap.ker f) : ℤ) = ((C + 2 - P : ℕ) : ℤ) := by
    rw [h3]
    exact h2
  exact_mod_cast h4

end EarthScience
