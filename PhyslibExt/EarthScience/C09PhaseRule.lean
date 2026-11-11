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
public import Mathlib.Tactic

/-!
# Gibbs phase rule: freedom count as a dimension count

For `C` independent components and `P` phases in a nonreacting regular
equilibrium system with pressure and temperature free, the local freedom
count is `F = C - P + 2`, under an independent-constraint rank hypothesis.

## i. Overview

Counting variables against constraints gives the rule: each phase has
`C` mole fractions summing to `1`, so `C - 1` independent compositions
per phase, plus `2` for temperature and pressure, for
`P * (C - 1) + 2` variables. For each of the `C` components, equality of
chemical potential across the `P` phases gives `P - 1` independent
equalities, for `C * (P - 1)` constraints. Subtracting gives
`C - P + 2`.

Counts alone are not a theorem of existence. The dimension form makes
the rank hypothesis explicit: if the constraint map `f` from the
variable space to the constraint space is surjective (independent
constraints), then the solution space, the kernel of `f`, has finite
dimension `C + 2 - P` by rank-nullity. No equilibrium existence,
no empirical validation, and no new framework is claimed.

## ii. Key results

- `EarthScience.phase_rule_variable_count`: the integer counting identity.
- `EarthScience.phase_rule_finrank`: the dimension form via rank-nullity.

## iii. Table of contents

- A. Counting identity
- B. Dimension form

## iv. References

- `LinearMap.finrank_range_add_finrank_ker` in Mathlib (rank-nullity).
-/

@[expose] public section

namespace EarthScience

/-- Gibbs phase-rule count: with `P` phases and `C` independent components,
there are `P * (C - 1) + 2` variables (compositions plus temperature and
pressure) and `C * (P - 1)` independent chemical-potential equalities, so
the freedom count is `C - P + 2`. -/
theorem phase_rule_variable_count (C P : ℤ) :
    (P * (C - 1) + 2) - (C * (P - 1)) = C - P + 2 := by
  ring

/-! ## B. Dimension form -/

/-- Gibbs phase rule as a dimension count: if the `C * (P - 1)` equilibrium
constraints are independent, i.e. the constraint map is surjective, then the
solution space (tangent space to the equilibrium manifold) has dimension
`C + 2 - P`. -/
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
