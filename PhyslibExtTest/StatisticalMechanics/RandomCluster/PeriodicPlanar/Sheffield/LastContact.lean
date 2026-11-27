/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.LastContact

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.LastContact`

All four headline lemmas (namespace `ContinuousHalfPlaneCrosscut`) applied to the constant path
at the origin and the line `{z 0 = 0}` (the boundary case where the path lies on the line):
* `exists_first_line_contact_prefix_in_halfPlane`, `exists_last_line_contact_suffix_in_halfPlane`;
* `exists_upper_line_excursion_path`, `exists_lower_line_excursion_path`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.LastContact

open _root_.StatMech.FK.PeriodicPlanar.ContinuousHalfPlaneCrosscut

/-- The constant path at the origin of the plane. -/
abbrev γ₀ : Path (0 : Fin 2 → ℝ) 0 := Path.refl 0

-- First contact of the constant path with the line `{z 0 = 0}`.
example : ∃ t : unitInterval, γ₀ t 0 = 0 ∧ (∀ u : unitInterval, γ₀ u 0 = 0 → t ≤ u) ∧
    Set.range (γ₀.subpath 0 t) ≤ Set.range γ₀ ∧
    ∀ z : Fin 2 → ℝ, z ∈ Set.range (γ₀.subpath 0 t) → z 0 ≤ 0 :=
  exists_first_line_contact_prefix_in_halfPlane γ₀ 0 0 le_rfl le_rfl

-- Last contact of the constant path with the line `{z 0 = 0}`.
example : ∃ t : unitInterval, γ₀ t 0 = 0 ∧ (∀ u : unitInterval, γ₀ u 0 = 0 → u ≤ t) ∧
    Set.range (γ₀.subpath t 1) ≤ Set.range γ₀ ∧
    ∀ z : Fin 2 → ℝ, z ∈ Set.range (γ₀.subpath t 1) → 0 ≤ z 0 :=
  exists_last_line_contact_suffix_in_halfPlane γ₀ 0 0 le_rfl le_rfl

-- An upper excursion from the line back to it.
example : ∃ (lo hi : Fin 2 → ℝ) (ex : Path lo hi), lo 0 = 0 ∧ hi 0 = 0 ∧
    Set.range ex ≤ Set.range γ₀ ∧ ∀ z : Fin 2 → ℝ, z ∈ Set.range ex → 0 ≤ z 0 :=
  exists_upper_line_excursion_path γ₀ 0 0 le_rfl le_rfl 0 le_rfl

-- A lower excursion from the line back to it.
example : ∃ (lo hi : Fin 2 → ℝ) (ex : Path lo hi), lo 0 = 0 ∧ hi 0 = 0 ∧
    Set.range ex ≤ Set.range γ₀ ∧ ∀ z : Fin 2 → ℝ, z ∈ Set.range ex → z 0 ≤ 0 :=
  exists_lower_line_excursion_path γ₀ 0 0 le_rfl le_rfl 0 le_rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.LastContact
