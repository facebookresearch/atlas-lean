/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Stoichiometry.Balance
public import PhyslibExt.Chemistry.Stoichiometry.Extent
public import PhyslibExt.Chemistry.Thermodynamics.Thermochemistry

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Combustion ports: complete methane combustion, balance and feasibility

## i. Overview

Complete methane combustion `CH4 + 2 O2 → CO2 + 2 H2O` is instantiated in the stoichiometry
layer: species `CH4, O2, CO2, H2O, N2`, balance coordinates the elements `C, H, O, N` (all
species are neutral), the composition matrix of the five molecules and the reaction vector
`methaneCombustion` with coefficient `0` on the inert `N2`. The reaction is balanced, so every
extent conserves the element totals, and the `N2` amount never changes, whether it is zero (pure
oxygen) or positive (air).

From nonnegative actual initial amounts `n₀` (products may be present initially), the feasible
forward extents are `[0, min n_CH4 (n_O2 / 2)]`. Complete combustion of the whole charge, the
extent `ξ = n_CH4` that leaves no methane, is feasible exactly when `2 * n_CH4 ≤ n_O2`. With
oxygen below twice the methane it is infeasible, oxygen is the limiting reagent, and the partial
extent `n_O2 / 2 < n_CH4` remains feasible. The reaction enthalpy does not depend on the
elemental reference state of the formation enthalpies.

Model inputs: the fixed complete-product set `CO2, H2O` (dissociation and incomplete products such
as `CO` are a different model), amounts as numerical coordinates in one amount unit (moles in the
tests). Each result assumes only the hypotheses its proof uses.

## ii. Key results

- `Chemistry.CombustionPorts.isBalanced_methaneCombustion`: the reaction is balanced.
- `Chemistry.CombustionPorts.forwardFeasibleExtents_methaneCombustion`: feasible extents
  `[0, min n_CH4 (n_O2 / 2)]`.
- `Chemistry.CombustionPorts.complete_mem_forwardFeasibleExtents_iff`: complete combustion is
  feasible exactly when `2 * n_CH4 ≤ n_O2`.
- `Chemistry.CombustionPorts.complete_not_mem_of_oxygen_lt`: oxygen-limited infeasibility.
- `Chemistry.CombustionPorts.reactionEnthalpy_shift_methaneCombustion`: reference-state
  invariance of the reaction enthalpy.

## iii. Table of contents

- A. Species, composition and the reaction
- B. Feasible extents and complete combustion
- C. Reference-state invariance of the reaction enthalpy

## iv. References

- OpenStax, *Chemistry 2e*, §4.1 and §4.4 (balancing, limiting reactant, theoretical yield).
- S. R. Turns, *An Introduction to Combustion*, McGraw-Hill, ch. 2 (complete-combustion
  stoichiometry `CH4 + 2 (O2 + 3.76 N2) → CO2 + 2 H2O + 7.52 N2`, equivalence ratio).
-/

@[expose] public section

namespace Chemistry.CombustionPorts

open Chemistry.Stoichiometry Chemistry.Thermodynamics Matrix

/-! ## A. Species, composition and the reaction -/

/-- The species of complete methane combustion with an inert diluent. -/
inductive Species
  /-- Methane. -/
  | CH4
  /-- Oxygen. -/
  | O2
  /-- Carbon dioxide. -/
  | CO2
  /-- Water. -/
  | H2O
  /-- Nitrogen, the inert diluent. -/
  | N2
  deriving DecidableEq

instance : Fintype Species where
  elems := {.CH4, .O2, .CO2, .H2O, .N2}
  complete s := by cases s <;> simp

/-- The balance coordinates: atoms of carbon, hydrogen, oxygen and nitrogen. Every species is
neutral, so no charge coordinate is needed. -/
inductive Element
  /-- Carbon. -/
  | C
  /-- Hydrogen. -/
  | H
  /-- Oxygen. -/
  | O
  /-- Nitrogen. -/
  | N
  deriving DecidableEq

instance : Fintype Element where
  elems := {.C, .H, .O, .N}
  complete b := by cases b <;> simp

/-- Composition matrix: `composition b s` is the number of atoms of the element `b` in one
molecule of the species `s`. -/
noncomputable def composition : Matrix Element Species ℝ :=
  Matrix.of fun b s =>
    match b, s with
    | .C, .CH4 => 1
    | .H, .CH4 => 4
    | .O, .O2 => 2
    | .C, .CO2 => 1
    | .O, .CO2 => 2
    | .H, .H2O => 2
    | .O, .H2O => 1
    | .N, .N2 => 2
    | _, _ => 0

/-- Complete methane combustion `CH4 + 2 O2 → CO2 + 2 H2O`: coefficients negative on the
reactants, positive on the products, and `0` on the inert `N2`. -/
noncomputable def methaneCombustion : Species → ℝ
  | .CH4 => -1
  | .O2 => -2
  | .CO2 => 1
  | .H2O => 2
  | .N2 => 0

/-- A reactant charge of `nCH4` methane, `nO2` oxygen and `nN2` nitrogen, with no products. -/
noncomputable def reactantCharge (nCH4 nO2 nN2 : ℝ) : Species → ℝ
  | .CH4 => nCH4
  | .O2 => nO2
  | .CO2 => 0
  | .H2O => 0
  | .N2 => nN2

/-- Complete methane combustion is balanced in carbon, hydrogen, oxygen and nitrogen. -/
lemma isBalanced_methaneCombustion : IsBalanced composition methaneCombustion := by
  have huniv : Finset.univ (α := Species) = {.CH4, .O2, .CO2, .H2O, .N2} := rfl
  change composition *ᵥ methaneCombustion = 0
  funext b
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  cases b <;> simp only [composition, methaneCombustion] <;> norm_num

/-- The reaction consumes a species (methane), so its maximal forward extent is defined. -/
lemma methaneCombustion_consumes : ∃ i, methaneCombustion i < 0 := by
  exact ⟨.CH4, by norm_num [methaneCombustion]⟩

/-- Element conservation: advancing the reaction by any extent `ξ` from any initial amounts `n₀`
leaves the totals of carbon, hydrogen, oxygen and nitrogen unchanged. -/
lemma composition_mulVec_add_smul (n₀ : Species → ℝ) (ξ : ℝ) :
    composition *ᵥ (n₀ + ξ • methaneCombustion) = composition *ᵥ n₀ := by
  exact mulVec_add_smul_of_isBalanced composition n₀ methaneCombustion ξ
    isBalanced_methaneCombustion

/-- The inert nitrogen amount is unchanged at every extent. -/
lemma inert_amount_unchanged (n₀ : Species → ℝ) (ξ : ℝ) :
    (n₀ + ξ • methaneCombustion) .N2 = n₀ .N2 := by
  simp [methaneCombustion]

/-! ## B. Feasible extents and complete combustion -/

/-- The maximal forward extent is `min n_CH4 (n_O2 / 2)`; the nitrogen amount does not enter. -/
lemma maxExtent_methaneCombustion (n₀ : Species → ℝ) :
    maxExtent methaneCombustion n₀ methaneCombustion_consumes = min (n₀ .CH4) (n₀ .O2 / 2) := by
  have hCH4 : methaneCombustion .CH4 < 0 := by norm_num [methaneCombustion]
  have hO2 : methaneCombustion .O2 < 0 := by norm_num [methaneCombustion]
  have eCH4 : n₀ .CH4 / |methaneCombustion .CH4| = n₀ .CH4 := by
    norm_num [methaneCombustion]
  have eO2 : n₀ .O2 / |methaneCombustion .O2| = n₀ .O2 / 2 := by
    norm_num [methaneCombustion]
  apply le_antisymm
  · have h1 : maxExtent methaneCombustion n₀ methaneCombustion_consumes ≤ n₀ .CH4 := by
      calc _ ≤ n₀ .CH4 / |methaneCombustion .CH4| :=
            maxExtent_le n₀ _ hCH4
        _ = n₀ .CH4 := eCH4
    have h2 : maxExtent methaneCombustion n₀ methaneCombustion_consumes ≤ n₀ .O2 / 2 := by
      calc _ ≤ n₀ .O2 / |methaneCombustion .O2| :=
            maxExtent_le n₀ _ hO2
        _ = n₀ .O2 / 2 := eO2
    exact le_min h1 h2
  · rw [le_maxExtent_iff]
    intro i hi
    cases i
    · rw [eCH4]; exact min_le_left _ _
    · rw [eO2]; exact min_le_right _ _
    · norm_num [methaneCombustion] at hi
    · norm_num [methaneCombustion] at hi
    · norm_num [methaneCombustion] at hi

/-- From nonnegative initial amounts the feasible forward extents are exactly
`[0, min n_CH4 (n_O2 / 2)]`. -/
lemma forwardFeasibleExtents_methaneCombustion {n₀ : Species → ℝ} (hn₀ : ∀ i, 0 ≤ n₀ i) :
    forwardFeasibleExtents methaneCombustion n₀ = Set.Icc 0 (min (n₀ .CH4) (n₀ .O2 / 2)) := by
  rw [forwardFeasibleExtents_eq_Icc _ _ hn₀ methaneCombustion_consumes,
    maxExtent_methaneCombustion]

/-- Complete combustion of the whole charge, the extent `ξ = n_CH4`, is feasible from
nonnegative initial amounts exactly when `2 * n_CH4 ≤ n_O2`. -/
lemma complete_mem_forwardFeasibleExtents_iff {n₀ : Species → ℝ} (hn₀ : ∀ i, 0 ≤ n₀ i) :
    n₀ .CH4 ∈ forwardFeasibleExtents methaneCombustion n₀ ↔ 2 * n₀ .CH4 ≤ n₀ .O2 := by
  rw [forwardFeasibleExtents_methaneCombustion hn₀, Set.mem_Icc]
  constructor
  · intro h
    have hle : n₀ .CH4 ≤ n₀ .O2 / 2 := le_trans h.2 (min_le_right _ _)
    linarith
  · intro h
    exact ⟨hn₀ _, le_min le_rfl (by linarith)⟩

/-- At the complete-combustion extent `ξ = n_CH4` no methane remains. -/
lemma complete_methane_eq_zero (n₀ : Species → ℝ) :
    (n₀ + n₀ .CH4 • methaneCombustion) .CH4 = 0 := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, methaneCombustion]
  ring

/-- Oxygen-limited infeasibility: with oxygen below twice the methane, complete combustion of the
whole charge is not feasible; it would leave a negative oxygen amount. -/
lemma complete_not_mem_of_oxygen_lt {n₀ : Species → ℝ} (hO2 : n₀ .O2 < 2 * n₀ .CH4) :
    n₀ .CH4 ∉ forwardFeasibleExtents methaneCombustion n₀ := by
  intro hmem
  obtain ⟨_, h⟩ := hmem
  have hO2' := h .O2
  simp only [methaneCombustion] at hO2'
  linarith

/-- With oxygen at most twice the methane, oxygen is a limiting reagent. -/
lemma isLimitingReagent_O2 {n₀ : Species → ℝ} (hn₀ : ∀ i, 0 ≤ n₀ i)
    (hO2 : n₀ .O2 ≤ 2 * n₀ .CH4) : IsLimitingReagent methaneCombustion n₀ .O2 := by
  have hO2neg : methaneCombustion .O2 < 0 := by norm_num [methaneCombustion]
  have eO2 : |methaneCombustion Species.O2| = 2 := by norm_num [methaneCombustion]
  have eCH4 : |methaneCombustion Species.CH4| = 1 := by norm_num [methaneCombustion]
  refine ⟨hn₀, hO2neg, fun j hj => ?_⟩
  cases j
  · rw [eO2, eCH4, div_one]
    linarith
  · exact le_rfl
  · norm_num [methaneCombustion] at hj
  · norm_num [methaneCombustion] at hj
  · norm_num [methaneCombustion] at hj

/-- In the oxygen-limited case a partial extent remains feasible: the maximal forward extent is
`n_O2 / 2`, it is feasible, and it is below the complete-combustion extent `n_CH4`. -/
lemma oxygen_limited_maxExtent {n₀ : Species → ℝ} (hn₀ : ∀ i, 0 ≤ n₀ i)
    (hO2 : n₀ .O2 < 2 * n₀ .CH4) :
    maxExtent methaneCombustion n₀ methaneCombustion_consumes = n₀ .O2 / 2 ∧
      n₀ .O2 / 2 ∈ forwardFeasibleExtents methaneCombustion n₀ ∧ n₀ .O2 / 2 < n₀ .CH4 := by
  have hlt : n₀ .O2 / 2 < n₀ .CH4 := by linarith
  refine ⟨?_, ?_, hlt⟩
  · rw [maxExtent_methaneCombustion, min_eq_right (le_of_lt hlt)]
  · rw [forwardFeasibleExtents_methaneCombustion hn₀, Set.mem_Icc]
    exact ⟨by linarith [hn₀ .O2], le_min (le_of_lt hlt) le_rfl⟩

/-! ## C. Reference-state invariance of the reaction enthalpy -/

/-- Shifting the formation enthalpies by element potentials, `Hf s + ∑ b, composition b s * e b`,
leaves the reaction enthalpy of complete methane combustion unchanged. -/
lemma reactionEnthalpy_shift_methaneCombustion (Hf : Species → ℝ) (e : Element → ℝ) :
    reactionEnthalpy (fun s => Hf s + ∑ b, composition b s * e b) methaneCombustion =
      reactionEnthalpy Hf methaneCombustion := by
  exact reactionEnthalpy_shift_of_isBalanced composition Hf e methaneCombustion
    isBalanced_methaneCombustion

end Chemistry.CombustionPorts
