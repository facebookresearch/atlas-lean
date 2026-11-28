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

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Combustion ports: complete methane combustion, feasibility and the adiabatic temperature

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

Adiabatic temperature: reactant amounts `nR` enter at the inlet temperature `Tin` and leave,
adiabatically and without work, as product amounts `nP` at the temperature `T`. With molar
enthalpies `H j T` the enthalpy residual is `R(T) = ∑ j, nP j * H j T - ∑ i, nR i * H i Tin`
(`enthalpyResidual`), and an adiabatic temperature is a root of `R`. Its derivative is the total
heat capacity of the products, `Ctot(T) = ∑ j, nP j * cp j T` (`totalHeatCapacity`); positive
`Ctot` on `[Tlo, Thi]` makes `R` strictly increasing there, and a sign change
`R(Tlo) ≤ 0 ≤ R(Thi)` then gives exactly one root by the intermediate value theorem. For products
`n₀ + ξ • ν` reached by the extent `ξ`, `R(T)` is the sensible enthalpy of the products minus the
heat release `Q = -ξ Δ_r H(Tin)` (`heatRelease`): `R(Tin) = -Q`, and with constant heat capacities
`R(T) = Ctot (T - Tin) - Q`. For a balanced reaction `R` does not depend on the elemental
reference of the enthalpies. With all product amounts zero `R` is constant, so positive total heat
capacity cannot be dropped. The thermochemical data `H`, `cp` and their validity range are model
inputs.

## ii. Key results

- `Chemistry.CombustionPorts.isBalanced_methaneCombustion`: the reaction is balanced.
- `Chemistry.CombustionPorts.forwardFeasibleExtents_methaneCombustion`: feasible extents
  `[0, min n_CH4 (n_O2 / 2)]`.
- `Chemistry.CombustionPorts.complete_mem_forwardFeasibleExtents_iff`: complete combustion is
  feasible exactly when `2 * n_CH4 ≤ n_O2`.
- `Chemistry.CombustionPorts.complete_not_mem_of_oxygen_lt`: oxygen-limited infeasibility.
- `Chemistry.CombustionPorts.reactionEnthalpy_shift_methaneCombustion`: reference-state
  invariance of the reaction enthalpy.
- `Chemistry.CombustionPorts.strictMonoOn_enthalpyResidual`: positive total heat capacity makes
  the enthalpy residual strictly increasing.
- `Chemistry.CombustionPorts.existsUnique_adiabaticTemperature`: the unique adiabatic
  temperature in a sign-changing bracket.
- `Chemistry.CombustionPorts.existsUnique_adiabaticTemperature_methane`: the same for feasible
  complete methane combustion products.
- `Chemistry.CombustionPorts.enthalpyResidual_shift_of_isBalanced`: the residual does not depend
  on the elemental reference.
- `Chemistry.CombustionPorts.not_strictMonoOn_enthalpyResidual_zero`: all-zero products.

## iii. Table of contents

- A. Species, composition and the reaction
- B. Feasible extents and complete combustion
- C. Reference-state invariance of the reaction enthalpy
- D. The adiabatic enthalpy residual
- E. Positive total heat capacity and the unique adiabatic temperature

## iv. References

- OpenStax, *Chemistry 2e*, §4.1 and §4.4 (balancing, limiting reactant, theoretical yield).
- S. R. Turns, *An Introduction to Combustion*, McGraw-Hill, ch. 2 (complete-combustion
  stoichiometry `CH4 + 2 (O2 + 3.76 N2) → CO2 + 2 H2O + 7.52 N2`, equivalence ratio; the
  constant-pressure adiabatic flame temperature from `H_reac(T_i) = H_prod(T_ad)`).
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

/-- From nonnegative amounts with oxygen at most twice the methane, oxygen is a limiting reagent. -/
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

/-- In the oxygen-limited case, from nonnegative amounts, a partial extent remains feasible: the
maximal forward extent is `n_O2 / 2`, it is feasible, and it is below the complete-combustion extent
`n_CH4`. -/
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

/-! ## D. The adiabatic enthalpy residual -/

/-- The adiabatic enthalpy residual: reactant amounts `nR` enter at the inlet temperature `Tin`,
product amounts `nP` leave at the temperature `T`, and `H i` is the molar enthalpy of species `i`
as a function of temperature: `R(T) = ∑ j, nP j * H j T - ∑ i, nR i * H i Tin`. An adiabatic
temperature is a root of `R`. -/
def enthalpyResidual {ι : Type*} [Fintype ι] (H : ι → ℝ → ℝ) (nR nP : ι → ℝ) (Tin T : ℝ) : ℝ :=
  ∑ j, nP j * H j T - ∑ i, nR i * H i Tin

/-- The total heat capacity `∑ j, nP j * cp j T` of the product amounts `nP` at the temperature
`T`, from the molar heat capacities `cp j`. -/
def totalHeatCapacity {ι : Type*} [Fintype ι] (cp : ι → ℝ → ℝ) (nP : ι → ℝ) (T : ℝ) : ℝ :=
  ∑ j, nP j * cp j T

/-- The heat released at the inlet temperature `Tin` when the reaction `ν` advances by the extent
`ξ`: `Q = -(ξ * Δ_r H(Tin))`, positive for an exothermic reaction run forward. -/
def heatRelease {ι : Type*} [Fintype ι] (H : ι → ℝ → ℝ) (ν : ι → ℝ) (ξ Tin : ℝ) : ℝ :=
  -(ξ * reactionEnthalpy (fun i => H i Tin) ν)

/-- If every `H j` has derivative `cp j T` at `T`, the temperature derivative of the residual is the
total heat capacity of the products. -/
lemma hasDerivAt_enthalpyResidual {ι : Type*} [Fintype ι] {H cp : ι → ℝ → ℝ} {nR nP : ι → ℝ}
    {Tin T : ℝ} (hH : ∀ j, HasDerivAt (H j) (cp j T) T) :
    HasDerivAt (enthalpyResidual H nR nP Tin) (totalHeatCapacity cp nP T) T := by
  unfold enthalpyResidual totalHeatCapacity
  have hsum : HasDerivAt (fun T' => ∑ j, nP j * H j T') (∑ j, nP j * cp j T) T :=
    HasDerivAt.fun_sum (fun j _ => HasDerivAt.const_mul (nP j) (hH j))
  exact hsum.sub_const _

/-- Kirchhoff form of the residual: between two temperatures where every `H j` has derivative
`cp j`, and with the total heat capacity interval-integrable, the residual grows by the integral of
the total heat capacity. -/
lemma enthalpyResidual_eq_add_integral {ι : Type*} [Fintype ι] {H cp : ι → ℝ → ℝ}
    {nR nP : ι → ℝ} {Tin T₁ T₂ : ℝ}
    (hH : ∀ T ∈ Set.uIcc T₁ T₂, ∀ j, HasDerivAt (H j) (cp j T) T)
    (hint : IntervalIntegrable (totalHeatCapacity cp nP) MeasureTheory.volume T₁ T₂) :
    enthalpyResidual H nR nP Tin T₂ =
      enthalpyResidual H nR nP Tin T₁ + ∫ T in T₁..T₂, totalHeatCapacity cp nP T := by
  exact kirchhoff_law _ _ _ _ (fun T hT => hasDerivAt_enthalpyResidual (hH T hT)) hint

/-- Sensible enthalpy minus heat release: for products `n₀ + ξ • ν` reached from the reactant
amounts `n₀` by the extent `ξ`, `R(T) = ∑ j, (n₀ + ξ • ν) j * (H j T - H j Tin) - Q`. -/
lemma enthalpyResidual_eq_sensible_sub_heatRelease {ι : Type*} [Fintype ι] (H : ι → ℝ → ℝ)
    (n₀ ν : ι → ℝ) (ξ Tin T : ℝ) :
    enthalpyResidual H n₀ (n₀ + ξ • ν) Tin T =
      ∑ j, (n₀ + ξ • ν) j * (H j T - H j Tin) - heatRelease H ν ξ Tin := by
  unfold enthalpyResidual heatRelease
  simp only [reactionEnthalpy_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ j, (n₀ j + ξ * ν j) * (H j T - H j Tin)
      = (n₀ j + ξ * ν j) * H j T - (n₀ j + ξ * ν j) * H j Tin := fun j => mul_sub _ _ _
  simp only [hterm, Finset.sum_sub_distrib]
  have hB : (∑ j, (n₀ j + ξ * ν j) * H j Tin)
      = (∑ j, n₀ j * H j Tin) + ξ * (∑ j, ν j * H j Tin) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hB]
  ring

/-- At the inlet temperature the residual is minus the heat release, `R(Tin) = -Q`: negative for
an exothermic reaction run forward. -/
lemma enthalpyResidual_inlet {ι : Type*} [Fintype ι] (H : ι → ℝ → ℝ) (n₀ ν : ι → ℝ)
    (ξ Tin : ℝ) :
    enthalpyResidual H n₀ (n₀ + ξ • ν) Tin Tin = -heatRelease H ν ξ Tin := by
  rw [enthalpyResidual_eq_sensible_sub_heatRelease]
  simp

/-- Reference-state invariance: shifting every molar enthalpy by element potentials,
`H i T + ∑ b, A b i * e b`, leaves the residual unchanged when the products are reached by a
reaction `ν` balanced for the composition matrix `A`. The adiabatic temperature therefore does
not depend on the enthalpy reference. -/
lemma enthalpyResidual_shift_of_isBalanced {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : Matrix κ ι ℝ) (H : ι → ℝ → ℝ) (e : κ → ℝ) (n₀ ν : ι → ℝ) (ξ Tin T : ℝ)
    (h : IsBalanced A ν) :
    enthalpyResidual (fun i T' => H i T' + ∑ b, A b i * e b) n₀ (n₀ + ξ • ν) Tin T =
      enthalpyResidual H n₀ (n₀ + ξ • ν) Tin T := by
  have hνshift : (∑ i, ν i * (∑ b, A b i * e b)) = 0 := by
    have hbal := reactionEnthalpy_shift_of_isBalanced A (fun _ => (0 : ℝ)) e ν h
    simp only [reactionEnthalpy_apply] at hbal
    simpa using hbal
  unfold enthalpyResidual
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hexp : ∀ (a b c : ℝ), a * (b + c) = a * b + a * c := fun a b c => mul_add _ _ _
  simp only [hexp, Finset.sum_add_distrib]
  have hB : (∑ j, (n₀ j + ξ * ν j) * (∑ b, A b j * e b))
      = (∑ j, n₀ j * (∑ b, A b j * e b)) + ξ * (∑ j, ν j * (∑ b, A b j * e b)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hνshift, mul_zero, add_zero] at hB
  rw [hB]
  ring

/-- Constant heat capacities: if `H j T = H j Tin + c j * (T - Tin)` for every species, the
residual is `Ctot * (T - Tin) - Q` with `Ctot = ∑ j, (n₀ + ξ • ν) j * c j`. -/
lemma enthalpyResidual_of_constant_cp {ι : Type*} [Fintype ι] {H : ι → ℝ → ℝ} {c : ι → ℝ}
    {n₀ ν : ι → ℝ} {ξ Tin T : ℝ} (hH : ∀ j, H j T = H j Tin + c j * (T - Tin)) :
    enthalpyResidual H n₀ (n₀ + ξ • ν) Tin T =
      (∑ j, (n₀ + ξ • ν) j * c j) * (T - Tin) - heatRelease H ν ξ Tin := by
  rw [enthalpyResidual_eq_sensible_sub_heatRelease]
  congr 1
  have hsub : ∀ j, H j T - H j Tin = c j * (T - Tin) := fun j => by rw [hH j]; ring
  simp only [hsub]
  have hfac : ∀ j, (n₀ + ξ • ν) j * (c j * (T - Tin))
      = ((n₀ + ξ • ν) j * c j) * (T - Tin) := fun j => by ring
  simp only [hfac, ← Finset.sum_mul]

/-! ## E. Positive total heat capacity and the unique adiabatic temperature -/

/-- Positive total heat capacity: nonnegative product amounts, one of them positive, and positive
molar heat capacities give `0 < ∑ j, nP j * cp j T`. -/
lemma totalHeatCapacity_pos {ι : Type*} [Fintype ι] {cp : ι → ℝ → ℝ} {nP : ι → ℝ} {T : ℝ}
    (hn : ∀ j, 0 ≤ nP j) (hpos : ∃ j, 0 < nP j) (hcp : ∀ j, 0 < cp j T) :
    0 < totalHeatCapacity cp nP T := by
  unfold totalHeatCapacity
  obtain ⟨j₀, hj₀⟩ := hpos
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hn j) (le_of_lt (hcp j))
  · exact ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ (hcp j₀)⟩

/-- Feasible products have positive total heat capacity: from nonnegative initial amounts, a
feasible positive extent `ξ` of a reaction that produces the species `j₀` leaves nonnegative amounts
with a positive amount of `j₀`, so with positive molar heat capacities `cp j T` their total heat
capacity is positive. -/
lemma totalHeatCapacity_pos_of_mem_forwardFeasibleExtents {ι : Type*} [Fintype ι]
    {cp : ι → ℝ → ℝ} {n₀ ν : ι → ℝ} {ξ T : ℝ} (hn₀ : ∀ i, 0 ≤ n₀ i)
    (hξ : ξ ∈ forwardFeasibleExtents ν n₀) (hξpos : 0 < ξ) {j₀ : ι} (hj₀ : 0 < ν j₀)
    (hcp : ∀ j, 0 < cp j T) :
    0 < totalHeatCapacity cp (n₀ + ξ • ν) T := by
  obtain ⟨_, hfeas⟩ := hξ
  have hn : ∀ j, 0 ≤ (n₀ + ξ • ν) j := by
    intro j
    have h := hfeas j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    have hcomm : ν j * ξ = ξ * ν j := mul_comm _ _
    rw [hcomm] at h
    linarith [h]
  have hpos : ∃ j, 0 < (n₀ + ξ • ν) j := by
    refine ⟨j₀, ?_⟩
    have h1 := hn₀ j₀
    have h2 := mul_pos hξpos hj₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  exact totalHeatCapacity_pos hn hpos hcp

/-- Positive total heat capacity on `[Tlo, Thi]`, where every `H j` has derivative `cp j`, makes
the residual strictly increasing there. -/
lemma strictMonoOn_enthalpyResidual {ι : Type*} [Fintype ι] {H cp : ι → ℝ → ℝ}
    {nR nP : ι → ℝ} {Tin Tlo Thi : ℝ}
    (hH : ∀ T ∈ Set.Icc Tlo Thi, ∀ j, HasDerivAt (H j) (cp j T) T)
    (hC : ∀ T ∈ Set.Icc Tlo Thi, 0 < totalHeatCapacity cp nP T) :
    StrictMonoOn (enthalpyResidual H nR nP Tin) (Set.Icc Tlo Thi) := by
  have hderiv : ∀ T ∈ Set.Icc Tlo Thi,
      HasDerivAt (enthalpyResidual H nR nP Tin) (totalHeatCapacity cp nP T) T :=
    fun T hT => hasDerivAt_enthalpyResidual (hH T hT)
  have hcont : ContinuousOn (enthalpyResidual H nR nP Tin) (Set.Icc Tlo Thi) :=
    fun T hT => (hderiv T hT).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
  intro x hx
  have hxIcc : x ∈ Set.Icc Tlo Thi := interior_subset hx
  have h := hderiv x hxIcc
  rw [h.deriv]
  exact hC x hxIcc

/-- The unique adiabatic temperature: with `Tlo < Thi`, every `H j` having derivative `cp j` on
`[Tlo, Thi]`, positive total heat capacity on `[Tlo, Thi]` and the sign change
`R(Tlo) ≤ 0 ≤ R(Thi)`, the residual has exactly one root in `[Tlo, Thi]`. -/
lemma existsUnique_adiabaticTemperature {ι : Type*} [Fintype ι] {H cp : ι → ℝ → ℝ}
    {nR nP : ι → ℝ} {Tin Tlo Thi : ℝ} (hlt : Tlo < Thi)
    (hH : ∀ T ∈ Set.Icc Tlo Thi, ∀ j, HasDerivAt (H j) (cp j T) T)
    (hC : ∀ T ∈ Set.Icc Tlo Thi, 0 < totalHeatCapacity cp nP T)
    (hlo : enthalpyResidual H nR nP Tin Tlo ≤ 0) (hhi : 0 ≤ enthalpyResidual H nR nP Tin Thi) :
    ∃! Tad, Tad ∈ Set.Icc Tlo Thi ∧ enthalpyResidual H nR nP Tin Tad = 0 := by
  have hmono : StrictMonoOn (enthalpyResidual H nR nP Tin) (Set.Icc Tlo Thi) :=
    strictMonoOn_enthalpyResidual hH hC
  have hcont : ContinuousOn (enthalpyResidual H nR nP Tin) (Set.Icc Tlo Thi) := by
    intro T hT
    exact (hasDerivAt_enthalpyResidual (hH T hT)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcz⟩ := intermediate_value_Icc (le_of_lt hlt) hcont ⟨hlo, hhi⟩
  exact ⟨c, ⟨hc, hcz⟩, fun y hy => hmono.injOn hy.1 hc (hy.2.trans hcz.symm)⟩

/-- The adiabatic temperature of the methane product model: from nonnegative reactant amounts `n₀`
and a feasible positive extent `ξ` of complete methane combustion, with `Tlo < Thi`, `H j` having
derivative `cp j > 0` on `[Tlo, Thi]` and the sign change `R(Tlo) ≤ 0 ≤ R(Thi)` of the residual, the
products `n₀ + ξ • methaneCombustion` have exactly one adiabatic temperature in `[Tlo, Thi]`. -/
lemma existsUnique_adiabaticTemperature_methane {H cp : Species → ℝ → ℝ} {n₀ : Species → ℝ}
    {ξ Tin Tlo Thi : ℝ} (hn₀ : ∀ i, 0 ≤ n₀ i)
    (hξ : ξ ∈ forwardFeasibleExtents methaneCombustion n₀) (hξpos : 0 < ξ) (hlt : Tlo < Thi)
    (hH : ∀ T ∈ Set.Icc Tlo Thi, ∀ j, HasDerivAt (H j) (cp j T) T)
    (hcp : ∀ T ∈ Set.Icc Tlo Thi, ∀ j, 0 < cp j T)
    (hlo : enthalpyResidual H n₀ (n₀ + ξ • methaneCombustion) Tin Tlo ≤ 0)
    (hhi : 0 ≤ enthalpyResidual H n₀ (n₀ + ξ • methaneCombustion) Tin Thi) :
    ∃! Tad, Tad ∈ Set.Icc Tlo Thi ∧
      enthalpyResidual H n₀ (n₀ + ξ • methaneCombustion) Tin Tad = 0 := by
  have hj₀ : (0 : ℝ) < methaneCombustion .CO2 := by
    change (0 : ℝ) < 1
    norm_num
  have hC : ∀ T ∈ Set.Icc Tlo Thi,
      0 < totalHeatCapacity cp (n₀ + ξ • methaneCombustion) T :=
    fun T hT => totalHeatCapacity_pos_of_mem_forwardFeasibleExtents hn₀ hξ hξpos hj₀ (hcp T hT)
  exact existsUnique_adiabaticTemperature hlt hH hC hlo hhi

/-- All-zero product amounts do not give strict monotonicity: with `nP = 0` the residual is
constant, so it is not strictly increasing on any `[Tlo, Thi]` with `Tlo < Thi`. -/
lemma not_strictMonoOn_enthalpyResidual_zero {ι : Type*} [Fintype ι] (H : ι → ℝ → ℝ)
    (nR : ι → ℝ) {Tin Tlo Thi : ℝ} (hlt : Tlo < Thi) :
    ¬ StrictMonoOn (enthalpyResidual H nR 0 Tin) (Set.Icc Tlo Thi) := by
  intro hmono
  have hlo : Tlo ∈ Set.Icc Tlo Thi := ⟨le_rfl, le_of_lt hlt⟩
  have hhi : Thi ∈ Set.Icc Tlo Thi := ⟨le_of_lt hlt, le_rfl⟩
  have hlt' := hmono hlo hhi hlt
  have hconst : enthalpyResidual H nR 0 Tin Tlo = enthalpyResidual H nR 0 Tin Thi := by
    unfold enthalpyResidual
    simp
  rw [hconst] at hlt'
  exact lt_irrefl _ hlt'

end Chemistry.CombustionPorts
