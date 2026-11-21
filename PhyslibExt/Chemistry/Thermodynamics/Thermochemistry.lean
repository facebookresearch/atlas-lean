/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Stoichiometry.Balance
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Thermochemistry: Hess's law, formation enthalpies, Kirchhoff, calorimetry

Enthalpy changes combine linearly, shift predictably with temperature, and balance in calorimeters.

## i. Overview

Species are indexed by a finite type `ι`; amount and enthalpy coordinates are plain real numbers
after a consistent amount-unit choice, and no dimensional-quantity algebra is in scope. Reaction
vectors use the CH04 sign convention: stoichiometric coefficients are positive on products and
negative on reactants (see `Chemistry.Stoichiometry.IsBalanced`).

Reaction enthalpy `Δ_r H` is a linear functional on the reaction space: for a fixed assignment of
molar enthalpies `H`, the enthalpy of a reaction `ν` is `∑ i, ν i * H i`. Hess's law is this
linearity: a linear combination of reactions has the same linear combination of reaction
enthalpies. `ΔH` is stated per mole of reaction as written, so scaling the written equation
scales `ΔH`; doubling is proved as a corollary.

Standard formation enthalpies `Δ_f H°` carry the definitional convention that elements in their
reference state have `Δ_f H° = 0`, stated here as a hypothesis on a distinguished finite set of
species. It is a convention, not a claim about nature, and this module assigns a formation
enthalpy to no real substance. For a balanced reaction, the reaction enthalpy is unchanged when
formation enthalpies shift by element potentials, which is the precise sense in which `Δ_r H°`
does not depend on the reference choice.

The `°` superscript marks the standard state. Formation enthalpies depend on the pressure
convention (`p° = 1 bar` in current tables versus `1 atm` in older ones); values from different
conventions must not be mixed, and this module takes no position beyond recording the dependence.

Kirchhoff's law relates the reaction enthalpy at two temperatures through the heat-capacity
difference `ΔCp`, taken as an abstract integrable function: no Cp polynomial fit is claimed.
The interval integral handles either temperature ordering. Calorimetry is proved inside the
constant-heat-capacity model: an isolated calorimeter with `q = C * ΔT`, where an exothermic
reaction has negative `q_rxn`.

No claim is made that enthalpy is a state function in full generality: Hess's and Kirchhoff's
laws here are consequences of the stated linearity and antiderivative hypotheses.

## ii. Key results

- `reactionEnthalpy` : reaction enthalpy as a linear functional on the reaction space.
- `hess_law` : Hess's law for finite linear combinations of reactions.
- `hess_add`, `hess_smul`, `hess_double` : additivity, scaling, and doubling corollaries.
- `IsReferenceState` : the `Δ_f H° = 0` convention on reference-state elements.
- `reference_species_contrib_eq_zero` : reference-state species contribute nothing.
- `reactionEnthalpy_shift_of_isBalanced` : `Δ_r H°` is unchanged by element-potential shifts.
- `kirchhoff_law` : `ΔH(T₂) = ΔH(T₁) + ∫ ΔCp`, for either temperature ordering.
- `kirchhoff_of_continuous`, `kirchhoff_swapped` : continuous-`ΔCp` and reversed corollaries.
- `calorimeterHeat` : `q = C * ΔT` for a constant-heat-capacity calorimeter.
- `calorimetry_reaction_heat` : `q_rxn = -q_cal` in an isolated calorimeter.
- `calorimetry_temp_change` : the temperature change from the reaction heat.
- `calorimetry_exothermic_iff_temp_rise` : exothermic reaction iff temperature rise.

## iii. Table of contents

- A. Reaction enthalpy as a linear functional (Hess's law)
- B. Formation enthalpies and the reference-state convention
- C. Kirchhoff's law
- D. Calorimetry energy balance

## iv. References

- OpenStax, *Chemistry 2e*, Ch. 5, "Thermochemistry" (chapter-level reference).
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book).

-/

@[expose] public section

namespace Chemistry.Thermodynamics

open Chemistry.Stoichiometry MeasureTheory intervalIntegral

/-!

## A. Reaction enthalpy as a linear functional (Hess's law)

-/

/-- Reaction enthalpy as a linear functional on the reaction space: for a fixed assignment of
molar enthalpies `H : ι → ℝ`, the enthalpy of the reaction `ν` is `∑ i, ν i * H i`, with
products positive and reactants negative. `ΔH` is per mole of reaction as written: scaling the
written equation scales `ΔH` (see `hess_smul` and `hess_double`). -/
def reactionEnthalpy {ι : Type*} [Fintype ι] (H : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun ν := ∑ i, ν i * H i
  map_add' ν₁ ν₂ := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c ν := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The reaction enthalpy of `ν` is the coefficient-weighted sum `∑ i, ν i * H i`. -/
@[simp]
lemma reactionEnthalpy_apply {ι : Type*} [Fintype ι] (H : ι → ℝ) (ν : ι → ℝ) :
    reactionEnthalpy H ν = ∑ i, ν i * H i :=
  rfl

/-- Hess's law, additivity: the reaction enthalpy of a sum of two reactions is the sum of their
reaction enthalpies. -/
lemma hess_add {ι : Type*} [Fintype ι] (H : ι → ℝ) (ν₁ ν₂ : ι → ℝ) :
    reactionEnthalpy H (ν₁ + ν₂) = reactionEnthalpy H ν₁ + reactionEnthalpy H ν₂ :=
  (reactionEnthalpy H).map_add ν₁ ν₂

/-- Hess's law, scaling: scaling a written reaction by `c` scales its reaction enthalpy by `c`. -/
lemma hess_smul {ι : Type*} [Fintype ι] (c : ℝ) (H : ι → ℝ) (ν : ι → ℝ) :
    reactionEnthalpy H (c • ν) = c * reactionEnthalpy H ν := by
  rw [map_smul, smul_eq_mul]

/-- Doubling a reaction as written doubles its reaction enthalpy. -/
lemma hess_double {ι : Type*} [Fintype ι] (H : ι → ℝ) (ν : ι → ℝ) :
    reactionEnthalpy H ((2 : ℝ) • ν) = 2 * reactionEnthalpy H ν :=
  hess_smul 2 H ν

/-- The zero reaction has zero reaction enthalpy. -/
lemma reactionEnthalpy_zero {ι : Type*} [Fintype ι] (H : ι → ℝ) :
    reactionEnthalpy H 0 = 0 :=
  map_zero _

/-- Hess's law: the reaction enthalpy of a finite linear combination of reactions is the same
linear combination of their reaction enthalpies. -/
theorem hess_law {ι ρ : Type*} [Fintype ι] [Fintype ρ] (H : ι → ℝ) (ν : ρ → ι → ℝ)
    (c : ρ → ℝ) :
    reactionEnthalpy H (∑ r, c r • ν r) = ∑ r, c r * reactionEnthalpy H (ν r) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact hess_smul _ _ _

/-!

## B. Formation enthalpies and the reference-state convention

-/

/-- The standard-formation-enthalpy convention: the species in `ref` (elements in their reference
state) have `Δ_f H° = 0`. This is a definitional convention, not a claim about nature. -/
def IsReferenceState {ι : Type*} (ref : Finset ι) (Hf : ι → ℝ) : Prop :=
  ∀ i ∈ ref, Hf i = 0

/-- Reference-state species contribute nothing to a formation-enthalpy sum. -/
lemma reference_species_contrib_eq_zero {ι : Type*} (ref : Finset ι)
    (Hf : ι → ℝ) (ν : ι → ℝ) (href : IsReferenceState ref Hf) :
    ∑ i ∈ ref, ν i * Hf i = 0 :=
  Finset.sum_eq_zero fun i hi => by rw [href i hi, mul_zero]

/-- The reaction enthalpy from formation enthalpies is unchanged when the formation enthalpies
shift by element potentials: for a reaction `ν` balanced for the composition matrix `A`, adding
`∑ b, A b i * e b` to each `Hf i` leaves `Δ_r H°` fixed. This is the precise sense in which
`Δ_r H°` does not depend on the formation-enthalpy reference choice. -/
lemma reactionEnthalpy_shift_of_isBalanced {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : Matrix κ ι ℝ) (Hf : ι → ℝ) (e : κ → ℝ) (ν : ι → ℝ) (h : IsBalanced A ν) :
    reactionEnthalpy (fun i => Hf i + ∑ b, A b i * e b) ν
      = reactionEnthalpy Hf ν := by
  have h0 : ∀ b, ∑ i, A b i * ν i = 0 := fun b => congrFun h b
  have hshift : (∑ i, ν i * (∑ b, A b i * e b)) = 0 := by
    trans ∑ b, ∑ i, (A b i * ν i) * e b
    · have e1 : (∑ i, ν i * (∑ b, A b i * e b))
          = ∑ i, ∑ b, (A b i * ν i) * e b := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      rw [e1]
      exact Finset.sum_comm
    · apply Finset.sum_eq_zero
      intro b _
      rw [← Finset.sum_mul, h0 b, zero_mul]
  simp only [reactionEnthalpy_apply, mul_add, Finset.sum_add_distrib, hshift, add_zero]

/-!

## C. Kirchhoff's law

-/

/-- Kirchhoff's law: when `ΔH` has derivative `ΔCp` at every temperature between `T1` and `T2`
and `ΔCp` is interval-integrable, `ΔH T2 = ΔH T1 + ∫ T in T1..T2, ΔCp T`. The temperatures may
be ordered either way: the hypotheses are stated over the unordered interval `uIcc T1 T2`, and
the interval integral changes sign when the endpoints are swapped. `ΔCp` is an abstract
integrable function; no heat-capacity fit is claimed. -/
theorem kirchhoff_law (H Cp : ℝ → ℝ) (T1 T2 : ℝ)
    (hderiv : ∀ T ∈ Set.uIcc T1 T2, HasDerivAt H (Cp T) T)
    (hint : IntervalIntegrable Cp volume T1 T2) :
    H T2 = H T1 + ∫ T in T1..T2, Cp T := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  linarith

/-- Kirchhoff's law for continuous `ΔCp`: continuity on the unordered interval supplies the
integrability hypothesis. -/
lemma kirchhoff_of_continuous (H Cp : ℝ → ℝ) (T1 T2 : ℝ)
    (hCp : Continuous Cp) (hderiv : ∀ T ∈ Set.uIcc T1 T2, HasDerivAt H (Cp T) T) :
    H T2 = H T1 + ∫ T in T1..T2, Cp T :=
  kirchhoff_law H Cp T1 T2 hderiv (hCp.intervalIntegrable T1 T2)

/-- Kirchhoff's law with the endpoints swapped: `ΔH T1 = ΔH T2 + ∫ T in T2..T1, ΔCp T`. -/
lemma kirchhoff_swapped (H Cp : ℝ → ℝ) (T1 T2 : ℝ)
    (hderiv : ∀ T ∈ Set.uIcc T1 T2, HasDerivAt H (Cp T) T)
    (hint : IntervalIntegrable Cp volume T1 T2) :
    H T1 = H T2 + ∫ T in T2..T1, Cp T := by
  have hderiv' : ∀ T ∈ Set.uIcc T2 T1, HasDerivAt H (Cp T) T := by
    rwa [Set.uIcc_comm]
  exact kirchhoff_law H Cp T2 T1 hderiv' hint.symm

/-!

## D. Calorimetry energy balance

-/

/-- The heat absorbed by a constant-heat-capacity calorimeter, `q = C * ΔT`. -/
def calorimeterHeat (C dT : ℝ) : ℝ := C * dT

/-- In an isolated calorimeter (`q_rxn + q_cal = 0`), the reaction heat is the negation of the
calorimeter heat: `q_rxn = -q_cal`. Sign convention: an exothermic reaction has negative `q_rxn`
(and hence positive `q_cal`). -/
lemma calorimetry_reaction_heat (C dT q_rxn : ℝ)
    (hisol : q_rxn + calorimeterHeat C dT = 0) :
    q_rxn = -calorimeterHeat C dT := by
  unfold calorimeterHeat at hisol ⊢
  linarith

/-- The calorimeter temperature change from the reaction heat: `ΔT = -q_rxn / C` for `C ≠ 0`. -/
lemma calorimetry_temp_change (C dT q_rxn : ℝ) (hC : C ≠ 0)
    (hisol : q_rxn + calorimeterHeat C dT = 0) :
    dT = -q_rxn / C := by
  have hmul : C * dT = -q_rxn := by
    unfold calorimeterHeat at hisol
    linarith
  rw [eq_div_iff hC, mul_comm dT C]
  exact hmul

/-- Sign convention: with positive heat capacity, the reaction is exothermic (`q_rxn < 0`) iff the
calorimeter temperature rises (`0 < ΔT`). -/
lemma calorimetry_exothermic_iff_temp_rise (C dT q_rxn : ℝ) (hC : 0 < C)
    (hisol : q_rxn + calorimeterHeat C dT = 0) :
    q_rxn < 0 ↔ 0 < dT := by
  have hq : q_rxn = -(C * dT) := by
    unfold calorimeterHeat at hisol
    linarith
  rw [hq, neg_lt_zero]
  constructor
  · intro h
    by_contra hcon
    have hle : dT ≤ 0 := not_lt.mp hcon
    have hnonpos : C * dT ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC.le hle
    linarith
  · intro h
    exact mul_pos hC h

end Chemistry.Thermodynamics
