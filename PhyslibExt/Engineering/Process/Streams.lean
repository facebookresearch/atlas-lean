/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Amounts.MolarMassComposition


/-!
# Process streams: amount-flow rates and composition

## i. Overview

A process stream is a vector of nonnegative species amount-flow rates
`ṅ : ι → ℝ` over a finite species type `ι`, in moles per declared time unit.
As in `Chemistry.Amounts`, all quantities are numerical values after a
consistent choice of units; dimensions are not tracked, and no new dimension
type is introduced here. Flows are rates, not stocks: integrating a constant
stream over a duration `Δt` gives amounts `Δt * ṅ i`.

Composition is produced only under a positive total flow, by applying the
existing `Chemistry.Amounts.moleFraction` and `Chemistry.Amounts.massFraction`
to the flow vector. A zero-flow stream has no composition: `composition`
returns `none`, and no lemma divides by a zero total. The mass-flow view is
`ṁ i = ṅ i * M i` for molar masses `M`. Generic mole/mass fraction algebra,
including normalization and the mutually inverse conversions, is imported
from `Chemistry.Amounts`, not reproved here.

## ii. Key results

- `StreamFlow.composition_eq_moleFraction`: under a positive total, the
  composition is `Chemistry.Amounts.moleFraction` of the flow vector.
- `StreamFlow.composition_eq_none_iff`: there is no composition exactly when
  the total flow is zero.
- `StreamFlow.composition_of_integrate`: time-unit erasure. The amount
  fractions of a constant stream integrated over `Δt > 0` equal its flow
  fractions.
- `StreamFlow.mass_mole_round_trip` and `StreamFlow.mole_mass_round_trip`:
  the mass/mole flow-composition conversions are the imported inverse pair.

## iii. Table of contents

- A. Streams and totals
- B. Mole composition of a stream
- C. Integrated amounts
- D. Mass-flow view and mass composition
- E. Rescaling and signed balances

## iv. References

- R. M. Felder, R. W. Rousseau and L. G. Bullard, *Elementary Principles of
  Chemical Processes*, 4th ed., Wiley (2016), Chapter 3 (mass and mole
  fractions, flow rates) and Chapter 4 (material balances).
- `PhyslibExt.Chemistry.Amounts.MolarMassComposition`: `moleFraction`,
  `massFraction`, their normalizations and inverse conversions, imported
  here.
-/

@[expose] public section

namespace Engineering.Process.Streams

/-! ## A. Streams and totals -/

/-- A process stream: nonnegative species amount-flow rates over a finite
species type `ι`, in moles per declared time unit. Numerical values after a
consistent choice of units; dimensions are not tracked. -/
structure StreamFlow (ι : Type*) [Fintype ι] where
  /-- The amount-flow rate `ṅ i` of species `i`. -/
  flow : ι → ℝ
  /-- Every species flow rate is nonnegative. -/
  nonneg : ∀ i, 0 ≤ flow i

namespace StreamFlow

/-- The zero stream, with every species flow rate equal to zero. -/
def zero (ι : Type*) [Fintype ι] : StreamFlow ι :=
  ⟨fun _ => 0, fun _ => le_refl 0⟩

/-- The total amount-flow rate `∑ i, ṅ i` of a stream. -/
def total {ι : Type*} [Fintype ι] (s : StreamFlow ι) : ℝ :=
  ∑ i, s.flow i

/-- The total flow of the zero stream is zero. -/
lemma zero_total (ι : Type*) [Fintype ι] : (zero ι).total = 0 := by
  simp only [zero, total, Finset.sum_const_zero]

/-- The total flow of a stream is nonnegative. -/
lemma total_nonneg {ι : Type*} [Fintype ι] (s : StreamFlow ι) : 0 ≤ s.total := by
  simp only [total]
  exact Finset.sum_nonneg fun i _ => s.nonneg i

/-- A stream has zero total flow exactly when every species flow is zero. -/
lemma total_eq_zero_iff {ι : Type*} [Fintype ι] (s : StreamFlow ι) :
    s.total = 0 ↔ ∀ i, s.flow i = 0 := by
  simp only [total]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => s.nonneg i)]
  simp

/-! ## B. Mole composition of a stream -/

/-- The mole composition of a stream, as mole fractions of its flow vector.
Produced only under a positive total flow; a zero-flow stream returns
`none`. -/
noncomputable def composition {ι : Type*} [Fintype ι] (s : StreamFlow ι) :
    Option (ι → ℝ) :=
  if 0 < s.total then some (Chemistry.Amounts.moleFraction s.flow) else none

/-- **Composition port.** Under a positive total flow, the composition of a
stream is `Chemistry.Amounts.moleFraction` of its flow vector. -/
lemma composition_eq_moleFraction {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    (hs : 0 < s.total) :
    s.composition = some (Chemistry.Amounts.moleFraction s.flow) := by
  unfold composition
  rw [ite_eq_left hs]

/-- A stream has no composition exactly when its total flow is zero. -/
lemma composition_eq_none_iff {ι : Type*} [Fintype ι] (s : StreamFlow ι) :
    s.composition = none ↔ s.total = 0 := by
  unfold composition
  by_cases hs : 0 < s.total
  · rw [ite_eq_left hs]
    exact iff_of_false (Option.some_ne_none _) hs.ne'
  · rw [ite_eq_right hs]
    exact iff_of_true rfl (le_antisymm (le_of_not_gt hs) (total_nonneg s))

/-- The zero stream has no composition. -/
lemma zero_composition (ι : Type*) [Fintype ι] : (zero ι).composition = none := by
  exact (composition_eq_none_iff _).mpr (zero_total _)

/-- The mole fractions of a positive-total stream are nonnegative. -/
lemma moleFraction_nonneg {ι : Type*} [Fintype ι] (s : StreamFlow ι) (i : ι) :
    0 ≤ Chemistry.Amounts.moleFraction s.flow i := by
  exact Chemistry.Amounts.moleFraction_nonneg s.nonneg i

/-- The composition of a stream sums to one: whenever
`s.composition = some x`, `∑ i, x i = 1`. By the imported
`Chemistry.Amounts.sum_moleFraction`. -/
lemma sum_composition {ι : Type*} [Fintype ι] (s : StreamFlow ι) {x : ι → ℝ}
    (hx : s.composition = some x) : ∑ i, x i = 1 := by
  unfold composition at hx
  by_cases hs : 0 < s.total
  · rw [ite_eq_left hs] at hx
    cases hx
    exact Chemistry.Amounts.sum_moleFraction hs
  · rw [ite_eq_right hs] at hx
    cases hx

/-! ## C. Integrated amounts -/

/-- The amounts obtained by running a constant stream for a duration `Δt`:
species `i` accumulates `Δt * ṅ i`. -/
def integrate {ι : Type*} [Fintype ι] (s : StreamFlow ι) (Δt : ℝ) : ι → ℝ :=
  fun i => Δt * s.flow i

/-- Integrating over a zero duration gives zero amounts. -/
lemma integrate_zero {ι : Type*} [Fintype ι] (s : StreamFlow ι) :
    s.integrate 0 = fun _ => 0 := by
  funext i
  simp [integrate]

/-- The total integrated amount is the duration times the total flow. -/
lemma sum_integrate {ι : Type*} [Fintype ι] (s : StreamFlow ι) (Δt : ℝ) :
    ∑ i, s.integrate Δt i = Δt * s.total := by
  simp only [integrate, total, Finset.mul_sum]

set_option linter.unusedVariables false in
/-- **Time-unit erasure.** For a positive duration `Δt > 0`, the amount
fractions of the integrated batch equal the flow fractions of the stream:
integrating a constant stream does not change its composition. -/
lemma composition_of_integrate {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    {Δt : ℝ} (hΔt : 0 < Δt) (hs : 0 < s.total) :
    Chemistry.Amounts.moleFraction (s.integrate Δt) =
      Chemistry.Amounts.moleFraction s.flow := by
  funext i
  simp only [Chemistry.Amounts.moleFraction, integrate, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hΔt.ne']

/-! ## D. Mass-flow view and mass composition -/

/-- The mass-flow view of a stream: species `i` carries mass at rate
`ṁ i = ṅ i * M i` for molar masses `M`. -/
def massFlow {ι : Type*} [Fintype ι] (s : StreamFlow ι) (M : ι → ℝ) : ι → ℝ :=
  fun i => s.flow i * M i

/-- Mass fractions of the flow vector are mole fractions of the mass-flow
vector. -/
lemma massFraction_eq_moleFraction_massFlow {ι : Type*} [Fintype ι]
    (s : StreamFlow ι) (M : ι → ℝ) :
    Chemistry.Amounts.massFraction M s.flow =
      Chemistry.Amounts.moleFraction (s.massFlow M) := by
  rfl

/-- The mass composition of a stream for molar masses `M`, as mass fractions
of its flow vector, in the imported API's domain `∀ i, 0 < M i`. Produced
only in that domain and under a positive total flow; otherwise (zero or
negative molar masses at any species, zero total flow) it returns `none`. -/
noncomputable def massComposition {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    (M : ι → ℝ) : Option (ι → ℝ) :=
  if (∀ i, 0 < M i) ∧ 0 < s.total then
    some (Chemistry.Amounts.massFraction M s.flow)
  else none

/-- A species with a nonpositive molar mass makes the mass composition
undefined, regardless of its flow. -/
lemma massComposition_eq_none_of_nonpos_at {ι : Type*} [Fintype ι]
    (s : StreamFlow ι) (M : ι → ℝ) (i : ι) (hi : M i ≤ 0) :
    s.massComposition M = none := by
  unfold massComposition
  rw [ite_eq_right (fun h => not_lt_of_ge hi (h.1 i))]

/-- With positive molar masses, a positive total amount flow gives a
positive total mass flow. By the imported
`Chemistry.Amounts.sum_amount_mul_molarMass_pos`. -/
lemma sum_massFlow_pos {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    (M : ι → ℝ) (hM : ∀ i, 0 < M i) (hs : 0 < s.total) :
    0 < ∑ i, s.massFlow M i := by
  have hs' : 0 < ∑ i, s.flow i := hs
  simpa only [massFlow] using
    Chemistry.Amounts.sum_amount_mul_molarMass_pos s.nonneg hs' hM

/-- A stream with no positive total mass flow has no mass composition. -/
lemma massComposition_eq_none_of_sum_nonpos {ι : Type*} [Fintype ι]
    (s : StreamFlow ι) (M : ι → ℝ) (h : ∑ i, s.massFlow M i ≤ 0) :
    s.massComposition M = none := by
  unfold massComposition
  rw [ite_eq_right (fun h' => not_lt_of_ge h (sum_massFlow_pos s M h'.1 h'.2))]

/-- Under a positive total flow and positive molar masses, the mass
composition is `Chemistry.Amounts.massFraction` of the flow vector. -/
lemma massComposition_eq_massFraction {ι : Type*} [Fintype ι]
    (s : StreamFlow ι) (M : ι → ℝ) (hM : ∀ i, 0 < M i) (hs : 0 < s.total) :
    s.massComposition M = some (Chemistry.Amounts.massFraction M s.flow) := by
  unfold massComposition
  rw [ite_eq_left ⟨hM, hs⟩]

/-- The mass composition of a stream sums to one for positive molar masses:
whenever `s.massComposition M = some w`, `∑ i, w i = 1`. By the imported
`Chemistry.Amounts.sum_massFraction`. -/
lemma sum_massComposition {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    (M : ι → ℝ) (hM : ∀ i, 0 < M i) {w : ι → ℝ}
    (hw : s.massComposition M = some w) : ∑ i, w i = 1 := by
  unfold massComposition at hw
  by_cases h : (∀ i, 0 < M i) ∧ 0 < s.total
  · rw [ite_eq_left h] at hw
    cases hw
    have hs' : 0 < ∑ i, s.flow i := h.2
    exact Chemistry.Amounts.sum_massFraction s.nonneg hs' hM
  · rw [ite_eq_right h] at hw
    cases hw

/-- **Mole to mass and back.** Converting a stream's mole composition to mass
fractions and back returns the mole composition. This is the imported
`Chemistry.Amounts.moleFractionOfMassFraction_massFraction_of_sum_eq_one`
applied to the flow fractions, which lie on the simplex by
`Chemistry.Amounts.sum_moleFraction`. -/
lemma mass_mole_round_trip {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    (M : ι → ℝ) (hM : ∀ i, 0 < M i) (hs : 0 < s.total) :
    Chemistry.Amounts.moleFractionOfMassFraction M
        (Chemistry.Amounts.massFraction M (Chemistry.Amounts.moleFraction s.flow)) =
      Chemistry.Amounts.moleFraction s.flow := by
  have hs' : 0 < ∑ i, s.flow i := hs
  exact Chemistry.Amounts.moleFractionOfMassFraction_massFraction_of_sum_eq_one
    (Chemistry.Amounts.moleFraction_nonneg s.nonneg)
    (Chemistry.Amounts.sum_moleFraction hs') hM

/-- **Mass to mole and back.** Converting a stream's mass composition to mole
fractions and back returns the mass composition. This is the imported
`Chemistry.Amounts.massFraction_moleFractionOfMassFraction_of_sum_eq_one`
applied to the mass-flow fractions, which lie on the simplex by
`Chemistry.Amounts.sum_massFraction`. -/
lemma mole_mass_round_trip {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    (M : ι → ℝ) (hM : ∀ i, 0 < M i) (hs : 0 < s.total) :
    Chemistry.Amounts.massFraction M
        (Chemistry.Amounts.moleFractionOfMassFraction M
          (Chemistry.Amounts.massFraction M s.flow)) =
      Chemistry.Amounts.massFraction M s.flow := by
  have hs' : 0 < ∑ i, s.flow i := hs
  exact Chemistry.Amounts.massFraction_moleFractionOfMassFraction_of_sum_eq_one
    (Chemistry.Amounts.massFraction_nonneg s.nonneg hM)
    (Chemistry.Amounts.sum_massFraction s.nonneg hs' hM) hM

/-! ## E. Rescaling and signed balances -/

/-- Rescale every species flow of a stream by a nonnegative factor `α`
(amount-unit or inverse-time-unit change). -/
def rescale {ι : Type*} [Fintype ι] (s : StreamFlow ι) {α : ℝ} (hα : 0 ≤ α) :
    StreamFlow ι :=
  ⟨fun i => α * s.flow i, fun i => mul_nonneg hα (s.nonneg i)⟩

/-- Rescaling scales the total flow by the same factor. -/
lemma total_rescale {ι : Type*} [Fintype ι] (s : StreamFlow ι) {α : ℝ}
    (hα : 0 ≤ α) : (s.rescale hα).total = α * s.total := by
  simp only [rescale, total, Finset.mul_sum]

/-- A species flow balance: inflow minus outflow plus net generation
equals accumulation, componentwise. The material streams `sIn` and `sOut`
are nonnegative `StreamFlow` rates, while net generation `gen` and
accumulation `acc` are signed rates: net consumption is negative
generation and draining is negative accumulation. -/
def IsBalance {ι : Type*} [Fintype ι] (sIn sOut : StreamFlow ι)
    (gen acc : ι → ℝ) : Prop :=
  ∀ i, sIn.flow i - sOut.flow i + gen i = acc i

/-- **Balance rescaling.** For a positive scale, the rescaled streams form
a balance exactly when the original streams do. -/
lemma balance_rescale_iff {ι : Type*} [Fintype ι] {α : ℝ} (hα : 0 < α)
    (sIn sOut : StreamFlow ι) (gen acc : ι → ℝ) :
    IsBalance (sIn.rescale hα.le) (sOut.rescale hα.le)
        (fun i => α * gen i) (fun i => α * acc i) ↔
      IsBalance sIn sOut gen acc := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  simp only [IsBalance, rescale]
  constructor
  · intro h i
    have hi := h i
    have hfac : α * (sIn.flow i - sOut.flow i + gen i) = α * acc i := by
      linear_combination hi
    exact mul_left_cancel₀ hα0 hfac
  · intro h i
    have hi := h i
    linear_combination α * hi

/-- Mole fractions are invariant under a common positive rescaling of the
flow vector (the algebraic core of composition invariance). -/
lemma moleFraction_rescale {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    {α : ℝ} (hα : α ≠ 0) :
    Chemistry.Amounts.moleFraction (fun i => α * s.flow i) =
      Chemistry.Amounts.moleFraction s.flow := by
  funext i
  simp only [Chemistry.Amounts.moleFraction, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hα]

/-- **Composition invariance.** Under a positive rescaling and a positive
total flow, the rescaled stream has the same composition as the original. -/
lemma composition_rescale {ι : Type*} [Fintype ι] (s : StreamFlow ι)
    {α : ℝ} (hα : 0 < α) (hs : 0 < s.total) :
    (s.rescale hα.le).composition = s.composition := by
  have hs' : 0 < (s.rescale hα.le).total := by
    rw [total_rescale]
    exact mul_pos hα hs
  rw [composition_eq_moleFraction _ hs', composition_eq_moleFraction _ hs]
  congr 1
  exact moleFraction_rescale s hα.ne'

end StreamFlow

end Engineering.Process.Streams
