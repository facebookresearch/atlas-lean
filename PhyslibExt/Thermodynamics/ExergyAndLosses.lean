/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import PhyslibExt.Thermodynamics.ProcessPorts

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Exergy and losses: exergy destruction from separately declared balances

## i. Overview

A steady open system exchanges heat `Q̇ⱼ` through ports `j` at boundary temperatures `Tⱼ`,
exchanges shaft power, and carries mass through inlet streams `i` and outlet streams `o`. The
first law and the entropy balance are separately declared model inputs with matched ports: each
stream enters both balances with the same mass flow `ṁ`, carrying energy `ṁ θ` and entropy
`ṁ s`, and each heat port enters both with the same heat rate, carrying energy `Q̇ⱼ` and entropy
`Q̇ⱼ / Tⱼ`. Here `θ = h + |v|² / 2 + g z` is the port energy per unit mass of
`ControlVolumes.portEnergyRate_eq_massFlow` (flow work counted once, inside `h`), and the shaft
work out is `ProcessPorts.workOut w` for the power `w` delivered to the system (IUPAC sign).
Heat rates are positive into the system; mass flows are positive along the flow, into the
system at an inlet and out of it at an outlet.

The entropy generation rate `Ṡ_gen = ∑ₒ ṁₒ sₒ - ∑ᵢ ṁᵢ sᵢ - ∑ⱼ Q̇ⱼ / Tⱼ` is the residual of the
steady entropy balance; it is not assumed nonnegative. The exergy destruction rate is the
residual of the steady exergy balance, exergy in minus exergy out,
`Ẋ_dest = ∑ⱼ (1 - T₀ / Tⱼ) Q̇ⱼ - Ẇ_out + ∑ᵢ ṁᵢ ψᵢ - ∑ₒ ṁₒ ψₒ`, with the flow exergy
`ψ = θ - h₀ - T₀ (s - s₀)` taken relative to one dead state `(T₀, h₀, s₀)` in every stream
term. The decomposition
`Ẋ_dest = (first-law residual) + (T₀ s₀ - h₀) (∑ ṁᵢ - ∑ ṁₒ) + T₀ Ṡ_gen` is algebra; with the
steady first law and the steady mass balance it is the Gouy-Stodola relation
`Ẋ_dest = T₀ Ṡ_gen`. Nonnegativity of `Ẋ_dest` follows only from the supplied second-law input
`Ṡ_gen ≥ 0`; energy conservation alone does not give it.

Model inputs and scope: the two balances are hypotheses, never derived. The stream exergy is
thermomechanical; chemical exergy is excluded (non-reacting streams, restricted dead state).
Temperatures are absolute; the physical case is `T₀ > 0` and `Tⱼ > 0`. The identities hold for
all real values, and each result assumes only the hypotheses its proof uses. The Carnot factor
`1 - T₀ / Tⱼ` is negative for a port colder than the environment, a physical case for exergy.

## ii. Key results

- `ExergyAndLosses.exergyDestroyed_eq_add`: the decomposition of `Ẋ_dest` for every dead state.
- `ExergyAndLosses.exergyDestroyed_eq_mul_entropyGen`: `Ẋ_dest = T₀ Ṡ_gen` under the steady
  first law and mass balance.
- `ExergyAndLosses.exergyDestroyed_nonneg`: `0 ≤ Ẋ_dest` from the supplied `0 ≤ Ṡ_gen`.
- `ExergyAndLosses.exergyDestroyed_sub_ref`, `ExergyAndLosses.exergyDestroyed_ref_eq`: a change
  of dead state moves `Ẋ_dest` by a multiple of the mass imbalance, so not at all in steady flow.

## iii. Table of contents

- A. Balances with matched ports
- B. Exergy destruction

## iv. References

- Y. A. Çengel and M. A. Boles, *Thermodynamics: An Engineering Approach*, McGraw-Hill,
  ch. 7-8: the entropy balance with entropy generation, flow exergy
  `ψ = (h - h₀) - T₀ (s - s₀) + V² / 2 + g z`, exergy of heat `(1 - T₀ / T) Q`, the exergy
  balance and `X_destroyed = T₀ S_gen`.
- A. Bejan, *Advanced Engineering Thermodynamics*, Wiley, ch. 3: the Gouy-Stodola theorem.
-/

@[expose] public section

namespace ExergyAndLosses

variable {σ ι κ : Type*} [Fintype σ] [Fintype ι] [Fintype κ]

/-! ## A. Balances with matched ports -/

/-- Residual of the steady first law of an open system: heat in, minus shaft work out, plus the
energy carried in by the inlet streams, minus that carried out by the outlet streams,
`∑ⱼ Q̇ⱼ - Ẇ_out + ∑ᵢ ṁᵢ θᵢ - ∑ₒ ṁₒ θₒ`, with `Ẇ_out = ProcessPorts.workOut w` for the power `w`
delivered to the system and `θ = h + |v|² / 2 + g z` the port energy per unit mass. The
declared steady first law is `energyResidual Q w mi θi mo θo = 0`. -/
def energyResidual (Q : σ → ℝ) (w : ℝ) (mi θi : ι → ℝ) (mo θo : κ → ℝ) : ℝ :=
  ∑ j, Q j - ProcessPorts.workOut w + ∑ i, mi i * θi i - ∑ o, mo o * θo o

/-- Entropy generation rate as the residual of the steady entropy balance with the same ports:
`Ṡ_gen = ∑ₒ ṁₒ sₒ - ∑ᵢ ṁᵢ sᵢ - ∑ⱼ Q̇ⱼ / Tⱼ`. It is a balance residual, not automatically
nonnegative; the second law is the separate input `0 ≤ Ṡ_gen`. Physical boundary temperatures
are positive; at `Tⱼ = 0` Lean's `x / 0 = 0` gives a meaningless term. -/
noncomputable def entropyGen (Q Tb : σ → ℝ) (mi si : ι → ℝ) (mo so : κ → ℝ) : ℝ :=
  ∑ o, mo o * so o - ∑ i, mi i * si i - ∑ j, Q j / Tb j

/-- Specific flow exergy of a stream with port energy `θ = h + |v|² / 2 + g z` and specific
entropy `s`, relative to the dead state at temperature `T₀` with enthalpy `h₀` and entropy `s₀`:
`ψ = θ - h₀ - T₀ (s - s₀) = (h - h₀) - T₀ (s - s₀) + |v|² / 2 + g z`. Thermomechanical part only;
chemical exergy is excluded. -/
def flowExergy (T0 h0 s0 θ s : ℝ) : ℝ := θ - h0 - T0 * (s - s0)

/-! ## B. Exergy destruction -/

/-- Exergy destruction rate as the residual of the steady exergy balance, exergy in minus exergy
out: `Ẋ_dest = ∑ⱼ (1 - T₀ / Tⱼ) Q̇ⱼ - Ẇ_out + ∑ᵢ ṁᵢ ψᵢ - ∑ₒ ṁₒ ψₒ`, with one dead state
`(T₀, h₀, s₀)` in every stream term. -/
noncomputable def exergyDestroyed (T0 h0 s0 : ℝ) (Q Tb : σ → ℝ) (w : ℝ) (mi θi si : ι → ℝ)
    (mo θo so : κ → ℝ) : ℝ :=
  ∑ j, (1 - T0 / Tb j) * Q j - ProcessPorts.workOut w +
    ∑ i, mi i * flowExergy T0 h0 s0 (θi i) (si i) - ∑ o, mo o * flowExergy T0 h0 s0 (θo o) (so o)

/-- **Exergy destruction decomposed.** For every dead state `(T₀, h₀, s₀)`, the destruction rate
is the first-law residual, plus the dead-state terms times the mass imbalance, plus `T₀` times
the entropy generation:
`Ẋ_dest = (first-law residual) + (T₀ s₀ - h₀) (∑ ṁᵢ - ∑ ṁₒ) + T₀ Ṡ_gen`. -/
lemma exergyDestroyed_eq_add (T0 h0 s0 : ℝ) (Q Tb : σ → ℝ) (w : ℝ) (mi θi si : ι → ℝ)
    (mo θo so : κ → ℝ) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so =
      energyResidual Q w mi θi mo θo + (T0 * s0 - h0) * (∑ i, mi i - ∑ o, mo o) +
        T0 * entropyGen Q Tb mi si mo so := by
  unfold exergyDestroyed energyResidual entropyGen flowExergy
  have hQ : ∑ j, (1 - T0 / Tb j) * Q j = ∑ j, Q j - T0 * ∑ j, Q j / Tb j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi : ∑ i, mi i * (θi i - h0 - T0 * (si i - s0))
      = ∑ i, mi i * θi i + (T0 * s0 - h0) * ∑ i, mi i - T0 * ∑ i, mi i * si i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ho : ∑ o, mo o * (θo o - h0 - T0 * (so o - s0))
      = ∑ o, mo o * θo o + (T0 * s0 - h0) * ∑ o, mo o - T0 * ∑ o, mo o * so o := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro o _
    ring
  rw [hQ, hi, ho]
  ring

/-- **Gouy-Stodola relation.** Under the declared steady first law and the steady mass balance
`∑ ṁᵢ = ∑ ṁₒ`, the destroyed exergy is `Ẋ_dest = T₀ Ṡ_gen`, for every dead state. -/
lemma exergyDestroyed_eq_mul_entropyGen {T0 h0 s0 w : ℝ} {Q Tb : σ → ℝ} {mi θi si : ι → ℝ}
    {mo θo so : κ → ℝ} (henergy : energyResidual Q w mi θi mo θo = 0)
    (hmass : ∑ i, mi i = ∑ o, mo o) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so = T0 * entropyGen Q Tb mi si mo so := by
  rw [exergyDestroyed_eq_add, henergy, hmass]
  ring

/-- **Nonnegative destruction from the supplied second law.** With the environment at
`T₀ > 0`, the steady first law, the steady mass balance and the second-law input `0 ≤ Ṡ_gen`,
the destroyed exergy is nonnegative. Without `0 ≤ Ṡ_gen` the conclusion can fail
(`fixture_energy_without_second_law`). -/
lemma exergyDestroyed_nonneg {T0 h0 s0 w : ℝ} {Q Tb : σ → ℝ} {mi θi si : ι → ℝ}
    {mo θo so : κ → ℝ} (hT0 : 0 < T0) (henergy : energyResidual Q w mi θi mo θo = 0)
    (hmass : ∑ i, mi i = ∑ o, mo o) (hgen : 0 ≤ entropyGen Q Tb mi si mo so) :
    0 ≤ exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so := by
  rw [exergyDestroyed_eq_mul_entropyGen henergy hmass]
  exact mul_nonneg (le_of_lt hT0) hgen

/-- **Change of dead state.** Replacing the dead-state enthalpy and entropy `(h₀, s₀)` by
`(h₀', s₀')` in every stream term changes the destroyed exergy by
`(h₀' - h₀ - T₀ (s₀' - s₀)) (∑ ṁᵢ - ∑ ṁₒ)`. -/
lemma exergyDestroyed_sub_ref (T0 h0 s0 h0' s0' : ℝ) (Q Tb : σ → ℝ) (w : ℝ)
    (mi θi si : ι → ℝ) (mo θo so : κ → ℝ) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so -
        exergyDestroyed T0 h0' s0' Q Tb w mi θi si mo θo so =
      (h0' - h0 - T0 * (s0' - s0)) * (∑ i, mi i - ∑ o, mo o) := by
  unfold exergyDestroyed flowExergy
  have hi : ∑ i, mi i * (θi i - h0 - T0 * (si i - s0))
      = ∑ i, mi i * (θi i - h0' - T0 * (si i - s0')) +
        (h0' - h0 - T0 * (s0' - s0)) * ∑ i, mi i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ho : ∑ o, mo o * (θo o - h0 - T0 * (so o - s0))
      = ∑ o, mo o * (θo o - h0' - T0 * (so o - s0')) +
        (h0' - h0 - T0 * (s0' - s0)) * ∑ o, mo o := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    ring
  rw [hi, ho]
  ring

/-- In steady flow (`∑ ṁᵢ = ∑ ṁₒ`) the destroyed exergy does not depend on the dead-state
enthalpy and entropy, provided the same dead state is used in every stream term. -/
lemma exergyDestroyed_ref_eq {T0 h0 s0 h0' s0' w : ℝ} {Q Tb : σ → ℝ} {mi θi si : ι → ℝ}
    {mo θo so : κ → ℝ} (hmass : ∑ i, mi i = ∑ o, mo o) :
    exergyDestroyed T0 h0 s0 Q Tb w mi θi si mo θo so =
      exergyDestroyed T0 h0' s0' Q Tb w mi θi si mo θo so := by
  have h := exergyDestroyed_sub_ref T0 h0 s0 h0' s0' Q Tb w mi θi si mo θo so
  rw [hmass, sub_self, mul_zero] at h
  exact sub_eq_zero.mp h

end ExergyAndLosses
