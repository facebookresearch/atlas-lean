/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.BigOperators.SumRangeDrop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Layered Darcy series conductivity

## i. Overview

For ordered saturated layers in series with thicknesses `L i`
and conductivities `K i`, continuous interface heads, and a
supplied common steady Darcy flux satisfying the per-layer drop
law `head i - head (i + 1) = q * (L i / K i)`, the effective
conductivity is the total thickness over the summed resistances
`L i / K i`, and the flux is recovered from the end heads. The
per-layer Darcy relation is a supplied model assumption; no
constitutive law is derived and the flux is discharge per bulk
area, not pore speed.

## ii. Key results

- `EarthScience.layeredEffectiveConductivity_pos`: positivity
  of the effective conductivity.
- `EarthScience.layeredDarcyFlux_of_drops`: flux recovery from
  the interface drop laws.
- `EarthScience.layeredDarcyFlux_eq_eff_mul`: the end-head flux
  formula through the effective conductivity.

## iii. Table of contents

- A. Effective conductivity and flux recovery

## iv. References

- J. Bear, *Dynamics of Fluids in Porous Media*, 1972
  (equivalent conductivity of layered media).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Effective conductivity and flux recovery -/

/-- Effective hydraulic conductivity for `n` ordered Darcy layers
in series: the total thickness divided by the summed layer
resistances `L i / K i`. Layers are indexed in flow order
`0, ..., n - 1`. This records the series effective conductivity
implied by a supplied common steady Darcy flux and continuous
interface heads satisfying the per-layer drop law below; it does
not derive Darcy's constitutive law.

The physical effective-conductivity reading is for positive
layer conductivities, the regime of the theorems below. As a
raw real quotient the definition is totalized outside that
regime: with the convention `x / 0 = 0`, a zero-conductivity
layer contributes `0` to the summed resistance, so an impermeable
layer in series is outside the domain of this formula, and the
value is `0` when the summed resistance is `0` (for example
`n = 0`). -/
noncomputable def layeredEffectiveConductivity {n : ℕ}
    (L K : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, L i) / (∑ i ∈ Finset.range n, L i / K i)

/-- The effective conductivity is positive for at least one layer
with positive thicknesses and conductivities. -/
theorem layeredEffectiveConductivity_pos {n : ℕ} (hn : 1 ≤ n)
    (L K : ℕ → ℝ) (hL : ∀ i < n, 0 < L i)
    (hK : ∀ i < n, 0 < K i) :
    0 < layeredEffectiveConductivity (n := n) L K := by
  have h0n : 0 < n := by omega
  have hT : 0 < ∑ i ∈ Finset.range n, L i :=
    Finset.sum_pos (fun i hi => hL i (Finset.mem_range.mp hi))
      ⟨0, Finset.mem_range.mpr h0n⟩
  have hS : 0 < ∑ i ∈ Finset.range n, L i / K i :=
    Finset.sum_pos
      (fun i hi => div_pos (hL i (Finset.mem_range.mp hi))
        (hK i (Finset.mem_range.mp hi)))
      ⟨0, Finset.mem_range.mpr h0n⟩
  unfold layeredEffectiveConductivity
  exact div_pos hT hS

/-- Flux recovery from interface drop laws (source direction).
Let `head 0, ..., head n` be continuous interface heads in flow
order of at least one layer with positive thicknesses `L i` and
conductivities `K i`, and let `q` be a supplied common steady Darcy flux satisfying
the per-layer drop law `head i - head (i + 1) = q * (L i / K i)`
for each layer. Then `q` is the total head drop divided by the
summed series resistance. The per-layer Darcy drop relation is an
explicit supplied model assumption, not derived here. -/
theorem layeredDarcyFlux_of_drops {n : ℕ} (hn : 1 ≤ n)
    {L K head : ℕ → ℝ} {q : ℝ}
    (hL : ∀ i < n, 0 < L i) (hK : ∀ i < n, 0 < K i)
    (hdrop : ∀ i < n, head i - head (i + 1) = q * (L i / K i)) :
    q = (head 0 - head n)
      / (∑ i ∈ Finset.range n, L i / K i) := by
  exact MathlibExt.eq_div_sum_range (R := fun i => L i / K i) (P := head) hn
    (fun i hi => div_pos (hL i hi) (hK i hi)) hdrop

/-- End-head flux formula through the effective conductivity:
for at least one layer with positive thicknesses and conductivities,
under the same supplied drop laws, the common flux equals
`K_eff * (head 0 - head n) / (∑ i, L i)`. -/
theorem layeredDarcyFlux_eq_eff_mul {n : ℕ} (hn : 1 ≤ n)
    {L K head : ℕ → ℝ} {q : ℝ}
    (hL : ∀ i < n, 0 < L i) (hK : ∀ i < n, 0 < K i)
    (hdrop : ∀ i < n, head i - head (i + 1) = q * (L i / K i)) :
    q = layeredEffectiveConductivity (n := n) L K * (head 0 - head n)
      / (∑ i ∈ Finset.range n, L i) := by
  have hq := layeredDarcyFlux_of_drops (n := n) hn hL hK hdrop
  have h0n : 0 < n := by omega
  have hT : (∑ i ∈ Finset.range n, L i) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun i hi => hL i (Finset.mem_range.mp hi))
      ⟨0, Finset.mem_range.mpr h0n⟩)
  have hS : (∑ i ∈ Finset.range n, L i / K i) ≠ 0 :=
    ne_of_gt (Finset.sum_pos
      (fun i hi => div_pos (hL i (Finset.mem_range.mp hi))
        (hK i (Finset.mem_range.mp hi)))
      ⟨0, Finset.mem_range.mpr h0n⟩)
  unfold layeredEffectiveConductivity
  rw [hq]
  field_simp

end EarthScience
