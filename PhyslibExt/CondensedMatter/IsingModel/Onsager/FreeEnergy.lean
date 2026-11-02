/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalPoint
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.Pressure
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.Torus

/-!

# Onsager's free energy and the torus pressure

Onsager's pressure `log 2 + (1 / 8π²) ∫∫ log g`, the torus pressure, and the reduction of its limit
to the even-subgraph sums.

## i. Overview

Onsager's pressure of the square-lattice Ising model is
`p(β) = log 2 + (1 / (8π²)) ∫∫ log (cosh² 2β - sinh 2β (cos k₁ + cos k₂)) dk₁ dk₂`, the integral
over `[-π, π]²`.
On the torus `ℤ_L × ℤ_L` (`L > 2`), with `L²` sites and `2 L²` edges, the finite-volume pressure is
`log 2 + 2 log cosh β + log X_L(tanh β) / L²`. So the torus pressure converges to `p(β)` exactly
when `log X_L(tanh β) / L²` converges to `(1 / 8π²) ∫∫ log g - 2 log cosh β`; this condition is
`ons_KacWardResidue β`.

## ii. Key results

- `ons_freeEnergyIntegral` : the double integral in Onsager's formula
- `ons_pressure` : Onsager's pressure
- `ons_KacWardResidue` : convergence of the normalized even-subgraph sums
- `ons_torusPressure_eq` : the torus pressure decomposition
- `ons_free_energy_of_KacWardResidue` : the torus pressure converges to Onsager's pressure when the
  residue converges

## iii. Table of contents

- A. Onsager's pressure
- B. The torus pressure

## iv. References

- L. Onsager, *Crystal statistics. I. A two-dimensional model with an order-disorder transition*,
  Phys. Rev. 65 (1944) 117-149

-/

@[expose] public section

namespace StatMech.Onsager

open StatMech.Ising

/-! ## A. Onsager's pressure -/

/-- The integral
`(1 / (8π²)) ∫_{-π}^{π} ∫_{-π}^{π} log (cosh² 2β - sinh 2β (cos k₁ + cos k₂)) dk₁ dk₂` in Onsager's
formula. -/
noncomputable def ons_freeEnergyIntegral (β : ℝ) : ℝ :=
  (1 / (8 * Real.pi ^ 2)) *
    ∫ k₁ in (-Real.pi)..Real.pi, ∫ k₂ in (-Real.pi)..Real.pi, Real.log (ons_gInt β k₁ k₂)

/-- Onsager's pressure (minus `β` times the free energy per site) of the square-lattice Ising model:
`log 2` plus `ons_freeEnergyIntegral β`. -/
noncomputable def ons_pressure (β : ℝ) : ℝ := Real.log 2 + ons_freeEnergyIntegral β

/-- The statement that `log X_L(tanh β) / L²` on the `L × L` torus converges to
`ons_freeEnergyIntegral β - 2 log cosh β` as `L → ∞`. -/
def ons_KacWardResidue (β : ℝ) : Prop :=
  Filter.Tendsto
    (fun L : ℕ => if h : 2 < L then
        (letI : Fact (2 < L) := ⟨h⟩
         Real.log (ons_X (onsTorusGraph L) (Real.tanh β)) / ((L : ℝ) ^ 2))
      else 0)
    Filter.atTop
    (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β)))

/-! ## B. The torus pressure -/

lemma ons_torusPressure_eq (L : ℕ) [Fact (2 < L)] (β : ℝ) (hβ : 0 ≤ β) :
    ons_pressureFinite (onsTorusGraph L) β
      = Real.log 2 + 2 * Real.log (Real.cosh β)
        + Real.log (ons_X (onsTorusGraph L) (Real.tanh β)) / ((L : ℝ) ^ 2) := by
  have hV : 0 < Fintype.card (ZMod L × ZMod L) := by
    rw [onsTorus_card_verts]
    have hL : 0 < L := by have := (Fact.out : 2 < L); omega
    exact pow_pos hL 2
  rw [ons_pressureFinite_eq _ β hβ hV, onsTorus_card_edges, onsTorus_card_verts]
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Fact.out : 2 < L); omega)
  have hcoef : ((2 * L ^ 2 : ℕ) : ℝ) / ((L ^ 2 : ℕ) : ℝ) = 2 := by
    push_cast
    rw [mul_div_assoc, div_self (pow_ne_zero 2 hLne), mul_one]
  rw [hcoef]
  push_cast
  ring

lemma ons_free_energy_of_KacWardResidue
    (β : ℝ) (hβ : 0 ≤ β) (hres : ons_KacWardResidue β) :
    Filter.Tendsto
      (fun L : ℕ => if h : 2 < L then
          (letI : Fact (2 < L) := ⟨h⟩; ons_pressureFinite (onsTorusGraph L) β)
        else 0)
      Filter.atTop (nhds (ons_pressure β)) := by
  have hval : ons_pressure β
      = (Real.log 2 + 2 * Real.log (Real.cosh β))
        + (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β)) := by
    unfold ons_pressure; ring
  rw [hval]
  unfold ons_KacWardResidue at hres
  have htend := hres.const_add (Real.log 2 + 2 * Real.log (Real.cosh β))
  refine htend.congr' ?_
  refine Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩
  have hLpos : 2 < L := by omega
  simp only [dite_eq_left hLpos]
  have : Fact (2 < L) := ⟨hLpos⟩
  rw [ons_torusPressure_eq L β hβ]

end StatMech.Onsager
