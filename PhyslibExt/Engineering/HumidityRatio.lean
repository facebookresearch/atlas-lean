/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# Humidity ratio over the shared vapor inventory

## i. Overview

Water-vapor mass is read in the shared finite node inventory
of `MathlibExt.Combinatorics.Graph.ArcNetwork`
(`stock_level_arc_balance`): one stock unit, distinct
transfers, external additions and retirements. With a constant
positive dry-air inventory (one real number, the same at both
ends of the interval), the humidity ratio is vapor mass
divided by dry-air mass, and the mass/ratio conversion is
reversible. A changing dry-air inventory would need both
endpoint denominators and a denominator-change term (or a
separate dry-air balance) and is not included; a quotient
derivative belongs to a continuous-time extension. The dry-air mass here
is a total over the same inventory nodes, held constant over
the interval; it is not a per-node field.

## ii. Key results

- `Engineering.HumidityRatio.humidityRatio`: vapor mass per unit dry-air
  mass.
- `Engineering.HumidityRatio.vaporMass_eq_humidityRatio_mul` and
  `humidityRatio_mul_dryAir`: the reversible conversion.
- `Engineering.HumidityRatio.totalHumidityRatio_update`: the total ratio
  over one inventory interval, from the shared balance.

## iii. Table of contents

- A. Humidity ratio and conversion
- B. Total ratio over one interval

## iv. References

- `MathlibExt.Combinatorics.Graph.ArcNetwork` for the shared
  stock-level balance.
- Standard psychrometric humidity ratio (mass of water vapor
  per mass of dry air); see e.g. ASHRAE Handbook,
  Fundamentals, Psychrometrics chapter.
-/

@[expose] public section

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork

namespace Engineering.HumidityRatio

/-! ## A. Humidity ratio and conversion -/

/-- Humidity ratio: vapor mass per unit dry-air mass. -/
noncomputable def humidityRatio (mVapor mDryAir : ℝ) : ℝ :=
  mVapor / mDryAir

/-- Vapor mass recovered from the humidity ratio and the
(constant, positive) dry-air mass. -/
theorem vaporMass_eq_humidityRatio_mul {mVapor mDryAir : ℝ}
    (hda : 0 < mDryAir) :
    mVapor = humidityRatio mVapor mDryAir * mDryAir := by
  unfold humidityRatio
  exact (div_mul_cancel₀ mVapor (ne_of_gt hda)).symm

/-- A vapor mass formed as ratio times dry-air mass has that
ratio. -/
theorem humidityRatio_mul_dryAir {W mDryAir : ℝ}
    (hda : 0 < mDryAir) :
    humidityRatio (W * mDryAir) mDryAir = W := by
  unfold humidityRatio
  exact mul_div_cancel_right₀ W (ne_of_gt hda)

/-- Zero vapor mass has zero humidity ratio (at the physical
positive dry-air mass). -/
theorem humidityRatio_zero_vapor {mDryAir : ℝ}
    (_hda : 0 < mDryAir) :
    humidityRatio 0 mDryAir = 0 := by
  unfold humidityRatio
  exact zero_div mDryAir

/-- The humidity ratio of a nonnegative vapor mass over
positive dry air is nonnegative. -/
theorem humidityRatio_nonneg {mVapor mDryAir : ℝ}
    (hm : 0 ≤ mVapor) (hda : 0 < mDryAir) :
    0 ≤ humidityRatio mVapor mDryAir := by
  unfold humidityRatio
  exact div_nonneg hm (le_of_lt hda)

/-! ## B. Total ratio over one interval -/

/-- Total humidity ratio over one inventory interval, from
the shared stock balance (supplied as `hbalance`): the
updated total ratio is the initial total ratio plus external
additions minus retirements, all over the same constant
dry-air mass. -/
private lemma totalHumidityRatio_update_of {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (hbalance : ∀ (tail head : E → V) (F : E → ℝ)
        {m m' s r : V → ℝ},
      m' = m + (incidenceMatrix tail head).mulVec F + s - r →
      ∑ v, m' v = ∑ v, m v + ∑ v, s v - ∑ v, r v)
    (tail head : E → V) (F : E → ℝ) {m m' s r : V → ℝ}
    (h : m' = m + (incidenceMatrix tail head).mulVec F + s - r)
    {mDryAir : ℝ} (_hda : 0 < mDryAir) :
    humidityRatio (∑ v, m' v) mDryAir
      = humidityRatio (∑ v, m v) mDryAir
        + ((∑ v, s v) - (∑ v, r v)) / mDryAir := by
  have htot := hbalance tail head F h
  unfold humidityRatio
  rw [htot, sub_div, add_div, sub_div, add_sub_assoc]

/-- Total humidity ratio over one inventory interval: the
updated total ratio is the initial total ratio plus external
additions minus retirements, all over the same constant
dry-air mass. -/
lemma totalHumidityRatio_update {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (F : E → ℝ) {m m' s r : V → ℝ}
    (h : m' = m + (incidenceMatrix tail head).mulVec F + s - r)
    {mDryAir : ℝ} (_hda : 0 < mDryAir) :
    humidityRatio (∑ v, m' v) mDryAir
      = humidityRatio (∑ v, m v) mDryAir
        + ((∑ v, s v) - (∑ v, r v)) / mDryAir :=
  totalHumidityRatio_update_of stock_level_arc_balance
    tail head F h _hda

end Engineering.HumidityRatio
