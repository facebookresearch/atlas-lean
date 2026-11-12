/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Chained-index non-additivity

A chained index links one-period Laspeyres volume growths; the chained real
value of a basket is its base-period nominal value times the chained index.
For one component the chained value is its base value times its own quantity
ratio, since for a single good the Laspeyres growth telescopes. The sum of
chained components need not equal the chained total: in the concrete example
below (period-0 prices `(1, 1)`, quantities `(100, 100)`; period-1 prices
`(1, 4)`, quantities `(50, 100)`; period-2 quantities `(50, 200)`) the
chained total is `850/3` while the components sum to `250`. One link alone is
additive; the second link, weighted by the changed period-1 prices, breaks
additivity. All values are exact rationals.

## Main results

* `MathlibExt.Economics.Macro.ChainedIndex.chained_components_not_additive`:
  the concrete non-additivity example.
* `MathlibExt.Economics.Macro.ChainedIndex.chained_example_growths`: the two
  one-period growths `3/4` and `17/9`.
* `MathlibExt.Economics.Macro.ChainedIndex.chainedComponentValue_eq`: a single
  component's chained value is its base price times its final quantity.

## References

Atlas roadmap target MA02.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.ChainedIndex

/-- Laspeyres volume growth from one period to the next: base-period prices
weight the quantity change. -/
noncomputable def laspeyresVolumeGrowth (pPrev qPrev qCurr : Fin 2 → ℚ) : ℚ :=
  (∑ i, pPrev i * qCurr i) / (∑ i, pPrev i * qPrev i)

/-- A two-link chained index is the product of the two one-period growths. -/
noncomputable def chainedIndexTwoLinks (g₁ g₂ : ℚ) : ℚ :=
  g₁ * g₂

/-- Chained real value of a basket: base-period nominal value times the
chained index. -/
noncomputable def chainedRealValue (baseNominal index : ℚ) : ℚ :=
  baseNominal * index

/-- Chained real value of one component: its base-period value times its own
quantity ratio `q₂ / q₀`. For a single good the Laspeyres growth telescopes
to the quantity ratio, since the base-period price cancels. -/
noncomputable def chainedComponentValue (baseValue q₀ q₂ : ℚ) : ℚ :=
  baseValue * (q₂ / q₀)

/-- A single component's chained value is its base-period price times its
final quantity: the base quantity cancels against the quantity ratio. -/
theorem chainedComponentValue_eq (basePrice q₀ q₂ : ℚ) (h₀ : q₀ ≠ 0) :
    chainedComponentValue (basePrice * q₀) q₀ q₂ = basePrice * q₂ := by
  unfold chainedComponentValue
  field_simp

/-- The two one-period Laspeyres growths of the concrete example.
Period 0: prices `(1, 1)`, quantities `(100, 100)`.
Period 1: prices `(1, 4)`, quantities `(50, 100)`.
Period 2: quantities `(50, 200)` (period-1 prices weight the second link). -/
theorem chained_example_growths :
    laspeyresVolumeGrowth ![1, 1] ![100, 100] ![50, 100] = 3 / 4 ∧
      laspeyresVolumeGrowth ![1, 4] ![50, 100] ![50, 200] = 17 / 9 := by
  constructor
  · unfold laspeyresVolumeGrowth
    simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · unfold laspeyresVolumeGrowth
    simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-- **Non-additivity of chained real components.** The chained total
(`200 * (3/4 * 17/9) = 850/3`) is not the sum of the chained components
(`50 + 200 = 250`). One link alone is additive; the second link, weighted by
the changed period-1 prices, breaks additivity. -/
theorem chained_components_not_additive :
    chainedComponentValue 100 100 50 + chainedComponentValue 100 100 200 ≠
      chainedRealValue (∑ i, ![1, 1] i * ![100, 100] i)
        (chainedIndexTwoLinks
          (laspeyresVolumeGrowth ![1, 1] ![100, 100] ![50, 100])
          (laspeyresVolumeGrowth ![1, 4] ![50, 100] ![50, 200])) := by
  unfold chainedComponentValue chainedRealValue chainedIndexTwoLinks laspeyresVolumeGrowth
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end MathlibExt.Economics.Macro.ChainedIndex
