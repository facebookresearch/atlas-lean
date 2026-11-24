/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Chained-index non-additivity

A chained index links one-period Laspeyres volume growths; the chained real
value of a basket over two links is its period-0 nominal value times the
product of the period-0-to-1 and period-1-to-2 growths. The chained real value
of one component is the same two-link chaining applied to the one-good basket
consisting of that component alone. When its period-1 price and its period-0
and period-1 quantities are nonzero, the component's links telescope and its
chained value is its period-0 price times its period-2 quantity.

The sum of chained components need not equal the chained total: in the
concrete example below (period-0 prices `(1, 1)`, quantities `(100, 100)`;
period-1 prices `(1, 4)`, quantities `(50, 100)`; period-2 quantities
`(50, 200)`) the chained total is `850/3` while the components sum to `250`.
One link alone is additive; the second link, weighted by the changed period-1
prices, breaks additivity. All values are exact rationals.

## Main results

* `MathlibExt.Economics.Macro.ChainedIndex.chained_components_not_additive`:
  the concrete non-additivity example.
* `MathlibExt.Economics.Macro.ChainedIndex.chained_example_growths`: the two
  one-period growths `3/4` and `17/9`.
* `MathlibExt.Economics.Macro.ChainedIndex.chainedComponentValue_eq`: under
  nonzero hypotheses, a component's chained value is its period-0 price times
  its period-2 quantity.

## References

* European Commission, IMF, OECD, United Nations and World Bank,
  *System of National Accounts 2008* (2009), Chapter 15 (Price and volume
  measures): Laspeyres volume indices and chain-linking.
* IMF, *Quarterly National Accounts Manual*, 2017 edition, Chapter 8 (price and
  volume measures): annually chain-linked Laspeyres-type volume measures and
  the lack of additivity of chain-linked components.
* Atlas roadmap target MA02.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.ChainedIndex

variable {ι K : Type*} [Fintype ι] [Field K]

/-- Laspeyres volume growth from one period to the next: previous-period prices
weight the quantity change. -/
def laspeyresVolumeGrowth (pPrev qPrev qCurr : ι → K) : K :=
  (∑ i, pPrev i * qCurr i) / (∑ i, pPrev i * qPrev i)

/-- A two-link chained index is the product of the two one-period growths. -/
def chainedIndexTwoLinks (g₁ g₂ : K) : K :=
  g₁ * g₂

/-- Chained real value of a basket: base-period nominal value times the
chained index. -/
def chainedRealValue (baseNominal index : K) : K :=
  baseNominal * index

/-- Chained real value of a basket over two links: its period-0 nominal value
times the chained index of its period-0-to-1 Laspeyres volume growth (period-0
prices) and its period-1-to-2 Laspeyres volume growth (period-1 prices). -/
def chainedValueTwoLinks (p₀ q₀ p₁ q₁ q₂ : ι → K) : K :=
  chainedRealValue (∑ i, p₀ i * q₀ i)
    (chainedIndexTwoLinks (laspeyresVolumeGrowth p₀ q₀ q₁) (laspeyresVolumeGrowth p₁ q₁ q₂))

/-- Chained real value of component `j`: the same two-link chaining applied to
the one-good basket consisting of `j` alone, so each link is `j`'s own
Laspeyres volume growth. -/
def chainedComponentValue (p₀ q₀ p₁ q₁ q₂ : ι → K) (j : ι) : K :=
  chainedValueTwoLinks (fun _ : Unit => p₀ j) (fun _ : Unit => q₀ j) (fun _ : Unit => p₁ j)
    (fun _ : Unit => q₁ j) (fun _ : Unit => q₂ j)

omit [Fintype ι] in
/-- **Endpoint simplification.** If component `j` has nonzero period-0 and
period-1 quantities and a nonzero period-1 price, its two links telescope and
its chained value is its period-0 price times its period-2 quantity. -/
theorem chainedComponentValue_eq (p₀ q₀ p₁ q₁ q₂ : ι → K) (j : ι) (hq₀ : q₀ j ≠ 0)
    (hq₁ : q₁ j ≠ 0) (hp₁ : p₁ j ≠ 0) :
    chainedComponentValue p₀ q₀ p₁ q₁ q₂ j = p₀ j * q₂ j := by
  unfold chainedComponentValue chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks
    laspeyresVolumeGrowth
  simp only [Fintype.sum_unique]
  by_cases hp₀ : p₀ j = 0
  · simp [hp₀]
  · field_simp

/-- The two one-period Laspeyres growths of the concrete example.
Period 0: prices `(1, 1)`, quantities `(100, 100)`.
Period 1: prices `(1, 4)`, quantities `(50, 100)`.
Period 2: quantities `(50, 200)` (period-1 prices weight the second link). -/
theorem chained_example_growths :
    laspeyresVolumeGrowth (![1, 1] : Fin 2 → ℚ) ![100, 100] ![50, 100] = 3 / 4 ∧
      laspeyresVolumeGrowth (![1, 4] : Fin 2 → ℚ) ![50, 100] ![50, 200] = 17 / 9 := by
  constructor
  · unfold laspeyresVolumeGrowth
    simp [Fin.sum_univ_two]
    norm_num
  · unfold laspeyresVolumeGrowth
    simp [Fin.sum_univ_two]
    norm_num

/-- **Non-additivity of chained real components.** For the concrete basket,
the chained components (`50 + 200 = 250`) do not add up to the chained total
(`200 * (3/4 * 17/9) = 850/3`). One link alone is additive; the second link,
weighted by the changed period-1 prices, breaks additivity. -/
theorem chained_components_not_additive :
    ∑ j, chainedComponentValue (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
        ![50, 200] j ≠
      chainedValueTwoLinks (![1, 1] : Fin 2 → ℚ) ![100, 100] ![1, 4] ![50, 100]
        ![50, 200] := by
  unfold chainedComponentValue chainedValueTwoLinks chainedRealValue chainedIndexTwoLinks
    laspeyresVolumeGrowth
  simp [Fin.sum_univ_two]
  norm_num

end MathlibExt.Economics.Macro.ChainedIndex
