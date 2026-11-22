/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.PlusStateDLRConsistency
public import PhyslibExt.CondensedMatter.IsingModel.PlusStateTI
public import PhyslibExt.CondensedMatter.IsingModel.PlusStateZeroOne

/-!
# Ergodicity and extremality of the plus and minus states from decay of shifted integrals

Under a decay condition for shifted plus-state integrals, the plus and minus states are ergodic
extreme DLR states.

## i. Overview

Combining translation invariance of the plus state (`PlusStateTI`), the DLR property
(`FVConsistencyProve`), and the zero–one law for translation-invariant events
(`AeTailInvariantProve2`), the plus state is ergodic under lattice translations and an extreme point
of the DLR states whenever the shifted integrals decay as assumed in `hdecay`. The minus-state
version also assumes the DLR property.

## ii. Key results

- `StatMech.Ising.gsu_plusState_ergodic_extreme_of_decay` : the plus state is ergodic and extreme
- `StatMech.Ising.gsu_minusState_ergodic_extreme_of_decay` : the minus state is ergodic and extreme

## iii. Table of contents

- A. Ergodic extreme states

## iv. References

- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter (1988; 2nd ed. 2011), Chapter 14
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}

/-! ## A. Ergodic extreme states -/

lemma gsu_plusState_ergodic_extreme_of_decay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pst_PlusIntegralShiftDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  atip2_plusState_isErgodic_extremePoint β h hd hβ hh
    (pst_plusState_isTranslationInvariant_of_decay β h hdecay)
    (plusState_isDLR β h)

lemma gsu_minusState_ergodic_extreme_of_decay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pst_MinusIntegralShiftDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) :=
  atip2_minusState_isErgodic_extremePoint β h hd hβ hh
    (pst_minusState_isTranslationInvariant_of_decay β h hdecay) hdlr

end Ising

end StatMech
