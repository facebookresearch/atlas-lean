/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.DiscreteValuationRegular

@[expose] public section

open IsLocalRing

namespace PowerSeriesDiscreteValuationRegularTest

universe u

/-- Exact-source consumer, with the original binders. -/
example (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    (p : ℕ) (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0) :
    ∃ (_ : IsRegularLocalRing (PowerSeries O)) (_ : IsRegularRing (PowerSeries O))
      (_ : IsAdicComplete (maximalIdeal (PowerSeries O)) (PowerSeries O))
      (_ : IsLocalHom (algebraMap O (PowerSeries O))),
      ringKrullDim (PowerSeries O) ≤ 2 ∧ ((p : ℕ) : PowerSeries O) ≠ 0 ∧
        ((p : ℕ) : PowerSeries O) ∈ maximalIdeal (PowerSeries O) :=
  PowerSeries.exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing
    O p hpO hpO0

/-- Higher-universe consumer. -/
example (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    (p : ℕ) (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0) :
    ∃ (_ : IsRegularLocalRing (PowerSeries O)) (_ : IsRegularRing (PowerSeries O))
      (_ : IsAdicComplete (maximalIdeal (PowerSeries O)) (PowerSeries O))
      (_ : IsLocalHom (algebraMap O (PowerSeries O))),
      ringKrullDim (PowerSeries O) ≤ 2 ∧ ((p : ℕ) : PowerSeries O) ≠ 0 ∧
        ((p : ℕ) : PowerSeries O) ∈ maximalIdeal (PowerSeries O) :=
  PowerSeries.exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing
    O p hpO hpO0

/-- Regularity without completeness or a characteristic witness. -/
example (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsRegularRing (PowerSeries O) :=
  PowerSeries.isRegularRing_of_isDiscreteValuationRing O

/-- Regular locality without completeness or a characteristic witness. -/
example (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsRegularLocalRing (PowerSeries O) :=
  PowerSeries.isRegularLocalRing_of_isDiscreteValuationRing O

/-- Boundary: the hypothesis `hpO0` is necessary, since for `p = 0` it
is false. -/
example (O : Type) [CommRing O] : ¬ ((0 : ℕ) : O) ≠ 0 := by simp

end PowerSeriesDiscreteValuationRegularTest
