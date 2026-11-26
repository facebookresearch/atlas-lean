/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleSqrtTrick
public import MathlibExt.Probability.Percolation.Universality.CrossingTranslationInvariance
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.RSWLowestCrossing

/-!
# Long rectangles for the Beffara–Duminil-Copin argument

The family of translated long rectangles used in the Beffara–Duminil-Copin square-root trick, and
the polynomial deficit of their union.

## i. Overview

A long rectangle of aspect `2α` is translated by `2α³` periodic offsets. For a translation-invariant
positively associated measure all translates have the same crossing probability. The square-root
trick then bounds the probability of no crossing of the original rectangle by a polynomial in the
probability of no crossing of the union. `bdcLongRectangle_polynomial_deficit` is conditional on
translation invariance (`hshift`) and positive association (`hpa`);
`bdcLongRectangle_polynomial_deficit_of_cover` also takes a cover `B` of the union.

## ii. Key results

- `bdcLongRectangleEvent_probability_eq`: translates have equal probability under a shift-invariant
  measure.
- `bdcLongRectangle_polynomial_deficit`: polynomial deficit bound, conditional on `hshift` and
  `hpa`.

## iii. Table of contents

- A. Index set and translates
- B. Events and their probabilities
- C. The union and its deficit

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatMech

namespace BeffaraDC

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip
open StatMech.Universality

/-! ## A. Index set and translates -/

/-- The index set `Fin (2 α²) × Fin α` of translates of a long rectangle. -/
abbrev BdcLongRectangleIndex (alpha : ℕ) :=
  Fin (2 * alpha ^ 2) × Fin alpha

/-- The period `2 α² n` of the translates. -/
def bdcLongRectanglePeriod (alpha n : ℕ) : ℕ :=
  2 * alpha ^ 2 * n

/-- The horizontal offset `k.1 * n` of translate `k`. -/
def bdcLongRectangleXOffset {alpha : ℕ} (n : ℕ)
    (k : BdcLongRectangleIndex alpha) : ℕ :=
  k.1.val * n

/-- The vertical offset `k.2 * (2 α n)` of translate `k`. -/
def bdcLongRectangleYOffset {alpha : ℕ} (n : ℕ)
    (k : BdcLongRectangleIndex alpha) : ℕ :=
  k.2.val * (2 * alpha * n)

/-- The translation vector of translate `k`. -/
def bdcLongRectangleShift {alpha : ℕ} (n : ℕ)
    (k : BdcLongRectangleIndex alpha) : Site 2 :=
  ![(bdcLongRectangleXOffset n k : ℤ),
    (bdcLongRectangleYOffset n k : ℤ)]

lemma bdcLongRectangleXOffset_lt_period {alpha n : ℕ} (hn : 0 < n)
    (k : BdcLongRectangleIndex alpha) :
    bdcLongRectangleXOffset n k < bdcLongRectanglePeriod alpha n := by
  unfold bdcLongRectangleXOffset bdcLongRectanglePeriod
  exact Nat.mul_lt_mul_of_pos_right k.1.isLt hn

lemma bdcLongRectangleYOffset_lt_period {alpha n : ℕ} (ha : 0 < alpha)
    (hn : 0 < n) (k : BdcLongRectangleIndex alpha) :
    bdcLongRectangleYOffset n k < bdcLongRectanglePeriod alpha n := by
  unfold bdcLongRectangleYOffset bdcLongRectanglePeriod
  have hm : 0 < 2 * alpha * n := by positivity
  have h := Nat.mul_lt_mul_of_pos_right k.2.isLt hm
  nlinarith

/-! ## B. Events and their probabilities -/

/-- The vertical crossing event of the base long rectangle. -/
def bdcLongRectangleBaseEvent (alpha n : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  verticalCrossingEvent 0 (2 * (n : ℤ)) 0
    (2 * (alpha : ℤ) * (n : ℤ))

/-- The vertical crossing event of the translate indexed by `k`. -/
def bdcLongRectangleEvent (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  verticalCrossingEvent
    (bdcLongRectangleXOffset n k : ℤ)
    ((bdcLongRectangleXOffset n k : ℤ) + 2 * (n : ℤ))
    (bdcLongRectangleYOffset n k : ℤ)
    ((bdcLongRectangleYOffset n k : ℤ) +
      2 * (alpha : ℤ) * (n : ℤ))

lemma bdcLongRectangleEvent_eq_preimage (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    bdcLongRectangleEvent alpha n k =
      translateConfig (bdcLongRectangleShift n k) ⁻¹'
        bdcLongRectangleBaseEvent alpha n := by
  simpa [bdcLongRectangleEvent, bdcLongRectangleBaseEvent, add_comm,
    bdcLongRectangleShift] using
    (cti_verticalCrossingEvent_translate 0 (2 * (n : ℤ)) 0
      (2 * (alpha : ℤ) * (n : ℤ))
      (bdcLongRectangleShift n k))

lemma bdcLongRectangleEvent_isIncreasing (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    IsIncreasing (bdcLongRectangleEvent alpha n k) := by
  exact verticalCrossingEvent_isIncreasing _ _ _ _

lemma bdcLongRectangleEvent_measurableSet (alpha n : ℕ)
    (k : BdcLongRectangleIndex alpha) :
    MeasurableSet (bdcLongRectangleEvent alpha n k) := by
  exact StatMech.Universality.measurableSet_verticalCrossingEvent _ _ _ _

lemma bdcLongRectangleBaseEvent_measurableSet (alpha n : ℕ) :
    MeasurableSet (bdcLongRectangleBaseEvent alpha n) := by
  exact StatMech.Universality.measurableSet_verticalCrossingEvent _ _ _ _

lemma bdcLongRectangleEvent_probability_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    (alpha n : ℕ) (k : BdcLongRectangleIndex alpha) :
    mu.real (bdcLongRectangleEvent alpha n k) =
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  rw [bdcLongRectangleEvent_eq_preimage]
  exact (hshift (bdcLongRectangleShift n k)).measureReal_preimage
    (bdcLongRectangleBaseEvent_measurableSet alpha n).nullMeasurableSet

lemma bdcLongRectangleEvent_pairwise_probability_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    (alpha n : ℕ) (k l : BdcLongRectangleIndex alpha) :
    mu.real (bdcLongRectangleEvent alpha n k) =
      mu.real (bdcLongRectangleEvent alpha n l) := by
  calc
    mu.real (bdcLongRectangleEvent alpha n k) =
        mu.real (bdcLongRectangleBaseEvent alpha n) :=
      bdcLongRectangleEvent_probability_eq mu hshift alpha n k
    _ = mu.real (bdcLongRectangleEvent alpha n l) :=
      (bdcLongRectangleEvent_probability_eq mu hshift alpha n l).symm

lemma bdcLongRectangleEvent_probability_eq_selfDual
    (alpha n : ℕ) (k : BdcLongRectangleIndex alpha) :
    halfMeasure.real (bdcLongRectangleEvent alpha n k) =
      halfMeasure.real (bdcLongRectangleBaseEvent alpha n) := by
  exact bdcLongRectangleEvent_probability_eq halfMeasure
    cti_selfDual_shift_invariant alpha n k

/-! ## C. The union and its deficit -/

/-- All translate indices, as a `Finset`. -/
def bdcLongRectangleIndices (alpha : ℕ) :
    Finset (BdcLongRectangleIndex alpha) :=
  Finset.univ

lemma bdcLongRectangleIndices_card (alpha : ℕ) :
    (bdcLongRectangleIndices alpha).card = 2 * alpha ^ 3 := by
  simp [bdcLongRectangleIndices]
  ring

/-- The union of the crossing events of all translates. -/
def bdcLongRectangleUnion (alpha n : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ k ∈ bdcLongRectangleIndices alpha, bdcLongRectangleEvent alpha n k

lemma bdcLongRectangleUnion_isIncreasing (alpha n : ℕ) :
    IsIncreasing (bdcLongRectangleUnion alpha n) := by
  unfold bdcLongRectangleUnion
  exact isUpperSet_iUnion₂ (fun k _ =>
    bdcLongRectangleEvent_isIncreasing alpha n k)

lemma bdcLongRectangleUnion_measurableSet (alpha n : ℕ) :
    MeasurableSet (bdcLongRectangleUnion alpha n) := by
  unfold bdcLongRectangleUnion
  exact Finset.measurableSet_biUnion (bdcLongRectangleIndices alpha)
    (fun k _ => bdcLongRectangleEvent_measurableSet alpha n k)

/-- The index of the untranslated rectangle. -/
def bdcLongRectangleOriginIndex (alpha : ℕ) (ha : 0 < alpha) :
    BdcLongRectangleIndex alpha :=
  (⟨0, by positivity⟩, ⟨0, ha⟩)

@[simp] lemma bdcLongRectangleOriginIndex_event (alpha n : ℕ)
    (ha : 0 < alpha) :
    bdcLongRectangleEvent alpha n (bdcLongRectangleOriginIndex alpha ha) =
      bdcLongRectangleBaseEvent alpha n := by
  ext omega
  simp [bdcLongRectangleEvent, bdcLongRectangleBaseEvent,
    bdcLongRectangleOriginIndex, bdcLongRectangleXOffset,
    bdcLongRectangleYOffset]

@[simp] lemma bdcLongRectangleOriginIndex_mem (alpha : ℕ)
    (ha : 0 < alpha) :
    bdcLongRectangleOriginIndex alpha ha ∈ bdcLongRectangleIndices alpha := by
  simp [bdcLongRectangleIndices]

/-- Polynomial deficit bound, conditional on `hshift` and `hpa`. -/
theorem bdcLongRectangle_polynomial_deficit
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (hpa : PositivelyAssociated mu)
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    {alpha n : ℕ} (ha : 0 < alpha) (hn : 1 ≤ n)
    {c epsilon : ℝ} (hc : 0 ≤ c)
    (hunion : 1 - mu.real (bdcLongRectangleUnion alpha n) ≤
      c * (n : ℝ) ^ (-epsilon)) :
    1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) *
        (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  let i0 := bdcLongRectangleOriginIndex alpha ha
  have h := finite_symmetric_polynomial_deficit mu hpa
    (bdcLongRectangleIndices alpha) (bdcLongRectangleEvent alpha n)
    (i₀ := i0) (bdcLongRectangleOriginIndex_mem alpha ha)
    (fun k _ => bdcLongRectangleEvent_isIncreasing alpha n k)
    (fun k _ => bdcLongRectangleEvent_measurableSet alpha n k)
    (fun k _ => by
      rw [bdcLongRectangleOriginIndex_event]
      exact bdcLongRectangleEvent_probability_eq mu hshift alpha n k)
    hc hn hunion
  simpa [i0, bdcLongRectangleIndices_card,
    bdcLongRectangleOriginIndex_event] using h

lemma bdcLongRectangleUnion_deficit_of_cover
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsFiniteMeasure mu]
    {alpha n : ℕ} (B : Set (ConfigSpace (Sym2 (Site 2))))
    (hcover : B ⊆ bdcLongRectangleUnion alpha n)
    {c epsilon : ℝ}
    (hB : 1 - mu.real B ≤ c * (n : ℝ) ^ (-epsilon)) :
    1 - mu.real (bdcLongRectangleUnion alpha n) ≤
      c * (n : ℝ) ^ (-epsilon) := by
  have hmono : mu.real B ≤
      mu.real (bdcLongRectangleUnion alpha n) :=
    measureReal_mono hcover
  linarith

lemma bdcLongRectangle_polynomial_deficit_of_cover
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (hpa : PositivelyAssociated mu)
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    {alpha n : ℕ} (ha : 0 < alpha) (hn : 1 ≤ n)
    (B : Set (ConfigSpace (Sym2 (Site 2))))
    (hcover : B ⊆ bdcLongRectangleUnion alpha n)
    {c epsilon : ℝ} (hc : 0 ≤ c)
    (hB : 1 - mu.real B ≤ c * (n : ℝ) ^ (-epsilon)) :
    1 - c ^ ((1 : ℝ) / (2 * alpha ^ 3 : ℕ)) *
        (n : ℝ) ^ (-epsilon / (2 * alpha ^ 3 : ℕ)) ≤
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  apply bdcLongRectangle_polynomial_deficit mu hpa hshift ha hn hc
  exact bdcLongRectangleUnion_deficit_of_cover mu B hcover hB

end BeffaraDC

end StatMech
