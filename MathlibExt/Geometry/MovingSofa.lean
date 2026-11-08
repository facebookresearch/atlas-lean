/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Continuous rigid passage through a unit right-angle corridor

The plane is `ℂ` with its canonical Lebesgue measure. A shape is Lebesgue-measurable
and connected, and one continuous rotation/translation path carries its entire set
from the horizontal entrance to the vertical exit while staying in the corridor.
Areas are optimized in `ENNReal`, so finiteness and attainment are not assumptions.

The square and its two-segment translation give an actual area-one example.
These source-independent definitions and proofs were authored by Codex Cedar.
The separately recorded catalogue bounds are not used by this module.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MovingSofa

/-- The planar corridor has two perpendicular semi-infinite arms of width one. -/
def corridor : Set ℂ :=
  {z | z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1} ∪
    {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im}

/-- The horizontal entrance is beyond the corner square. -/
def entrance : Set ℂ := {z | z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- The vertical exit is beyond the corner square. -/
def exit : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 1 ≤ z.im}

/-- A motion uses actual continuous unit rotations and planar translations. -/
structure Motion where
  /-- The orientation-preserving unit complex rotation at each time. -/
  rotation : C(unitInterval, Circle)
  /-- The planar translation at each time. -/
  translation : C(unitInterval, ℂ)

/-- The physical position of a point under a direct planar rigid motion. -/
def Motion.position (m : Motion) (t : unitInterval) (z : ℂ) : ℂ :=
  (m.rotation t : ℂ) * z + m.translation t

/-- A continuous path starts before the corner and ends beyond it. -/
def CanPass (K : Set ℂ) : Prop :=
  ∃ m : Motion,
    m.position 0 '' K ⊆ entrance ∧
    m.position 1 '' K ⊆ exit ∧
    ∀ t : unitInterval, m.position t '' K ⊆ corridor

/-- Admissible shapes are Lebesgue-measurable, connected, and genuinely movable. -/
def IsSofa (K : Set ℂ) : Prop :=
  NullMeasurableSet K volume ∧ IsConnected K ∧ CanPass K

/-- Actual Lebesgue areas are optimized in the extended nonnegative reals. -/
noncomputable def optimalArea : ℝ≥0∞ := ⨆ (K : Set ℂ) (_ : IsSofa K), volume K

/-- A positive-area square, not a supplied area or motion oracle. -/
def unitSquare : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)

/-- The square follows a two-segment translation through the corner. -/
noncomputable def squareMotion : Motion where
  rotation := ContinuousMap.const unitInterval 1
  translation :=
    ⟨fun t ↦ ((min (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) +
      ((max (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) * Complex.I, by fun_prop⟩

/-- Every motion position preserves the distance between two points. -/
theorem motion_preserves_distance (m : Motion) (t : unitInterval) (z w : ℂ) :
    dist (m.position t z) (m.position t w) = dist z w := by
  simp only [Motion.position, dist_eq_norm, add_sub_add_right_eq_sub, ← mul_sub]
  simp

/-- The square is measurable for the canonical planar Borel structure. -/
theorem square_measurable : MeasurableSet unitSquare :=
  (measurableSet_Icc.prod measurableSet_Icc).preimage
    Complex.measurableEquivRealProd.measurable

/-- The square is connected, including its nonemptiness. -/
theorem square_connected : IsConnected unitSquare := by
  have h := (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num)).prod
    (isConnected_Icc (show (0 : ℝ) ≤ 1 by norm_num))
  have hi := h.image Complex.measurableEquivRealProd.symm
    Complex.equivRealProdCLM.symm.continuous.continuousOn
  have heq : Complex.measurableEquivRealProd.symm ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = unitSquare := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa [unitSquare] using hp
    · intro hz
      exact ⟨Complex.measurableEquivRealProd z, hz,
        Complex.measurableEquivRealProd.symm_apply_apply z⟩
  rwa [heq] at hi

/-- Canonical planar Lebesgue measure assigns the square area one. -/
theorem square_area : volume unitSquare = 1 := by
  rw [unitSquare, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet]
  change (volume.prod volume) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num [Real.volume_Icc]

/-- One actual continuous translation carries the whole square through the corridor. -/
theorem square_canPass : CanPass unitSquare := by
  refine ⟨squareMotion, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [entrance, Motion.position, squareMotion]
    exact ⟨by linarith, him0, him1⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [exit, Motion.position, squareMotion]
    exact ⟨hre0, hre1, by linarith⟩
  · intro t
    rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    change ((squareMotion.position t z).re ≤ 1 ∧
      0 ≤ (squareMotion.position t z).im ∧ (squareMotion.position t z).im ≤ 1) ∨
      (0 ≤ (squareMotion.position t z).re ∧ (squareMotion.position t z).re ≤ 1 ∧
        0 ≤ (squareMotion.position t z).im)
    by_cases ht : 2 * (t : ℝ) - 1 ≤ 0
    · left
      have h : z.re + (2 * (t : ℝ) - 1) ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 :=
        ⟨by linarith, him0, him1⟩
      simpa [Motion.position, squareMotion, min_eq_left ht, max_eq_right ht] using h
    · right
      have ht' : 0 ≤ 2 * (t : ℝ) - 1 := le_of_not_ge ht
      have h : 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im + (2 * (t : ℝ) - 1) :=
        ⟨hre0, hre1, by linarith⟩
      simpa [Motion.position, squareMotion, min_eq_right ht', max_eq_left ht'] using h

/-- The square is an admissible positive-area moving shape. -/
theorem square_isSofa : IsSofa unitSquare :=
  ⟨square_measurable.nullMeasurableSet, square_connected, square_canPass⟩

/-- The actual square witness bounds the global area supremum from below. -/
theorem one_le_optimalArea : 1 ≤ optimalArea := by
  rw [← square_area]
  exact le_iSup_of_le unitSquare (le_iSup_of_le square_isSofa le_rfl)

/-- The mirror-image unit corridor, with the horizontal arm extending to the
right and the vertical arm occupying `-1 ≤ Re z ≤ 0`. Passing this corridor
is the opposite turn from `corridor`. -/
def corridorOther : Set ℂ :=
  {z | -1 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ 1} ∪
    {z | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 0 ≤ z.im}

/-- The entrance arm of the mirrored corridor, beyond its corner square. -/
def entranceOther : Set ℂ := {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- The vertical exit of the mirrored corridor, beyond its corner square. -/
def exitOther : Set ℂ := {z | -1 ≤ z.re ∧ z.re ≤ 0 ∧ 1 ≤ z.im}

/-- A continuous rigid motion carries the whole shape through the mirrored
corridor, making the opposite turn. -/
def CanPassOther (K : Set ℂ) : Prop :=
  ∃ m : Motion,
    m.position 0 '' K ⊆ entranceOther ∧
    m.position 1 '' K ⊆ exitOther ∧
    ∀ t : unitInterval, m.position t '' K ⊆ corridorOther


/-- The Z-shaped (S-shaped) unit corridor with corner separation `d`:
a horizontal entrance arm (`0 ≤ Im z ≤ 1`), a vertical middle channel
of height `2 + d` (`0 ≤ Im z ≤ 2 + d`), and a horizontal exit arm on
the opposite side (`1 + d ≤ Im z ≤ 2 + d`). The middle channel is
bounded: it does not contain the upward ray above the exit arm. For
`d = 1` the two corner squares are separated by one full corridor
width. Passing it requires one turn in each direction inside a single
passage. -/
def corridorZ (d : ℝ) : Set ℂ :=
  {z | z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1} ∪
    {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 2 + d} ∪
    {z | 0 ≤ z.re ∧ 1 + d ≤ z.im ∧ z.im ≤ 2 + d}

/-- The horizontal entrance arm of the Z corridor, beyond its first corner. -/
def entranceZ : Set ℂ := {z | z.re ≤ 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- The horizontal exit arm of the Z corridor with corner separation
`d`, beyond its second corner. -/
def exitZ (d : ℝ) : Set ℂ := {z | 1 ≤ z.re ∧ 1 + d ≤ z.im ∧ z.im ≤ 2 + d}

/-- A single continuous rigid motion carries the whole shape through
the Z corridor at the fixed corner separation `d`, turning once in
each direction. -/
def CanPassZAt (K : Set ℂ) (d : ℝ) : Prop :=
  ∃ m : Motion,
    m.position 0 '' K ⊆ entranceZ ∧
    m.position 1 '' K ⊆ exitZ d ∧
    ∀ t : unitInterval, m.position t '' K ⊆ corridorZ d

/-- The shape passes the Z corridor for all sufficiently large corner
separations (equivalently, `∀ᶠ d in Filter.atTop, CanPassZAt K d`):
the source's "sufficiently separated corners". Unlike the mirrored
corridor, this is not implied by an ordinary passage: time reversal
plus a rigid motion transports an ordinary passage to the *mirrored*
corridor, but a Z passage couples both turns in one motion. -/
def CanPassZ (K : Set ℂ) : Prop :=
  ∃ D : ℝ, ∀ d : ℝ, D ≤ d → CanPassZAt K d

/-- The square follows a three-segment translation through the Z
corridor at separation `d`: east into the middle channel, north by
`1 + d`, then east out. -/
noncomputable def squareMotionZAt (d : ℝ) : Motion where
  rotation := ContinuousMap.const unitInterval 1
  translation :=
    ⟨fun t ↦ ((-1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 : ℝ) : ℂ) +
      (((1 + d) * min (max (3 * (t : ℝ) - 1) 0) 1 : ℝ) : ℂ) * Complex.I,
      by fun_prop⟩

/-- The unit square passes the Z corridor at any nonnegative
separation. -/
theorem square_canPassZAt (d : ℝ) (hd : 0 ≤ d) : CanPassZAt unitSquare d := by
  refine ⟨squareMotionZAt d, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [entranceZ, Motion.position, squareMotionZAt]
    exact ⟨by linarith, him0, him1⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    norm_num [exitZ, Motion.position, squareMotionZAt]
    exact ⟨by linarith, by linarith, by linarith⟩
  · intro t
    rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    change ((((squareMotionZAt d).position t z).re ≤ 1 ∧
      0 ≤ ((squareMotionZAt d).position t z).im ∧
      ((squareMotionZAt d).position t z).im ≤ 1) ∨
      (0 ≤ ((squareMotionZAt d).position t z).re ∧
        ((squareMotionZAt d).position t z).re ≤ 1 ∧
        0 ≤ ((squareMotionZAt d).position t z).im ∧
        ((squareMotionZAt d).position t z).im ≤ 2 + d)) ∨
      (0 ≤ ((squareMotionZAt d).position t z).re ∧
        1 + d ≤ ((squareMotionZAt d).position t z).im ∧
        ((squareMotionZAt d).position t z).im ≤ 2 + d)
    by_cases h1 : 3 * (t : ℝ) ≤ 1
    · refine Or.inl (Or.inl ?_)
      have hx : -1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 =
          -1 + 3 * (t : ℝ) := by
        rw [min_eq_left h1, max_eq_right (by linarith)]; ring
      have hy : min (max (3 * (t : ℝ) - 1) 0) 1 = (0 : ℝ) := by
        rw [max_eq_right (by linarith)]; exact min_eq_left (by norm_num)
      have h : z.re + (-1 + 3 * (t : ℝ)) ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 :=
        ⟨by linarith, him0, him1⟩
      simpa [Motion.position, squareMotionZAt, hx, hy] using h
    · by_cases h2 : 3 * (t : ℝ) ≤ 2
      · refine Or.inl (Or.inr ?_)
        have hx : -1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 = (0 : ℝ) := by
          rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
        have hy : min (max (3 * (t : ℝ) - 1) 0) 1 = 3 * (t : ℝ) - 1 := by
          rw [max_eq_left (by linarith), min_eq_left (by linarith)]
        have hprod0 : 0 ≤ (1 + d) * (3 * (t : ℝ) - 1) :=
          mul_nonneg (by linarith) (by linarith)
        have hprod1 : (1 + d) * (3 * (t : ℝ) - 1) ≤ 1 + d :=
          mul_le_of_le_one_right (by linarith) (by linarith)
        have h : 0 ≤ z.re ∧ z.re ≤ 1 ∧
            0 ≤ z.im + (1 + d) * (3 * (t : ℝ) - 1) ∧
            z.im + (1 + d) * (3 * (t : ℝ) - 1) ≤ 2 + d :=
          ⟨hre0, hre1, by linarith, by linarith⟩
        simpa [Motion.position, squareMotionZAt, hx, hy] using h
      · refine Or.inr ?_
        have hx : -1 + min (3 * (t : ℝ)) 1 + max (3 * (t : ℝ) - 2) 0 =
            3 * (t : ℝ) - 2 := by
          rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring
        have hy : min (max (3 * (t : ℝ) - 1) 0) 1 = (1 : ℝ) := by
          rw [min_eq_right]
          have hle := le_max_left (3 * (t : ℝ) - 1) (0 : ℝ)
          linarith
        have h : 0 ≤ z.re + (3 * (t : ℝ) - 2) ∧
            1 + d ≤ z.im + (1 + d) * 1 ∧ z.im + (1 + d) * 1 ≤ 2 + d :=
          ⟨by linarith, by linarith, by linarith⟩
        simpa [Motion.position, squareMotionZAt, hx, hy] using h

/-- The square's Z motion at separation one. -/
noncomputable def squareMotionZ : Motion := squareMotionZAt 1

/-- The unit square passes the Z corridor at separation one. -/
theorem square_canPassZAt_one : CanPassZAt unitSquare 1 :=
  square_canPassZAt 1 (by norm_num)

/-- The unit square passes the Z corridor for all sufficiently large
separations. -/
theorem square_canPassZ : CanPassZ unitSquare :=
  ⟨0, fun d hd => square_canPassZAt d hd⟩

/-- An ambidextrous sofa is an admissible sofa that can also pass the
Z corridor in a single passage, turning once in each direction. (Two
independent passages, one through each mirrored L corridor, would not
suffice: an ordinary passage transports to the mirrored corridor by time
reversal plus a rigid motion, so that formulation would collapse to the
ordinary sofa condition.) -/
def IsAmbidextrousSofa (K : Set ℂ) : Prop :=
  IsSofa K ∧ CanPassZ K

/-- Supremal area of an ambidextrous sofa in `ENNReal`. -/
noncomputable def ambidextrousOptimalArea : ℝ≥0∞ :=
  ⨆ (K : Set ℂ) (_ : IsAmbidextrousSofa K), volume K

/-- Every ambidextrous sofa is an ordinary sofa, so its supremal area is at
most the ordinary moving-sofa supremum. -/
theorem ambidextrousOptimalArea_le_optimalArea :
    ambidextrousOptimalArea ≤ optimalArea := by
  apply iSup_le
  intro K
  apply iSup_le
  intro hK
  exact le_iSup_of_le K (le_iSup_of_le hK.1 le_rfl)

/-- The square follows a two-segment translation through the mirrored corner:
first left into the vertical arm, then upward. -/
noncomputable def squareMotionOther : Motion where
  rotation := ContinuousMap.const unitInterval 1
  translation :=
    ⟨fun t ↦ ((-1 - min (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) +
      ((max (2 * (t : ℝ) - 1) 0 : ℝ) : ℂ) * Complex.I, by fun_prop⟩

/-- The same unit square passes the mirrored corridor. -/
theorem square_canPassOther : CanPassOther unitSquare := by
  refine ⟨squareMotionOther, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, _hre1⟩, ⟨him0, him1⟩⟩
    norm_num [entranceOther, Motion.position, squareMotionOther]
    exact ⟨hre0, him0, him1⟩
  · rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, _him1⟩⟩
    norm_num [exitOther, Motion.position, squareMotionOther]
    exact ⟨by linarith, by linarith, by linarith⟩
  · intro t
    rintro _ ⟨z, hz, rfl⟩
    change (0 ≤ z.re ∧ z.re ≤ 1) ∧ (0 ≤ z.im ∧ z.im ≤ 1) at hz
    rcases hz with ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    change (-1 ≤ (squareMotionOther.position t z).re ∧
      0 ≤ (squareMotionOther.position t z).im ∧
      (squareMotionOther.position t z).im ≤ 1) ∨
      (-1 ≤ (squareMotionOther.position t z).re ∧
        (squareMotionOther.position t z).re ≤ 0 ∧
        0 ≤ (squareMotionOther.position t z).im)
    by_cases ht : 2 * (t : ℝ) - 1 ≤ 0
    · left
      have h : -1 ≤ z.re + (-1 - (2 * (t : ℝ) - 1)) ∧ 0 ≤ z.im ∧ z.im ≤ 1 :=
        ⟨by linarith, him0, him1⟩
      simpa [Motion.position, squareMotionOther, min_eq_left ht,
        max_eq_right ht] using h
    · right
      have ht' : 0 ≤ 2 * (t : ℝ) - 1 := le_of_not_ge ht
      have h : -1 ≤ z.re + -1 ∧ z.re + -1 ≤ 0 ∧
          0 ≤ z.im + (2 * (t : ℝ) - 1) :=
        ⟨by linarith, by linarith, by linarith⟩
      simpa [Motion.position, squareMotionOther, min_eq_right ht',
        max_eq_left ht'] using h

/-- The unit square is an ambidextrous sofa. -/
theorem square_isAmbidextrousSofa : IsAmbidextrousSofa unitSquare :=
  ⟨square_isSofa, square_canPassZ⟩

/-- The square witness bounds the ambidextrous supremum from below by one. -/
theorem one_le_ambidextrousOptimalArea : 1 ≤ ambidextrousOptimalArea := by
  rw [← square_area]
  exact le_iSup_of_le unitSquare
    (le_iSup_of_le square_isAmbidextrousSofa le_rfl)

end MovingSofa
