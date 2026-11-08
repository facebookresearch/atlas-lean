/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Probability.IdentDistribIndep

/-!
# Beardwood-Halton-Hammersley theorem and catalogue bounds: wishlist

The primary sources fix independent uniform points in the unit square. This module represents
the source constant as a real number: the infimum of all real values satisfying the generic
almost-sure BHH limit characterization. The source-facing closed theorem says that this real
value is the unique unit-square limit. It is an unproved `Prop`, not an axiom or proof of the
Beardwood-Halton-Hammersley theorem.

The generic common-law definitions expose all probability and i.i.d. quantifiers. The six
catalogue bounds concern the same real unit-square constant. The source reports these as known
results, not open conjectures; their missing Lean proofs are recorded with `theorem_wanted`.
-/

open scoped BigOperators ENNReal
open Filter MeasureTheory Metric Set

namespace MathlibExt.Probability.BeardwoodHaltonHammersleyConstantWanted

/-- A point in the Euclidean plane. -/
abbrev PlanarPoint := EuclideanSpace ℝ (Fin 2)

local instance planarMeasurableSpace : MeasurableSpace PlanarPoint := borel PlanarPoint
local instance planarBorelSpace : BorelSpace PlanarPoint := ⟨rfl⟩

/-- The next index in a finite cyclic order. There is no input when `n = 0`. -/
def cyclicNext {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- The length of the closed tour obtained by visiting `points` in the order `order`. -/
noncomputable def tourLength
    {n : ℕ} (points : Fin n → PlanarPoint) (order : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, dist (points (order i)) (points (order (cyclicNext i)))

/-- `L_n`: the minimum length among all cyclic tours through the `n` indexed points. -/
noncomputable def shortestTourLength {n : ℕ} (points : Fin n → PlanarPoint) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf'
    ⟨Equiv.refl (Fin n), Finset.mem_univ _⟩ (tourLength points)

/--
The source quotient `L_n / sqrt n` for the first `n` points of an infinite sample. The explicit
zero branch makes the degenerate input auditable and does not affect a limit along `atTop`.
-/
noncomputable def normalizedTourLength
    {Ω : Type*} (points : ℕ → Ω → PlanarPoint) (ω : Ω) (n : ℕ) : ℝ :=
  if 0 < n then
    shortestTourLength (fun i : Fin n => points i.val ω) / Real.sqrt n
  else
    0

/--
The points are independent and identically distributed with the explicit common law `law`.
Measurability is stated before the totalized `Measure.map` operation is used.
-/
def IsIIDWithLaw
    {Ω : Type*}
    (mΩ : MeasurableSpace Ω)
    (probability : Measure Ω)
    (points : ℕ → Ω → PlanarPoint)
    (law : Measure PlanarPoint) : Prop :=
  letI := mΩ
  IsProbabilityMeasure probability ∧
    IsProbabilityMeasure law ∧
    (∀ i, Measurable (points i)) ∧
    ProbabilityTheory.iIndepFun points probability ∧
    ∀ i, Measure.map (points i) probability = law

/-- A realization of an infinite i.i.d. sample with common law `law`. -/
structure IIDRealization (law : Measure PlanarPoint) where
  Ω : Type
  measurableSpace : MeasurableSpace Ω
  probability : Measure Ω
  points : ℕ → Ω → PlanarPoint
  isIID : IsIIDWithLaw measurableSpace probability points law

/-- The almost-sure BHH limit clause for a fixed realization and real candidate `β`. -/
def HasBHHLimit
    {Ω : Type*}
    (mΩ : MeasurableSpace Ω)
    (probability : Measure Ω)
    (points : ℕ → Ω → PlanarPoint)
    (β : ℝ) : Prop :=
  letI := mΩ
  ∀ᵐ ω ∂probability,
    Tendsto (normalizedTourLength points ω) atTop (nhds β)

/--
`β` is the BHH limit for the explicit common law `law`. A realization is required before the
universal limit clause, preventing an empty realization type from making the claim vacuous.
-/
def IsBHHConstantFor (law : Measure PlanarPoint) (β : ℝ) : Prop :=
  Nonempty (IIDRealization law) ∧
    ∀ realization : IIDRealization law,
      HasBHHLimit realization.measurableSpace realization.probability realization.points β

/-- The candidate BHH limit values for the explicit common law `law`. -/
def bhhLimitValues (law : Measure PlanarPoint) : Set ℝ :=
  {β | IsBHHConstantFor law β}

/-- Membership in `bhhLimitValues` unfolds to the generic BHH characterization. -/
theorem mem_bhhLimitValues_iff (law : Measure PlanarPoint) (β : ℝ) :
    β ∈ bhhLimitValues law ↔ IsBHHConstantFor law β :=
  Iff.rfl

/-- The source's singular constant clause for an explicit sampling law. -/
def HasUniqueBHHConstantFor (law : Measure PlanarPoint) : Prop :=
  ∃! β : ℝ, IsBHHConstantFor law β

/--
A real-valued BHH constant for an explicit law, canonically constructed as the infimum of all
real values satisfying the BHH limit characterization. The source theorem below asserts that the
unit-square value satisfies that characterization and is unique. No existence theorem is assumed.
-/
noncomputable def bhhConstantFor (law : Measure PlanarPoint) : ℝ :=
  sInf (bhhLimitValues law)

/--
If `β` is exactly the unique real satisfying the BHH characterization for `law`, the canonical
infimum construction equals `β`. This isolates the empty-set totalization from the source case.
-/
theorem bhhConstantFor_eq_of_unique_characterization
    (law : Measure PlanarPoint) (β : ℝ)
    (h : ∀ γ : ℝ, IsBHHConstantFor law γ ↔ γ = β) :
    bhhConstantFor law = β := by
  have hset : bhhLimitValues law = {β} := by
    ext γ
    simpa [bhhLimitValues] using h γ
  rw [bhhConstantFor, hset, csInf_singleton]

/-- The closed unit square from the primary BHH formulation. -/
def unitSquare : Set PlanarPoint :=
  {point | ∀ coordinate, point coordinate ∈ Set.Icc (0 : ℝ) 1}

/-- Lebesgue measure restricted to the source's unit square. -/
noncomputable def unitSquareUniformLaw : Measure PlanarPoint :=
  volume.restrict unitSquare

/-- The real-valued unit-square Beardwood-Halton-Hammersley constant. -/
noncomputable def beardwoodHaltonHammersleyConstant : ℝ :=
  bhhConstantFor unitSquareUniformLaw

/-- The source notation `β_2`, definitionally equal to the real BHH constant. -/
noncomputable abbrev β₂ : ℝ := beardwoodHaltonHammersleyConstant

/-- The source notation `C_12`, definitionally equal to `β_2`. -/
noncomputable abbrev C₁₂ : ℝ := β₂

/--
The source BHH theorem: `β_2` is the almost-sure unit-square limit for every i.i.d. realization,
and every real value with that characterization equals `β_2`. This is a closed unproved claim.
-/
def unitSquareBHHTheorem : Prop :=
  IsBHHConstantFor unitSquareUniformLaw β₂ ∧
    ∀ β : ℝ, IsBHHConstantFor unitSquareUniformLaw β → β = β₂

/-- [BHH1959] reported upper bound `β_2 ≤ 0.92117`. -/
def bhh1959UpperBound : Prop :=
  β₂ ≤ (92117 : ℝ) / 100000

/-- [S2015] improvement `β_2 ≤ 0.92117 - (9 / 16) * 10^-6`. -/
def steinerberger2015ImprovedUpperBound : Prop :=
  β₂ ≤ (92117 : ℝ) / 100000 - (9 : ℝ) / 16 * (1 / 1000000)

/-- [YC2023] strict computer-aided upper bound `β_2 < 0.90304`. -/
def yuCarlsson2023StrictUpperBound : Prop :=
  β₂ < (90304 : ℝ) / 100000

/-- [BHH1959] reported lower bound `0.625 ≤ β_2`. -/
def bhh1959LowerBound : Prop :=
  (5 : ℝ) / 8 ≤ β₂

/--
[GJ2020]'s correction of the Steinerberger argument gives the exact symbolic lower bound
`0.625 + 19 / 10368 ≤ β_2`. The nearby decimal in the catalogue is only approximate.
-/
def steinerberger2015CorrectedSymbolicLowerBound : Prop :=
  (5 : ℝ) / 8 + 19 / 10368 ≤ β₂

/-- [GJ2020] rigorous lower bound `0.6277 ≤ β_2`. -/
def gaudioJaillet2020LowerBound : Prop :=
  (6277 : ℝ) / 10000 ≤ β₂

/-- Source: Beardwood, Halton and Hammersley (1959), quoted in Steinerberger (2015). -/
theorem_wanted unitSquareBHHTheorem_holds : unitSquareBHHTheorem

/-- Source: Beardwood, Halton and Hammersley (1959), catalogue upper-bound row. -/
theorem_wanted bhh1959UpperBound_holds : bhh1959UpperBound

/-- Source: Steinerberger, New Bounds for the Traveling Salesman Constant (2015). -/
theorem_wanted steinerberger2015ImprovedUpperBound_holds :
    steinerberger2015ImprovedUpperBound

/-- Source: Yu and Carlsson (2023), strict upper-bound row in the frozen catalogue. -/
theorem_wanted yuCarlsson2023StrictUpperBound_holds : yuCarlsson2023StrictUpperBound

/-- Source: Beardwood, Halton and Hammersley (1959), catalogue lower-bound row. -/
theorem_wanted bhh1959LowerBound_holds : bhh1959LowerBound

/-- Source: Gaudio and Jaillet (2020), correction of Steinerberger's lower coefficient. -/
theorem_wanted steinerberger2015CorrectedSymbolicLowerBound_holds :
    steinerberger2015CorrectedSymbolicLowerBound

/-- Source: Gaudio and Jaillet, An improved lower bound for the Traveling Salesman constant. -/
theorem_wanted gaudioJaillet2020LowerBound_holds : gaudioJaillet2020LowerBound

end MathlibExt.Probability.BeardwoodHaltonHammersleyConstantWanted
