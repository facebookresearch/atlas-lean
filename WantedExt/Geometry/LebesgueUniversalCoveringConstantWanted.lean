/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Lebesgue universal covering constant

The constant is the infimal area of a nonempty convex planar set containing a
congruent copy of every nonempty convex planar set of diameter exactly one.
Area is planar Lebesgue measure; congruences include reflections.

The bounds and reductions below are known results requested as `theorem_wanted`,
not assumptions or proofs. Source: optimization catalogue, constant 13b.
-/

open MeasureTheory

namespace MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted

noncomputable section

/-- The planar ambient space in the source. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/--
The source's quantified objects: nonempty convex planar sets whose metric
diameter is exactly `1`. Nonemptiness excludes the totalized empty diameter.
-/
def IsUnitDiameterConvexSet (K : Set Plane) : Prop :=
  K.Nonempty ∧ Convex ℝ K ∧ Metric.diam K = 1

/-- A surjective planar isometry carries the entire set `K` into `Ω`. -/
def CoversCongruentCopy (Ω K : Set Plane) : Prop :=
  ∃ e : Plane ≃ᵢ Plane, e '' K ⊆ Ω

/-- Nonempty convex covers of every nonempty convex planar unit-diameter set. -/
def IsUniversalConvexCover (Ω : Set Plane) : Prop :=
  Ω.Nonempty ∧ Convex ℝ Ω ∧
    ∀ K : Set Plane, IsUnitDiameterConvexSet K → CoversCongruentCopy Ω K

/-- Planar Lebesgue area, retained in `ENNReal` to preserve infinite area. -/
def planarArea (S : Set Plane) : ENNReal :=
  volume S

/-- Areas of precisely the admissible universal convex covers. -/
def admissibleCoverAreas : Set ENNReal :=
  {a | ∃ Ω : Set Plane, IsUniversalConvexCover Ω ∧ planarArea Ω = a}

/--
The infimum of admissible cover areas. An empty family has infimum `⊤`;
minimal-cover existence is a separate requested result, not an assumption.
-/
def lebesgueUniversalCoveringConstant : ENNReal :=
  sInf admissibleCoverAreas

/--
Directional support width. Its use below is guarded by nonemptiness and
compactness, so the extrema range over nonempty bounded images.
-/
def directionalWidth (K : Set Plane) (u : Plane) : ℝ :=
  sSup ((fun x : Plane => inner ℝ u x) '' K) -
    sInf ((fun x : Plane => inner ℝ u x) '' K)

/-- Nonempty compact convex planar sets of width one in every unit direction. -/
def IsConstantWidthOne (K : Set Plane) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
    ∀ u : Plane, ‖u‖ = 1 → directionalWidth K u = 1

/-- Blaschke selection yields a convex cover attaining the infimum. -/
def elekes1994MinimalCoverExists : Prop :=
  ∃ Ω : Set Plane,
    IsUniversalConvexCover Ω ∧
      planarArea Ω = lebesgueUniversalCoveringConstant

/-- Covering every constant-width-one set suffices for a nonempty convex cover. -/
def vrecica1981ConstantWidthOneSuffices : Prop :=
  ∀ Ω : Set Plane,
    Ω.Nonempty →
      Convex ℝ Ω →
        (∀ K : Set Plane, IsConstantWidthOne K → CoversCongruentCopy Ω K) →
          IsUniversalConvexCover Ω

/-- Jung's theorem gives the exact upper bound `π / 3`. -/
def trivialJungElekes1994UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.pi / 3)

/-- Pál's regular hexagon gives the exact upper bound `√3 / 2`. -/
def pal1920HexagonUpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal (Real.sqrt 3 / 2)

/-- Pál's truncated hexagon gives the exact upper bound `2 - 2 / √3`. -/
def pal1920TruncatedHexagonUpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤
    ENNReal.ofReal (2 - 2 / Real.sqrt 3)

/-- Sprague's finite-decimal upper bound. -/
def sprague1936UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708436

/-- Hansen's finite-decimal upper bound, corrected by Baez, Bagdasaryan and Gibbs. -/
def hansen1992CorrectedBBG2015UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.844137708398

/--
Baez, Bagdasaryan and Gibbs's approximate upper bound. A real with the printed
18-digit prefix is bound existentially; the truncation is not the exact bound.
-/
def bbg2015ApproximateUpperBound : Prop :=
  ∃ b : ℝ,
    0.844115297128419059 ≤ b ∧
      b < 0.844115297128419060 ∧
        lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal b

/-- Gibbs's finite-decimal upper bound. -/
def gibbs2018UpperBound : Prop :=
  lebesgueUniversalCoveringConstant ≤ ENNReal.ofReal 0.8440935944

/-- The radius-half disk gives the exact lower bound `π / 4`. -/
def trivialUnitDiskLowerBound : Prop :=
  ENNReal.ofReal (Real.pi / 4) ≤ lebesgueUniversalCoveringConstant

/-- Elekes's disk-and-triangle finite-decimal lower bound. -/
def elekes1994DiskTriangleLowerBound : Prop :=
  ENNReal.ofReal 0.8257 ≤ lebesgueUniversalCoveringConstant

/-- Elekes's finite-decimal lower bound using regular `3^j`-gons as well. -/
def elekes1994RegularPolygonLowerBound : Prop :=
  ENNReal.ofReal 0.8271 ≤ lebesgueUniversalCoveringConstant

/-- Brass and Sharifi's rigorous computer-aided finite-decimal lower bound. -/
def brassSharifi2005LowerBound : Prop :=
  ENNReal.ofReal 0.832 ≤ lebesgueUniversalCoveringConstant

/-- Source: Elekes, Generalized breadths, circular Cantor sets, and the least area UCC (1994). -/
theorem_wanted elekes1994MinimalCoverExists_holds : elekes1994MinimalCoverExists

/-- Source: Vrećica, A note on sets of constant width (1981). -/
theorem_wanted vrecica1981ConstantWidthOneSuffices_holds : vrecica1981ConstantWidthOneSuffices

/-- Source: Jung's theorem, quoted in Elekes (1994), catalogue constant 13b. -/
theorem_wanted trivialJungElekes1994UpperBound_holds : trivialJungElekes1994UpperBound

/-- Source: Pál, Über ein elementares Variationsproblem (1920), hexagon bound. -/
theorem_wanted pal1920HexagonUpperBound_holds : pal1920HexagonUpperBound

/-- Source: Pál, Über ein elementares Variationsproblem (1920), truncated hexagon bound. -/
theorem_wanted pal1920TruncatedHexagonUpperBound_holds : pal1920TruncatedHexagonUpperBound

/-- Source: Sprague, Über ein elementares Variationsproblem (1936). -/
theorem_wanted sprague1936UpperBound_holds : sprague1936UpperBound

/-- Source: Hansen (1992), corrected in Baez, Bagdasaryan and Gibbs (2015). -/
theorem_wanted hansen1992CorrectedBBG2015UpperBound_holds : hansen1992CorrectedBBG2015UpperBound

/-- Source: Baez, Bagdasaryan and Gibbs, The Lebesgue universal covering problem (2015). -/
theorem_wanted bbg2015ApproximateUpperBound_holds : bbg2015ApproximateUpperBound

/-- Source: Gibbs, An Upper Bound for Lebesgue's Covering Problem (2018). -/
theorem_wanted gibbs2018UpperBound_holds : gibbs2018UpperBound

/-- Source: Radius-half disk lower-bound row, optimization catalogue constant 13b. -/
theorem_wanted trivialUnitDiskLowerBound_holds : trivialUnitDiskLowerBound

/-- Source: Elekes (1994), disk and equilateral triangle lower bound. -/
theorem_wanted elekes1994DiskTriangleLowerBound_holds : elekes1994DiskTriangleLowerBound

/-- Source: Elekes (1994), additional regular polygon lower bound. -/
theorem_wanted elekes1994RegularPolygonLowerBound_holds : elekes1994RegularPolygonLowerBound

/-- Source: Brass and Sharifi, A lower bound for Lebesgue's universal cover problem (2005). -/
theorem_wanted brassSharifi2005LowerBound_holds : brassSharifi2005LowerBound

end

end MathlibExt.Geometry.LebesgueUniversalCoveringConstantWanted
