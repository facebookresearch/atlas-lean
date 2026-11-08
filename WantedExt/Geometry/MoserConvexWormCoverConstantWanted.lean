/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.MoserWormCover

/-!
# Moser's convex worm cover constant: literature requests

Source: Optimization Problems, constant 13a; Panraksa and Wichiramala,
Wetzel's sector covers unit arcs (2021); Fässler and Orponen,
Curve packing and modulus estimates (2018).

The completed geometry is imported from its canonical upstream implementation.
The 20 literature propositions and 20 private proof requests are not assumptions
or proofs. Two conditional witness corollaries stay with their source claims.
There is no source-supplied exact-value conjecture. The PWW2007 polygonal-testing
companion remains an explicit partial-scope gap.
-/

@[expose] public section

open MeasureTheory Set

namespace MoserConvexWormCoverConstant

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundPiOverFour : Prop := convexWormCoverConstant ≤ Real.pi / 4

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundPiOverEight : Prop := convexWormCoverConstant ≤ Real.pi / 8

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundWetzel1973 : Prop := convexWormCoverConstant ≤ (34501 : ℝ) / 100000

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundGerriets1972 : Prop := convexWormCoverConstant ≤ (3214 : ℝ) / 10000

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundGerrietsPoole1974 : Prop := convexWormCoverConstant ≤ (28610 : ℝ) / 100000

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundNorwoodPooleLaidacker1992 : Prop :=
  convexWormCoverConstant ≤ (27524 : ℝ) / 100000

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundWang2006 : Prop := convexWormCoverConstant ≤ (270911861 : ℝ) / 1000000000

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def upperBoundPiOverTwelve : Prop := convexWormCoverConstant ≤ Real.pi / 12

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def lowerBoundWetzel1973 : Prop := (2194 : ℝ) / 10000 ≤ convexWormCoverConstant

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def lowerBoundKhandhawitSriswasdi2009 : Prop :=
  (227498 : ℝ) / 1000000 ≤ convexWormCoverConstant

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def lowerBoundKhandhawitPagonakisSriswasdi2013 : Prop :=
  (232239 : ℝ) / 1000000 ≤ convexWormCoverConstant

/-- Minimum attainment, not an assumption included in the optimization domain. Source:
Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc adaptation.
-/
def minimalConvexCoverExists : Prop :=
  ∃ Ω : Set ℂ, IsConvexUniversalCover Ω ∧
    volume Ω = ENNReal.ofReal convexWormCoverConstant

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexCoverNorwoodPoole2003 : Prop :=
  ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω ≤ ENNReal.ofReal ((2604370 : ℝ) / 10000000)

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexCoverPloymaklamWichiramala2018 : Prop :=
  ∃ Ω : Set ℂ, IsUniversalCover Ω ∧ volume Ω ≤ ENNReal.ofReal ((26007 : ℝ) / 100000)

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexUpperBoundNorwoodPoole2003 : Prop :=
  nonconvexWormCoverConstant ≤ (2604370 : ℝ) / 10000000

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexUpperBoundPloymaklamWichiramala2018 : Prop :=
  nonconvexWormCoverConstant ≤ (26007 : ℝ) / 100000

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def nonconvexStrictPositivity : Prop := 0 < nonconvexWormCoverConstant

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def halfDiskCovers : Prop := CoversEveryUnitArc halfDisk

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def halfSemidiskCovers : Prop := CoversEveryUnitArc halfSemidisk

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
def wetzelSectorCovers : Prop := CoversEveryUnitArc wetzelSector

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexUpperBoundNorwoodPoole2003_of_cover
    (h : nonconvexCoverNorwoodPoole2003) : nonconvexUpperBoundNorwoodPoole2003 :=
  nonconvexUpperBound_of_cover (by norm_num) h

/-- Source: Optimization Problems, constant 13a (frozen 2c1968cd); source-specific interval-arc
adaptation.
-/
theorem nonconvexUpperBoundPloymaklamWichiramala2018_of_cover
    (h : nonconvexCoverPloymaklamWichiramala2018) :
    nonconvexUpperBoundPloymaklamWichiramala2018 :=
  nonconvexUpperBound_of_cover (by norm_num) h

/-- Source: Optimization Problems, constant 13a, closed claim `upperBoundPiOverFour`. -/
theorem_wanted upperBoundPiOverFour_holds : upperBoundPiOverFour

/-- Source: Optimization Problems, constant 13a, closed claim `upperBoundPiOverEight`. -/
theorem_wanted upperBoundPiOverEight_holds : upperBoundPiOverEight

/-- Source: Optimization Problems, constant 13a, closed claim `upperBoundWetzel1973`. -/
theorem_wanted upperBoundWetzel1973_holds : upperBoundWetzel1973

/-- Source: Optimization Problems, constant 13a, closed claim `upperBoundGerriets1972`. -/
theorem_wanted upperBoundGerriets1972_holds : upperBoundGerriets1972

/-- Source: Optimization Problems, constant 13a, closed claim `upperBoundGerrietsPoole1974`. -/
theorem_wanted upperBoundGerrietsPoole1974_holds : upperBoundGerrietsPoole1974

/-- Source: Optimization Problems, constant 13a, closed claim
`upperBoundNorwoodPooleLaidacker1992`.
-/
theorem_wanted upperBoundNorwoodPooleLaidacker1992_holds : upperBoundNorwoodPooleLaidacker1992

/-- Source: Optimization Problems, constant 13a, closed claim `upperBoundWang2006`. -/
theorem_wanted upperBoundWang2006_holds : upperBoundWang2006

/-- Source: Optimization Problems, constant 13a, closed claim `upperBoundPiOverTwelve`. -/
theorem_wanted upperBoundPiOverTwelve_holds : upperBoundPiOverTwelve

/-- Source: Optimization Problems, constant 13a, closed claim `lowerBoundWetzel1973`. -/
theorem_wanted lowerBoundWetzel1973_holds : lowerBoundWetzel1973

/-- Source: Optimization Problems, constant 13a, closed claim
`lowerBoundKhandhawitSriswasdi2009`.
-/
theorem_wanted lowerBoundKhandhawitSriswasdi2009_holds : lowerBoundKhandhawitSriswasdi2009

/-- Source: Optimization Problems, constant 13a, closed claim
`lowerBoundKhandhawitPagonakisSriswasdi2013`.
-/
theorem_wanted lowerBoundKhandhawitPagonakisSriswasdi2013_holds :
    lowerBoundKhandhawitPagonakisSriswasdi2013

/-- Source: Optimization Problems, constant 13a, closed claim `minimalConvexCoverExists`. -/
theorem_wanted minimalConvexCoverExists_holds : minimalConvexCoverExists

/-- Source: Optimization Problems, constant 13a, closed claim `nonconvexCoverNorwoodPoole2003`. -/
theorem_wanted nonconvexCoverNorwoodPoole2003_holds : nonconvexCoverNorwoodPoole2003

/-- Source: Optimization Problems, constant 13a, closed claim
`nonconvexCoverPloymaklamWichiramala2018`.
-/
theorem_wanted nonconvexCoverPloymaklamWichiramala2018_holds :
    nonconvexCoverPloymaklamWichiramala2018

/-- Source: Optimization Problems, constant 13a, closed claim
`nonconvexUpperBoundNorwoodPoole2003`.
-/
theorem_wanted nonconvexUpperBoundNorwoodPoole2003_holds : nonconvexUpperBoundNorwoodPoole2003

/-- Source: Optimization Problems, constant 13a, closed claim
`nonconvexUpperBoundPloymaklamWichiramala2018`.
-/
theorem_wanted nonconvexUpperBoundPloymaklamWichiramala2018_holds :
    nonconvexUpperBoundPloymaklamWichiramala2018

/-- Source: Optimization Problems, constant 13a, closed claim `nonconvexStrictPositivity`. -/
theorem_wanted nonconvexStrictPositivity_holds : nonconvexStrictPositivity

/-- Source: Optimization Problems, constant 13a, closed claim `halfDiskCovers`. -/
theorem_wanted halfDiskCovers_holds : halfDiskCovers

/-- Source: Optimization Problems, constant 13a, closed claim `halfSemidiskCovers`. -/
theorem_wanted halfSemidiskCovers_holds : halfSemidiskCovers

/-- Source: Optimization Problems, constant 13a, closed claim `wetzelSectorCovers`. -/
theorem_wanted wetzelSectorCovers_holds : wetzelSectorCovers

end MoserConvexWormCoverConstant
