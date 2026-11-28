/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Condensed.GeometricDGModules
public import MathlibExt.RingTheory.CompleteHuberPairModels
public import Mathlib.RingTheory.Flat.Basic

/-!
# Genuine perfectoid integral/solid/almost coefficient models

The coefficient algebra is the actual plus ring. The almost ideal is
characterized by actual topological nilpotence in the parent Tate ring,
with the source idempotence/flatness conditions. It is not an arbitrary
ideal assigned a geometric name. Modified and almost coefficients retain
the actual full DG module mapping complexes of the normalized compact model.

Completed almost-ideal source: TauCetiProject/TauCeti revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
`TauCeti/RingTheory/Perfectoid/AlmostSetup.lean` (Apache2.0),
`almostSetupPlus_ideal` and `mem_almostSetupPlus_ideal`.
The native model identification is an explicit source-integration input;
no duplicate almost/Tate/Cartier-duality theorem is requested.
-/

@[expose] public noncomputable section

namespace MathlibExt.Condensed.PerfectoidSolidCoefficientModels

open _root_.CategoryTheory
open MathlibExt.RingTheory.CompleteHuberPairModels
open SolidAnalyticModules AdicSolidGenerators GeometricDGModules

variable (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p)

abbrev IntegralRing := ULift.{1} P.plus

/-- The actual geometric almost ideal, with no independent carrier choice. -/
structure AlmostIdealData where
  ideal : Ideal (IntegralRing p P)
  mem_iff : ∀ a : IntegralRing p P,
    a ∈ ideal ↔ IsTopologicallyNilpotent (a.down : P.ring)
  idempotent : ideal * ideal = ideal
  [flat : Module.Flat (IntegralRing p P) ideal]
  nonzero : Nontrivial P.ring → ideal ≠ ⊥

attribute [instance] AlmostIdealData.flat

/-- The exact integral plus-ring analytic generator dictionary. -/
abbrev IntegralCompactModel
    (E : RestrictionInput (IntegralRing p P) ⊤)
    (L : AnalyticReflection (IntegralRing p P) ⊤ E)
    (I : Ideal (IntegralRing p P)) (C : CompletionModel (IntegralRing p P) I) :=
  CompactDGModel (IntegralRing p P)
    (completedGenerator (IntegralRing p P) ⊤ E L I C)

/-- Full DG almost-modified coefficients on the actual perfectoid plus ring. -/
abbrev IntegralAlmostModules
    (E : RestrictionInput (IntegralRing p P) ⊤)
    (L : AnalyticReflection (IntegralRing p P) ⊤ E)
    (I : Ideal (IntegralRing p P)) (C : CompletionModel (IntegralRing p P) I)
    (M : IntegralCompactModel p P E L I C) (J : AlmostIdealData p P) :=
  AlmostModifiedModules (IntegralRing p P) M J.ideal

end MathlibExt.Condensed.PerfectoidSolidCoefficientModels
