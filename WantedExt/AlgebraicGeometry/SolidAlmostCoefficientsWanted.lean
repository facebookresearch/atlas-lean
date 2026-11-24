/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Condensed.PerfectoidSolidCoefficientModels
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Actual perfectoid solid-analytic and completed compact DG construction requests

Anschuetz--Mann, *Descent for solid quasi-coherent sheaves on perfectoid
spaces*, arXiv:2403.01951v2, Section2.1/Definition2.4 and Section4.2.
The coefficient ring/modules, integer/Z[T] scalar tests, localized free
profinite generators, completion unit and full DG mapping model are fixed.
The source-unit and ordinary completion inputs are explicit; no affine
comparison, v-descent or arbitrary geometric equivalence is assumed.

Generic local Tate/plus/almost and cochain DG primitives are positively
reused. Global coefficient restrictions, v-hyperdescent and Frobenius
comparisons remain separately normalized companions.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SolidAlmostCoefficients

open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.Condensed.SolidAnalyticModules
open MathlibExt.Condensed.AdicSolidGenerators
open MathlibExt.Condensed.GeometricDGModules
open MathlibExt.Condensed.PerfectoidSolidCoefficientModels

/-- The actual integral analytic reflector, with its prescribed unit universal property. -/
public def_wanted integralAnalyticReflection
    (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p) [Nontrivial P.ring]
    (E : RestrictionInput (IntegralRing p P) ⊤)
    (hUnit : IsAnalyticComplete (IntegralRing p P) ⊤ E
      (unitObject (IntegralRing p P))) :
    AnalyticReflection (IntegralRing p P) ⊤ E

/-- The small completed compact dictionary retains genuine full DG Hom complexes. -/
public def_wanted completedIntegralCompactModel
    (p : ℕ) [Fact p.Prime] (P : PerfectoidPair p) [Nontrivial P.ring]
    (E : RestrictionInput (IntegralRing p P) ⊤)
    (L : AnalyticReflection (IntegralRing p P) ⊤ E)
    (I : Ideal (IntegralRing p P)) (hAdic : IsAdic I)
    [IsAdicComplete I (IntegralRing p P)] (hFinite : I.FG)
    (C : CompletionModel (IntegralRing p P) I)
    (hUnitAnalytic : IsAnalyticComplete (IntegralRing p P) ⊤ E
      (unitObject (IntegralRing p P)))
    (hUnitComplete : IsComplete (IntegralRing p P) I
      (unitObject (IntegralRing p P))) :
    IntegralCompactModel p P E L I C

end WantedExt.AlgebraicGeometry.SolidAlmostCoefficients
