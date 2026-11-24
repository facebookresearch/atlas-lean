/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PeriodGroupPositionModels

/-!
# Source-normalized algebraic representation and period lattice requests

The group, cocharacter and representations are natural maps on every
original algebra test. The resulting modules, basis columns and Plucker
conditions use the actual native period rings and matrices. No arbitrary
representation fibre functor or relative-position predicate is supplied.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections VI.1--VI.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PeriodGroupPositions

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations

/-- Every actual G_m action splits into its source-normalized integer characters. -/
public def_wanted weightSplitting (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    (n : ℕ) (ρ : Representation E G n) (μ : Cocharacter E G) : WeightSplitting E G n ρ μ

open MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields
open MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings
open MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels
open MathlibExt.AlgebraicGeometry.PeriodGroupPositionModels

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  {S : Base p C} (T : Untilting p C S) (L : ScalarLift p C S T) (x : Parameter p C T L)
  (G : Over (Spec (.of E.field))) [GrpObj G]

/-- The actual invertible representation matrix carries the standard lattice to a full lattice. -/
public def_wanted representedLattice (n : ℕ) (ρ : Representation E.field G n)
    (g : GenericGroup p C T L x G) : RepresentedLattice p C T L x G ρ g

/-- Native scalar extension fixes every source basis column in the standard integral lattice. -/
public def_wanted weightFrame (n : ℕ) (ρ : Representation E.field G n)
    (μ : Cocharacter E.field G) (W : WeightSplitting E.field G n ρ μ) :
    WeightFrame p C T L x G W

end WantedExt.AlgebraicGeometry.PeriodGroupPositions
