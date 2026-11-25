/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PDivisibleLieModels
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Representing the actual formal tangent of a p-divisible group

Messing, *The crystals associated to Barsotti-Tate groups* (1972),
ChapterII, and Scholze--Weinstein, arXiv:1211.6357v2, Sections1-2.
The tangent tests are actual p-nilpotent algebras with square-zero modules,
and the group is an actual finite-flat scheme tower. The representing
cotangent and formal Lie modules are fixed by naturality on all those
algebra/module tests. This includes p-complete bases such as O_C, where
differentiating finite torsion groups directly would miss the formal Lie.

Crystalline/Dieudonne and Hodge filtration comparisons are separate
normalized companions. The generic source crystalline sites, ordinary
Tate construction and finite-group Cartier duality are not requested again.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleFormalLie

open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleLieModels
open _root_.AlgebraicGeometry

/-- Finite-projective representation of the actual formal tangent functor. -/
public def_wanted formalLieModel
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    (G : PDivisibleGroup (Spec (.of R)) p) : LieModel p R G

end WantedExt.AlgebraicGeometry.PDivisibleFormalLie
