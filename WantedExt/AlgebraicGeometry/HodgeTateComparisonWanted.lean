/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.HodgeTateComparison

/-!
# Hodge–Tate comparison for actual proper smooth schemes over Q_p

Construct the C_p-linear, Galois-equivariant comparison between the
actual rational pro-étale cohomology of the geometric fibre and the
coherent cohomology of its actual differential-form sheaves. The negative
Tate twist in Hodge degree i uses the constructed cyclotomic character.

The fields, coefficient sheaves, scheme Galois operators, completed field
action, differential sheaves and right-derived coherent sections are
fixed constructions. No replacement representation, free period ring or
chosen Galois character is assumed.

Reference: Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*,
Corollary 1.8, p. 4, and preceding Theorem 1.6 for Galois equivariance;
the algebraic scheme case follows by the comparisons described on p. 5.
https://arxiv.org/abs/1205.3463
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HodgeTateComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison

/-- The geometric Hodge–Tate comparison in every cohomological degree. -/
public def_wanted hodgeTateComparison
    (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))
    [IsProper X.hom] [Smooth X.hom] (n : ℕ) : Comparison p X n

end WantedExt.AlgebraicGeometry.HodgeTateComparison
