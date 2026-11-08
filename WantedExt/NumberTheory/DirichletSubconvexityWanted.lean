/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Established bounds for the Dirichlet subconvexity exponent
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LSeries.DirichletSubconvexity

@[expose] public section

namespace MathlibExt.NumberTheory.DirichletSubconvexity

/-- Burgess's conductor-aspect central-value bound makes `3/16` admissible.

Source: Petrow and Young, *The Weyl bound for Dirichlet L-functions of
cube-free conductor*, Annals of Mathematics 192 (2020), introduction equation
(1.2), quoting Burgess's 1963 theorem. -/
public theorem_wanted burgessThreeSixteenths_admissible :
    IsDirichletSubconvexityExponent ((3 : ℝ) / 16)

/-- The catalogue's exact upper bound `C62b ≤ 3/16`.

Source: teorth/optimizationproblems `constants/62b.md`, commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, citing Burgess (1963) through
Petrow--Young (2020). -/
public theorem_wanted dirichletSubconvexityExponent_le_threeSixteenths :
    dirichletSubconvexityExponent ≤ (((3 : ℝ) / 16 : ℝ) : EReal)

/-- Petrow--Young's Weyl exponent for primitive characters of cube-free level.

Source: Petrow and Young, *The Weyl bound for Dirichlet L-functions of
cube-free conductor*, Annals of Mathematics 192 (2020), abstract and
introduction. -/
public theorem_wanted petrowYoungCubeFreeOneSixth_admissible :
    IsCentralValueExponentOn {q | q.IsPowerFree 3} ((1 : ℝ) / 6)

end MathlibExt.NumberTheory.DirichletSubconvexity
