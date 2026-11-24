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

/-- **Burgess's bound for Dirichlet central values.** The number $3/16$ is an admissible
conductor-aspect exponent for primitive Dirichlet characters: for every $\varepsilon > 0$ there are
a real number $C > 0$ and a natural number $Q$ such that for every positive integer $q \ge Q$ and
every primitive Dirichlet character $\chi$ modulo $q$, the analytically continued Dirichlet
$L$-function satisfies $|L(1/2, \chi)| \le C q^{3/16 + \varepsilon}$.

Source: Petrow and Young, *The Weyl bound for Dirichlet L-functions of
cube-free conductor*, Annals of Mathematics 192 (2020), introduction equation
(1.2), quoting Burgess's 1963 theorem. -/
public theorem_wanted burgessThreeSixteenths_admissible :
    IsDirichletSubconvexityExponent ((3 : ℝ) / 16)

/-- **The Dirichlet subconvexity exponent is at most 3/16.** The conductor-aspect Dirichlet
subconvexity exponent, an extended real number, is at most $3/16$.

Source: teorth/optimizationproblems `constants/62b.md`, commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, citing Burgess (1963) through
Petrow--Young (2020). -/
public theorem_wanted dirichletSubconvexityExponent_le_threeSixteenths :
    dirichletSubconvexityExponent ≤ (((3 : ℝ) / 16 : ℝ) : EReal)

/-- **Petrow–Young Weyl bound for central values.** The number $1/6$ is a central-value exponent
on the set of cube-free levels, the natural numbers $q > 0$ such that $p^3$ does not divide $q$
for any prime $p$: for every $\varepsilon > 0$ there are a real number $C > 0$ and a natural
number $Q$ such that for every cube-free $q \ge Q$ and every primitive Dirichlet character $\chi$
modulo $q$, the analytically continued Dirichlet $L$-function satisfies
$|L(1/2, \chi)| \le C q^{1/6 + \varepsilon}$.

Source: Petrow and Young, *The Weyl bound for Dirichlet L-functions of
cube-free conductor*, Annals of Mathematics 192 (2020), abstract and
introduction. -/
public theorem_wanted petrowYoungCubeFreeOneSixth_admissible :
    IsCentralValueExponentOn {q | q.IsPowerFree 3} ((1 : ℝ) / 6)

end MathlibExt.NumberTheory.DirichletSubconvexity
