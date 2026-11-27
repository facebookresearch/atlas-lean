/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 591
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.SetTheory.Cardinal.SimpleGraph
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

open Cardinal Ordinal

universe u

namespace MathlibExt.Combinatorics.ErdosProblem591Wanted

/-! Source record `FC-ErdosProblem591`, ported from FormalConjectures
`ErdosProblems/591.lean` (`theorem erdos_591`) and checked against
erdosproblems.com/591. `OrdinalCardinalRamsey` is MathlibExt's (ported from
FC's `FormalConjecturesForMathlib`). The `answer(True)` wrapper is elaborated
to a direct proposition. Status: resolved true (Schipperus [Sc10] and Darby,
independently). -/

/-- **Erdős Problem 591.** The statement that, for $\alpha = \omega^{\omega^2}$, every red/blue
colouring of the edges of the complete graph on the ordinals less than $\alpha$ (that is, every
pair of complementary simple graphs, red and blue, on this set) has a red clique whose order
type is $\alpha$ or a blue clique with exactly $3$ elements. In partition notation,
$\alpha \to (\alpha, 3)^2$. -/
def conjecture : Prop :=
  OrdinalCardinalRamsey (ω ^ ω ^ 2 : Ordinal.{u}) (ω ^ ω ^ 2 : Ordinal.{u}) (3 : Cardinal.{u})

/--
**Erdős Problem 591 is true.** Let $\alpha = \omega^{\omega^2}$. For every red/blue colouring of
the edges of the complete graph on the ordinals less than $\alpha$, that is, every pair of
complementary simple graphs (red and blue) on this set, there is a red clique whose order type
is $\alpha$ or a blue clique with exactly $3$ elements. In partition notation,
$\alpha \to (\alpha, 3)^2$.

Source: Schipperus [Sc10] and Darby, independently, per
erdosproblems.com/591, https://www.erdosproblems.com/591. Moved from
`OpenConjectures/Combinatorics/ErdosProblem591`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem591Wanted
