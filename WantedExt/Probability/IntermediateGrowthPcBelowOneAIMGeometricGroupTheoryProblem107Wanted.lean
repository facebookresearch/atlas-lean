/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# p_c < 1 for groups of intermediate growth (AimPL Amenability of discrete groups, Problem 3.7)

AimPL, Amenability of discrete groups, Problem 3.7: is `ρ_c < 1` for all groups of intermediate
growth?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import MathlibExt.GroupTheory.GroupGrowth
public import MathlibExt.Probability.ProductBondPercolation

@[expose] public section

namespace MathlibExt.Probability.IntermediateGrowthPcBelowOneAIMGeometricGroupTheoryProblem107Wanted

/-!
Source: AimPL: Amenability of discrete groups, Problem 3.7, http://aimpl.org/amenablediscrete/3/.
UnsolvedMath record UM-20001598 (`AIM-GEOMETRIC_GROUP_THEORY-0107`), dataset ulamai/UnsolvedMath
v1.8.0.

`ρ_c` is read as the critical probability `p_c` of Bernoulli bond percolation on a Cayley graph
(MathlibExt's `criticalProb`), for every finite generating family `P : Group.Generators G ι`. The
Cayley graph is Mathlib's `SimpleGraph.mulCayley (Set.range P.val)` (`g` and `h ≠ g` adjacent when
`h = g s` or `g = h s` for a generator `s`). Intermediate growth uses MathlibExt's growth function
`P.growth` (word balls of Mathlib's word metric): not `HasPolynomialGrowth`, and eventually below
`bⁿ` for every `b > 1`. Finitely generated groups are countable, which `criticalProb` needs.
-/

open Filter

/-- AimPL Problem 3.7 (Amenability of discrete groups), with `ρ_c` read as the critical probability
of Bernoulli bond percolation (`criticalProb` of MathlibExt): for every finitely generated group of
intermediate growth, i.e. every finite generating family `P` whose growth function
(`Group.Generators.growth` of MathlibExt) is not polynomially bounded (`HasPolynomialGrowth` fails)
and is eventually at most `bⁿ` for every `b > 1`, the Cayley graph (Mathlib's
`SimpleGraph.mulCayley` of the generators) has `p_c < 1`. -/
def intermediateGrowthPercolationThreshold : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (ι : Type) [Finite ι] (P : Group.Generators G ι),
    ¬ P.HasPolynomialGrowth → (∀ b : ℝ, 1 < b → ∀ᶠ n in atTop, (P.growth n : ℝ) ≤ b ^ n) →
    MathlibExt.Probability.ProductBondPercolation.criticalProb
      (SimpleGraph.mulCayley (Set.range P.val)) < 1

/--
Resolved true: Duminil-Copin, Goswami, Raoufi, Severo and Yadin proved that Bernoulli percolation on
every quasi-transitive graph of super-linear growth has `p_c < 1` (Theorem 1.3), in particular on
every Cayley graph of a finitely generated group of intermediate growth, whose balls grow faster
than any polynomial. Source: AimPL: Amenability of discrete groups, Problem 3.7,
http://aimpl.org/amenablediscrete/3/; resolution: H. Duminil-Copin, S. Goswami, A. Raoufi, F. Severo
and A. Yadin, Existence of phase transition for percolation using the Gaussian free field, Duke
Math. J. 169 (2020), 3539-3563, arXiv:1806.07733, Theorem 1.3: every quasi-transitive graph with
super-linear growth (limsup |B_r(x)|/r = ∞) has p_c(G) < 1, in particular every Cayley graph of a
finitely generated group of super-linear growth, answering a conjecture of Benjamini and Schramm;
intermediate growth is super-linear, https://doi.org/10.1215/00127094-2020-0036.
-/
public theorem_wanted intermediateGrowthPercolationThreshold_holds :
    intermediateGrowthPercolationThreshold

end MathlibExt.Probability.IntermediateGrowthPcBelowOneAIMGeometricGroupTheoryProblem107Wanted
