/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Product-free subsets of alternating groups have density o(1) (AIM additive comb., Problem 4.3)

AIM workshop Recent trends in additive combinatorics, Problem 4.3 (V. Sós): let `P` be a
product-free subset of a group `G` with `|G| = n` (the list prints 'an abelian group', then turns to
`G = Aₙ`). How large can `P` be? For abelian groups one has `|P| ≥ 2n/7` (Alon-Kleitman), which is
sharp. The case `G = Aₙ` is already interesting, and Green conjectures that in this case `|P| =
o(|Aₙ|)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import MathlibExt.Algebra.Group.ProductFree

@[expose] public section

namespace MathlibExt.GroupTheory.AlternatingProductFreeDensityAIMCombinatoricsProblem259Wanted

/-!
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 4.3 (V. Sós;
conjecture of B. Green). UnsolvedMath record UM-20001134 (`AIM-COMBINATORICS-0259`), dataset
ulamai/UnsolvedMath v1.8.0.

Product-free is MathlibExt's `Set.IsProductFree` (no `a, b ∈ P` with `a b ∈ P`, `a = b` allowed),
inside `alternatingGroup (Fin n)`. Green's conjecture is the formalized part; the open-ended 'how
large can `P` be' for general groups is not formalized.
-/

/-- Green's conjecture (AIM, Recent trends in additive combinatorics, Problem 4.3): a product-free
subset `P` of the alternating group `Aₙ` (no `a, b ∈ P` with `a b ∈ P`, `Set.IsProductFree` of
MathlibExt) has `|P| = o(|Aₙ|)`. -/
def productFreeAlternatingDensityTendsToZero : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ P : Set (alternatingGroup (Fin n)),
    P.IsProductFree → (P.ncard : ℝ) ≤ ε * Nat.card (alternatingGroup (Fin n))

/--
Resolved true: product-free subsets of `Aₙ` have density at most `(n - 1)^{-1/3}` (Gowers, via
quasirandomness, as recorded by Keevash, Lifshitz and Minzer), improved to `O(n^{-1/2} log^{7/2} n)`
by Eberhard; Keevash, Lifshitz and Minzer determined the maximum for large `n`. In particular `|P| =
o(|Aₙ|)`. Source: AIM workshop Recent trends in additive combinatorics (2004), problem list
collected by E. Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem
4.3 (V. Sós; conjecture of B. Green); resolution: W. T. Gowers, Quasirandom groups, Combin. Probab.
Comput. 17 (2008), 363-387, arXiv:0710.3877; S. Eberhard, Product mixing in the alternating group,
Discrete Anal. 2016:2; P. Keevash, N. Lifshitz and D. Minzer, On the largest product-free subsets of
the alternating groups, Invent. Math. 237 (2024), 1329-1375, arXiv:2205.15191,
Keevash-Lifshitz-Minzer, Section 1: Gowers established the upper bound (n - 1)^{-1/3} for the
density of product-free subsets of Aₙ, Eberhard showed μ(A) = O(n^{-1/2} log^{7/2} n), and their
Theorem 1.1 determines the maximum for large n (density Θ(n^{-1/2})),
https://doi.org/10.1007/s00222-024-01273-1.
-/
public theorem_wanted productFreeAlternatingDensityTendsToZero_holds :
    productFreeAlternatingDensityTendsToZero

end MathlibExt.GroupTheory.AlternatingProductFreeDensityAIMCombinatoricsProblem259Wanted
