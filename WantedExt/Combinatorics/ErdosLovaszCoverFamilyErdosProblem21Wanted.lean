/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Intersecting families with full covering number (Erdős Problem 21)

Erdős Problem 21 (Erdős and Lovász): let `f(n)` be the least size of an intersecting family `𝓕` of
`n`-element sets such that every set of at most `n - 1` elements is disjoint from some member of
`𝓕`. Is `f(n) ≪ n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosLovaszCoverFamilyErdosProblem21Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #21, https://www.erdosproblems.com/21 (status PROVED
(LEAN)). UnsolvedMath record UM-30006683 (`EP-21`), dataset ulamai/UnsolvedMath v1.8.0.

Sets are finite subsets of `ℕ` (the ground set is immaterial). `f(n) ≪ n` is stated without `f`: for
some `C` and every `n ≥ 1` such a family of size at most `C n` exists. Compared with the
formal-conjectures statement `ErdosProblems/21.lean` (`f` as an infimum with `f n ≤ C n` eventually,
equivalent; no code imported).
-/

/-- `F` is an intersecting family of `n`-element sets such that every set of at most `n - 1`
elements is disjoint from some member of `F`. -/
def IsErdosLovaszFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
    ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/-- Erdős Problem 21: `f(n) ≪ n`, where `f(n)` is the least size of an intersecting family of
`n`-sets such that every set of size at most `n - 1` is disjoint from some member; stated as the
existence of such families of size at most `C n` for all `n ≥ 1`. -/
def intersectingFamilyFullCoverLinearSize : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card ≤ C * n

/--
Resolved true: Kahn proved `f(n) = O(n)`, improving his earlier `O(n log n)` from random lines in
projective planes; erdosproblems.com/21 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #21, https://www.erdosproblems.com/21 (status PROVED (LEAN)); resolution: J. Kahn,
On a problem of Erdős and Lovász. II. n(r) = O(r), J. Amer. Math. Soc. 7 (1994), 125-143, main
theorem n(r) = O(r); erdosproblems.com/21: solved by Kahn [Ka94], https://doi.org/10.2307/2152722.
-/
public theorem_wanted intersectingFamilyFullCoverLinearSize_holds :
    intersectingFamilyFullCoverLinearSize

end MathlibExt.Combinatorics.ErdosLovaszCoverFamilyErdosProblem21Wanted
