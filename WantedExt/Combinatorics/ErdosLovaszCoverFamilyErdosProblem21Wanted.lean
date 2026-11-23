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

/-- **Erdős–Lovász family.** For a natural number $n$, a finite family $\mathcal{F}$ of finite
sets of natural numbers is an Erdős–Lovász family of order $n$ when every member of
$\mathcal{F}$ has exactly $n$ elements, any two members of $\mathcal{F}$ (not necessarily
distinct) have a common element, and every set of at most $n - 1$ natural numbers is disjoint
from some member of $\mathcal{F}$, where $n - 1$ is read as $0$ when $n = 0$. -/
def IsErdosLovaszFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
    ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/-- **Erdős Problem 21 (Erdős–Lovász).** The statement that there is a natural number $C$ such
that for every $n \ge 1$ there is a finite family $\mathcal{F}$ of finite sets of natural numbers
in which every member has exactly $n$ elements, any two members have a common element, every
set of at most $n - 1$ natural numbers is disjoint from some member, and
$|\mathcal{F}| \le C n$. This expresses $f(n) \ll n$, where $f(n)$ is the least size of such a
family. -/
def intersectingFamilyFullCoverLinearSize : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card ≤ C * n

/--
**Kahn's theorem on the Erdős–Lovász problem.** There is a natural number $C$ such that for
every $n \ge 1$ there is a finite family $\mathcal{F}$ of finite sets of natural numbers with
the following properties: every member of $\mathcal{F}$ has exactly $n$ elements, any two
members of $\mathcal{F}$ have a common element, every set of at most $n - 1$ natural numbers is
disjoint from some member of $\mathcal{F}$, and $|\mathcal{F}| \le C n$.

Kahn proved this, improving his earlier bound $O(n \log n)$ obtained from random lines in
projective planes; it answers Erdős Problem 21 in the affirmative.

Source: T. F. Bloom, Erdős
Problems, Problem #21, https://www.erdosproblems.com/21 (status PROVED (LEAN)); resolution: J. Kahn,
On a problem of Erdős and Lovász. II. n(r) = O(r), J. Amer. Math. Soc. 7 (1994), 125-143, main
theorem n(r) = O(r); erdosproblems.com/21: solved by Kahn [Ka94], https://doi.org/10.2307/2152722.
-/
public theorem_wanted intersectingFamilyFullCoverLinearSize_holds :
    intersectingFamilyFullCoverLinearSize

end MathlibExt.Combinatorics.ErdosLovaszCoverFamilyErdosProblem21Wanted
