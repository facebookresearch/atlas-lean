/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic progressions of primes (Erdős Problem 1187)

Erdős Problem 1187: let `k ≥ 3`. In any finite colouring of the integers, are there monochromatic
arithmetic progressions of primes of length `k`? Are there monochromatic arithmetic progressions of
length `k` whose common difference is a prime?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.AP.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.MonochromaticPrimeProgressionsErdosProblem1187Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1187, https://www.erdosproblems.com/1187 (status
SOLVED). UnsolvedMath record UM-30007228 (`EP-1187`), dataset ulamai/UnsolvedMath v1.8.0.

A finite colouring is a map `ℤ → Fin r`. A `k`-term progression is a set of `k` integers in
arithmetic progression (MathlibExt's `Set.IsAPOfLength`); the first question is read for every `k ≥
3`. Only the first question is stated: the source calls the answer to the second trivially no
(colour by residue modulo `4`; no two integers at a prime distance share a colour), so it is not a
wanted theorem. Compared with the formal-conjectures statement `ErdosProblems/1187.lean` (equivalent
to `erdos_1187.parts.i`; no code imported).
-/

/-- Erdős Problem 1187, first question: for every `k ≥ 3`, every colouring of the integers with
finitely many colours has a monochromatic `k`-term arithmetic progression of primes
(`Set.IsAPOfLength`: a set of `k` integers `a, a + d, …, a + (k - 1) d`). -/
def monochromaticPrimeProgressions : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ (r : ℕ) (c : ℤ → Fin r), ∃ S : Set ℤ, S.IsAPOfLength k ∧
    (∀ n ∈ S, ∃ p : ℕ, p.Prime ∧ (p : ℤ) = n) ∧ ∃ γ : Fin r, ∀ n ∈ S, c n = γ

/--
Resolved true: with `r` colours one colour class contains a set of primes of relative upper density
at least `1/r`, and Green and Tao proved (Theorem 1.2) that every set of primes of positive relative
upper density contains arithmetic progressions of every length; erdosproblems.com/1187 records this
answer. Source: T. F. Bloom, Erdős Problems, Problem #1187, https://www.erdosproblems.com/1187
(status SOLVED); resolution: B. Green and T. Tao, The primes contain arbitrarily long arithmetic
progressions, Ann. of Math. (2) 167 (2008), 481-547, Theorem 1.2: every set of primes of positive
relative upper density contains arbitrarily long arithmetic progressions; with r colours some colour
class has relative upper density ≥ 1/r (erdosproblems.com/1187),
https://doi.org/10.4007/annals.2008.167.481.
-/
public theorem_wanted monochromaticPrimeProgressions_holds : monochromaticPrimeProgressions

end MathlibExt.NumberTheory.MonochromaticPrimeProgressionsErdosProblem1187Wanted
