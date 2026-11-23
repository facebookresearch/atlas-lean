/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lacunary sequences whose reciprocal sums contain an interval of rationals (Erdős Problem 355)

Erdős Problem 355: is there a lacunary sequence `A ⊆ ℕ` (`a_{n+1} / a_n ≥ λ > 1`) such that the sums
`∑_{a ∈ A'} 1/a` over finite `A' ⊆ A` contain all rationals in some open interval?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.LacunaryReciprocalSumsRationalsErdosProblem355Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #355, https://www.erdosproblems.com/355 (status PROVED
(LEAN)). UnsolvedMath record UM-30006835 (`EP-355`), dataset ulamai/UnsolvedMath v1.8.0.

The sequence is `a : ℕ → ℕ` with positive terms and `a (n + 1) ≥ c · a n` for a fixed `c > 1`, so it
is strictly increasing; `A'` is a finite set of its terms. Compared with the formal-conjectures
statement `ErdosProblems/355.lean` (equivalent; no code imported).
-/

/-- `a` is a lacunary sequence of positive integers: `a (n + 1) ≥ c * a n` for all `n`, for some
`c > 1`. -/
def IsLacunary (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ ∃ c : ℝ, 1 < c ∧ ∀ n, c * a n ≤ a (n + 1)

/-- Erdős Problem 355: there are a lacunary sequence `a` and a nonempty open interval `(u, v)` such
that every rational in `(u, v)` is `∑_{m ∈ S} 1/m` for a finite set `S` of terms of `a`. -/
def lacunaryReciprocalSumsContainRationalInterval : Prop :=
  ∃ a : ℕ → ℕ, IsLacunary a ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, u < q → (q : ℝ) < v →
    ∃ S : Finset ℕ, (∀ m ∈ S, m ∈ Set.range a) ∧ ∑ m ∈ S, (1 : ℚ) / m = q

/--
Resolved true: van Doorn and Kovač constructed, for every `λ ∈ (1, 2)`, a sequence with `a_{n+1} /
a_n ≥ λ` whose finite reciprocal sums contain every rational in an open interval (Bleicher and Erdős
had conjectured the answer no); erdosproblems.com/355 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #355, https://www.erdosproblems.com/355 (status PROVED (LEAN));
resolution: W. van Doorn and V. Kovač, Lacunary sequences whose reciprocal sums represent all
rationals in an interval, arXiv:2509.24971 (2025); formal proof github.com/Woett/Lean-files,
ErdosProblem355.lean, yes, for every lacunarity constant λ ∈ (1, 2) (erdosproblems.com/355),
https://arxiv.org/abs/2509.24971.
-/
public theorem_wanted lacunaryReciprocalSumsContainRationalInterval_holds :
    lacunaryReciprocalSumsContainRationalInterval

end MathlibExt.NumberTheory.LacunaryReciprocalSumsRationalsErdosProblem355Wanted
