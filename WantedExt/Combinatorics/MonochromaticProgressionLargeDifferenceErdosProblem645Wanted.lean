/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic progressions with large difference (Erdős Problem 645)

Erdős Problem 645: if `ℕ` is `2`-coloured then must there exist a monochromatic three-term
arithmetic progression `x, x + d, x + 2d` such that `d > x`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Notation

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticProgressionLargeDifferenceErdosProblem645Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #645, https://www.erdosproblems.com/645 (status PROVED
(LEAN)). UnsolvedMath record UM-30006965 (`EP-645`), dataset ulamai/UnsolvedMath v1.8.0.

`ℕ` is the positive integers, so `x ≥ 1` (the colour of `0` plays no role); colourings are functions
to `Bool`. Compared with the formal-conjectures statement `ErdosProblems/645.lean` (equivalent; no
code imported).
-/

/-- Erdős Problem 645: every `2`-colouring of the positive integers has a monochromatic three-term
progression `x, x + d, x + 2d` with `d > x ≥ 1`. -/
def monochromaticProgressionLargeDifference : Prop :=
  ∀ c : ℕ → Bool, ∃ x d : ℕ, 0 < x ∧ x < d ∧ c x = c (x + d) ∧ c (x + d) = c (x + 2 * d)

/--
Resolved true: Brown and Landman proved that every `2`-colouring of the positive integers has a
monochromatic progression `x, x + d, x + 2d` with `d > f(x)`, for any increasing function `f`;
erdosproblems.com/645 lists the problem as proved and records a short argument of Alweiss. Source:
T. F. Bloom, Erdős Problems, Problem #645, https://www.erdosproblems.com/645 (status PROVED (LEAN));
resolution: T. C. Brown and B. M. Landman, Monochromatic arithmetic progressions with large
differences, Bull. Austral. Math. Soc. (1999), 21-35, erdosproblems.com/645: first proved by Brown
and Landman, with d > f(x) for any increasing f; the page records a short argument of Alweiss,
https://www.erdosproblems.com/645.
-/
public theorem_wanted monochromaticProgressionLargeDifference_holds :
    monochromaticProgressionLargeDifference

end MathlibExt.Combinatorics.MonochromaticProgressionLargeDifferenceErdosProblem645Wanted
