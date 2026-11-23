/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Edges outside monochromatic triangles (Erdős Problem 639)

Erdős Problem 639: is it true that if the edges of `K_n` are `2`-coloured then there are at most
`n²/4` many edges which do not occur in a monochromatic triangle?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Sym2

@[expose] public section

namespace MathlibExt.GraphTheory.MonochromaticTriangleUncoveredEdgesErdosProblem639Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #639, https://www.erdosproblems.com/639 (status PROVED
(LEAN)). UnsolvedMath record UM-30006963 (`EP-639`), dataset ulamai/UnsolvedMath v1.8.0.

The page states the question without a range of `n`, but the bound fails for `3 ≤ n ≤ 6` (by Keevash
and Sudakov the maximum is `C(n, 2)` for `n ≤ 5` and `10` for `n = 6`), so the statement is
formalized for `n ≥ 7`, the range of their theorem. Colourings are functions `Sym2 (Fin n) → Fin 2`;
`n²/4` is `⌊n²/4⌋` in `ℕ`, the same bound for an integer count. Compared with the formal-conjectures
statement `ErdosProblems/639.lean` (the formal-conjectures statement is for all large `n`, implied
by this one; no code imported).
-/

/-- In the red/blue colouring `c` of the edges of `K_n`, the edge `{x, y}` lies in a monochromatic
triangle. -/
def InMonoTriangle {n : ℕ} (c : Sym2 (Fin n) → Fin 2) (x y : Fin n) : Prop :=
  ∃ z, z ≠ x ∧ z ≠ y ∧ c s(x, z) = c s(x, y) ∧ c s(y, z) = c s(x, y)

/-- Erdős Problem 639, for `n ≥ 7`: in every red/blue colouring of the edges of `K_n` at most
`⌊n²/4⌋` edges lie in no monochromatic triangle. -/
def uncoveredEdgesAtMostQuarter : Prop :=
  ∀ n : ℕ, 7 ≤ n → ∀ c : Sym2 (Fin n) → Fin 2,
    {e : Sym2 (Fin n) | ∃ x y, x ≠ y ∧ e = s(x, y) ∧ ¬ InMonoTriangle c x y}.ncard ≤ n ^ 2 / 4

/--
Resolved true: Keevash and Sudakov proved that for every `n ≥ 7` every red/blue colouring of the
edges of `K_n` has at most `⌊n²/4⌋` edges in no monochromatic triangle (the maximum is `C(n, 2)` for
`n ≤ 5` and `10` for `n = 6`); erdosproblems.com/639 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #639, https://www.erdosproblems.com/639 (status PROVED (LEAN));
resolution: P. Keevash and B. Sudakov, On the number of edges not covered by monochromatic copies of
a fixed graph, J. Combin. Theory Ser. B (2004), 41-53, erdosproblems.com/639: the correct threshold
is ⌊n²/4⌋ for all n ≥ 7, C(n, 2) for n ≤ 5 and 10 for n = 6 (Theorem 1.1 as cited in
formal-conjectures), https://www.erdosproblems.com/639.
-/
public theorem_wanted uncoveredEdgesAtMostQuarter_holds : uncoveredEdgesAtMostQuarter

end MathlibExt.GraphTheory.MonochromaticTriangleUncoveredEdgesErdosProblem639Wanted
