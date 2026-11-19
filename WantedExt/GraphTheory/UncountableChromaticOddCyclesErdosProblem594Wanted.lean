/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Odd cycles in graphs of uncountable chromatic number (Erdős Problem 594)

Erdős Problem 594 (Erdős and Hajnal): does every graph `G` with chromatic number at least `ℵ₁`
contain all sufficiently large odd cycles?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.UncountableChromaticOddCyclesErdosProblem594Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #594, https://www.erdosproblems.com/594 (status PROVED
(LEAN)). UnsolvedMath record UM-30006945 (`EP-594`), dataset ulamai/UnsolvedMath v1.8.0.

Chromatic number at least `ℵ₁` means that there is no proper colouring with countably many colours,
`IsEmpty (G.Coloring ℕ)`; an odd cycle of length `2k + 1` is a closed walk with `Walk.IsCycle`.
Vertex types are in `Type`. Compared with the formal-conjectures statement `ErdosProblems/594.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 594 (Erdős and Hajnal): every graph with chromatic number at least `ℵ₁` (no
proper colouring with countably many colours) contains cycles of all sufficiently large odd
lengths. -/
def uncountableChromaticOddCycles : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
    ∃ N : ℕ, ∀ k ≥ N, ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * k + 1

/--
Resolved true: Erdős, Hajnal and Shelah proved that every graph with uncountable chromatic number
contains cycles of every sufficiently large odd length (Erdős and Hajnal had proved this for
chromatic number at least `ℵ₂`); erdosproblems.com/594 lists the problem as proved, with a Lean
proof of the formal-conjectures statement. Source: T. F. Bloom, Erdős Problems, Problem #594,
https://www.erdosproblems.com/594 (status PROVED (LEAN)); resolution: P. Erdős, A. Hajnal and S.
Shelah, On some general properties of chromatic numbers, Topics in topology (Proc. Colloq.,
Keszthely, 1972) (1974), 243-255, erdosproblems.com/594: proved by Erdős, Hajnal and Shelah (Erdős
and Hajnal had proved it for chromatic number at least ℵ₂), https://www.erdosproblems.com/594.
-/
public theorem_wanted uncountableChromaticOddCycles_holds : uncountableChromaticOddCycles

end MathlibExt.GraphTheory.UncountableChromaticOddCyclesErdosProblem594Wanted
