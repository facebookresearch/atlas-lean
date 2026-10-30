/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Steiner triple systems of high girth (Erdős Problem 207)

Erdős Problem 207: for every `g ≥ 2`, if `n` is large and `n ≡ 1, 3 (mod 6)`, is there a Steiner
triple system on `n` points in which any `j` triples, `2 ≤ j ≤ g`, contain at least `j + 3` points?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Filter.AtTopBot.Defs
public import MathlibExt.Combinatorics.SetFamily.IndependentSet

@[expose] public section

namespace MathlibExt.Combinatorics.HighGirthSteinerTripleSystemErdosProblem207Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #207, https://www.erdosproblems.com/207 (status
PROVED). UnsolvedMath record UM-30006765 (`EP-207`), dataset ulamai/UnsolvedMath v1.8.0.

A Steiner triple system on `Fin n` is the canonical `SetFamily.IsSteinerTripleSystem` of MathlibExt:
3-element blocks covering every pair of distinct points exactly once. Compared with the
formal-conjectures statement `ErdosProblems/207.lean` (equivalent, there via `IsBlockDesign 2 3`; no
code imported).
-/

open Filter

/-- Erdős Problem 207: for every `g ≥ 2` and all large `n ≡ 1, 3 (mod 6)` there is a Steiner triple
system on `n` points (`SetFamily.IsSteinerTripleSystem`: three-point blocks, every pair of distinct
points in exactly one block) in which any `j` blocks, `2 ≤ j ≤ g`, cover at least `j + 3` points. -/
def highGirthSteinerTripleSystemsExist : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ᶠ n : ℕ in atTop, (n % 6 = 1 ∨ n % 6 = 3) →
    ∃ H : Finset (Finset (Fin n)), SetFamily.IsSteinerTripleSystem H ∧
      ∀ E ⊆ H, 2 ≤ E.card → E.card ≤ g → E.card + 3 ≤ (E.biUnion id).card

/--
Resolved true: Kwan, Sah, Sawhney and Simkin proved Erdős's conjecture that for every `g` and all
large `n ≡ 1, 3 (mod 6)` there is a Steiner triple system on `n` points of girth greater than `g`:
no `j` triples with `2 ≤ j ≤ g` span at most `j + 2` points (for `j ≤ 3` this holds in every Steiner
triple system). Source: T. F. Bloom, Erdős Problems, Problem #207, https://www.erdosproblems.com/207
(status PROVED); resolution: M. Kwan, A. Sah, M. Sawhney and M. Simkin, High-girth Steiner triple
systems, Ann. of Math. (2) 200 (2024), 1059-1156, arXiv:2201.04554, main theorem: Erdős's 1973
conjecture, Steiner triple systems of girth greater than g on all large admissible n,
https://doi.org/10.4007/annals.2024.200.3.4.
-/
public theorem_wanted highGirthSteinerTripleSystemsExist_holds : highGirthSteinerTripleSystemsExist

end MathlibExt.Combinatorics.HighGirthSteinerTripleSystemErdosProblem207Wanted
