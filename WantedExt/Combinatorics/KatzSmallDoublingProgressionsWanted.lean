/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.KatzSmallDoublingProgressionsWanted

/-- Sumset `A + A` of a finite set of integers as a `Finset ℤ`, whose
cardinality is `|A + A|` in the source. Source: [AIM-COMBINATORICS-0211],
AIM Problem Lists, Recent trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`. -/
def katzSumset (A : Finset ℤ) : Finset ℤ :=
  Finset.image (fun p : ℤ × ℤ => p.1 + p.2) (Finset.product A A)

/-- Set of `k`-term arithmetic progressions in `A`, as start/difference pairs
`(a, d)` with `a + i * d ∈ A` for all `i < k`; its `Set.ncard` is the number
of `k`-term progressions in the source. Source: [AIM-COMBINATORICS-0211],
AIM Problem Lists, Recent trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`. -/
def katzAPSet (k : ℕ) (A : Finset ℤ) : Set (ℤ × ℤ) :=
  {p : ℤ × ℤ | ∀ i : ℕ, i < k → p.1 + (i : ℤ) * p.2 ∈ A}

/-- Katz's question (Problem 1.5): for fixed integer `k ≥ 3` and real `C ≥ 2`,
does every finite `A ⊆ ℤ` with `|A + A| < C * |A|` contain at least
`c * |A|^2` `k`-term arithmetic progressions for some `c > 0` depending only
on `k` and `C`? Source: [AIM-COMBINATORICS-0211], AIM Problem Lists, Recent
trends in additive combinatorics, item 1.5,
`aim-combinatorics-notes.json notes[210]`,
https://aimath.org/WWN/additivecomb/additivecomb.pdf. -/
def conjecture : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ C : ℝ, 2 ≤ C → ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℤ,
    (Finset.card (katzSumset A) : ℝ) < C * (Finset.card A : ℝ) →
    c * ((Finset.card A : ℝ) ^ 2) ≤ (Set.ncard (katzAPSet k A) : ℝ)

/--
Resolved true: Resolved true: on the AIM additive-combinatorics list B. Green answers Katz's
Problem 1.5: a large subset of A is Freiman-isomorphic to a dense subset of Z/pZ (Ruzsa's
lemma), and Szemerédi's theorem with Varnavides averaging gives >>_{k,C} |A|^2 k-term
progressions. The d = 0 pairs counted by the Lean statement cover small sets. Source: AIM
workshop problem list, Additive combinatorics (additivecomb.pdf), Problem 1.5 (N. Katz) and
remark by B. Green, https://aimath.org/WWN/additivecomb/additivecomb.pdf. Moved from
`OpenConjectures/Combinatorics/KatzSmallDoublingProgressions`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.KatzSmallDoublingProgressionsWanted
