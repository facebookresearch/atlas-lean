/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial-size list of discrepancy colorings
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.PolysizeColoringListWanted

/-! Source record `AIM-COMBINATORICS-0047__20000922`. -/

open scoped BigOperators

/-- Discrepancy of the real matrix `A` restricted to the column set `S`,
minimized over all `±1` signings (encoded by `Bool`): the least `r` such
that some signing has every weighted restricted row sum at most `r` in
absolute value. -/
noncomputable def discrepancyOn {n m : ℕ} (A : Fin n → Fin m → ℝ)
    (S : Finset (Fin m)) : ℝ :=
  sInf ((fun ε : Fin m → Bool =>
    ⨆ i : Fin n, |∑ j ∈ S, A i j * (if ε j then (1 : ℝ) else -1)|) ''
    Set.univ)

/-- Hereditary discrepancy `h` of the real matrix `A`: the maximum of
`discrepancyOn` over all column subsets `S`. -/
noncomputable def hereditaryDisc {n m : ℕ} (A : Fin n → Fin m → ℝ) : ℝ :=
  ⨆ S : Finset (Fin m), discrepancyOn A S

/-- Polynomial-size coloring lists with hereditary-discrepancy bound
(AIM-COMBINATORICS-0047__20000922; AIM Hereditary discrepancy,
item 1.85): there are uniform constants `C` and `k` such that every real
matrix `A` has a list of at most `m ^ k` signings, one of which achieves
weighted discrepancy at most `C * h` on every column subset `S`, where
`h` is the hereditary discrepancy of `A`. -/
def conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ A : Fin n → Fin m → ℝ,
      ∃ L : Finset (Fin m → ℝ),
        (L.card : ℝ) ≤ (m : ℝ) ^ k ∧
        (∀ ε ∈ L, ∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ S : Finset (Fin m),
          ∃ ε ∈ L, ∀ i, |∑ j ∈ S, A i j * ε j| ≤
            C * hereditaryDisc A

/--
Resolved false: Resolved false by the source's own note: the AIM list (Hereditary discrepancy
and factorization norms, Problem 1.85) records a negative answer via sqrt(n) disjoint rows of
size sqrt(n): hereditary discrepancy is 1, yet for fixed C and polynomial list size some column
subset has discrepancy above C under every listed colouring. Source: AIM Problem Lists,
Hereditary discrepancy and factorization norms, Problem 1.85 (Polysize list of colorings),
https://aimpl.org/hereddiscrep/1/. Moved from
`OpenConjectures/Combinatorics/PolysizeColoringList`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.PolysizeColoringListWanted
