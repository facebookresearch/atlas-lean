/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Faithful stable actions of nilpotent groups on abelian groups (Kourovka Notebook Problem 2.59)

Kourovka Notebook, Archive of Solved Problems, Problem 2.59 (B. I. Plotkin): let `Γ` be any
nilpotent group of class `n - 1`. Does `Γ` always admit a faithful representation as a group of
automorphisms of an abelian group with a series of length `n` stable relative to `Γ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentGroupStableSeriesActionKourovka2Problem59Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.59 (B. I.
Plotkin). UnsolvedMath record UM-00700130 (`KOU-2.59`), dataset ulamai/UnsolvedMath v1.8.0.

Class `n - 1` is written as class `c` (`Group.nilpotencyClass Γ = c`) and length `n` as `c + 1`; a
faithful representation by automorphisms of an abelian group `A` is a faithful distributive action
of `Γ` on `A`; the series `0 = A₀ ≤ ⋯ ≤ A_{c+1} = A` of subgroups is stable when `g a - a ∈ A_i` for
`a ∈ A_{i+1}`. The class is exactly `c`, which makes the refutation the stronger statement.
-/

/-- Kourovka 2.59 (B. I. Plotkin): every nilpotent group `Γ` of class `c` acts faithfully by
automorphisms on some abelian group `A` with a series `0 = A₀ ≤ A₁ ≤ ⋯ ≤ A_{c+1} = A` of length
`c + 1` stable relative to `Γ`: `g a - a ∈ A_i` for all `g ∈ Γ` and `a ∈ A_{i+1}`. (The problem's
class `n - 1` and length `n` is written here as class `c` and length `c + 1`.) -/
def nilpotentGroupHasFaithfulStableAction : Prop :=
  ∀ (c : ℕ) (Γ : Type) [Group Γ], Group.IsNilpotent Γ → Group.nilpotencyClass Γ = c →
    ∃ (A : Type) (_ : AddCommGroup A) (_ : DistribMulAction Γ A), FaithfulSMul Γ A ∧
      ∃ S : Fin (c + 2) → AddSubgroup A, S 0 = ⊥ ∧ S (Fin.last (c + 1)) = ⊤ ∧
        (∀ i : Fin (c + 1), S i.castSucc ≤ S i.succ) ∧
        ∀ (i : Fin (c + 1)) (g : Γ) (a : A), a ∈ S i.succ → g • a - a ∈ S i.castSucc

/--
Resolved false: the Kourovka Archive answers 2.59 "Not always", citing Rips (1972): some nilpotent
group of class `n - 1` admits no faithful representation by automorphisms of an abelian group
stabilizing a series of length `n`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 2.59 (B. I. Plotkin); resolution: E. Rips, Israel J. Math. 12 (1972),
342-346, Kourovka Archive, Problem 2.59: Not always (Rips), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted nilpotentGroupHasFaithfulStableAction_refuted :
    ¬ nilpotentGroupHasFaithfulStableAction

end MathlibExt.GroupTheory.NilpotentGroupStableSeriesActionKourovka2Problem59Wanted
