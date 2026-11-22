/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kourovka Notebook 21, Problem 38

KOU-21.38: does there exist a group with spread exactly 1?

The spread of `G` is the greatest `k` such that any `k` nontrivial elements
simultaneously generate `G` with a suitable common partner `y`; spread
exactly 1 means this holds for single elements but fails for pairs (hence
for every `m > 1`, since a failing pair extends to an `m`-tuple).
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

universe u

namespace MathlibExt.GroupTheory.Kourovka21Problem38Wanted

/-! Source record `UM-00002547-Q001` (KOU-21.38). -/

/-- `G` has spread at least `k`: any `k` nontrivial elements share a common
partner generating `G` with each of them. -/
def HasSpreadAtLeast (G : Type u) [Group G] (k : ℕ) : Prop :=
  ∀ x : Fin k → G, (∀ i, x i ≠ 1) →
    ∃ y : G, ∀ i, Subgroup.closure {x i, y} = ⊤

/-- `G` has spread exactly `k`: spread at least `k`, failing above `k`. -/
def HasSpreadExactly (G : Type u) [Group G] (k : ℕ) : Prop :=
  HasSpreadAtLeast G k ∧ ∀ m : ℕ, m > k → ¬ HasSpreadAtLeast G m

/-- [KOU-21.38] There exists a group of spread exactly 1 (in any universe). -/
def conjecture : Prop :=
  ∃ (G : Type u) (_ : Group G), HasSpreadExactly G 1

-- Carried source audit `UM-00002547-Q001` (see the Moved/ record).

/--
Resolved true: Answered affirmatively: the Nilradical note A group of spread one (17 September
2026, Kourovka Notebook site), Theorem 1, shows that the subgroup {f ∈ F : f′(0+) = f′(1−)} of
Thompson's group F is infinite and has spread exactly one. The note is not refereed; the
Kourovka Notebook (arXiv:1401.0300v49) marks Problem 21.38 solved (AI solution confirmed by S.
Corson). Source: Nilradical, A group of spread one (note of 17 September 2026, Kourovka Notebook
site),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-21-38.pdf;
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (20 October 2026), Problem 21.38,
https://arxiv.org/abs/1401.0300v49. Moved from
`OpenConjectures/GroupTheory/Kourovka21Problem38`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GroupTheory.Kourovka21Problem38Wanted
