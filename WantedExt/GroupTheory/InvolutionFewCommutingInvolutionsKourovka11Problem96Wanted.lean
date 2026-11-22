/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple groups with an involution commuting with few involutions (Kourovka Notebook Problem 11.96)

Kourovka Notebook, Problem 11.96 (S. P. Strunkov): (a) for a given `n`, are there only finitely many
finite simple groups each containing an involution that commutes with at most `n` involutions? (b)
Are there no infinite simple groups satisfying this condition?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.96 (S. P. Strunkov). UnsolvedMath record
UM-00700788 (`KOU-11.96`), dataset ulamai/UnsolvedMath v1.8.0.

An involution is an element of order 2; the involutions commuting with `t` include `t`, and their
number is counted with `Set.encard`, so an infinite set never satisfies the bound. "Finitely many"
up to isomorphism in (a) is a bound on the order. In (b) "this condition" is the condition of (a)
for some `n`.
-/

/-- The involutions of `G` that commute with `t`. -/
def commutingInvolutions {G : Type*} [Group G] (t : G) : Set G :=
  {s | orderOf s = 2 ∧ s * t = t * s}

/-- Kourovka 11.96(a) (S. P. Strunkov): for each `n` there are only finitely many finite simple
groups containing an involution that commutes with at most `n` involutions. "Finitely many" up to
isomorphism is stated as a bound on the order. -/
def finitelyManySimpleFewCommutingInvolutions : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ t : G, orderOf t = 2 ∧ (commutingInvolutions t).encard ≤ n) → Nat.card G ≤ N

/-- Kourovka 11.96(b) (S. P. Strunkov): no infinite simple group contains an involution that
commutes with at most `n` involutions (for any `n`). -/
def noInfiniteSimpleFewCommutingInvolutions : Prop :=
  ∀ n : ℕ, ∀ (G : Type) [Group G], Infinite G → IsSimpleGroup G →
    ¬ ∃ t : G, orderOf t = 2 ∧ (commutingInvolutions t).encard ≤ n

/--
Resolved true (modulo the classification of finite simple groups, as accepted by the Kourovka
Notebook): Skresanov proves that a locally finite group with an involution commuting with at most
`n` involutions is finite of `n`-bounded order, so in particular there are only finitely many such
finite simple groups; the Kourovka Notebook (21st issue) marks 11.96(a) solved, "Yes". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 11.96 (S. P. Strunkov); resolution: S. V. Skresanov, J.
Group Theory 27, no. 6 (2024), 1197-1202, the Kourovka Notebook (21st issue) marks 11.96 solved: (a)
yes (mod CFSG), and a locally finite group with such an involution is finite of `n`-bounded order;
(b) no, `PSL_2(ℝ)` is an infinite simple group with an involution and no Klein four-subgroup,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted finitelyManySimpleFewCommutingInvolutions_holds :
    finitelyManySimpleFewCommutingInvolutions

/--
Resolved false: `PSL_2(ℝ)` is an infinite simple group that contains an involution but no Klein
four-subgroup, so each of its involutions commutes with no involution but itself (`n = 1`); the
Kourovka Notebook (21st issue) marks 11.96(b) solved, "No", citing Skresanov. Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 11.96 (S. P. Strunkov); resolution: S. V. Skresanov, J. Group
Theory 27, no. 6 (2024), 1197-1202, the Kourovka Notebook (21st issue) marks 11.96 solved: (a) yes
(mod CFSG), and a locally finite group with such an involution is finite of `n`-bounded order; (b)
no, `PSL_2(ℝ)` is an infinite simple group with an involution and no Klein four-subgroup,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted noInfiniteSimpleFewCommutingInvolutions_refuted :
    ¬ noInfiniteSimpleFewCommutingInvolutions

end MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96Wanted
