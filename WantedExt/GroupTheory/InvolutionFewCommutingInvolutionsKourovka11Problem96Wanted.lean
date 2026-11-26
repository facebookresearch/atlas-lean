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
public import MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96

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

/-- **Strunkov's finiteness question for simple groups (Kourovka 11.96(a)).** This is the statement
that for every natural number $n$ there is a bound $N$ such that every finite simple group $G$
containing an involution $t$ that commutes with at most $n$ involutions of $G$ (counting $t$
itself) has order at most $N$. Bounding the order expresses "only finitely many such groups up to
isomorphism". -/
def finitelyManySimpleFewCommutingInvolutions : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ t : G, orderOf t = 2 ∧ (commutingInvolutions t).encard ≤ n) → Nat.card G ≤ N

/--
**Finitely many finite simple groups with an involution commuting with few involutions.** For
every natural number $n$ there is a bound $N$ such that every finite simple group $G$ containing
an involution $t$ that commutes with at most $n$ involutions of $G$ (counting $t$ itself) has
order at most $N$.

This answers Kourovka Problem 11.96(a) in the affirmative; the Kourovka Notebook (21st issue)
marks it solved, "Yes", modulo the classification of finite simple groups.

Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 11.96 (S. P. Strunkov); resolution: S. V. Skresanov, J.
Group Theory 27, no. 6 (2024), 1197-1202, the Kourovka Notebook (21st issue) marks 11.96 solved: (a)
yes (mod CFSG), and a locally finite group with such an involution is finite of `n`-bounded order;
(b) no, `PSL_2(ℝ)` is an infinite simple group with an involution and no Klein four-subgroup,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted finitelyManySimpleFewCommutingInvolutions_holds :
    finitelyManySimpleFewCommutingInvolutions

end MathlibExt.GroupTheory.InvolutionFewCommutingInvolutionsKourovka11Problem96Wanted
