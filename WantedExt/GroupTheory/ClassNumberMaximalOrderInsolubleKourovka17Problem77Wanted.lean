/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups of maximal order with a given number of conjugacy classes (Kourovka Notebook Problem 17.77)

Kourovka Notebook, Archive of Solved Problems, Problem 17.77 (R. Heffernan, D. MacHale): let `k` be
a positive integer such that there is an insoluble finite group with exactly `k` conjugacy classes.
Is it true that a finite group of maximal order with exactly `k` conjugacy classes is insoluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.ClassNumberMaximalOrderInsolubleKourovka17Problem77Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.77 (R.
Heffernan, D. MacHale). UnsolvedMath record UM-00701379 (`KOU-17.77`), dataset ulamai/UnsolvedMath
v1.8.0.

The number of conjugacy classes is `Nat.card (ConjClasses G)`; a group of maximal order with `k`
classes is one whose order is at least that of every finite group with `k` classes (such groups
exist by Landau's theorem). Insoluble is `¬ Group.IsSolvable`; groups are taken in `Type`.
-/

/-- **Heffernan–MacHale problem on groups of maximal order with a given class number.** The
proposition that for every integer $k \ge 1$ such that some insoluble finite group has exactly $k$
conjugacy classes, every finite group $G$ with exactly $k$ conjugacy classes whose order is at
least the order of every finite group with exactly $k$ conjugacy classes is insoluble. This is
Kourovka Problem 17.77 (R. Heffernan, D. MacHale). -/
def maximalOrderClassNumberInsoluble : Prop :=
  ∀ k : ℕ, 0 < k →
    (∃ (H : Type) (_ : Group H) (_ : Finite H),
      ¬ Group.IsSolvable H ∧ Nat.card (ConjClasses H) = k) →
    ∀ (G : Type) [Group G] [Finite G], Nat.card (ConjClasses G) = k →
      (∀ (H : Type) [Group H] [Finite H], Nat.card (ConjClasses H) = k → Nat.card H ≤ Nat.card G) →
        ¬ Group.IsSolvable G

/-- **A finite group of maximal order with a given class number can be soluble.** There are an
integer $k \ge 1$, an insoluble finite group with exactly $k$ conjugacy classes, and a soluble
finite group $G$ with exactly $k$ conjugacy classes whose order is at least the order of every
finite group with exactly $k$ conjugacy classes. So it is not true that whenever some insoluble
finite group has exactly $k \ge 1$ conjugacy classes, every finite group of maximal order with
exactly $k$ conjugacy classes is insoluble.

Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.77 (R. Heffernan, D. MacHale);
resolution: A. Vera-López and J. Sangroniz, Math. Nachr. 280 (2007), 676-694, Kourovka Archive,
Problem 17.77 (No, it is not; see Table 1 in Vera-López-Sangroniz).
-/
public theorem_wanted maximalOrderClassNumberInsoluble_refuted : ¬ maximalOrderClassNumberInsoluble

end MathlibExt.GroupTheory.ClassNumberMaximalOrderInsolubleKourovka17Problem77Wanted
