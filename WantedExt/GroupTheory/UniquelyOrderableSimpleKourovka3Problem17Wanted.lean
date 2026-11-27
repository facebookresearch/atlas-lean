/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Original formalization by Adam Kiezun, with contributions by Metamate
(consolidation commit `f204b2a6`, PR #9859); ported with attribution.
-/

/-
# Uniquely orderable groups and simplicity (Kourovka Notebook Problem 3.17)

Kourovka Notebook, Archive of Solved Problems, Problem 3.17 (A. I. Kokorin): (a) is a non-abelian
group with a unique linear ordering necessarily simple? (b) Is a non-commutative orderable group
simple if it has no non-trivial normal relatively convex subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Simple
public import MathlibExt.GroupTheory.Orderability

@[expose] public section

namespace MathlibExt.GroupTheory.UniquelyOrderableSimpleKourovka3Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.17 (A. I.
Kokorin). UnsolvedMath record UM-00700171 (`KOU-3.17`), dataset ulamai/UnsolvedMath v1.8.0.

Orders are bi-invariant linear orders (Kokorin's linearly ordered groups; the neutral predicates
`IsBiInvariantOrder`, `IsOrderable`, and `IsRelativelyConvex` from
`MathlibExt.GroupTheory.Orderability` are reused by import). Since the reverse of an order
is an order, a unique linear ordering means unique up to reversal: an order `o` such that every
order is `o` or its reverse (read literally, no non-trivial group qualifies). Non-trivial normal
relatively convex subgroups are those other than `1` and `G`.
-/

open MathlibExt.GroupTheory (IsBiInvariantOrder IsOrderable IsRelativelyConvex)

/-- Kourovka 3.17(a) (A. I. Kokorin): a non-abelian group with a unique linear ordering (a
bi-invariant order `o` such that every bi-invariant order is `o` or its reverse) is simple. -/
def uniquelyOrderableNonabelianSimple : Prop :=
  ∀ (G : Type) [Group G], (∃ a b : G, a * b ≠ b * a) →
    (∃ o : LinearOrder G, IsBiInvariantOrder o ∧ ∀ o' : LinearOrder G, IsBiInvariantOrder o' →
      (∀ a b : G, o'.le a b ↔ o.le a b) ∨ ∀ a b : G, o'.le a b ↔ o.le b a) →
    IsSimpleGroup G

/-- Kourovka 3.17(b) (A. I. Kokorin): a non-commutative orderable group with no normal relatively
convex subgroups other than `1` and itself is simple. -/
def noNormalRelativelyConvexSimple : Prop :=
  ∀ (G : Type) [Group G], (∃ a b : G, a * b ≠ b * a) → IsOrderable G →
    (∀ N : Subgroup G, N.Normal → IsRelativelyConvex N → N = ⊥ ∨ N = ⊤) → IsSimpleGroup G

/--
Resolved false: the Kourovka Archive answers 3.17 "Not always, in both cases", citing Bludov
(Algebra and Logic 13 (1974)): some non-abelian group with a unique linear ordering (up to reversal)
is not simple. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
3.17 (A. I. Kokorin); resolution: V. V. Bludov, Algebra and Logic 13 (1974), 343-360, Kourovka
Archive, Problem 3.17: Not always, in both cases, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted uniquelyOrderableNonabelianSimple_refuted :
    ¬ uniquelyOrderableNonabelianSimple

private example : ProofWanted.Stmt uniquelyOrderableNonabelianSimple_refuted ↔
    ¬ uniquelyOrderableNonabelianSimple :=
  Iff.rfl

/--
Resolved false: the Kourovka Archive answers 3.17 "Not always, in both cases", citing Bludov
(Algebra and Logic 13 (1974)): some non-commutative orderable group without normal relatively convex
subgroups other than `1` and itself is not simple. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 3.17 (A. I. Kokorin); resolution: V. V. Bludov, Algebra and
Logic 13 (1974), 343-360, Kourovka Archive, Problem 3.17: Not always, in both cases,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted noNormalRelativelyConvexSimple_refuted : ¬ noNormalRelativelyConvexSimple

private example : ProofWanted.Stmt noNormalRelativelyConvexSimple_refuted ↔
    ¬ noNormalRelativelyConvexSimple :=
  Iff.rfl

end MathlibExt.GroupTheory.UniquelyOrderableSimpleKourovka3Problem17Wanted
