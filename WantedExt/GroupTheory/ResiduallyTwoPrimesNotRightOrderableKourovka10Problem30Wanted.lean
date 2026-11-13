/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-right-orderable groups residually `p` for two primes (Kourovka Notebook Problem 10.30)

Kourovka Notebook, Archive of Solved Problems, Problem 10.30 (N. Ya. Medvedev): does there exist a
non-right-orderable group which is residually a finite `p`-group for a finite set of primes `p`
containing at least two different primes?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.30 (N. Ya.
Medvedev). UnsolvedMath record UM-00700645 (`KOU-10.30`), dataset ulamai/UnsolvedMath v1.8.0.

A group that is residually a finite `p`-group for every prime of a finite set with two distinct
primes `p ≠ q` is residually `p` and residually `q`, so the statement uses two distinct primes; such
a group is torsion-free, so there is no trivial witness. Right-orderable means that some linear
order is invariant under right multiplication.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsResiduallyFiniteP)

/-- **Right-orderable groups.** A group $G$ is right-orderable when it admits a linear order $\le$
that is invariant under right multiplication: $a \le b$ implies $ac \le bc$ for all
$a, b, c \in G$. -/
def IsRightOrderable (G : Type*) [Group G] : Prop :=
  ∃ _ : LinearOrder G, ∀ a b c : G, a ≤ b → a * c ≤ b * c

/-- **Medvedev's question on right-orderability (Kourovka 10.30).** The statement that there exist
a group $G$ and distinct primes $p$ and $q$ such that $G$ is residually a finite $p$-group and
residually a finite $q$-group, but $G$ is not right-orderable. -/
def residuallyTwoPrimesNotRightOrderable : Prop :=
  ∃ (G : Type) (_ : Group G) (p q : ℕ), p.Prime ∧ q.Prime ∧ p ≠ q ∧
    IsResiduallyFiniteP p G ∧ IsResiduallyFiniteP q G ∧ ¬ IsRightOrderable G

/--
**A non-right-orderable group that is residually $p$ for two primes (Linnell).** There exist a
group $G$ and distinct primes $p$ and $q$ such that $G$ is residually a finite $p$-group and
residually a finite $q$-group but is not right-orderable.

By Rhemtulla, a group that is residually a finite $p$-group for infinitely many primes $p$ is
orderable.

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 10.30 (N. Ya. Medvedev); resolution: P. A. Linnell, J.
Algebra 248 (2002), 605-607, Kourovka Archive, Problem 10.30 ("Yes, there does").
-/
public theorem_wanted residuallyTwoPrimesNotRightOrderable_holds :
    residuallyTwoPrimesNotRightOrderable

end MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted
