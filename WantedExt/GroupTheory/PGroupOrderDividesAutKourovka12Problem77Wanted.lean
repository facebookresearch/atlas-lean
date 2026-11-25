/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Orders of `p`-groups and of their automorphism groups (Kourovka Notebook Problem 12.77)

Kourovka Notebook, Archive of Solved Problems, Problem 12.77 (well-known problem; A. I. Starostin):
does the order (if it is greater than `p²`) of a finite non-cyclic `p`-group divide the order of its
automorphism group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupOrderDividesAutKourovka12Problem77Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.77
(well-known problem; A. I. Starostin). UnsolvedMath record UM-00700895 (`KOU-12.77`), dataset
ulamai/UnsolvedMath v1.8.0.

`Aut(P)` is `MulAut P`. The target is stated for some prime `p` (the strongest true form,
existential when refuted, as in WantedExt/Sources/UnsolvedMath.md), so its refutation asserts a
counterexample for every prime: stronger than the source's negative answer, which needs one prime,
and what González-Sánchez and Jaikin-Zapirain prove (a family for each prime `p`).
-/

/-- **Divisibility conjecture for orders of automorphism groups of $p$-groups (Kourovka 12.77).**
The statement that there is a prime $p$ such that for every finite non-cyclic $p$-group $P$ of
order greater than $p^2$, the order of $P$ divides the order of its automorphism group
$\mathrm{Aut}(P)$.

The source asks this for every prime $p$; stating it for some prime makes its refutation assert a
counterexample for every prime. -/
def pGroupOrderDividesAutOrder : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∀ (P : Type) [Group P] [Finite P], IsPGroup p P → ¬ IsCyclic P →
    p ^ 2 < Nat.card P → Nat.card P ∣ Nat.card (MulAut P)

/--
**Orders of $p$-groups need not divide orders of their automorphism groups.** For every prime $p$
there is a finite non-cyclic $p$-group $P$ of order greater than $p^2$ whose order does not divide
the order of its automorphism group $\mathrm{Aut}(P)$.

González-Sánchez and Jaikin-Zapirain construct, for each prime $p$, finite $p$-groups $G_i$ with
$|\mathrm{Aut}(G_i)| / |G_i| \to 0$; they are non-abelian, hence non-cyclic of order greater than
$p^2$, and eventually $|\mathrm{Aut}(G_i)| < |G_i|$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 12.77 (well-known problem; A. I. Starostin); resolution: J. González-Sánchez and
A. Jaikin-Zapirain, Finite p-groups with small automorphism group, Forum Math. Sigma 3 (2015), Paper
No. e7, main theorem (abstract): for each prime p, finite p-groups G_i with |Aut(G_i)|/|G_i| → 0;
Kourovka Archive, Problem 12.77.
-/
public theorem_wanted pGroupOrderDividesAutOrder_refuted : ¬ pGroupOrderDividesAutOrder

end MathlibExt.GroupTheory.PGroupOrderDividesAutKourovka12Problem77Wanted
