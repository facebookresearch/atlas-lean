/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Perfectness of the intersection of the derived series (Kourovka Notebook Problem 17.82)

Kourovka Notebook, Archive of Solved Problems, Problem 17.82 (R. Mikhailov): is it true that in
every finitely presented group the intersection of the derived series has trivial abelianization?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.DerivedSeriesIntersectionPerfectKourovka17Problem82Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.82 (R.
Mikhailov). UnsolvedMath record UM-00701384 (`KOU-17.82`), dataset ulamai/UnsolvedMath v1.8.0.

The intersection is `D = ⨅ n, derivedSeries G n` (the `ω`-th term), trivial abelianization is `[D,
D] = D`, and finitely presented is Mathlib's `Group.IsFinitelyPresented`; groups are taken in
`Type`.
-/

/-- **Perfectness of the intersection of the derived series (Kourovka 17.82).** The conjecture of
R. Mikhailov that for every finitely presented group $G$, the intersection
$D = \bigcap_{n} G^{(n)}$ of the terms $G^{(n)}$ of the derived series of $G$ satisfies
$[D, D] = D$, that is, $D$ has trivial abelianization. -/
def derivedSeriesIntersectionPerfect : Prop :=
  ∀ (G : Type) [Group G], Group.IsFinitelyPresented G →
    ⁅⨅ n, derivedSeries G n, ⨅ n, derivedSeries G n⁆ = ⨅ n, derivedSeries G n

/--
**The intersection of the derived series need not be perfect.** There exists a finitely presented
group $G$ such that the intersection $D = \bigcap_{n} G^{(n)}$ of the terms $G^{(n)}$ of the
derived series of $G$ satisfies $[D, D] \ne D$. That is, the conjecture of Kourovka Problem 17.82
is false; the Kourovka Archive credits this answer to V. A. Roman'kov (2011).

Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.82 (R. Mikhailov);
resolution: V. A. Roman'kov, Siberian Math. J. 52 (2011), 348-351, Kourovka Archive, Problem 17.82
(No, not always).
-/
public theorem_wanted derivedSeriesIntersectionPerfect_refuted : ¬ derivedSeriesIntersectionPerfect

end MathlibExt.GroupTheory.DerivedSeriesIntersectionPerfectKourovka17Problem82Wanted
