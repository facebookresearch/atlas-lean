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
# Centres of relatively convex subgroups (Kourovka Notebook Problem 1.42)

Kourovka Notebook, Archive of Solved Problems, Problem 1.42 (A. I. Kokorin): is the centre of a
relatively convex subgroup relatively convex?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Center
public import MathlibExt.GroupTheory.Orderability

@[expose] public section

namespace MathlibExt.GroupTheory.CentreRelativelyConvexKourovka1Problem42Wanted

export MathlibExt.GroupTheory
  (IsBiInvariantOrder IsOrderable IsRelativelyConvex)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.42 (A. I.
Kokorin). UnsolvedMath record UM-00700037 (`KOU-1.42`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). A subgroup is relatively convex
(Kourovka Archive 1.41) if it is convex for some such order of `G`; for a subgroup, convexity is the
condition `1 ≤ g ≤ h`, `h ∈ H` implies `g ∈ H`. The centre of `H` is taken as a subgroup of `G`.
-/

/-- Kourovka 1.42 (A. I. Kokorin): the centre of a relatively convex subgroup `H` of an orderable
group `G` (as a subgroup of `G`) is relatively convex in `G`. -/
def centreOfRelativelyConvexIsRelativelyConvex : Prop :=
  ∀ (G : Type) [Group G] (H : Subgroup G), IsRelativelyConvex H →
    IsRelativelyConvex ((Subgroup.center H).map H.subtype)

/--
Resolved false: the Kourovka Archive answers 1.42 "Not always", citing Kokorin and Kopytov's
monograph: some relatively convex subgroup of an orderable group has a centre that is not relatively
convex. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.42
(A. I. Kokorin); resolution: A. I. Kokorin and V. M. Kopytov, Fully ordered groups, John Wiley, New
York, 1974, Kourovka Archive, Problem 1.42 (Not always).
-/
public theorem_wanted centreOfRelativelyConvexIsRelativelyConvex_refuted :
    ¬ centreOfRelativelyConvexIsRelativelyConvex

private example :
    ProofWanted.Stmt centreOfRelativelyConvexIsRelativelyConvex_refuted ↔
      ¬ centreOfRelativelyConvexIsRelativelyConvex :=
  Iff.rfl

end MathlibExt.GroupTheory.CentreRelativelyConvexKourovka1Problem42Wanted
