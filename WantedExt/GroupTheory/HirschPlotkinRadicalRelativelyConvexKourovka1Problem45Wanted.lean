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
# Locally nilpotent radicals of orderable groups (Kourovka Notebook Problem 1.45)

Kourovka Notebook, Archive of Solved Problems, Problem 1.45 (A. I. Kokorin): is the largest locally
nilpotent normal subgroup relatively convex?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.CompletePartialOrder
public import MathlibExt.GroupTheory.Orderability
public import WantedExt.GroupTheory.LocallyNilpotentShared

@[expose] public section

namespace MathlibExt.GroupTheory.HirschPlotkinRadicalRelativelyConvexKourovka1Problem45Wanted

export MathlibExt.GroupTheory
  (IsBiInvariantOrder IsOrderable IsRelativelyConvex)

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.45 (A. I.
Kokorin). UnsolvedMath record UM-00700040 (`KOU-1.45`), dataset ulamai/UnsolvedMath v1.8.0.

"Orderable" is the Kokorin-Kopytov sense of the problem list (fully ordered): `G` admits a linear
order invariant under multiplication on both sides (`IsOrderable`). A subgroup is relatively convex
(Kourovka Archive 1.41) if it is convex for some such order of `G`; for a subgroup, convexity is the
condition `1 ≤ g ≤ h`, `h ∈ H` implies `g ∈ H`. The largest locally nilpotent normal subgroup (the
Hirsch-Plotkin radical) is defined as the join of all locally nilpotent normal subgroups, which is
locally nilpotent by the Hirsch-Plotkin theorem.
-/

open MathlibExt.GroupTheory.LocallyNilpotentShared

/-- Kourovka 1.45 (A. I. Kokorin): the largest locally nilpotent normal subgroup of an orderable
group is relatively convex. -/
def hirschPlotkinRadicalIsRelativelyConvex : Prop :=
  ∀ (G : Type) [Group G], IsOrderable G → IsRelativelyConvex (hirschPlotkinRadical G)

/-- Deprecated alias of `MathlibExt.GroupTheory.LocallyNilpotentShared.IsLocallyNilpotent`, where
the definition moved unchanged. -/
@[deprecated (since := "2026-10-23")]
alias IsLocallyNilpotent := MathlibExt.GroupTheory.LocallyNilpotentShared.IsLocallyNilpotent

/-- Deprecated alias of `MathlibExt.GroupTheory.LocallyNilpotentShared.hirschPlotkinRadical`,
where the definition moved unchanged. -/
@[deprecated (since := "2026-10-23")]
alias hirschPlotkinRadical := MathlibExt.GroupTheory.LocallyNilpotentShared.hirschPlotkinRadical

/--
Resolved false: the Kourovka Archive answers 1.45 "Not always", citing Smirnov (1966): the largest
locally nilpotent normal subgroup of an orderable group need not be relatively convex. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.45 (A. I. Kokorin);
resolution: D. M. Smirnov, Algebra i Logika 5 (1966), no. 6, 41-60 (Russian), Kourovka Archive,
Problem 1.45 (Not always).
-/
public theorem_wanted hirschPlotkinRadicalIsRelativelyConvex_refuted :
    ¬ hirschPlotkinRadicalIsRelativelyConvex

private example : ProofWanted.Stmt hirschPlotkinRadicalIsRelativelyConvex_refuted ↔
    ¬ hirschPlotkinRadicalIsRelativelyConvex :=
  Iff.rfl

end MathlibExt.GroupTheory.HirschPlotkinRadicalRelativelyConvexKourovka1Problem45Wanted
