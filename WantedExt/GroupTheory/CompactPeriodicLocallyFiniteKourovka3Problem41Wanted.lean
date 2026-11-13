/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Compact periodic groups are locally finite (Kourovka Notebook Problem 3.41)

Kourovka Notebook, Archive of Solved Problems, Problem 3.41 (V. P. Platonov): is every compact
periodic group locally finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace MathlibExt.GroupTheory.CompactPeriodicLocallyFiniteKourovka3Problem41Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.41 (V. P.
Platonov). UnsolvedMath record UM-00700190 (`KOU-3.41`), dataset ulamai/UnsolvedMath v1.8.0.

Compact groups are Hausdorff compact topological groups (without Hausdorff, any periodic group with
the indiscrete topology would be compact); locally finite: finitely generated subgroups are finite.
-/

/-- Kourovka 3.41 (V. P. Platonov): every compact (Hausdorff) periodic group is locally finite:
each finitely generated subgroup is finite. -/
def compactPeriodicLocallyFinite : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G],
    (∀ g : G, IsOfFinOrder g) → ∀ H : Subgroup G, H.FG → Finite H

/--
Resolved true: the Kourovka Archive answers 3.41 "Yes, it is", citing Zel'manov (Israel J. Math. 77
(1992)): every compact Hausdorff periodic group is locally finite. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.41 (V. P. Platonov); resolution: E.
I. Zel'manov, Israel J. Math. 77 (1992), 83-95, Kourovka Archive, Problem 3.41: Yes, it is,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted compactPeriodicLocallyFinite_holds : compactPeriodicLocallyFinite

end MathlibExt.GroupTheory.CompactPeriodicLocallyFiniteKourovka3Problem41Wanted
