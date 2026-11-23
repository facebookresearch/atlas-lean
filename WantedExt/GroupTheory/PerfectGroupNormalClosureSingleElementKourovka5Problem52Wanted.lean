/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated perfect groups of weight one (Kourovka Notebook Problem 5.52)

Kourovka Notebook, Problem 5.52 (J. Wiegold), marked solved in the 21st issue: it is not hard to
show that a finite perfect group is the normal closure of a single element; is the same true for
infinite finitely generated groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.IsPerfect

@[expose] public section

namespace MathlibExt.GroupTheory.PerfectGroupNormalClosureSingleElementKourovka5Problem52Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 5.52 (J. Wiegold). UnsolvedMath record
UM-00700333 (`KOU-5.52`), dataset ulamai/UnsolvedMath v1.8.0.

Perfect is Mathlib's `Group.IsPerfect` (`[G, G] = G`). The target is the claim for infinite finitely
generated perfect groups. The problem is in the main list of the 21st issue, marked solved by a 2025
preprint accepted by the editors.
-/

/-- Kourovka 5.52 (J. Wiegold): every infinite finitely generated perfect group (`[G, G] = G`,
Mathlib's `Group.IsPerfect`) is the normal closure of a single element. -/
def finitelyGeneratedPerfectNormallyMonogenic : Prop :=
  ∀ (G : Type) [Group G] [Group.FG G] [Infinite G] [Group.IsPerfect G],
    ∃ g : G, Subgroup.normalClosure {g} = ⊤

/--
Resolved false: Chen and Lodha (arXiv:2510.26073, abstract) prove that a free product of non-trivial
left-orderable groups is not the normal closure of a single element, so a free product of finitely
generated perfect left-orderable groups is an infinite finitely generated perfect group of weight
greater than one; the Kourovka Notebook (21st issue) marks 5.52 solved. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 5.52 (J. Wiegold); resolution: L. Chen and Y. Lodha, The Wiegold
problem and free products of left-orderable groups, preprint, 2025, arXiv:2510.26073, abstract: any
free product of non-trivial left-orderable groups has normal rank greater than one, which solves the
Wiegold problem by taking free products of finitely generated perfect left-orderable groups; the
Kourovka Notebook (21st issue) marks 5.52 solved: there exist finitely presented perfect groups that
are not normal closures of a single element, https://arxiv.org/abs/2510.26073.
-/
public theorem_wanted finitelyGeneratedPerfectNormallyMonogenic_refuted :
    ¬ finitelyGeneratedPerfectNormallyMonogenic

end MathlibExt.GroupTheory.PerfectGroupNormalClosureSingleElementKourovka5Problem52Wanted
