/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derived length of finite Alperin groups (Kourovka Notebook Problem 18.33)

Kourovka Notebook, Archive of Solved Problems, Problem 18.33 (B. M. Veretennikov): a group in which
the derived subgroup of every 2-generated subgroup is cyclic is an Alperin group. Is there a bound
for the derived length of finite Alperin groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.AlperinGroupDerivedLengthKourovka18Problem33Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.33 (B. M.
Veretennikov). UnsolvedMath record UM-00701462 (`KOU-18.33`), dataset ulamai/UnsolvedMath v1.8.0.

The target states the bound given in the Archive answer, derived length at most `6`, that is `G⁽⁶⁾ =
1`; it implies the existence of a bound asked for.
-/

/-- `G` is an Alperin group: the derived subgroup of every 2-generated subgroup `⟨x, y⟩` is
cyclic. -/
def IsAlperinGroup (G : Type) [Group G] : Prop :=
  ∀ x y : G, IsCyclic (⁅Subgroup.closure {x, y}, Subgroup.closure {x, y}⁆ : Subgroup G)

/-- Kourovka 18.33 (B. M. Veretennikov), with the bound given in the answer: every finite Alperin
group has derived length at most `6`. -/
def alperinGroupDerivedLengthAtMostSix : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsAlperinGroup G → derivedSeries G 6 = ⊥

/--
Resolved true: the Kourovka Archive answers 18.33 "Yes, there is: it is at most 6": finite Alperin
groups are supersoluble and those of odd order are metabelian (Longobardi-Maj-Smith, 2006), so the
elements of odd order form a metabelian normal subgroup, and finite Alperin 2-groups have derived
length at most `4` (Wilkens, 2014). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 18.33 (B. M. Veretennikov); resolution: P. Longobardi, M. Maj and H. Smith,
Rend. Sem. Mat. Univ. Padova 115 (2006), 29-40; B. Wilkens, J. Group Theory 17 (2014), no. 1,
151-174, Kourovka Archive, Problem 18.33: Yes, it is at most 6: finite Alperin groups of odd order
are metabelian and finite Alperin groups are supersoluble (Longobardi-Maj-Smith), so the elements of
odd order form a metabelian normal subgroup, and finite Alperin 2-groups have derived length at most
4 (Wilkens), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted alperinGroupDerivedLengthAtMostSix_holds : alperinGroupDerivedLengthAtMostSix

end MathlibExt.GroupTheory.AlperinGroupDerivedLengthKourovka18Problem33Wanted
