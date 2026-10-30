/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite `2`-groups with metacyclic `2`-generator subgroups (Kourovka Notebook Problem 15.33)

Kourovka Notebook, Archive of Solved Problems, Problem 15.33 (Ya. G. Berkovich): suppose that all
`2`-generator subgroups of a finite `2`-group `G` are metacyclic. Is the derived length of `G`
bounded? (For `p ≠ 2` this is true, see Suzuki's book.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.TwoGeneratorMetacyclicDerivedLengthKourovka15Problem33Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.33 (Ya. G.
Berkovich). UnsolvedMath record UM-00701121 (`KOU-15.33`), dataset ulamai/UnsolvedMath v1.8.0.

Metacyclic means a cyclic normal subgroup with cyclic quotient. "Bounded" is replaced by the bound
`2` of the resolution, `G'' = 1`, i.e. `derivedSeries G 2 = ⊥`. The `2`-generator subgroups are the
subgroups `⟨x, y⟩` for arbitrary `x, y` (cyclic ones included).
-/

/-- `G` is metacyclic: it has a cyclic normal subgroup with cyclic quotient. -/
def IsMetacyclic (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, ∃ _ : N.Normal, IsCyclic N ∧ IsCyclic (G ⧸ N)

/-- Kourovka 15.33 (Ya. G. Berkovich), with the bound `2` of its resolution: every finite `2`-group
all of whose `2`-generator subgroups are metacyclic has derived length at most `2`. -/
def twoGeneratorMetacyclicMetabelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G →
    (∀ x y : G, IsMetacyclic (Subgroup.closure ({x, y} : Set G))) → derivedSeries G 2 = ⊥

/--
Resolved true: the Kourovka Archive answers 15.33 "Yes, it is at most 2" (Crestani and Menegazzo): a
finite `2`-group all of whose `2`-generator subgroups are metacyclic is metabelian. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.33 (Ya. G. Berkovich);
resolution: E. Crestani and F. Menegazzo, J. Group Theory 15 (2012), no. 3, 359-383, Kourovka
Archive, Problem 15.33 (answer: Yes, it is at most 2).
-/
public theorem_wanted twoGeneratorMetacyclicMetabelian_holds : twoGeneratorMetacyclicMetabelian

end MathlibExt.GroupTheory.TwoGeneratorMetacyclicDerivedLengthKourovka15Problem33Wanted
