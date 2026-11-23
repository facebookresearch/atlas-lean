/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A finitely generated perfect right-orderable group (Kourovka Notebook Problem 2.71)

Kourovka Notebook, Archive of Solved Problems, Problem 2.71 (D. M. Smirnov): does there exist a
finitely generated right-orderable group which coincides with its derived subgroup and, therefore,
does not have the property RN?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

namespace MathlibExt.GroupTheory.PerfectRightOrderableGroupKourovka2Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.71 (D. M.
Smirnov). UnsolvedMath record UM-00700141 (`KOU-2.71`), dataset ulamai/UnsolvedMath v1.8.0.

The group must be nontrivial (the trivial group is perfect and orderable). Right-orderable means
some linear order satisfies `a ≤ b → a c ≤ b c`, Bergman's definition; coinciding with the derived
subgroup is `commutator G = ⊤`.
-/

/-- Kourovka 2.71 (D. M. Smirnov): there is a nontrivial finitely generated right-orderable group
that coincides with its derived subgroup; right-orderable means some linear order `≤` on `G`
satisfies `a ≤ b → a c ≤ b c`. -/
def perfectRightOrderableGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G), Nontrivial G ∧ Group.FG G ∧
    (∃ o : LinearOrder G, ∀ a b c : G, o.le a b → o.le (a * c) (b * c)) ∧ commutator G = ⊤

/--
Resolved true: Bergman (1991) shows that the universal covering group of `SL(2, ℝ)` is right
orderable and contains nontrivial finitely generated perfect subgroups, which are right orderable as
subgroups; the Kourovka Archive answers 2.71 "Yes, there does". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.71 (D. M. Smirnov); resolution: G.
M. Bergman, Right orderable groups that are not locally indicable, Pacific J. Math. 147 (1991), no.
2, 243-248, Abstract and Sections 5-6: the universal covering group of SL(2, R) is right orderable
and contains nontrivial finitely generated perfect subgroups; Kourovka Archive, Problem 2.71: Yes,
there does (Bergman), https://msp.org/pjm/1991/147-2/pjm-v147-n2-p04-p.pdf.
-/
public theorem_wanted perfectRightOrderableGroupExists_holds : perfectRightOrderableGroupExists

end MathlibExt.GroupTheory.PerfectRightOrderableGroupKourovka2Problem71Wanted
