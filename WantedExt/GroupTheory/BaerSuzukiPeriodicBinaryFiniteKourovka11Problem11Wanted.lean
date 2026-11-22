/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Baer-Suzuki theorem for periodic and binary finite groups (Kourovka Notebook Problem 11.11)

Kourovka Notebook, Archive of Solved Problems, Problem 11.11 (A. V. Borovik): the Baer-Suzuki
theorem states that if every two conjugates of an element `a` of a finite group `G` generate a
finite `p`-subgroup, then `a` lies in a normal `p`-subgroup. (a) Does such a theorem hold in the
class of periodic groups? The case `p = 2` is of particular interest. (b) Does it hold in the class
of binary finite groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.BaerSuzukiPeriodicBinaryFiniteKourovka11Problem11Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.11 (A. V.
Borovik). UnsolvedMath record UM-00700704 (`KOU-11.11`), dataset ulamai/UnsolvedMath v1.8.0.

Part (a) is formalized for `p = 2`, the case the Archive answers. A normal `p`-subgroup is a normal
subgroup all of whose elements have `p`-power order. Binary finite means that every two elements
generate a finite subgroup; in (b) the finiteness of `⟨x, y⟩` is then automatic, and `p` is any
prime.
-/

/-- Kourovka 11.11(a) (A. V. Borovik), case `p = 2`: in every periodic group, an element `a` any two
of whose conjugates generate a finite `2`-subgroup lies in a normal `2`-subgroup (the Baer-Suzuki
theorem for periodic groups). -/
def baerSuzukiPeriodicTwo : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, IsOfFinOrder g) → ∀ a : G,
    (∀ x y : G, IsConj a x → IsConj a y →
      (Subgroup.closure {x, y} : Set G).Finite ∧ IsPGroup 2 (Subgroup.closure {x, y})) →
    ∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ a ∈ N

/-- Kourovka 11.11(b): in every binary finite group (every two elements generate a finite subgroup),
for every prime `p`, an element `a` any two of whose conjugates generate a `p`-subgroup lies in a
normal `p`-subgroup. -/
def baerSuzukiBinaryFinite : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G], (∀ x y : G, (Subgroup.closure {x, y} : Set G).Finite) →
    ∀ a : G, (∀ x y : G, IsConj a x → IsConj a y → IsPGroup p (Subgroup.closure {x, y})) →
      ∃ N : Subgroup G, N.Normal ∧ IsPGroup p N ∧ a ∈ N

/--
Resolved false: the Kourovka Archive answers 11.11(a) "No, it does not hold for `p = 2`", citing
Mazurov, Olshanskii and Sozutov (2015): some periodic group has an element any two of whose
conjugates generate a finite `2`-subgroup but which lies in no normal `2`-subgroup. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.11 (A. V. Borovik);
resolution: V. D. Mazurov, A. Yu. Olshanskii and A. I. Sozutov, Algebra and Logic 54, no. 2 (2015),
161-166 (a); A. I. Sozutov, Siberian Math. J. 41, no. 3 (2000), 561-562 (b), Kourovka Archive,
Problem 11.11.
-/
public theorem_wanted baerSuzukiPeriodicTwo_refuted : ¬ baerSuzukiPeriodicTwo

/--
Resolved true: the Kourovka Archive answers 11.11(b) Yes (Sozutov, 2000): by the Baer-Suzuki theorem
`⟨a₁, b⟩` is a finite `p`-group for every conjugate `a₁` of `a` and every `p`-element `b`, so by
induction every product `a₁ ⋯ aₙ` of conjugates of `a` is a `p`-element, and the normal closure of
`a` is a normal `p`-subgroup. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 11.11 (A. V. Borovik); resolution: V. D. Mazurov, A. Yu. Olshanskii and A. I.
Sozutov, Algebra and Logic 54, no. 2 (2015), 161-166 (a); A. I. Sozutov, Siberian Math. J. 41, no. 3
(2000), 561-562 (b), Kourovka Archive, Problem 11.11.
-/
public theorem_wanted baerSuzukiBinaryFinite_holds : baerSuzukiBinaryFinite

end MathlibExt.GroupTheory.BaerSuzukiPeriodicBinaryFiniteKourovka11Problem11Wanted
