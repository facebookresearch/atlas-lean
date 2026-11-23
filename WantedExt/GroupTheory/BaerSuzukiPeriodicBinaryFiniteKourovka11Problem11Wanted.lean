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

/-- **Baer–Suzuki property for periodic groups at the prime 2.** The proposition that for every
group $G$ in which every element has finite order and every element $a \in G$ such that any two
conjugates of $a$ generate a finite $2$-subgroup, there is a normal $2$-subgroup of $G$ containing
$a$. Here a $2$-subgroup is a subgroup in which every element has order a power of $2$.

This is the case $p = 2$ of Kourovka Problem 11.11(a) (A. V. Borovik). -/
def baerSuzukiPeriodicTwo : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, IsOfFinOrder g) → ∀ a : G,
    (∀ x y : G, IsConj a x → IsConj a y →
      (Subgroup.closure {x, y} : Set G).Finite ∧ IsPGroup 2 (Subgroup.closure {x, y})) →
    ∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ a ∈ N

/-- **Baer–Suzuki property for binary finite groups.** The proposition that for every prime $p$,
every group $G$ in which any two elements generate a finite subgroup, and every element $a \in G$
such that any two conjugates of $a$ generate a $p$-subgroup, there is a normal $p$-subgroup of $G$
containing $a$. Here a $p$-subgroup is a subgroup in which every element has order a power of $p$.

This is the statement asked about in Kourovka Problem 11.11(b) (A. V. Borovik). -/
def baerSuzukiBinaryFinite : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G], (∀ x y : G, (Subgroup.closure {x, y} : Set G).Finite) →
    ∀ a : G, (∀ x y : G, IsConj a x → IsConj a y → IsPGroup p (Subgroup.closure {x, y})) →
      ∃ N : Subgroup G, N.Normal ∧ IsPGroup p N ∧ a ∈ N

/-- **Failure of the Baer–Suzuki theorem for periodic groups at the prime 2.** There is a group $G$
in which every element has finite order, together with an element $a \in G$ such that any two
conjugates of $a$ generate a finite $2$-subgroup, but no normal $2$-subgroup of $G$ contains $a$.
Here a $2$-subgroup is a subgroup in which every element has order a power of $2$.

This answers Kourovka Problem 11.11(a) negatively for $p = 2$ (Mazurov, Olshanskii and
Sozutov, 2015).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.11 (A. V.
Borovik); resolution: V. D. Mazurov, A. Yu. Olshanskii and A. I. Sozutov, Algebra and Logic 54, no.
2 (2015), 161-166 (a); A. I. Sozutov, Siberian Math. J. 41, no. 3 (2000), 561-562 (b), Kourovka
Archive, Problem 11.11.
-/
public theorem_wanted baerSuzukiPeriodicTwo_refuted : ¬ baerSuzukiPeriodicTwo

/-- **Baer–Suzuki theorem for binary finite groups.** For every prime $p$, every group $G$ in
which any two elements generate a finite subgroup, and every element $a \in G$ such that any two
conjugates of $a$ generate a $p$-subgroup, there is a normal $p$-subgroup of $G$ containing $a$.
Here a $p$-subgroup is a subgroup in which every element has order a power of $p$.

This answers Kourovka Problem 11.11(b) affirmatively (Sozutov, 2000): by the Baer–Suzuki theorem
for finite groups, $\langle a_1, b \rangle$ is a finite $p$-group for every conjugate $a_1$ of $a$
and every element $b$ of $p$-power order, so by induction every product $a_1 \cdots a_n$ of
conjugates of $a$ has $p$-power order, and the normal closure of $a$ is a normal $p$-subgroup.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.11 (A. V.
Borovik); resolution: V. D. Mazurov, A. Yu. Olshanskii and A. I. Sozutov, Algebra and Logic 54, no.
2 (2015), 161-166 (a); A. I. Sozutov, Siberian Math. J. 41, no. 3 (2000), 561-562 (b), Kourovka
Archive, Problem 11.11.
-/
public theorem_wanted baerSuzukiBinaryFinite_holds : baerSuzukiBinaryFinite

end MathlibExt.GroupTheory.BaerSuzukiPeriodicBinaryFiniteKourovka11Problem11Wanted
