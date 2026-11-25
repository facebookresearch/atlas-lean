/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Torsion-free three-class groups with an index-2 subgroup (Kourovka Notebook Problem 11.42)

Kourovka Notebook, Archive of Solved Problems, Problem 11.42 (A. V. Izosov): does there exist a
torsion-free group having exactly three conjugacy classes and containing a subgroup of index 2?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeThreeClassesIndexTwoKourovka11Problem42Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.42 (A. V.
Izosov). UnsolvedMath record UM-00700734 (`KOU-11.42`), dataset ulamai/UnsolvedMath v1.8.0.

Torsion-free is "no nontrivial element has finite order". "Exactly three conjugacy classes" is
`Nat.card (ConjClasses G) = 3` (which forces finitely many classes, since `Nat.card` of an infinite
type is `0`).
-/

/-- **Kourovka Problem 11.42 (statement).** The statement that there is a torsion-free group $G$ (no
element of $G$ other than the identity has finite order) that has exactly three conjugacy classes
and has a subgroup of index $2$.

The problem was posed by A. V. Izosov. -/
def torsionFreeThreeClassesIndexTwo : Prop :=
  ∃ (G : Type) (_ : Group G), (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    Nat.card (ConjClasses G) = 3 ∧ ∃ H : Subgroup G, H.index = 2

/--
**Minasyan's theorem (Kourovka Problem 11.42).** There is a torsion-free group $G$ (no element of
$G$ other than the identity has finite order) that has exactly three conjugacy classes and has a
subgroup of index $2$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.42 (A. V.
Izosov); resolution: A. Minasyan, Comment. Math. Helv. 84 (2009), 259-296, Kourovka Archive,
Problem 11.42: "Yes, there does", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted torsionFreeThreeClassesIndexTwo_holds : torsionFreeThreeClassesIndexTwo

end MathlibExt.GroupTheory.TorsionFreeThreeClassesIndexTwoKourovka11Problem42Wanted
