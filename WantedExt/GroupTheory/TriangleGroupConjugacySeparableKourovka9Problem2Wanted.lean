/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjugacy separability of triangle groups (Kourovka Notebook Problem 9.2)

Kourovka Notebook, Archive of Solved Problems, Problem 9.2 (R. B. J. T. Allenby): is `G = ⟨a, b |
a^l = b^m = (ab)^n = 1⟩` conjugacy separable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PresentedGroup
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.TriangleGroupConjugacySeparableKourovka9Problem2Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.2 (R. B. J.
T. Allenby). UnsolvedMath record UM-00700537 (`KOU-9.2`), dataset ulamai/UnsolvedMath v1.8.0.

`l, m, n` range over the positive integers, since the Archive's answer is unqualified, and the group
is the presented group on `a = of 0` and `b = of 1`. For `1/l + 1/m + 1/n < 1` it is a Fuchsian
triangle group, covered by Fine and Rosenberger's theorem; the other triples give finite groups and
the three Euclidean triangle groups, which have a normal subgroup of finite index isomorphic to
`ℤ²`. Conjugacy separable is `IsConjugacySeparable` of `KourovkaNotebookShared`: elements
conjugate in every finite quotient are conjugate, that is, any two non-conjugate elements have
non-conjugate images in some finite quotient `G / N` (`N` normal of finite index,
`g x g⁻¹ y⁻¹ ∉ N` for all `g`).
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsConjugacySeparable)

/-- The group `⟨a, b | a^l = b^m = (ab)^n = 1⟩`, with `a = of 0` and `b = of 1`. -/
abbrev TriangleGroup (l m n : ℕ) : Type :=
  PresentedGroup ({FreeGroup.of 0 ^ l, FreeGroup.of 1 ^ m, (FreeGroup.of 0 * FreeGroup.of 1) ^ n} :
    Set (FreeGroup (Fin 2)))

/-- Kourovka 9.2 (R. B. J. T. Allenby): for all positive integers `l, m, n` the group
`⟨a, b | a^l = b^m = (ab)^n = 1⟩` is conjugacy separable. -/
def triangleGroupConjugacySeparable : Prop :=
  ∀ l m n : ℕ, 0 < l → 0 < m → 0 < n → IsConjugacySeparable (TriangleGroup l m n)

/--
Resolved true: the Kourovka Archive answers 9.2 "Yes, it is", citing Fine and Rosenberger, who prove
that every Fuchsian group is conjugacy separable (zbMATH review Zbl 0743.20045, which notes that
this answers Allenby's question for the triangle groups): the groups `⟨a, b | a^l = b^m = (ab)^n =
1⟩` are conjugacy separable. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 9.2 (R. B. J. T. Allenby); resolution: B. Fine and G. Rosenberger, Conjugacy
separability of Fuchsian groups and related questions, Contemp. Math. 109 (1990), 11-18, main
theorem as stated in the zbMATH review Zbl 0743.20045: every Fuchsian group is conjugacy separable,
which answers Allenby's question for the triangle groups; Kourovka Archive of Solved Problems,
Problem 9.2: Yes, it is, https://doi.org/10.1090/conm/109/1076372.
-/
public theorem_wanted triangleGroupConjugacySeparable_holds : triangleGroupConjugacySeparable

end MathlibExt.GroupTheory.TriangleGroupConjugacySeparableKourovka9Problem2Wanted
