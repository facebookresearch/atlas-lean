/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated groups with two conjugacy classes (Kourovka Notebook Problem 9.10)

Kourovka Notebook, Archive of Solved Problems, Problem 9.10 (V. S. Guba): do there exist finitely
generated groups different from `ℤ/2ℤ` which have precisely two conjugacy classes?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

namespace MathlibExt.GroupTheory.TwoConjugacyClassesFinitelyGeneratedKourovka9Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.10 (V. S.
Guba). UnsolvedMath record UM-00700545 (`KOU-9.10`), dataset ulamai/UnsolvedMath v1.8.0.

"Different from `ℤ/2ℤ`" is "not isomorphic to `ℤ/2ℤ`"; two conjugacy classes is `Nat.card
(ConjClasses G) = 2`.
-/

/-- Kourovka 9.10 (V. S. Guba): there is a finitely generated group, not isomorphic to `ℤ/2ℤ`, with
exactly two conjugacy classes. -/
def existsFGTwoConjugacyClasses : Prop :=
  ∃ (G : Type) (_ : Group G), Group.FG G ∧ Nat.card (ConjClasses G) = 2 ∧
    IsEmpty (G ≃* Multiplicative (ZMod 2))

/--
Resolved true: Osin constructs infinite finitely generated groups with exactly `n` conjugacy classes
for every `n ≥ 2`, in particular a finitely generated group other than `ℤ/2ℤ` all of whose
non-trivial elements are conjugate; the Kourovka Archive answers 9.10 "Yes, there do". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.10 (V. S. Guba); resolution:
D. Osin, Small cancellations over relatively hyperbolic groups and embedding theorems, Ann. of Math.
172 (2010), 1-39, abstract: infinite finitely generated groups with exactly n conjugacy classes for
every n ≥ 2, in particular an affirmative answer to the question of a finitely generated group other
than ℤ/2ℤ all of whose non-trivial elements are conjugate; Kourovka Archive of Solved Problems,
Problem 9.10: Yes, there do, https://doi.org/10.4007/annals.2010.172.1.
-/
public theorem_wanted existsFGTwoConjugacyClasses_holds : existsFGTwoConjugacyClasses

end MathlibExt.GroupTheory.TwoConjugacyClassesFinitelyGeneratedKourovka9Problem10Wanted
