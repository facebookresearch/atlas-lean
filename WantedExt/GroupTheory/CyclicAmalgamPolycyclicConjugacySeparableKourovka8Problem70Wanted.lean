/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjugacy separability of cyclic amalgams (Kourovka Notebook Problem 8.70)

Kourovka Notebook, Archive of Solved Problems, Problem 8.70 (C. Y. Tang): let `A`, `B` be
polycyclic-by-finite groups. Let `G = A *_H B` where `H` is cyclic. Is `G` conjugacy separable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PushoutI
public import WantedExt.GroupTheory.KourovkaNotebookShared
public import WantedExt.GroupTheory.GroupClassesShared

@[expose] public section

namespace MathlibExt.GroupTheory.CyclicAmalgamPolycyclicConjugacySeparableKourovka8Problem70Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.70 (C. Y.
Tang). UnsolvedMath record UM-00700518 (`KOU-8.70`), dataset ulamai/UnsolvedMath v1.8.0.

The amalgamated free product of `A = G 0` and `B = G 1` over `H`, embedded in both by injective `φ
i`, is Mathlib's `Monoid.PushoutI φ`. Polycyclic-by-finite is `IsAlmostPolycyclic` of
`WantedExt/GroupTheory/GroupClassesShared.lean`; conjugacy separable is `IsConjugacySeparable`
(`WantedExt/GroupTheory/KourovkaNotebookShared.lean`).
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsConjugacySeparable)
open MathlibExt.GroupTheory.GroupClassesShared (IsAlmostPolycyclic)

/-- Kourovka 8.70 (C. Y. Tang): the free product `A *_H B` of two polycyclic-by-finite groups
`A = G 0` and `B = G 1` amalgamating a cyclic subgroup `H` (embedded in both by `φ`) is conjugacy
separable. -/
def cyclicAmalgamPolycyclicByFiniteConjugacySeparable : Prop :=
  ∀ (G : Fin 2 → Type) [∀ i, Group (G i)] (H : Type) [Group H] (φ : ∀ i, H →* G i),
    (∀ i, Function.Injective (φ i)) → IsCyclic H → (∀ i, IsAlmostPolycyclic (G i)) →
      IsConjugacySeparable (Monoid.PushoutI φ)

/--
Resolved true: the Kourovka Archive answers 8.70 "Yes, it is", citing Ribes, Segal and Zalesskii
(1998): by their Theorem A the free product of two groups of a class of groups they define,
amalgamating a cyclic subgroup, is again in the class, in particular conjugacy separable, and by
Theorem B the class contains all polycyclic-by-finite groups; the introduction says this answers
Problem 8.70. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.70
(C. Y. Tang); resolution: L. Ribes, D. Segal and P. A. Zalesskii, Conjugacy separability and free
products of groups with cyclic amalgamation, J. London Math. Soc. (2) 57 (1998), 609-628, Kourovka
Archive, Problem 8.70: Yes, it is; paper, Theorems A and B (p. 610): the free product of two groups
of the paper's class, which contains all polycyclic-by-finite groups, amalgamating a cyclic subgroup
is conjugacy separable, https://doi.org/10.1112/S0024610798006267.
-/
public theorem_wanted cyclicAmalgamPolycyclicByFiniteConjugacySeparable_holds :
    cyclicAmalgamPolycyclicByFiniteConjugacySeparable

end MathlibExt.GroupTheory.CyclicAmalgamPolycyclicConjugacySeparableKourovka8Problem70Wanted
