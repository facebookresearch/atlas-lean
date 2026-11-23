/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinite centralizers in periodic groups (Kourovka Notebook Problem 2.75)

Kourovka Notebook, Archive of Solved Problems, Problem 2.75 (S. P. Strunkov): let `G` be a periodic
group containing an infinite family of finite subgroups whose intersection contains non-trivial
elements. Does `G` contain a non-trivial element with infinite centralizer?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Torsion

@[expose] public section

namespace MathlibExt.GroupTheory.PeriodicGroupInfiniteCentralizerKourovka2Problem75Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.75 (S. P.
Strunkov). UnsolvedMath record UM-00700145 (`KOU-2.75`), dataset ulamai/UnsolvedMath v1.8.0.

The family is an infinite set of (distinct) finite subgroups: with repetitions allowed, a single
finite subgroup of a finite group would qualify and the question would be trivial. Periodic is
`IsMulTorsion G`.
-/

/-- Kourovka 2.75 (S. P. Strunkov): if a periodic group `G` contains infinitely many distinct
finite subgroups whose intersection is non-trivial, then some non-identity element of `G` has an
infinite centralizer. -/
def periodicGroupHasInfiniteCentralizer : Prop :=
  ∀ (G : Type) [Group G], IsMulTorsion G →
    (∃ 𝓕 : Set (Subgroup G), 𝓕.Infinite ∧ (∀ H ∈ 𝓕, Finite H) ∧ (⨅ H ∈ 𝓕, H) ≠ ⊥) →
      ∃ g : G, g ≠ 1 ∧ (Subgroup.centralizer {g} : Set G).Infinite

/--
Resolved false: the Kourovka Archive answers 2.75 "Not always", citing Lossov (1988). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.75 (S. P. Strunkov);
resolution: K. I. Lossov, Dep. no. 5528-V88, VINITI, Moscow, 1988 (Russian), Kourovka Archive,
Problem 2.75: Not always (Lossov), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted periodicGroupHasInfiniteCentralizer_refuted :
    ¬ periodicGroupHasInfiniteCentralizer

end MathlibExt.GroupTheory.PeriodicGroupInfiniteCentralizerKourovka2Problem75Wanted
