/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjugacy separability of one-relator groups with torsion (Kourovka Notebook Problem 8.69)

Kourovka Notebook, Archive of Solved Problems, Problem 8.69 (C. Y. Tang): is every 1-relator group
with non-trivial torsion conjugacy separable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PresentedGroup
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorTorsionConjugacySeparableKourovka8Problem69Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.69 (C. Y.
Tang). UnsolvedMath record UM-00700517 (`KOU-8.69`), dataset ulamai/UnsolvedMath v1.8.0.

A one-relator group is `⟨x₁, …, xₙ | r⟩` (Mathlib's `PresentedGroup` on `Fin n`); non-trivial
torsion means a non-trivial element of finite order. Conjugacy separable is `IsConjugacySeparable`
(`WantedExt/GroupTheory/KourovkaNotebookShared.lean`): elements conjugate in every finite quotient
are conjugate.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared (IsConjugacySeparable)

/-- Kourovka 8.69 (C. Y. Tang): every one-relator group `⟨x₁, …, xₙ | r⟩` with non-trivial torsion
is conjugacy separable. -/
def oneRelatorTorsionConjugacySeparable : Prop :=
  ∀ (n : ℕ) (r : FreeGroup (Fin n)),
    (∃ g : PresentedGroup ({r} : Set (FreeGroup (Fin n))), g ≠ 1 ∧ IsOfFinOrder g) →
      IsConjugacySeparable (PresentedGroup ({r} : Set (FreeGroup (Fin n))))

/--
Resolved true: the Kourovka Archive answers 8.69 "Yes, it is", citing Minasyan and Zalesskii (2013),
who prove that one-relator groups with torsion are hereditarily conjugacy separable, using Wise's
results. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.69
(C. Y. Tang); resolution: A. Minasyan and P. Zalesskii, One-relator groups with torsion are
conjugacy separable, J. Algebra 382 (2013), 39-45, Kourovka Archive, Problem 8.69: Yes, it is;
paper, Theorem 1.1: one-relator groups with torsion are hereditarily conjugacy separable (the paper
says it answers Kourovka 8.69), https://arxiv.org/abs/1211.0488.
-/
public theorem_wanted oneRelatorTorsionConjugacySeparable_holds :
    oneRelatorTorsionConjugacySeparable

end MathlibExt.GroupTheory.OneRelatorTorsionConjugacySeparableKourovka8Problem69Wanted
