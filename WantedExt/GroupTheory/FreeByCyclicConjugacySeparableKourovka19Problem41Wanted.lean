/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free-by-cyclic groups are conjugacy separable (Kourovka Notebook Problem 19.41)

Kourovka Notebook, Problem 19.41 (I. Kapovich), marked solved in the 21st issue: let `φ` be an
automorphism of a free group `Fₙ` of finite rank. Is the split extension `Fₙ ⋊_φ ℤ` conjugacy
separable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.SemidirectProduct
public import WantedExt.GroupTheory.KourovkaNotebookShared

@[expose] public section

namespace MathlibExt.GroupTheory.FreeByCyclicConjugacySeparableKourovka19Problem41Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.41 (I. Kapovich). UnsolvedMath record
UM-00701589 (`KOU-19.41`), dataset ulamai/UnsolvedMath v1.8.0.

Conjugacy separable: elements whose images are conjugate in every finite quotient `G / N` (`N`
normal of finite index, written as `g x g⁻¹ y⁻¹ ∈ N` for some `g`) are conjugate in `G`. `Fₙ ⋊_φ ℤ`
is Mathlib's semidirect product of `FreeGroup (Fin n)` by `Multiplicative ℤ` acting through the
powers of `φ`. `IsConjugacySeparable` is the shared definition in
`WantedExt/GroupTheory/KourovkaNotebookShared.lean`.
-/

open MathlibExt.GroupTheory.KourovkaNotebookShared

/-- Kourovka 19.41 (I. Kapovich): for every automorphism `φ` of the free group `Fₙ` of finite rank,
the split extension `Fₙ ⋊_φ ℤ` is conjugacy separable. -/
def freeByCyclicConjugacySeparable : Prop :=
  ∀ (n : ℕ) (φ : MulAut (FreeGroup (Fin n))),
    IsConjugacySeparable
      (FreeGroup (Fin n) ⋊[zpowersHom (MulAut (FreeGroup (Fin n))) φ] Multiplicative ℤ)

/--
Resolved true: Dahmani, Hughes, Kudlinska and Touikan prove that every finitely generated
free-by-cyclic group, in particular every `Fₙ ⋊_φ ℤ`, is conjugacy separable; the 21st issue of the
Kourovka Notebook marks 19.41 solved ("Yes, it is"). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 19.41 (I. Kapovich); resolution: F. Dahmani, S. Hughes, M. Kudlinska and N. Touikan,
Free-by-cyclic groups are conjugacy separable, preprint, arXiv:2509.22346v2 (2026), abstract: all
finitely generated free-by-cyclic groups are conjugacy separable, resolving Question 19.41; the
Kourovka Notebook (21st issue) marks 19.41 solved: Yes, it is, https://arxiv.org/abs/2509.22346.
-/
public theorem_wanted freeByCyclicConjugacySeparable_holds : freeByCyclicConjugacySeparable

end MathlibExt.GroupTheory.FreeByCyclicConjugacySeparableKourovka19Problem41Wanted
