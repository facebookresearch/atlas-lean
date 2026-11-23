/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The conjugacy problem for metabelian groups (Kourovka Notebook Problem 4.32)

Kourovka Notebook, Archive of Solved Problems, Problem 4.32 (M. I. Kargapolov): the conjugacy
problem for metabelian groups.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.MetabelianConjugacyProblemKourovka4Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.32 (M. I.
Kargapolov). UnsolvedMath record UM-00700240 (`KOU-4.32`), dataset ulamai/UnsolvedMath v1.8.0.

The problem is read as the solvability of the conjugacy problem in finitely generated metabelian
groups, the setting of Noskov's paper. A finitely generated metabelian group is finitely presented
in the variety of metabelian groups (P. Hall), so it is `F_n / N` with `N` the normal closure of a
finite set `R` together with `F_n''`. The conjugacy problem is solvable when the set of pairs of
words representing conjugate elements is decidable (`ComputablePred`), for each such presentation.
-/

/-- The kernel of the metabelian presentation `⟨x₁, …, xₙ | R⟩` in the variety of metabelian
groups: the normal closure in `F_n` of `R` together with the second derived subgroup `F_n''`. -/
def metabelianPresentationKernel (n : ℕ) (R : Finset (FreeGroup (Fin n))) :
    Subgroup (FreeGroup (Fin n)) :=
  Subgroup.normalClosure ((R : Set (FreeGroup (Fin n))) ∪ derivedSeries (FreeGroup (Fin n)) 2)

/-- Kourovka 4.32 (M. I. Kargapolov), the conjugacy problem for metabelian groups: in every
finitely generated metabelian group, given by a finite presentation in the variety of metabelian
groups, the set of pairs of words representing conjugate elements is decidable. -/
def metabelianConjugacyProblemDecidable : Prop :=
  ∀ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    ComputablePred fun w : List (Fin n × Bool) × List (Fin n × Bool) =>
      ∃ g : FreeGroup (Fin n),
        g * FreeGroup.mk w.1 * g⁻¹ * (FreeGroup.mk w.2)⁻¹ ∈ metabelianPresentationKernel n R

/--
Resolved true: Noskov proves that the conjugacy problem is solvable in finitely generated metabelian
groups; the Kourovka Archive answers 4.32 "This is algorithmically soluble". Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.32 (M. I. Kargapolov); resolution:
G. A. Noskov, Conjugacy problem in metabelian groups, Math. Notes 31 (1982), 252-258, main theorem,
as stated in F. Cannonito's zbMATH review of a later paper (Zbl 0799.20033): Noskov proved the
decidability of the conjugacy problem for finitely generated metabelian groups, which are finitely
presented in the variety of metabelian groups; Kourovka Archive of Solved Problems, Problem 4.32:
This is algorithmically soluble, https://doi.org/10.1007/BF01138933.
-/
public theorem_wanted metabelianConjugacyProblemDecidable_holds :
    metabelianConjugacyProblemDecidable

end MathlibExt.GroupTheory.MetabelianConjugacyProblemKourovka4Problem32Wanted
