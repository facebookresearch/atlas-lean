/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Absorbing direct summands of torsion-free abelian groups (Kourovka Notebook Problem 17.21)

Kourovka Notebook, Archive of Solved Problems, Problem 17.21 (G. M. Bergman): a) If `A, B, C` are
torsion-free abelian groups with `A ≅ A ⊕ B ⊕ C`, must `A ≅ A ⊕ B`? b) What if, furthermore, `B ≅
C`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Notation.Prod

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeAbelianDirectSumCancellationKourovka17Problem21Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.21 (G. M.
Bergman). UnsolvedMath record UM-00701323 (`KOU-17.21`), dataset ulamai/UnsolvedMath v1.8.0.

Torsion-free: `n • a = 0` with `n ≠ 0` forces `a = 0`. Direct sums are products `A × B × C`, groups
are taken in `Type`; one target per part.
-/

/-- An additive group is torsion-free: `n • a = 0` with `n ≠ 0` forces `a = 0`. -/
def IsTorsionFreeAddGroup (A : Type*) [AddCommGroup A] : Prop :=
  ∀ (n : ℕ) (a : A), n ≠ 0 → n • a = 0 → a = 0

/-- Kourovka 17.21(a) (G. M. Bergman): for torsion-free abelian groups `A, B, C`,
`A ≅ A ⊕ B ⊕ C` implies `A ≅ A ⊕ B`. -/
def torsionFreeAbsorbsDirectSummand : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C],
    IsTorsionFreeAddGroup A → IsTorsionFreeAddGroup B → IsTorsionFreeAddGroup C →
      Nonempty (A ≃+ A × B × C) → Nonempty (A ≃+ A × B)

/-- Kourovka 17.21(b) (G. M. Bergman): the same implication under the extra hypothesis `B ≅ C`. -/
def torsionFreeAbsorbsDirectSummandOfIso : Prop :=
  ∀ (A B C : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C],
    IsTorsionFreeAddGroup A → IsTorsionFreeAddGroup B → IsTorsionFreeAddGroup C →
      Nonempty (B ≃+ C) → Nonempty (A ≃+ A × B × C) → Nonempty (A ≃+ A × B)

/--
Resolved false: the Kourovka Archive answers 17.21 "No, not necessarily, even in case b)", citing
Corner (1964) and Bergman (letter of 2011, an example with `B` and `C` of rank 1): there are
torsion-free abelian groups with `A ≅ A ⊕ B ⊕ C` but `A ≇ A ⊕ B`. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.21 (G. M. Bergman); resolution: A.
L. S. Corner, in Proc. Colloq. Abelian Groups (Tihany, 1963), Budapest, 1964, 43-48; G. M. Bergman,
letter of 20 February 2011, as recorded in the Kourovka Archive, Kourovka Archive, Problem 17.21
(No, not necessarily, even in case b); see Corner (1964); Bergman also has an example with B and C
of rank 1).
-/
public theorem_wanted torsionFreeAbsorbsDirectSummand_refuted : ¬ torsionFreeAbsorbsDirectSummand

/--
Resolved false: the Kourovka Archive answers 17.21(b) negatively as well ("even in case b)", Corner
1964; Bergman, letter of 2011): there are torsion-free abelian groups with `B ≅ C` and `A ≅ A ⊕ B ⊕
C` but `A ≇ A ⊕ B`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 17.21 (G. M. Bergman); resolution: A. L. S. Corner, in Proc. Colloq. Abelian Groups (Tihany,
1963), Budapest, 1964, 43-48; G. M. Bergman, letter of 20 February 2011, as recorded in the Kourovka
Archive, Kourovka Archive, Problem 17.21 (No, not necessarily, even in case b); see Corner (1964);
Bergman also has an example with B and C of rank 1).
-/
public theorem_wanted torsionFreeAbsorbsDirectSummandOfIso_refuted :
    ¬ torsionFreeAbsorbsDirectSummandOfIso

end MathlibExt.GroupTheory.TorsionFreeAbelianDirectSumCancellationKourovka17Problem21Wanted
