/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Category.Grp.ModQuotientAdjunction
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology and quotient coefficients at a terminal degree

The quotient-by-`ell` functor preserves cokernels.  At any degree where the
outgoing object of a homological complex is zero, homology is a cokernel.
Consequently coefficient reduction commutes with homology at that degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u

variable {I : Type*} {c : ComplexShape I}

/-- If the object after degree `i` is zero, homology after quotienting every
chain group by `ell` is the quotient by `ell` of integral homology. -/
noncomputable def modQuotientHomologyIsoOfNextIsZero
    (ell : ℕ) (K : HomologicalComplex AddCommGrpCat.{u} c) (i : I)
    (hnext : IsZero (K.X (c.next i))) :
    (((AddCommGrpCat.modQuotientFunctor ell).mapHomologicalComplex c).obj K
        ).homology i ≅
      AddCommGrpCat.modQuotientObj (K.homology i) ell := by
  let Q := AddCommGrpCat.modQuotientFunctor ell
  let S := K.sc i
  have hg : S.g = 0 := by
    exact hnext.eq_of_tgt _ _
  letI : Q.PreservesLeftHomologyOf S :=
    Q.preservesLeftHomology_of_zero_g S hg
  exact S.mapHomologyIso Q

end HomologicalComplex
