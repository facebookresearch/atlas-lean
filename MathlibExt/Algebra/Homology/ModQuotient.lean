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
# Homology and quotient coefficients when the next object is zero

Let K be a complex of abelian groups of any shape and ℓ∈ℕ. Applying Q_ℓ(A)=A/ℓA to each term
gives a complex of ZMod(ℓ)-modules.

If K at the next object after index i is zero, its outgoing differential is zero and homology at
i is a cokernel of the incoming map. Since Q_ℓ preserves cokernels, H_i(Q_ℓK)≅Q_ℓ(H_iK). The
scalar reduction includes ℓ=0.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u

variable {I : Type*} {c : ComplexShape I}

/-- Let ℓ∈ℕ, c be a complex shape on an arbitrary index type I, and K a c-shaped complex of abelian
groups in universe u. If K_{c.next(i)} is a zero object, there is a ZMod(ℓ)-module isomorphism
H_i(Q_ℓK)≅H_i(K)/ℓH_i(K). Here Q_ℓ is termwise quotient by ℓ-multiples, and the comparison
follows from its cokernel preservation. -/
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
