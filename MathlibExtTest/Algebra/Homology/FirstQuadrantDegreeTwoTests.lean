/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FirstQuadrantDegreeTwo

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The exactness of the actual total in degree two suffices; no vanishing of
the other total homology groups is imposed. Object and Hom universes remain
independent. -/
example {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (hTotal : (K.total (ComplexShape.down ℕ)).ExactAt 2)
    (h01 : IsZero
      (((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence K).page 2).X
        (0, 1))) :
    IsZero
      (((HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence K).page 2).X
        (2, 0)) :=
  HomologicalComplex₂.isZero_horizontalSecondPage_two_zero_of_totalH2_zero
    K hTotal.isZero_homology h01

end
