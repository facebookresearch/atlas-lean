/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Functor

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v u w

variable {A : Type*} [Category* A]
variable {C : Type u} {D : Type v} [Category* C] [Category* D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable [CategoryWithHomology C] [CategoryWithHomology D]
variable {ι : Type w} {c : ComplexShape ι}

noncomputable def mapShortComplexHomologyNatIso₁
    (S : A ⥤ ShortComplex (HomologicalComplex C c))
    (T : A ⥤ ShortComplex (HomologicalComplex D c))
    (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesHomology F]
    (e : S ⋙ (F.mapHomologicalComplex c).mapShortComplex ≅ T)
    (i : ι) :
    (S ⋙ ShortComplex.π₁ ⋙ HomologicalComplex.homologyFunctor C c i ⋙ F) ≅
      (T ⋙ ShortComplex.π₁ ⋙ HomologicalComplex.homologyFunctor D c i) :=
  let eH := HomologicalComplex.mapHomologyFunctorIso (c := c) i F
  isoWhiskerLeft (S ⋙ ShortComplex.π₁) eH.symm ≪≫
    isoWhiskerRight
      (isoWhiskerRight e
        (ShortComplex.π₁ :
          ShortComplex (HomologicalComplex D c) ⥤ HomologicalComplex D c))
      (HomologicalComplex.homologyFunctor D c i)

noncomputable def mapShortComplexHomologyNatIso₂
    (S : A ⥤ ShortComplex (HomologicalComplex C c))
    (T : A ⥤ ShortComplex (HomologicalComplex D c))
    (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesHomology F]
    (e : S ⋙ (F.mapHomologicalComplex c).mapShortComplex ≅ T)
    (i : ι) :
    (S ⋙ ShortComplex.π₂ ⋙ HomologicalComplex.homologyFunctor C c i ⋙ F) ≅
      (T ⋙ ShortComplex.π₂ ⋙ HomologicalComplex.homologyFunctor D c i) :=
  let eH := HomologicalComplex.mapHomologyFunctorIso (c := c) i F
  isoWhiskerLeft (S ⋙ ShortComplex.π₂) eH.symm ≪≫
    isoWhiskerRight
      (isoWhiskerRight e
        (ShortComplex.π₂ :
          ShortComplex (HomologicalComplex D c) ⥤ HomologicalComplex D c))
      (HomologicalComplex.homologyFunctor D c i)

noncomputable def mapShortComplexHomologyNatIso₃
    (S : A ⥤ ShortComplex (HomologicalComplex C c))
    (T : A ⥤ ShortComplex (HomologicalComplex D c))
    (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesHomology F]
    (e : S ⋙ (F.mapHomologicalComplex c).mapShortComplex ≅ T)
    (i : ι) :
    (S ⋙ ShortComplex.π₃ ⋙ HomologicalComplex.homologyFunctor C c i ⋙ F) ≅
      (T ⋙ ShortComplex.π₃ ⋙ HomologicalComplex.homologyFunctor D c i) :=
  let eH := HomologicalComplex.mapHomologyFunctorIso (c := c) i F
  isoWhiskerLeft (S ⋙ ShortComplex.π₃) eH.symm ≪≫
    isoWhiskerRight
      (isoWhiskerRight e
        (ShortComplex.π₃ :
          ShortComplex (HomologicalComplex D c) ⥤ HomologicalComplex D c))
      (HomologicalComplex.homologyFunctor D c i)

end CategoryTheory.Functor
