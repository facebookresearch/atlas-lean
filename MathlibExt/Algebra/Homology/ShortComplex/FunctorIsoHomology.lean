/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Functor

/-! # Transport of homology through short-complex diagram isomorphisms

Let `S`, `T` be diagrams of short complexes of complexes in categories `C`, `D`
with zero morphisms and homology. A functor `F : C ⥤ D` preserving zero morphisms
and homology, together with an isomorphism from the image of `S` under `F` to `T`,
gives natural isomorphisms on degree-`i` homology of each of the three objects.
The construction uses the given diagram isomorphism and the canonical homology
comparison for `F`; the complex shape and category universes are independent.
-/

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

/-- Let `S`, `T` be diagrams, indexed by a category `A`, of short complexes of
complexes in categories `C`, `D` with zero morphisms and homology. Suppose `F : C ⥤ D`
preserves zero morphisms and homology, and `e` identifies the image of `S` under `F`
with `T`. For every degree `i` in the given complex shape, there is a natural
isomorphism `F(H_i(S_1)) ≅ H_i(T_1)`, obtained from the canonical
homology comparison and the first component of `e`. All diagram/category/shape
universes retain their given independent values. -/
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

/-- Let `S`, `T` be diagrams, indexed by a category `A`, of short complexes of
complexes in categories `C`, `D` with zero morphisms and homology. Suppose `F : C ⥤ D`
preserves zero morphisms and homology, and `e` identifies the image of `S` under `F`
with `T`. For every degree `i` in the given complex shape, there is a natural
isomorphism `F(H_i(S_2)) ≅ H_i(T_2)`, obtained from the canonical
homology comparison and the middle component of `e`. All diagram/category/shape
universes retain their given independent values. -/
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

/-- Let `S`, `T` be diagrams, indexed by a category `A`, of short complexes of
complexes in categories `C`, `D` with zero morphisms and homology. Suppose `F : C ⥤ D`
preserves zero morphisms and homology, and `e` identifies the image of `S` under `F`
with `T`. For every degree `i` in the given complex shape, there is a natural
isomorphism `F(H_i(S_3)) ≅ H_i(T_3)`, obtained from the canonical
homology comparison and the third component of `e`. All diagram/category/shape
universes retain their given independent values. -/
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
