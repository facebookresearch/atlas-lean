/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting

/-!
# Functoriality of splitting transport and normalization

Zero-preserving functors map generalized-inverse splittings, with identity
and composition laws and compatibility with reflexive normalization.
Additive functors additionally preserve the square-zero normalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.Splitting

universe u v w uD vD uE vE

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/--
Let K be a complex of shape c in a category C with zero morphisms and let s be a
generalized-inverse splitting of K. Mapping every component by the identity functor leaves the
splitting unchanged: s.map(𝟭C)=s.
-/
@[simp]
lemma map_id (s : Splitting K) : s.map (𝟭 C) = s := by
  ext i j
  rfl

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E]

/--
Let K be a complex of shape c in a category C with zero morphisms and let s be a
generalized-inverse splitting of K. For zero-preserving F:C⥤D and G:D⥤E between categories
with zero morphisms, s.map(F⋙G)=(s.map F).map G.
-/
lemma map_comp (s : Splitting K) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    s.map (F ⋙ G) = (s.map F).map G := by
  ext i j
  rfl

/--
Let K be a complex of shape c in a category C with zero morphisms, s a generalized-inverse
splitting, and F:C⥤D a zero-preserving functor into a category D with zero morphisms.
Reflexive normalization h d h is preserved: (s.map F).reflexive=s.reflexive.map F.
-/
lemma map_reflexive (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    (s.map F).reflexive = s.reflexive.map F := by
  ext i j
  change F.map (s.hom i j) ≫ F.map (K.d j i) ≫ F.map (s.hom i j) =
    F.map (s.hom i j ≫ K.d j i ≫ s.hom i j)
  simp only [Functor.map_comp]

end HomologicalComplex.Splitting

namespace HomologicalComplex.Splitting

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/--
Let C,D be preadditive categories, K a c-complex with splitting s and F:C⥤D additive. Then
(s.map F).normalize=s.normalize.map F, so the square-zero normalized inverse maps are
functorially preserved.
-/
lemma map_normalize (s : Splitting K) (F : C ⥤ D) [F.Additive] :
    (s.map F).normalize = s.normalize.map F := by
  ext i j
  change
    (𝟙 (F.obj (K.X i)) -
      F.map (K.d i (c.next i)) ≫
        (F.map (s.hom (c.next i) i) ≫ F.map (K.d i (c.next i)) ≫
          F.map (s.hom (c.next i) i))) ≫
      (F.map (s.hom i j) ≫ F.map (K.d j i) ≫ F.map (s.hom i j)) =
    F.map
      ((𝟙 (K.X i) - K.d i (c.next i) ≫
          (s.hom (c.next i) i ≫ K.d i (c.next i) ≫ s.hom (c.next i) i)) ≫
        (s.hom i j ≫ K.d j i ≫ s.hom i j))
  simp only [Functor.map_comp, Functor.map_sub]
  rw [F.map_id]

end HomologicalComplex.Splitting
