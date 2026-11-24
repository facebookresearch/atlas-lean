/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting

/-!
# Functor coherence for actual complex splittings

The maps are the componentwise transport already provided by `Splitting.map`.
Identity, composition and reflexive normalization require only preservation of
zero morphisms. The source and target object and morphism universes, and the
index universe, are independent. Only commuting with the square-zero
normalization requires additive source and target categories and an additive
functor. No homology, abelian, ring or projective assumption is used.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.Splitting

universe u v w uD vD uE vE

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- Componentwise transport through the identity functor fixes the actual splitting. -/
@[simp]
lemma map_id (s : Splitting K) : s.map (𝟭 C) = s := by
  ext i j
  rfl

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
  {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E]

/-- Successive componentwise transports agree with transport through the composite. -/
lemma map_comp (s : Splitting K) (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    s.map (F ⋙ G) = (s.map F).map G := by
  ext i j
  rfl

/-- Zero-preserving functors commute with the actual reflexive inverse construction. -/
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

/-- An additive functor commutes with the proved square-zero normalization. -/
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
