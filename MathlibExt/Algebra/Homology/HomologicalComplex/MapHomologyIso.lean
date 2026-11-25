/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Functors preserving homology

A functor preserving zero morphisms and homology between categories with
homology commutes with the homology functor on complexes. At each degree,
the natural isomorphism is the homology comparison for the associated short
complex. Its naturality follows from the short-complex comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
  {I : Type*} (c : ComplexShape I) (n : I)

/-- Short-complex homology comparison, regarded as a natural isomorphism on complexes. -/
def mapHomologicalComplexHomologyIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c n ≅
      HomologicalComplex.homologyFunctor C c n ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso F) (fun f =>
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c n).map f) F)

/-- The component is exactly the short-complex homology comparison. -/
theorem mapHomologicalComplexHomologyIso_app (K : HomologicalComplex C c) :
    (mapHomologicalComplexHomologyIso F c n).app K = (K.sc n).mapHomologyIso F := rfl

/-- Complex maps preserve the homology-comparison square. -/
@[reassoc]
theorem mapHomologicalComplexHomologyIso_hom_naturality
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map f) n ≫
        ((mapHomologicalComplexHomologyIso F c n).app L).hom =
      ((mapHomologicalComplexHomologyIso F c n).app K).hom ≫
        F.map (HomologicalComplex.homologyMap f n) :=
  (mapHomologicalComplexHomologyIso F c n).hom.naturality f

end CategoryTheory.Functor
