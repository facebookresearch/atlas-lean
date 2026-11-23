/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomology

/-!
# Relative singular homology as a coefficient functor

Packages relative singular chains as a functor in the coefficient object and the
topological pair, using the cokernel of the inclusion chain map. Postcomposition
with homology recovers the fixed-coefficient relative homology functors.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [HasCokernels (ChainComplex C ℕ)]

/-- Coefficient-natural relative singular chain complex functor:
`singularChainComplexFunctor C ⋙ mapArrowFunctor ⋙ whiskeringLeft topPairArrowFunctor
⋙ whiskeringRight coker`. Naturality is inherited from composition. -/
noncomputable def relativeSingularChainComplexFunctor :
    C ⥤ TopPair.{w} ⥤ ChainComplex C ℕ :=
  singularChainComplexFunctor C ⋙
    Functor.mapArrowFunctor TopCat.{w} (ChainComplex C ℕ) ⋙
    (Functor.whiskeringLeft TopPair.{w} (Arrow TopCat.{w})
        (Arrow (ChainComplex C ℕ))).obj
      topPairArrowFunctor ⋙
    (Functor.whiskeringRight TopPair.{w} (Arrow (ChainComplex C ℕ))
        (ChainComplex C ℕ)).obj
      (Limits.coker (C := ChainComplex C ℕ))

/-- Objectwise cokernel formula: evaluating the coefficient-natural relative
singular chain functor at `R` and `P` gives the cokernel of the map of
singular chain complexes induced by the pair inclusion `P.map`. -/
@[simp]
lemma relativeSingularChainComplexFunctor_obj_obj (R : C) (P : TopPair.{w}) :
    ((relativeSingularChainComplexFunctor (C := C)).obj R).obj P =
      (Limits.coker (C := ChainComplex C ℕ)).obj
        (Arrow.mk (((singularChainComplexFunctor C).obj R).map P.map)) :=
  rfl

section Abelian

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- Fixing the coefficient `R`, the coefficient-natural relative chain functor
agrees definitionally with the fixed-coefficient relative chain functor
`relativeSingularChainFunctor C R`. -/
@[simp]
lemma relativeSingularChainComplexFunctor_obj (R : C) :
    (relativeSingularChainComplexFunctor (C := C)).obj R =
      relativeSingularChainFunctor C R :=
  rfl

/-- Coefficient-natural relative singular homology in degree `n`,
obtained by postcomposing the chain-complex functor with homology. -/
noncomputable def relativeSingularHomologyCoefficientFunctor (n : ℕ) :
    C ⥤ TopPair.{w} ⥤ C :=
  relativeSingularChainComplexFunctor (C := C) ⋙
    (Functor.whiskeringRight TopPair.{w} (ChainComplex C ℕ) C).obj
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n)

/-- Fixing the coefficient `R`, the coefficient-natural relative homology
functor in degree `n` agrees definitionally with the fixed-coefficient
relative homology functor `relativeSingularHomologyFunctor C R n`. -/
@[simp]
lemma relativeSingularHomologyCoefficientFunctor_obj (R : C) (n : ℕ) :
    (relativeSingularHomologyCoefficientFunctor (C := C) n).obj R =
      relativeSingularHomologyFunctor C R n :=
  rfl

end Abelian

end AlgebraicTopology
