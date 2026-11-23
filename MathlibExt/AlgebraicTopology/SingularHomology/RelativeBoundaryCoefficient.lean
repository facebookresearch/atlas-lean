/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.HomologySequenceFunctor

public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeBaseCases
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeCoefficientFunctor

/-!
# Coefficient naturality of relative singular boundaries

Packages the short complexes for relative singular chains as a functor of the
coefficient object. For abelian coefficients, constructs the relative boundary
as a natural transformation and proves its coefficient naturality, together
with the homology comparison when the subspace is empty.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u

section Core

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [HasCokernels (ChainComplex C ℕ)]

/-- The coefficient-natural singular-chain cokernel sequence of a topological pair. -/
noncomputable def singularPairShortComplexCoefficientFunctor :
    C ⥤ TopPair.{w} ⥤ ShortComplex (ChainComplex C ℕ) :=
  singularChainComplexFunctor C ⋙
    Functor.mapArrowFunctor TopCat.{w} (ChainComplex C ℕ) ⋙
    (Functor.whiskeringLeft TopPair.{w} (Arrow TopCat.{w})
      (Arrow (ChainComplex C ℕ))).obj topPairArrowFunctor ⋙
    (Functor.whiskeringRight TopPair.{w} (Arrow (ChainComplex C ℕ))
      (ShortComplex (ChainComplex C ℕ))).obj
        (ShortComplex.cokernelSequenceFunctor (C := ChainComplex C ℕ))

end Core

section Abelian

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Fixing the coefficient object recovers the existing singular-pair short-complex functor. -/
@[simp]
lemma singularPairShortComplexCoefficientFunctor_obj (R : C) :
    (singularPairShortComplexCoefficientFunctor (C := C)).obj R =
      singularPairShortComplexFunctor C R :=
  rfl

/-- The absolute-to-relative comparison for a fixed pair with empty subspace is natural
in the coefficient object. -/
theorem singularHomologyEmptyPairObjIso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (P : TopPair.{w}) [IsEmpty P.snd] (n : ℕ) :
    ((singularHomologyFunctor C n).map a).app P.fst ≫
        (singularHomologyEmptyPairObjIso C S P n).hom =
      (singularHomologyEmptyPairObjIso C R P n).hom ≫
        ((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app P := by
  change HomologicalComplex.homologyMap
        (((singularPairShortComplexCoefficientFunctor (C := C)).map a).app P).τ₂ n ≫
      HomologicalComplex.homologyMap
        (((singularPairShortComplexCoefficientFunctor (C := C)).obj S).obj P).g n =
    HomologicalComplex.homologyMap
        (((singularPairShortComplexCoefficientFunctor (C := C)).obj R).obj P).g n ≫
      HomologicalComplex.homologyMap
        (((singularPairShortComplexCoefficientFunctor (C := C)).map a).app P).τ₃ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun f => HomologicalComplex.homologyMap f n)
    (((singularPairShortComplexCoefficientFunctor (C := C)).map a).app P).comm₂₃

/-- Coefficient-natural absolute singular homology of the subspace in a topological pair. -/
noncomputable def singularHomologySubspaceCoefficientFunctor (n : ℕ) :
    C ⥤ TopPair.{w} ⥤ C :=
  singularHomologyFunctor C n ⋙
    (Functor.whiskeringLeft TopPair.{w} TopCat.{w} C).obj TopPair.proj₂

/-- The relative singular connecting map, natural in both coefficients and the pair. -/
noncomputable def relativeSingularBoundaryCoefficient (n : ℕ) :
    relativeSingularHomologyCoefficientFunctor (C := C) (n + 1) ⟶
      singularHomologySubspaceCoefficientFunctor C n where
  app R := relativeSingularBoundary C R n
  naturality {R S} α := by
    ext P
    exact (HomologicalComplex.HomologySequence.δNatTrans
      (C := C) (n + 1) n (by simp)).naturality
        (show (⟨(singularPairShortComplexFunctor C R).obj P,
          singularPairShortComplex_shortExact C R P⟩ :
            ShortComplex.ShortExactSequences (ChainComplex C ℕ)) ⟶
          ⟨(singularPairShortComplexFunctor C S).obj P,
            singularPairShortComplex_shortExact C S P⟩ from
          ⟨((singularPairShortComplexCoefficientFunctor (C := C)).map α).app P⟩)

@[simp]
theorem relativeSingularBoundaryCoefficient_app (n : ℕ) (R : C) :
    (relativeSingularBoundaryCoefficient (C := C) n).app R =
      relativeSingularBoundary C R n :=
  rfl

/-- Pointwise coefficient-naturality square for the relative singular boundary. -/
theorem relativeSingularBoundary_naturality_coefficient
    (n : ℕ) {R S : C} (α : R ⟶ S) (P : TopPair.{w}) :
    ((relativeSingularHomologyCoefficientFunctor (C := C) (n + 1)).map α).app P ≫
        (relativeSingularBoundary C S n).app P =
      (relativeSingularBoundary C R n).app P ≫
        ((singularHomologyFunctor C n).map α).app P.snd :=
  congr_app ((relativeSingularBoundaryCoefficient (C := C) n).naturality α) P

end Abelian

end AlgebraicTopology
