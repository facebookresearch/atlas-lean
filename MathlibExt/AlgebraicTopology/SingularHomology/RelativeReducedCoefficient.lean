/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.ReducedCoefficientFunctor
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeBoundaryCoefficient

/-!
# Relative and reduced homology with varying coefficients

For a topological pair with contractible ambient space and coefficients in an
abelian category, identifies relative homology in degree `n + 1` with reduced
homology of the subspace in degree `n`. Proves naturality in the coefficient
object and packages these comparisons as a natural isomorphism.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The contractible-ambient relative-to-reduced comparison is coefficient-natural
as soon as the relative boundary is coefficient-natural. -/
private theorem relativeSingularHomologyReducedIsoOfContractibleAmbient_naturality_coefficient_aux
    {R S : C} (α : R ⟶ S) (P : TopPair.{w}) [ContractibleSpace P.fst] (n : ℕ)
    (hδ :
      ((relativeSingularHomologyCoefficientFunctor (C := C) (n + 1)).map α).app P ≫
          (relativeSingularBoundary C S n).app P =
        (relativeSingularBoundary C R n).app P ≫
          ((singularHomologyFunctor C n).map α).app P.snd) :
    ((relativeSingularHomologyCoefficientFunctor (C := C) (n + 1)).map α).app P ≫
        (relativeSingularHomologyReducedIsoOfContractibleAmbient C S P n).hom =
      (relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
        (reducedSingularHomologyCoefficientMap C n α).app P.snd := by
  have : Mono ((reducedSingularHomologyι C S n).app P.snd) := by
    rw [← reducedSingularHomologyObjIso_hom_ι]
    infer_instance
  let φ : (relativeSingularHomologyFunctor C R (n + 1)).obj P ⟶
      (relativeSingularHomologyFunctor C S (n + 1)).obj P :=
    ((relativeSingularHomologyCoefficientFunctor (C := C) (n + 1)).map α).app P
  change φ ≫ (relativeSingularHomologyReducedIsoOfContractibleAmbient C S P n).hom =
      (relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
        (reducedSingularHomologyCoefficientMap C n α).app P.snd
  have hred :
      (reducedSingularHomologyCoefficientMap C n α).app P.snd ≫
          (reducedSingularHomologyι C S n).app P.snd =
        (reducedSingularHomologyι C R n).app P.snd ≫
          ((singularHomologyFunctor C n).map α).app P.snd := by
    exact congr_app
      (reducedSingularHomologyCoefficientMap_comp_ι C n α) P.snd
  have hrhs :
      ((relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
          (reducedSingularHomologyCoefficientMap C n α).app P.snd) ≫
        (reducedSingularHomologyι C S n).app P.snd =
      (relativeSingularBoundary C R n).app P ≫
        ((singularHomologyFunctor C n).map α).app P.snd := by
    calc
      ((relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
          (reducedSingularHomologyCoefficientMap C n α).app P.snd) ≫
          (reducedSingularHomologyι C S n).app P.snd =
        (relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
          ((reducedSingularHomologyCoefficientMap C n α).app P.snd ≫
            (reducedSingularHomologyι C S n).app P.snd) := Category.assoc _ _ _
      _ = (relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
          ((reducedSingularHomologyι C R n).app P.snd ≫
            ((singularHomologyFunctor C n).map α).app P.snd) := by rw [hred]
      _ = ((relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
            (reducedSingularHomologyι C R n).app P.snd) ≫
          ((singularHomologyFunctor C n).map α).app P.snd := (Category.assoc _ _ _).symm
      _ = (relativeSingularBoundary C R n).app P ≫
          ((singularHomologyFunctor C n).map α).app P.snd := by
            exact congrArg
              (fun k => k ≫ ((singularHomologyFunctor C n).map α).app P.snd)
              (relativeSingularHomologyReducedIsoOfContractibleAmbient_hom_ι C R P n)
  apply (cancel_mono ((reducedSingularHomologyι C S n).app P.snd)).mp
  change (φ ≫ (relativeSingularHomologyReducedIsoOfContractibleAmbient C S P n).hom) ≫
        (reducedSingularHomologyι C S n).app P.snd =
      ((relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
        (reducedSingularHomologyCoefficientMap C n α).app P.snd) ≫
          (reducedSingularHomologyι C S n).app P.snd
  rw [Category.assoc]
  erw [relativeSingularHomologyReducedIsoOfContractibleAmbient_hom_ι]
  erw [hδ]
  exact hrhs.symm

/-- The contractible-ambient relative-to-reduced comparison is natural in the
coefficient object. -/
theorem relativeSingularHomologyReducedIsoOfContractibleAmbient_naturality_coefficient
    {R S : C} (α : R ⟶ S) (P : TopPair.{w}) [ContractibleSpace P.fst] (n : ℕ) :
    ((relativeSingularHomologyCoefficientFunctor (C := C) (n + 1)).map α).app P ≫
        (relativeSingularHomologyReducedIsoOfContractibleAmbient C S P n).hom =
      (relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n).hom ≫
        (reducedSingularHomologyCoefficientMap C n α).app P.snd :=
  relativeSingularHomologyReducedIsoOfContractibleAmbient_naturality_coefficient_aux
    C α P n (relativeSingularBoundary_naturality_coefficient C n α P)

/-- For fixed `P` with contractible ambient, the relative-to-reduced comparison
is a natural isomorphism in the coefficient variable. -/
noncomputable def relativeSingularHomologyReducedCoefficientIsoOfContractibleAmbient
    (P : TopPair.{w}) [ContractibleSpace P.fst] (n : ℕ) :
    (relativeSingularHomologyCoefficientFunctor (C := C) (n + 1) ⋙
      (evaluation TopPair.{w} C).obj P) ≅
    (reducedSingularHomologyCoefficientFunctor C n ⋙
      (evaluation TopCat.{w} C).obj P.snd) :=
  NatIso.ofComponents
    (fun R => relativeSingularHomologyReducedIsoOfContractibleAmbient C R P n)
    (fun {_R _S} α =>
      relativeSingularHomologyReducedIsoOfContractibleAmbient_naturality_coefficient C α P n)

end AlgebraicTopology
