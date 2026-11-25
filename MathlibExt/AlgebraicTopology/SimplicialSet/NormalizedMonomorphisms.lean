/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NormalizedCoproduct
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Monomorphisms of normalized chain complexes

Shows that normalized chains with fixed coefficients preserve simplicial
monomorphisms, using their nondegenerate-simplex coproduct bases. A degree
component is an isomorphism when the corresponding nondegenerate embedding is
surjective.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

section DegreewiseMono

variable {X Y : SSet.{w}} (f : X ⟶ Y) [Mono f] (R : C) (n : ℕ)

/-- For a monomorphism `f : X ⟶ Y` of simplicial sets, each degree component of
the normalized chain map `normalizedChainComplexMap f R` is a monomorphism.

The embedding of nondegenerate simplices is injective, hence a mono in `Type`,
and the coproduct functor `sigmaConst.obj R` preserves monos. The result follows
from the naturality of the canonical coproduct basis isomorphisms. -/
instance normalizedChainComplexMap_f_mono :
    Mono ((normalizedChainComplexMap f R).f n) := by
  have : Mono (TypeCat.ofHom (nonDegenerateEmbeddingOfMono f n :
      X.nonDegenerate n → Y.nonDegenerate n)) := by
    rw [mono_iff_injective]
    exact (nonDegenerateEmbeddingOfMono f n).injective
  rw [← mono_comp_iff_of_isIso (X.normalizedChainComplexCoproductIso R n).hom]
  rw [normalizedChainComplexCoproductIso_hom_naturality_of_mono]
  have h : Mono ((sigmaConst.obj R).map
      (TypeCat.ofHom (nonDegenerateEmbeddingOfMono f n :
        X.nonDegenerate n → Y.nonDegenerate n)) ≫
      (Y.normalizedChainComplexCoproductIso R n).hom) :=
    inferInstance
  exact h

/-- If the nondegenerate embedding for `f` is surjective in degree `n`,
then the degree-`n` component of the normalized chain map is an iso.
Bijectivity in `Type` gives an iso in `TypeCat`; `sigmaConst` preserves it,
and the coproduct-basis naturality cancels the left iso. -/
theorem normalizedChainComplexMap_f_isIso_of_surjective_nonDegenerateEmbedding
    (h_surj : Function.Surjective (nonDegenerateEmbeddingOfMono f n)) :
    IsIso ((normalizedChainComplexMap f R).f n) := by
  have hb : Function.Bijective (nonDegenerateEmbeddingOfMono f n) :=
    ⟨(nonDegenerateEmbeddingOfMono f n).injective, h_surj⟩
  have : IsIso (TypeCat.ofHom (nonDegenerateEmbeddingOfMono f n :
      X.nonDegenerate n → Y.nonDegenerate n)) := by
    rwa [isIso_iff_bijective]
  let isoType : (X.nonDegenerate n : Type w) ≅ (Y.nonDegenerate n : Type w) :=
    (Equiv.ofBijective (nonDegenerateEmbeddingOfMono f n) hb).toIso
  let eMap : (∐ fun _ : X.nonDegenerate n => R) ≅
      (∐ fun _ : Y.nonDegenerate n => R) :=
    (sigmaConst.obj R).mapIso isoType
  let eComp : (∐ fun _ : X.nonDegenerate n => R) ≅
      (Y.normalizedChainComplex R).X n :=
    eMap ≪≫ Y.normalizedChainComplexCoproductIso R n
  have h_left : IsIso ((X.normalizedChainComplexCoproductIso R n).hom ≫
      (normalizedChainComplexMap f R).f n) := by
    have h_eq : (X.normalizedChainComplexCoproductIso R n).hom ≫
        (normalizedChainComplexMap f R).f n = eComp.hom := by
      rw [normalizedChainComplexCoproductIso_hom_naturality_of_mono]
      rfl
    rw [h_eq]
    infer_instance
  exact (isIso_comp_left_iff
    (X.normalizedChainComplexCoproductIso R n).hom
    ((normalizedChainComplexMap f R).f n)).mp h_left

end DegreewiseMono

section FunctorPreserves

variable (R : C)

/-- For a fixed coefficient object `R`, the Mathlib functor
`normalizedChainComplexFunctorObj R` preserves monomorphisms.
Componentwise, this is `normalizedChainComplexMap_f_mono`, packaged via
`HomologicalComplex.mono_of_mono_f`. -/
instance normalizedChainComplexFunctorObj_preservesMonomorphisms :
    (normalizedChainComplexFunctorObj (C := C) R).PreservesMonomorphisms where
  preserves := by
    intro X Y f hf
    have : Mono f := hf
    exact HomologicalComplex.mono_of_mono_f
      (normalizedChainComplexMap f R) fun _ => inferInstance

end FunctorPreserves

end SSet
