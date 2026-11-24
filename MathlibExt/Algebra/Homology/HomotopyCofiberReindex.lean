/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomotopyCofiber

/-!
# Homotopy cofiber reindexing

The chain to cochain comparison is the integer specialization of the generic
homotopy-cofiber restriction comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ComplexShape

/-- Reindexing relation for the integer chain-to-cochain embedding. -/
lemma embeddingUpIntDownInt_rel (i : ℤ) :
    (down ℤ).Rel
      (embeddingUpIntDownInt.f i)
      (embeddingUpIntDownInt.f (i + 1)) :=
  embeddingUpIntDownInt.rel (by simp)

/-- The integer chain-to-cochain embedding is closed under outgoing edges.

This records the surjectivity of the degree negation used by the embedding. -/
instance : embeddingUpIntDownInt.IsTruncGE where
  mem_next {_ k} _ := ⟨-k, by simp [embeddingUpIntDownInt]⟩

end ComplexShape

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Every integer cochain degree has a predecessor. -/
theorem chainToCochainUpHasPrev :
    ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j :=
  fun j ↦ ⟨j - 1, by simp⟩

/-- Every integer chain degree has a predecessor. -/
theorem chainToCochainDownHasPrev :
    ∀ j : ℤ, ∃ i, (ComplexShape.down ℤ).Rel i j :=
  fun j ↦ ⟨j + 1, by simp⟩

/-- The natural comparison between reindexed chain homotopy cofibers and
cochain homotopy cofibers. -/
noncomputable def chainToCochainNatIso :
    HomologicalComplex.homotopyCofiberFunctor
        (c := ComplexShape.down ℤ) chainToCochainDownHasPrev ⋙
          (ChainComplex.cochainComplexEquivalence C).functor ≅
      (ChainComplex.cochainComplexEquivalence C).functor.mapArrow ⋙
        HomologicalComplex.homotopyCofiberFunctor
          (c := ComplexShape.up ℤ) chainToCochainUpHasPrev :=
  restrictionNatIso
    (C := C) ComplexShape.embeddingUpIntDownInt
      chainToCochainUpHasPrev chainToCochainDownHasPrev

/-- The forward component of `chainToCochainNatIso` is the generic restriction
comparison. -/
@[simp]
theorem chainToCochainNatIso_hom_app (φ : Arrow (ChainComplex C ℤ)) :
    (chainToCochainNatIso (C := C)).hom.app φ =
      (restrictionIso φ.hom ComplexShape.embeddingUpIntDownInt).hom :=
  rfl

/-- The inverse component of `chainToCochainNatIso` is the inverse generic restriction
comparison. -/
@[simp]
theorem chainToCochainNatIso_inv_app (φ : Arrow (ChainComplex C ℤ)) :
    (chainToCochainNatIso (C := C)).inv.app φ =
      (restrictionIso φ.hom ComplexShape.embeddingUpIntDownInt).inv :=
  rfl

/-- The chain-to-cochain homotopy-cofiber comparison with its short-complex compatibility property. -/
theorem chainToCochainNatIso_exists :
    ∃ e :
        HomologicalComplex.homotopyCofiberFunctor
            (c := ComplexShape.down ℤ) (fun j ↦ ⟨j + 1, by simp⟩) ⋙
              (ChainComplex.cochainComplexEquivalence C).functor ≅
          (ChainComplex.cochainComplexEquivalence C).functor.mapArrow ⋙
            HomologicalComplex.homotopyCofiberFunctor
              (c := ComplexShape.up ℤ) (fun j ↦ ⟨j - 1, by simp⟩),
      ∀ S : ShortComplex (ChainComplex C ℤ),
        (e.app (Arrow.mk S.f)).hom ≫
            HomologicalComplex.homotopyCofiber.descShortComplex
              (S.map (ChainComplex.cochainComplexEquivalence C).functor) =
          (ChainComplex.cochainComplexEquivalence C).functor.map
            (HomologicalComplex.homotopyCofiber.descShortComplex S) := by
  refine ⟨chainToCochainNatIso (C := C), ?_⟩
  intro S
  change
    ((chainToCochainNatIso (C := C)).app (Arrow.mk S.f)).hom ≫
        descShortComplex
          (S.map (ComplexShape.embeddingUpIntDownInt.restrictionFunctor C)) =
      HomologicalComplex.restrictionMap (descShortComplex S)
        ComplexShape.embeddingUpIntDownInt
  have h :
      ((chainToCochainNatIso (C := C)).app (Arrow.mk S.f)).hom =
        (restrictionIso S.f ComplexShape.embeddingUpIntDownInt).hom :=
    chainToCochainNatIso_hom_app (Arrow.mk S.f)
  rw [h]
  exact restrictionIso_hom_descShortComplex ComplexShape.embeddingUpIntDownInt S

@[reassoc]
theorem chainToCochainNatIso_hom_descShortComplex
    (S : ShortComplex (ChainComplex C ℤ)) :
    ((chainToCochainNatIso (C := C)).app (Arrow.mk S.f)).hom ≫
        HomologicalComplex.homotopyCofiber.descShortComplex
          (S.map (ChainComplex.cochainComplexEquivalence C).functor) =
      (ChainComplex.cochainComplexEquivalence C).functor.map
        (HomologicalComplex.homotopyCofiber.descShortComplex S) :=
  by
    have h :
        ((chainToCochainNatIso (C := C)).app (Arrow.mk S.f)).hom =
          (restrictionIso S.f ComplexShape.embeddingUpIntDownInt).hom :=
      chainToCochainNatIso_hom_app (Arrow.mk S.f)
    rw [h]
    exact restrictionIso_hom_descShortComplex ComplexShape.embeddingUpIntDownInt S

end HomologicalComplex.homotopyCofiber
