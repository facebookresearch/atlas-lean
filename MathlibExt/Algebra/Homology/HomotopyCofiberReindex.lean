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
# Integer reindexing of homotopy cofibers

In a preadditive category with binary biproducts, degree negation
identifies reindexed integer-chain homotopy cofibers with the integer-
cochain homotopy cofibers of reindexed arrows. The comparison is
natural in the arrow and preserves the canonical descendant of every
short complex. The degree-negation embedding is bijective, hence
closed under all outgoing edges.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ComplexShape

/-- For integer degree negation from `up ℤ` to `down ℤ`, the
images of `i` and `i+1` satisfy the chain relation
`down.Rel(-i,-(i+1))`. -/
lemma embeddingUpIntDownInt_rel (i : ℤ) :
    (down ℤ).Rel
      (embeddingUpIntDownInt.f i)
      (embeddingUpIntDownInt.f (i + 1)) :=
  embeddingUpIntDownInt.rel (by simp)

/-- The degree-negation embedding from integer cochain shape to
integer chain shape is of truncation type `IsTruncGE`: every
outgoing chain edge remains in its image, since every integer
degree is an image. -/
instance : embeddingUpIntDownInt.IsTruncGE where
  mem_next {_ k} _ := ⟨-k, by simp [embeddingUpIntDownInt]⟩

end ComplexShape

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Every integer cochain degree `j` has a predecessor `j-1`,
with `up.Rel(j-1,j)`. -/
theorem chainToCochainUpHasPrev :
    ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j :=
  fun j ↦ ⟨j - 1, by simp⟩

/-- Every integer chain degree `j` has a predecessor `j+1`,
with `down.Rel(j+1,j)`. -/
theorem chainToCochainDownHasPrev :
    ∀ j : ℤ, ∃ i, (ComplexShape.down ℤ).Rel i j :=
  fun j ↦ ⟨j + 1, by simp⟩

/-- Let `C` be preadditive with binary biproducts. Reindex integer
chains to integer cochains by degree negation `i ↦ -i`. There is a natural isomorphism from
reindexing the chain
homotopy cofiber of an arrow to the cochain homotopy cofiber of
its reindexed arrow. -/
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

/-- Let `C` be preadditive with binary biproducts. Reindex integer
chains to integer cochains by degree negation `i ↦ -i`. At an integer chain arrow `φ`, the forward
natural
cofiber comparison is the canonical restriction comparison for
the degree-negation embedding. -/
@[simp]
theorem chainToCochainNatIso_hom_app (φ : Arrow (ChainComplex C ℤ)) :
    (chainToCochainNatIso (C := C)).hom.app φ =
      (restrictionIso φ.hom ComplexShape.embeddingUpIntDownInt).hom :=
  rfl

/-- Let `C` be preadditive with binary biproducts. Reindex integer
chains to integer cochains by degree negation `i ↦ -i`. At an integer chain arrow `φ`, the inverse
natural
cofiber comparison is the inverse canonical restriction comparison
for degree negation. -/
@[simp]
theorem chainToCochainNatIso_inv_app (φ : Arrow (ChainComplex C ℤ)) :
    (chainToCochainNatIso (C := C)).inv.app φ =
      (restrictionIso φ.hom ComplexShape.embeddingUpIntDownInt).inv :=
  rfl

/-- Let `C` be preadditive with binary biproducts. Reindex integer
chains to integer cochains by degree negation `i ↦ -i`. The natural cofiber comparison can be
chosen so that, for
any short complex `S` of integer chains, its forward component on
`S.f` followed by the descendant of the reindexed `S` equals the
reindexing of the original descendant. -/
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
