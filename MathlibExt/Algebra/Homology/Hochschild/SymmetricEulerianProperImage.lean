/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianProperNormalization
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianHodge

/-!
# Proper shuffle quotients and first Eulerian images

Over a rational ground algebra, the
proper both-positive relation quotient
and the image of the full
zero-plus-first Eulerian projector
are splittings of the same chain
endomorphism. Their inclusion and
factor maps give A-linear chain
isomorphisms, retaining both
weights zero and one and the
degree-zero coefficient. This does
not identify the full coefficient-ideal
quotient or the ordinary Harrison–AQ
functor.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The original full raw first chain projector is idempotent in the original A-module category. -/
theorem algebraFirstEulerianChainMap_idempotent :
    algebraFirstEulerianChainMap k A M ≫ algebraFirstEulerianChainMap k A M =
      algebraFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, algebraFirstEulerianChainMap_f]
  exact algebraFirstEulerianOperator_idempotent k A M n

/-- The original normalized full first chain projector is idempotent over A. -/
theorem algebraNormalizedFirstEulerianChainMap_idempotent :
    algebraNormalizedFirstEulerianChainMap k A M ≫ algebraNormalizedFirstEulerianChainMap k A M =
      algebraNormalizedFirstEulerianChainMap k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, algebraNormalizedFirstEulerianChainMap_f]
  exact algebraNormalizedFirstEulerianOperator_idempotent k A M n

/-- The native image of the original raw zero-plus-first Eulerian chain projector. -/
def algebraFirstEulerianImageComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraFirstEulerianChainMap k A M)

/-- The native image of the original normalized zero-plus-first Eulerian chain projector. -/
def algebraNormalizedFirstEulerianImageComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraNormalizedFirstEulerianChainMap k A M)

/-- The original raw proper-shuffle quotient is the raw full first Eulerian image complex. -/
def algebraFirstEulerianQuotientIso :
    algebraPositiveQuotientComplex k A M ≅ algebraFirstEulerianImageComplex k A M where
  hom := algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M)
  inv := image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M
  hom_inv_id := by
    change (algebraPositiveEulerianSection k A M ≫
        factorThruImage (algebraFirstEulerianChainMap k A M)) ≫
      (image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M) =
        𝟙 (algebraPositiveQuotientComplex k A M)
    calc
      _ = algebraPositiveEulerianSection k A M ≫ algebraFirstEulerianChainMap k A M ≫
          algebraRawPositiveProjection k A M := by simp only [Category.assoc, image.fac_assoc]
      _ = (algebraPositiveEulerianSection k A M ≫ algebraRawPositiveProjection k A M) ≫
          (algebraPositiveEulerianSection k A M ≫ algebraRawPositiveProjection k A M) := by
        rw [← algebraRawPositiveProjection_eulerianSection]
        simp only [Category.assoc]
      _ = 𝟙 _ := by rw [algebraPositiveEulerianSection_projection, Category.id_comp]
  inv_hom_id := by
    change (image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M) ≫
      (algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M)) =
        𝟙 (image (algebraFirstEulerianChainMap k A M))
    have hi := image_ι_factorThruImage_of_idempotent (algebraFirstEulerianChainMap k A M)
      (algebraFirstEulerianChainMap_idempotent k A M)
    calc
      _ = image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraFirstEulerianChainMap k A M ≫
          factorThruImage (algebraFirstEulerianChainMap k A M) := by
        rw [Category.assoc, ← Category.assoc (algebraRawPositiveProjection k A M),
          algebraRawPositiveProjection_eulerianSection]
      _ = (image.ι (algebraFirstEulerianChainMap k A M) ≫
          factorThruImage (algebraFirstEulerianChainMap k A M)) ≫
            (image.ι (algebraFirstEulerianChainMap k A M) ≫
              factorThruImage (algebraFirstEulerianChainMap k A M)) := by
        have h := congrArg
          (fun t : algebraRawComplex k A M ⟶ algebraRawComplex k A M =>
            image.ι (algebraFirstEulerianChainMap k A M) ≫ t ≫
              factorThruImage (algebraFirstEulerianChainMap k A M))
          (image.fac (algebraFirstEulerianChainMap k A M)).symm
        simp only [Category.assoc] at h ⊢
        exact h
      _ = 𝟙 _ := by rw [hi, Category.id_comp]

/-- The original normalized proper quotient is the normalized full first image complex. -/
def algebraNormalizedFirstEulerianQuotientIso :
    algebraNormalizedPositiveQuotientComplex k A M ≅ algebraNormalizedFirstEulerianImageComplex k A M where
  hom := algebraNormalizedPositiveEulerianSection k A M ≫
    factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)
  inv := image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫ algebraNormalizedPositiveProjection k A M
  hom_inv_id := by
    change (algebraNormalizedPositiveEulerianSection k A M ≫
        factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) ≫
      (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
        algebraNormalizedPositiveProjection k A M) =
          𝟙 (algebraNormalizedPositiveQuotientComplex k A M)
    calc
      _ = algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizedFirstEulerianChainMap k A M ≫
          algebraNormalizedPositiveProjection k A M := by simp only [Category.assoc, image.fac_assoc]
      _ = (algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizedPositiveProjection k A M) ≫
          (algebraNormalizedPositiveEulerianSection k A M ≫ algebraNormalizedPositiveProjection k A M) := by
        rw [← algebraNormalizedPositiveProjection_eulerianSection]
        simp only [Category.assoc]
      _ = 𝟙 _ := by rw [algebraNormalizedPositiveEulerianSection_projection, Category.id_comp]
  inv_hom_id := by
    change (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
        algebraNormalizedPositiveProjection k A M) ≫
      (algebraNormalizedPositiveEulerianSection k A M ≫
        factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) =
          𝟙 (image (algebraNormalizedFirstEulerianChainMap k A M))
    have hi := image_ι_factorThruImage_of_idempotent (algebraNormalizedFirstEulerianChainMap k A M)
      (algebraNormalizedFirstEulerianChainMap_idempotent k A M)
    calc
      _ = image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
          algebraNormalizedFirstEulerianChainMap k A M ≫
            factorThruImage (algebraNormalizedFirstEulerianChainMap k A M) := by
        rw [Category.assoc, ← Category.assoc (algebraNormalizedPositiveProjection k A M),
          algebraNormalizedPositiveProjection_eulerianSection]
      _ = (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
          factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) ≫
            (image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫
              factorThruImage (algebraNormalizedFirstEulerianChainMap k A M)) := by
        have h := congrArg
          (fun t : algebraNormalizedChainComplex k A M ⟶ algebraNormalizedChainComplex k A M =>
            image.ι (algebraNormalizedFirstEulerianChainMap k A M) ≫ t ≫
              factorThruImage (algebraNormalizedFirstEulerianChainMap k A M))
          (image.fac (algebraNormalizedFirstEulerianChainMap k A M)).symm
        simp only [Category.assoc] at h ⊢
        exact h
      _ = 𝟙 _ := by rw [hi, Category.id_comp]

/-- The raw comparison maps a quotient through its first-projector
section and native image factor. -/
theorem algebraFirstEulerianQuotientIso_hom :
    (algebraFirstEulerianQuotientIso k A M).hom =
      algebraPositiveEulerianSection k A M ≫ factorThruImage (algebraFirstEulerianChainMap k A M) := rfl

/-- The image comparison returns by the original image inclusion and original quotient projection. -/
theorem algebraFirstEulerianQuotientIso_inv :
    (algebraFirstEulerianQuotientIso k A M).inv =
      image.ι (algebraFirstEulerianChainMap k A M) ≫ algebraRawPositiveProjection k A M := rfl

/-- Original normalization commutes with the two first-projector quotient sections. -/
@[reassoc]
theorem algebraPositiveEulerianSection_normalization :
    algebraPositiveEulerianSection k A M ≫ algebraNormalizationProjection k A M =
      algebraPositiveNormalization k A M ≫ algebraNormalizedPositiveEulerianSection k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext y
  refine Quotient.inductionOn' y ?_
  intro x
  exact DFunLike.congr_fun (algebraNormalizationLevelMap_firstEulerian k A M n) x

/-- The raw and normalized full first image complexes inherit the original normalization homotopy equivalence. -/
def algebraFirstEulerianImageNormalizationHomotopyEquiv :
    HomotopyEquiv (algebraFirstEulerianImageComplex k A M)
      (algebraNormalizedFirstEulerianImageComplex k A M) :=
  HomologicalComplex.homotopyEquivOnSplitImages
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId
    (image.ι (algebraFirstEulerianChainMap k A M)) (factorThruImage (algebraFirstEulerianChainMap k A M))
    (image_ι_factorThruImage_of_idempotent _ (algebraFirstEulerianChainMap_idempotent k A M))
    (image.ι (algebraNormalizedFirstEulerianChainMap k A M))
    (factorThruImage (algebraNormalizedFirstEulerianChainMap k A M))
    (image_ι_factorThruImage_of_idempotent _ (algebraNormalizedFirstEulerianChainMap_idempotent k A M))
    (by
      change (factorThruImage (algebraFirstEulerianChainMap k A M) ≫
          image.ι (algebraFirstEulerianChainMap k A M)) ≫ algebraNormalizationProjection k A M =
        algebraNormalizationProjection k A M ≫
          (factorThruImage (algebraNormalizedFirstEulerianChainMap k A M) ≫
            image.ι (algebraNormalizedFirstEulerianChainMap k A M))
      exact (congrArg (fun t => t ≫ algebraNormalizationProjection k A M)
        (image.fac (algebraFirstEulerianChainMap k A M))).trans
        ((algebraNormalizationProjection_firstEulerian k A M).symm.trans
          (congrArg (fun t => algebraNormalizationProjection k A M ≫ t)
            (image.fac (algebraNormalizedFirstEulerianChainMap k A M)).symm)))

end ModuleCat.Algebra.Hochschild.Symmetric
