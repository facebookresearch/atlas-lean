/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianComplex
public import MathlibExt.Algebra.Homology.LocallyFiniteIdempotentImages
public import MathlibExt.Algebra.Homology.HomotopyEquivOnSplitImages

/-!
# Eulerian images and their normalization

For rational ground algebras, finite
complete Eulerian projectors give
complex and homology coproduct
decompositions. Restricting and
projecting the normalization section
and homotopy gives a homotopy
equivalence on each image; those
maps need not commute with the
Eulerian operators before projection.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The image of the original raw A-linear Eulerian chain map. -/
def algebraEulerianImageComplex (i : ℕ) : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraEulerianChainMap k A M i)

/-- The image of the original normalized A-linear Eulerian chain map. -/
def algebraNormalizedEulerianImageComplex (i : ℕ) :
    ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  image (algebraNormalizedEulerianChainMap k A M i)

/-- The original raw Eulerian chain-map component vanishes outside its degree support. -/
theorem algebraEulerianChainMap_support (n i : ℕ) (hi : n < i) :
    (algebraEulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  simp only [algebraEulerianChainMap_f, ModuleCat.hom_zero]
  exact algebraEulerianOperator_outside k A M n i hi

/-- The original normalized Eulerian chain-map component has the same degree support. -/
theorem algebraNormalizedEulerianChainMap_support (n i : ℕ) (hi : n < i) :
    (algebraNormalizedEulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  simp only [algebraNormalizedEulerianChainMap_f, ModuleCat.hom_zero]
  exact algebraNormalizedEulerianOperator_outside k A M n i hi

/-- The original raw Eulerian chain-map components sum to the identity in every degree. -/
theorem algebraEulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (algebraEulerianChainMap k A M i.val).f n) =
      𝟙 ((algebraRawComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, algebraEulerianChainMap_f]
  exact algebraEulerianOperator_sum k A M n

/-- The original normalized Eulerian chain-map components sum to the identity in every degree. -/
theorem algebraNormalizedEulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (algebraNormalizedEulerianChainMap k A M i.val).f n) =
      𝟙 ((algebraNormalizedChainComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, algebraNormalizedEulerianChainMap_f]
  exact algebraNormalizedEulerianOperator_sum k A M n

/-- Native raw Eulerian image inclusions give the all-degree A-linear Hodge decomposition. -/
def algebraHodgeComplexIso :
    (∐ (fun i : ℕ => algebraEulerianImageComplex k A M i)) ≅ algebraRawComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (algebraRawComplex k A M) (algebraEulerianChainMap k A M)
    (algebraEulerianChainMap_comp k A M) id
    (algebraEulerianChainMap_support k A M) (algebraEulerianChainMap_sum k A M)

/-- The raw Hodge map is exactly the native sum of the original Eulerian image inclusions. -/
theorem algebraHodgeComplexIso_hom :
    (algebraHodgeComplexIso k A M).hom =
      Sigma.desc (fun i => image.ι (algebraEulerianChainMap k A M i)) := rfl

/-- Native normalized Eulerian image inclusions give the normalized A-linear Hodge decomposition. -/
def algebraNormalizedHodgeComplexIso :
    (∐ (fun i : ℕ => algebraNormalizedEulerianImageComplex k A M i)) ≅
      algebraNormalizedChainComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (algebraNormalizedChainComplex k A M) (algebraNormalizedEulerianChainMap k A M)
    (algebraNormalizedEulerianChainMap_comp k A M) id
    (algebraNormalizedEulerianChainMap_support k A M) (algebraNormalizedEulerianChainMap_sum k A M)

/-- The raw Eulerian image homologies have an finite-projection coproduct inverse in each degree. -/
def algebraHodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (algebraEulerianImageComplex k A M i).homology n)) ≅
      (algebraRawComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (algebraRawComplex k A M) (algebraEulerianChainMap k A M)
    (algebraEulerianChainMap_comp k A M) id
    (algebraEulerianChainMap_support k A M) (algebraEulerianChainMap_sum k A M) n

/-- Each normalized homology degree has the normalized Eulerian image coproduct decomposition. -/
def algebraNormalizedHodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (algebraNormalizedEulerianImageComplex k A M i).homology n)) ≅
      (algebraNormalizedChainComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (algebraNormalizedChainComplex k A M) (algebraNormalizedEulerianChainMap k A M)
    (algebraNormalizedEulerianChainMap_comp k A M) id
    (algebraNormalizedEulerianChainMap_support k A M) (algebraNormalizedEulerianChainMap_sum k A M) n

/-- The raw homology decomposition uses exactly the original image inclusion homology maps. -/
theorem algebraHodgeHomologyIso_hom (n : ℕ) :
    (algebraHodgeHomologyIso k A M n).hom =
      Sigma.desc (fun i => HomologicalComplex.homologyMap
        (image.ι (algebraEulerianChainMap k A M i)) n) := rfl

/-- Each Eulerian image inherits the original A-linear normalization
homotopy equivalence from the normalization and projector square. -/
def algebraEulerianImageNormalizationHomotopyEquiv (i : ℕ) :
    HomotopyEquiv (algebraEulerianImageComplex k A M i)
      (algebraNormalizedEulerianImageComplex k A M i) :=
  HomologicalComplex.homotopyEquivOnSplitImages
    (algebraNormalizationProjection k A M) (algebraNormalizationInverse k A M)
    (algebraNormalizationInverse_projection k A M)
    (algebraNormalizationHomotopyEquiv k A M).homotopyHomInvId
    (image.ι (algebraEulerianChainMap k A M i)) (factorThruImage (algebraEulerianChainMap k A M i))
    (image_ι_factorThruImage_of_idempotent _
      (by
        have h := algebraEulerianChainMap_comp k A M i i
        simp only [ite_true] at h
        exact h))
    (image.ι (algebraNormalizedEulerianChainMap k A M i))
    (factorThruImage (algebraNormalizedEulerianChainMap k A M i))
    (image_ι_factorThruImage_of_idempotent _
      (by
        have h := algebraNormalizedEulerianChainMap_comp k A M i i
        simp only [ite_true] at h
        exact h))
    (by
      change (factorThruImage (algebraEulerianChainMap k A M i) ≫
          image.ι (algebraEulerianChainMap k A M i)) ≫ algebraNormalizationProjection k A M =
        algebraNormalizationProjection k A M ≫
          (factorThruImage (algebraNormalizedEulerianChainMap k A M i) ≫
            image.ι (algebraNormalizedEulerianChainMap k A M i))
      exact (congrArg (fun t => t ≫ algebraNormalizationProjection k A M)
        (image.fac (algebraEulerianChainMap k A M i))).trans
        ((algebraNormalizationProjection_eulerian k A M i).symm.trans
          (congrArg (fun t => algebraNormalizationProjection k A M ≫ t)
            (image.fac (algebraNormalizedEulerianChainMap k A M i)).symm)))

/-- The image normalization map is the original image inclusion, original
normalization and original normalized image factor, in that order. -/
theorem algebraEulerianImageNormalizationHomotopyEquiv_hom (i : ℕ) :
    (algebraEulerianImageNormalizationHomotopyEquiv k A M i).hom =
      image.ι (algebraEulerianChainMap k A M i) ≫ algebraNormalizationProjection k A M ≫
        factorThruImage (algebraNormalizedEulerianChainMap k A M i) := rfl

/-- The projected original section gives normalization invariance
of every original A-linear Eulerian homology degree. -/
def algebraEulerianImageNormalizationHomologyIso (n i : ℕ) :
    (algebraEulerianImageComplex k A M i).homology n ≅
      (algebraNormalizedEulerianImageComplex k A M i).homology n :=
  (algebraEulerianImageNormalizationHomotopyEquiv k A M i).toHomologyIso n

end ModuleCat.Algebra.Hochschild.Symmetric
