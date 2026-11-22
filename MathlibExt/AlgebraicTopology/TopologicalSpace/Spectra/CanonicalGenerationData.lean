/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Data
import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamilyReindex
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Basic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex

/-!
# Actual generation data on the three canonical spectrum indices

Each record is the existing native model's generation value on its actual
enriched index, at the original cardinal and caller bottom. Original
degree-labelled free images identify the same entire native families.
No model, adjunction, or factor algorithm is reconstructed.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.CanonicalGeneration

open HomotopicalAlgebra.EnrichedProjective
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual sequential generation record on the existing one-sphere native model. -/
def sequential :
    letI : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      Native.modelCategory (A := Sequential.Index.{u, v})
    CofibrantGenerationData PointedCGWH.SequentialSpectrum.{u, v}
      realizedGeneratorCardinal.{v} :=
  Native.Data.generationData (A := Sequential.Index.{u, v})

/-- The actual symmetric generation record keeps the complete original operator index. -/
def symmetric :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
      Native.modelCategory (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
    CofibrantGenerationData
      (EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
      realizedGeneratorCardinal.{v} :=
  Native.Data.generationData (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The actual orthogonal generation record keeps the full original continuous coend Homs. -/
def orthogonal :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :=
      Native.modelCategory (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    CofibrantGenerationData
      (EnrichedFunctorCat PointedCGWH.{u, v} CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
      realizedGeneratorCardinal.{v} :=
  Native.Data.generationData (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})

omit B in
/-- Original natural degrees cover the actual sequential enriched index. -/
theorem sequentialDegree_surjective :
    Function.Surjective
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v}) := by
  rintro ⟨n⟩
  exact ⟨n, rfl⟩

omit B in
/-- Original finite-bijection labels cover the actual symmetric sphere operator objects. -/
theorem symmetricObject_surjective :
    Function.Surjective PointedCGWH.symmetricOperatorObj.{u, v} := by
  rintro ⟨n⟩
  exact ⟨(show CategoryTheory.Operad.SmallFinBijGroupoid from n), rfl⟩

omit B in
/-- Original dimensions cover the actual continuous orthogonal sphere operator objects. -/
theorem orthogonalObject_surjective :
    Function.Surjective CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex.{u, v} := by
  rintro ⟨n⟩
  exact ⟨n, rfl⟩

/-- The sequential boundary family retains exactly its original natural degree/base labels. -/
theorem sequential_I :
    letI : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      Native.modelCategory (A := Sequential.Index.{u, v})
    sequential.{u, v}.I =
      adjointFamilyGenerators
        (fun n : ℕ => EnrichedFunctorCat.Free.functor
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n))
        PointedCGWH.realizedBoundaryInclusions.{u, v} := by
  let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    Native.modelCategory (A := Sequential.Index.{u, v})
  change generators (A := Sequential.Index.{u, v}) PointedCGWH.realizedBoundaryInclusions = _
  exact (adjointFamilyGenerators_reindex _ sequentialDegree_surjective _ _).symm

/-- The sequential horn family retains every original natural degree and horn arrow. -/
theorem sequential_J :
    letI : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      Native.modelCategory (A := Sequential.Index.{u, v})
    sequential.{u, v}.J =
      adjointFamilyGenerators
        (fun n : ℕ => EnrichedFunctorCat.Free.functor
          (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n))
        PointedCGWH.realizedHornInclusions.{u, v} := by
  let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
    Native.modelCategory (A := Sequential.Index.{u, v})
  change generators (A := Sequential.Index.{u, v}) PointedCGWH.realizedHornInclusions = _
  exact (adjointFamilyGenerators_reindex _ sequentialDegree_surjective _ _).symm

/-- The symmetric boundary family retains all original finite-bijection/base-arrow labels. -/
theorem symmetric_I :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
      Native.modelCategory (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
    symmetric.{u, v}.I =
      adjointFamilyGenerators
        (fun n : CategoryTheory.Operad.SmallFinBijGroupoid =>
          EnrichedFunctorCat.Free.functor (PointedCGWH.symmetricOperatorObj n))
        PointedCGWH.realizedBoundaryInclusions.{u, v} := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) := Native.modelCategory
  change generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
    PointedCGWH.realizedBoundaryInclusions = _
  exact (adjointFamilyGenerators_reindex _ symmetricObject_surjective _ _).symm

/-- The symmetric horn family retains every original finite-bijection and horn arrow. -/
theorem symmetric_J :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
      Native.modelCategory (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
    symmetric.{u, v}.J =
      adjointFamilyGenerators
        (fun n : CategoryTheory.Operad.SmallFinBijGroupoid =>
          EnrichedFunctorCat.Free.functor (PointedCGWH.symmetricOperatorObj n))
        PointedCGWH.realizedHornInclusions.{u, v} := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    PointedCGWH.SymmetricOperatorIndex.{u, v}) := Native.modelCategory
  change generators (A := PointedCGWH.SymmetricOperatorIndex.{u, v})
    PointedCGWH.realizedHornInclusions = _
  exact (adjointFamilyGenerators_reindex _ symmetricObject_surjective _ _).symm

/-- The orthogonal boundary family retains every original dimension and base arrow. -/
theorem orthogonal_I :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :=
      Native.modelCategory (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    orthogonal.{u, v}.I =
      adjointFamilyGenerators
        (fun n : CategoryTheory.Spectra.OrthogonalIndex =>
          EnrichedFunctorCat.Free.functor
            (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n))
        PointedCGWH.realizedBoundaryInclusions.{u, v} := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) := Native.modelCategory
  change generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    PointedCGWH.realizedBoundaryInclusions = _
  exact (adjointFamilyGenerators_reindex _ orthogonalObject_surjective _ _).symm

/-- The orthogonal horn family retains every original dimension and horn arrow. -/
theorem orthogonal_J :
    letI : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
      CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :=
      Native.modelCategory (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    orthogonal.{u, v}.J =
      adjointFamilyGenerators
        (fun n : CategoryTheory.Spectra.OrthogonalIndex =>
          EnrichedFunctorCat.Free.functor
            (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n))
        PointedCGWH.realizedHornInclusions.{u, v} := by
  let _ : ModelCategory (EnrichedFunctorCat PointedCGWH.{u, v}
    CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) := Native.modelCategory
  change generators (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    PointedCGWH.realizedHornInclusions = _
  exact (adjointFamilyGenerators_reindex _ orthogonalObject_surjective _ _).symm

end PointedCGWH.Spectra.CanonicalGeneration
