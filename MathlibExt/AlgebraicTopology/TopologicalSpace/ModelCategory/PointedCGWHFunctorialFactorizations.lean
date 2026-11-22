/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated

/-!
# Functorial factorizations for pointed CGWH spaces

The selected pointed CGWH cofibrant-generation datum supplies both standard
functorial factorizations inside the existing CGWH model-category scope.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra

open scoped CGWH.modelCategory

namespace CGWH.modelCategory

noncomputable scoped instance
    instPointedCGWHHasFunctorialFactorizationCofibrationsTrivialFibrations :
    HasFunctorialFactorization (cofibrations PointedCGWH.{u, v})
      (trivialFibrations PointedCGWH.{u, v}) :=
  CofibrantGenerationData.hasFunctorialFactorizationCofibrationsTrivialFibrations
    PointedCGWH.cofibrantGenerationData

noncomputable scoped instance
    instPointedCGWHHasFunctorialFactorizationTrivialCofibrationsFibrations :
    HasFunctorialFactorization (trivialCofibrations PointedCGWH.{u, v})
      (fibrations PointedCGWH.{u, v}) :=
  CofibrantGenerationData.hasFunctorialFactorizationTrivialCofibrationsFibrations
    PointedCGWH.cofibrantGenerationData

end CGWH.modelCategory
