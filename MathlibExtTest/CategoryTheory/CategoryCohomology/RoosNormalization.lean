/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosNormalization

/-!
# Normalized Roos coefficient maps and cohomology

These clients compare coefficient maps under normalization and use the
normalization inclusion to transport Roos cohomology.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosNormalizationTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A] [HasProducts.{max u₁ v₁} A]

/-- An actual coefficient map commutes with the actual cochain projection. -/
example {M N : I ⥤ A} (α : M ⟶ N) :
    (roosComplexFunctor (I := I) (A := A)).map α ≫
        (roosNormalizationProjection (I := I) (A := A)).app N =
      (roosNormalizationProjection (I := I) (A := A)).app M ≫
        (normalizedRoosComplexFunctor (I := I) (A := A)).map α :=
  (roosNormalizationProjection (I := I) (A := A)).naturality α

/-- The actual normalized inclusion computes the original native Roos cohomology. -/
example (M : I ⥤ A) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((inclusionOfNormalizedRoosComplex (I := I) (A := A)).app M) n) := by
  infer_instance

end RoosNormalizationTests

end
