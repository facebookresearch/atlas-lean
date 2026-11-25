/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Tactic.Linarith

/-!
# Row permutations preserve the C-star matrix metric

Only the rows are permuted. The proof preserves the actual Gram matrix
`star X * X` and uses the C-star norm law; the row map is not treated as
an algebra equivalence. The coefficient algebra may be zero, nonunital
or noncommutative, and the square index may be empty.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace CStarMatrix

universe u v

/-- Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type. For `p : ι ≃ ι`.
Use the spectral order on `A`. A permutation of the rows of a square C-star matrix is an isometry
for the operator metric, with the coefficient's computed spectral order.
-/
theorem isometry_reindexₗ_rows
    {A : Type u} [NonUnitalCStarAlgebra A]
    {ι : Type v} [Fintype ι] (p : ι ≃ ι) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A;
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A;
    Isometry (reindexₗ ℂ A p (Equiv.refl ι) :
      CStarMatrix ι ι A → CStarMatrix ι ι A) := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let e : CStarMatrix ι ι A ≃ₗ[ℂ] CStarMatrix ι ι A :=
    reindexₗ ℂ A p (Equiv.refl ι)
  have hNorm : ∀ X : CStarMatrix ι ι A, ‖e X‖ = ‖X‖ := by
    intro X
    have hGram : star (e X) * e X = star X * X := by
      apply CStarMatrix.ext
      intro i j
      change (∑ k : ι, star (X (p.symm k) i) * X (p.symm k) j) =
        ∑ k : ι, star (X k i) * X k j
      exact Fintype.sum_equiv p.symm _ _ (fun _ => rfl)
    have hSquare : ‖e X‖ * ‖e X‖ = ‖X‖ * ‖X‖ := by
      calc
        ‖e X‖ * ‖e X‖ = ‖star (e X) * e X‖ :=
          (CStarRing.norm_star_mul_self (x := e X)).symm
        _ = ‖star X * X‖ := congrArg norm hGram
        _ = ‖X‖ * ‖X‖ := CStarRing.norm_star_mul_self (x := X)
    nlinarith only [hSquare, norm_nonneg (e X), norm_nonneg X]
  let eIso : CStarMatrix ι ι A →ₗᵢ[ℂ] CStarMatrix ι ι A :=
    { toLinearMap := e.toLinearMap
      norm_map' := hNorm }
  exact eIso.isometry

end CStarMatrix
