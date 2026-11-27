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

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# Continuous functions and finite C-star matrices

Interchanging the continuous-function variable with the two finite matrix
indices preserves the actual matrix multiplication and conjugate transpose.
The construction uses the public product-topology port of `CStarMatrix`;
it does not give matrices an entrywise replacement norm.

The algebraic equivalence does not require compactness of the domain.
For compact domains the existing C-star instances and `StarAlgEquiv.norm_map`
also give its norm preservation, with no separate norm construction.
-/

@[expose] public section

namespace CStarMatrix

universe uX uι uA

/-- Let `X` be a topological space, `ι` a finite index type and `A` a possibly nonunital complex
C*-algebra. Using the spectral order on `A`, entrywise evaluation gives a complex star-algebra
equivalence between `ι × ι` matrices of continuous functions `X → A` and continuous functions `X →
CStarMatrix ι ι A`. The index type and the space may be empty.
-/
noncomputable def continuousMapStarAlgEquiv
    (X : Type uX) [TopologicalSpace X]
    (ι : Type uι) [Fintype ι]
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A;
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A;
    CStarMatrix ι ι C(X, A) ≃⋆ₐ[ℂ] C(X, CStarMatrix ι ι A) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact {
    toFun M :=
      { toFun x := ofMatrix fun i j => M i j x
        continuous_toFun :=
          (ofMatrixL : Matrix ι ι A ≃L[ℂ] CStarMatrix ι ι A).continuous.comp
            (ContinuousMap.pi fun i : ι =>
              ContinuousMap.pi fun j : ι => M i j).continuous }
    invFun f :=
      ofMatrix fun i j =>
        { toFun x := f x i j
          continuous_toFun :=
            ((ofMatrixL : Matrix ι ι A ≃L[ℂ] CStarMatrix ι ι A).symm.continuous.comp
              f.continuous).matrix_elem i j }
    left_inv M := by
      apply CStarMatrix.ext
      intro i j
      apply ContinuousMap.ext
      intro x
      rfl
    right_inv f := by
      apply ContinuousMap.ext
      intro x
      apply CStarMatrix.ext
      intro i j
      rfl
    map_add' M N := by
      apply ContinuousMap.ext
      intro x
      apply CStarMatrix.ext
      intro i j
      rfl
    map_mul' M N := by
      apply ContinuousMap.ext
      intro x
      apply CStarMatrix.ext
      intro i j
      change (∑ k : ι, M i k * N k j) x = ∑ k : ι, M i k x * N k j x
      simpa only [ContinuousMap.mul_apply] using
        (ContinuousMap.sum_apply Finset.univ (fun k : ι => M i k * N k j) x)
    map_star' M := by
      apply ContinuousMap.ext
      intro x
      apply CStarMatrix.ext
      intro i j
      rfl
    map_smul' z M := by
      apply ContinuousMap.ext
      intro x
      apply CStarMatrix.ext
      intro i j
      rfl }

/-- Let `X` be a topological space. Let `ι` be a finite index type. Let `A` be a possibly nonunital
complex C*-algebra. For `M : CStarMatrix ι ι C(X, A)`, `x : X` and `i` and `j : ι`. Use the spectral
order on `A`. The forward equivalence evaluates each continuous matrix entry at the same point,
without changing its row or column.
-/
@[simp]
theorem continuousMapStarAlgEquiv_apply
    (X : Type uX) [TopologicalSpace X]
    (ι : Type uι) [Fintype ι]
    (A : Type uA) [NonUnitalCStarAlgebra A]
    (M : CStarMatrix ι ι C(X, A)) (x : X) (i j : ι) :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A;
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A;
    continuousMapStarAlgEquiv X ι A M x i j = M i j x := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rfl

/-- Let `X` be a topological space. Let `ι` be a finite index type. Let `A` be a possibly nonunital
complex C*-algebra. Use the spectral order on `A`. The inverse equivalence takes the continuous
row-column coefficient of the matrix-valued function.
-/
@[simp]
theorem continuousMapStarAlgEquiv_symm_apply
    (X : Type uX) [TopologicalSpace X]
    (ι : Type uι) [Fintype ι]
    (A : Type uA) [NonUnitalCStarAlgebra A] :
    letI : PartialOrder A := CStarAlgebra.spectralOrder A;
    letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A;
    ∀ (f : C(X, CStarMatrix ι ι A)) (i j : ι) (x : X),
      (continuousMapStarAlgEquiv X ι A).symm f i j x = f x i j := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  intro f i j x
  rfl

end CStarMatrix
