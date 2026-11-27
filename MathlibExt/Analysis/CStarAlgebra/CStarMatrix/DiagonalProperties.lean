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
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Units and projections in finite diagonal C-star matrix copies

These algebraic facts use the actual matrix multiplication and do not require
a norm, completeness, coefficient commutativity, or a nonempty index.
-/

@[expose] public section

namespace CStarMatrix

universe uI uR

variable {ι : Type uI} {R : Type uR} [Fintype ι] [DecidableEq ι]

/-- Let `ι` be a finite index type with decidable equality. Let `R` be a semiring. For `d : ι → R`.
Assume `∀ i, IsUnit (d i)`. A finite diagonal with unit entries is a unit, also over noncommutative
coefficients.
-/
theorem isUnit_ofMatrix_diagonal [Semiring R] (d : ι → R) (hd : ∀ i, IsUnit (d i)) :
    IsUnit (ofMatrix (Matrix.diagonal d)) := by
  classical
  choose u hu using hd
  let w : (CStarMatrix ι ι R)ˣ :=
    { val := ofMatrix (Matrix.diagonal d)
      inv := ofMatrix (Matrix.diagonal (fun i => ((u i)⁻¹ : Rˣ)))
      val_inv := by
        rw [of_mul_of, Matrix.diagonal_mul_diagonal]
        have h : (fun i => d i * ((u i)⁻¹ : Rˣ)) = fun _ => (1 : R) := by
          funext i
          rw [← hu i]
          exact (u i).val_inv
        rw [h]
        rfl
      inv_val := by
        rw [of_mul_of, Matrix.diagonal_mul_diagonal]
        have h : (fun i => ((u i)⁻¹ : Rˣ) * d i) = fun _ => (1 : R) := by
          funext i
          rw [← hu i]
          exact (u i).inv_val
        rw [h]
        rfl }
  exact w.isUnit

/-- Let `ι` be a finite index type with decidable equality. Let `R` be a possibly nonunital semiring.
The star on `R` is an additive involution reversing products. For `d : ι → R`. Assume `∀ i,
IsStarProjection (d i)`. A finite diagonal of star projections is a star projection in the matrix
copy.
-/
theorem isStarProjection_ofMatrix_diagonal [NonUnitalSemiring R] [StarRing R]
    (d : ι → R) (hd : ∀ i, IsStarProjection (d i)) :
    IsStarProjection (ofMatrix (Matrix.diagonal d)) := by
  refine ⟨?_, ?_⟩
  · change ofMatrix (Matrix.diagonal d) * ofMatrix (Matrix.diagonal d) =
      ofMatrix (Matrix.diagonal d)
    rw [of_mul_of, Matrix.diagonal_mul_diagonal]
    exact congrArg ofMatrix
      (congrArg Matrix.diagonal (funext fun i => (hd i).isIdempotentElem.eq))
  · change star (ofMatrix (Matrix.diagonal d)) = ofMatrix (Matrix.diagonal d)
    apply CStarMatrix.ext
    intro i j
    rw [CStarMatrix.star_apply]
    change star (Matrix.diagonal d j i) = Matrix.diagonal d i j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using (hd i).isSelfAdjoint.star_eq
    · simp only [Matrix.diagonal_apply, hij, Ne.symm hij, ↓reduceIte, star_zero]

end CStarMatrix
