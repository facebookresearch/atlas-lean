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

public import MathlibExt.Analysis.InnerProductSpace.Matrix.Adjoint
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Operator matrices on the finite Hilbert product

The existing column action and coordinate recovery form the actual star-algebra
equivalence on finite PiLp products. Its raw algebraic version uses RCLike scalars;
the CStarMatrix norm/isometry statements are complex-only and use the coefficient's
computed spectral order. No norm is transported from ordinary Matrix.

Empty index types and zero Hilbert spaces are allowed. No Hilbert tensor,
compact-quotient, entrywise-normality or source classification is asserted here.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

universe uScalar uIndex uHilbert

namespace Matrix

variable {𝕜 : Type uScalar} [RCLike 𝕜]
variable {n : Type uIndex} [Fintype n] [DecidableEq n]
variable {H : Type uHilbert} [NormedAddCommGroup H]
variable [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The existing finite column action and coordinate recovery, as a star-algebra
equivalence. Operator multiplication is composition, in the original order. -/
def piLpStarAlgEquiv :
    Matrix n n (H →L[𝕜] H) ≃⋆ₐ[𝕜]
      ((PiLp 2 (fun _ : n => H)) →L[𝕜] (PiLp 2 (fun _ : n => H))) :=
  { Matrix.piLpContinuousLinearMapEquiv (R := 𝕜) (m := n) (n := n) (E := H) (F := H) with
    map_add' := by
      intro M N
      change toPiLpContinuousLinearMap (M + N) =
        toPiLpContinuousLinearMap M + toPiLpContinuousLinearMap N
      apply ContinuousLinearMap.ext
      intro v
      apply PiLp.ext
      intro i
      simp only [toPiLpContinuousLinearMap_apply, Matrix.add_apply, _root_.add_apply,
        PiLp.add_apply, Finset.sum_add_distrib]
    map_mul' := by
      intro M N
      change toPiLpContinuousLinearMap (M * N) =
        toPiLpContinuousLinearMap M * toPiLpContinuousLinearMap N
      exact toPiLpContinuousLinearMap_mul M N
    map_star' := by
      intro M
      change toPiLpContinuousLinearMap (star M) = star (toPiLpContinuousLinearMap M)
      have hStar :
          (M.map fun T : H →L[𝕜] H => ContinuousLinearMap.adjoint T).transpose = star M := by
        apply Matrix.ext
        intro i j
        rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.star_apply]
        exact (ContinuousLinearMap.star_eq_adjoint (M j i)).symm
      rw [ContinuousLinearMap.star_eq_adjoint, toPiLpContinuousLinearMap_adjoint M, hStar]
    map_smul' := by
      intro c M
      change toPiLpContinuousLinearMap (c • M) = c • toPiLpContinuousLinearMap M
      apply ContinuousLinearMap.ext
      intro v
      apply PiLp.ext
      intro i
      simp only [toPiLpContinuousLinearMap_apply, Matrix.smul_apply, _root_.smul_apply,
        PiLp.smul_apply, Finset.smul_sum] }

/-- The bundled map retains the literal column-sum value. -/
@[simp]
theorem piLpStarAlgEquiv_apply (M : Matrix n n (H →L[𝕜] H))
    (v : PiLp 2 (fun _ : n => H)) (i : n) :
    piLpStarAlgEquiv (𝕜 := 𝕜) (n := n) (H := H) M v i = ∑ j : n, M i j (v j) := by
  change toPiLpContinuousLinearMap M v i = _
  exact toPiLpContinuousLinearMap_apply M v i

/-- The inverse coefficients are the existing coordinate injection/projection maps. -/
@[simp]
theorem piLpStarAlgEquiv_symm_apply_entry
    (T : PiLp 2 (fun _ : n => H) →L[𝕜] PiLp 2 (fun _ : n => H))
    (i j : n) (x : H) :
    (piLpStarAlgEquiv (𝕜 := 𝕜) (n := n) (H := H)).symm T i j x = T (PiLp.single 2 j x) i := by
  change ContinuousLinearMap.toPiLpMatrix T i j x = _
  exact ContinuousLinearMap.toPiLpMatrix_apply T i j x

end Matrix

namespace CStarMatrix

variable {n : Type uIndex} [Fintype n] [DecidableEq n]
variable {H : Type uHilbert} [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual C-star operator-matrix equivalence on the finite Hilbert product.
The type-copy transport is algebraic; the norm comparison is proved separately. -/
def piLpStarAlgEquiv :
    CStarMatrix n n (H →L[ℂ] H) ≃⋆ₐ[ℂ]
      ((PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H))) :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := H →L[ℂ] H)).symm.trans
    (Matrix.piLpStarAlgEquiv (𝕜 := ℂ) (n := n) (H := H))

/-- The C-star copy acts by the same actual operator column sum. -/
@[simp]
theorem piLpStarAlgEquiv_apply (X : CStarMatrix n n (H →L[ℂ] H))
    (v : PiLp 2 (fun _ : n => H)) (i : n) :
    piLpStarAlgEquiv (n := n) (H := H) X v i = ∑ j : n, X i j (v j) := by
  change Matrix.toPiLpContinuousLinearMap (CStarMatrix.ofMatrix.symm X) v i = _
  exact Matrix.toPiLpContinuousLinearMap_apply (CStarMatrix.ofMatrix.symm X) v i

/-- The inverse has the literal recovered continuous-linear coefficient maps. -/
@[simp]
theorem piLpStarAlgEquiv_symm_apply_entry
    (T : PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H))
    (i j : n) (x : H) :
    (piLpStarAlgEquiv (n := n) (H := H)).symm T i j x = T (PiLp.single 2 j x) i := by
  change ContinuousLinearMap.toPiLpMatrix T i j x = _
  exact ContinuousLinearMap.toPiLpMatrix_apply T i j x

/-- The constructed equivalence preserves the actual C-star/Hilbert operator metric. -/
theorem piLpStarAlgEquiv_isometry :
    letI : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _;
    Isometry (piLpStarAlgEquiv (n := n) (H := H)) := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let e := piLpStarAlgEquiv (n := n) (H := H)
  exact NonUnitalStarAlgHom.isometry e.toNonUnitalStarAlgHom e.injective

/-- The norm here is the CStarMatrix operator norm, not a plain matrix row norm. -/
theorem piLpStarAlgEquiv_norm_map :
    letI : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _;
    ∀ X : CStarMatrix n n (H →L[ℂ] H),
      ‖piLpStarAlgEquiv (n := n) (H := H) X‖ = ‖X‖ := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let e := piLpStarAlgEquiv (n := n) (H := H)
  exact fun X : CStarMatrix n n (H →L[ℂ] H) =>
    NonUnitalStarAlgHom.norm_map e.toNonUnitalStarAlgHom e.injective X

end CStarMatrix

end
