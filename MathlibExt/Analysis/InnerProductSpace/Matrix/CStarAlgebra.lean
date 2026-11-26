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
# Operator matrices on finite Hilbert products

Let H be a Hilbert space over an RCLike field 𝕜 and I finite. The operator-valued matrix
action Θ(A):H^I→H^I is (Θ(A)v)_i=∑j A_ij(v_j), with the Hilbert ℓ² product norm. Its inverse
reads A_ij=proj_i∘T∘single_j. This is a star-algebra equivalence. For complex H, the
CStarMatrix version is isometric for its C-star matrix norm and the operator norm on H^I,
including zero H and empty I.
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

/-- **Star-algebra equivalence of operator matrices and finite block operators.**

Let H be a Hilbert space over an RCLike field 𝕜 and I finite. The operator-valued matrix
action Θ(A):H^I→H^I is (Θ(A)v)_i=∑j A_ij(v_j), with the Hilbert ℓ² product norm. Its inverse
reads A_ij=proj_i∘T∘single_j. The equivalence Matrix.piLpStarAlgEquiv:M_I(B(H))≃⋆ₐ[𝕜]B(H^I) is
Θ.
-/
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

/-- **Column formula of the operator-matrix equivalence.**

Let H be a Hilbert space over an RCLike field 𝕜 and I finite. The operator-valued matrix
action Θ(A):H^I→H^I is (Θ(A)v)_i=∑j A_ij(v_j), with the Hilbert ℓ² product norm. Its inverse
reads A_ij=proj_i∘T∘single_j. For A and v∈H^I, piLpStarAlgEquiv A v i=∑j A_ij(v_j).
-/
@[simp]
theorem piLpStarAlgEquiv_apply (M : Matrix n n (H →L[𝕜] H))
    (v : PiLp 2 (fun _ : n => H)) (i : n) :
    piLpStarAlgEquiv (𝕜 := 𝕜) (n := n) (H := H) M v i = ∑ j : n, M i j (v j) := by
  change toPiLpContinuousLinearMap M v i = _
  exact toPiLpContinuousLinearMap_apply M v i

/-- **Inverse entries of the finite Hilbert block equivalence.**

Let H be a Hilbert space over an RCLike field 𝕜 and I finite. The operator-valued matrix
action Θ(A):H^I→H^I is (Θ(A)v)_i=∑j A_ij(v_j), with the Hilbert ℓ² product norm. Its inverse
reads A_ij=proj_i∘T∘single_j. For T∈B(H^I), (piLpStarAlgEquiv⁻¹ T)_ij(x)=proj_i(T(single_j
x)).
-/
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

/-- **Complex C-star matrix equivalence on a finite Hilbert product.**

Let H be a complex Hilbert space,I finite and H^I the ℓ² Hilbert product. The equivalence
CStarMatrix.piLpStarAlgEquiv:CStarMatrix I I B(H)≃⋆ₐ[ℂ]B(H^I) acts by column sums
(Θ(X)v)_i=∑jX_ij(v_j).
-/
def piLpStarAlgEquiv :
    CStarMatrix n n (H →L[ℂ] H) ≃⋆ₐ[ℂ]
      ((PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H))) :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := n) (A := H →L[ℂ] H)).symm.trans
    (Matrix.piLpStarAlgEquiv (𝕜 := ℂ) (n := n) (H := H))

/-- **Column formula of the C-star matrix equivalence.**

For complex Hilbert H,I finite,X∈CStarMatrix I I B(H) and v∈H^I, CStarMatrix.piLpStarAlgEquiv
X v i=∑jX_ij(v_j).
-/
@[simp]
theorem piLpStarAlgEquiv_apply (X : CStarMatrix n n (H →L[ℂ] H))
    (v : PiLp 2 (fun _ : n => H)) (i : n) :
    piLpStarAlgEquiv (n := n) (H := H) X v i = ∑ j : n, X i j (v j) := by
  change Matrix.toPiLpContinuousLinearMap (CStarMatrix.ofMatrix.symm X) v i = _
  exact Matrix.toPiLpContinuousLinearMap_apply (CStarMatrix.ofMatrix.symm X) v i

/-- **Recovered entries of the C-star matrix inverse.**

For complex Hilbert H,I finite and T∈B(H^I), the inverse C-star matrix has entry
x↦proj_i(T(single_j x)).
-/
@[simp]
theorem piLpStarAlgEquiv_symm_apply_entry
    (T : PiLp 2 (fun _ : n => H) →L[ℂ] PiLp 2 (fun _ : n => H))
    (i j : n) (x : H) :
    (piLpStarAlgEquiv (n := n) (H := H)).symm T i j x = T (PiLp.single 2 j x) i := by
  change ContinuousLinearMap.toPiLpMatrix T i j x = _
  exact ContinuousLinearMap.toPiLpMatrix_apply T i j x

/-- **Isometry of the finite Hilbert operator-matrix equivalence.**

Let H be a complex Hilbert space and I finite. The equivalence Θ:CStarMatrix I I B(H)→B(H^I)
is an isometry for the canonical C-star matrix metric and Hilbert operator metric.
-/
theorem piLpStarAlgEquiv_isometry :
    letI : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _;
    Isometry (piLpStarAlgEquiv (n := n) (H := H)) := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let e := piLpStarAlgEquiv (n := n) (H := H)
  exact NonUnitalStarAlgHom.isometry e.toNonUnitalStarAlgHom e.injective

/-- **Norm of a C-star operator matrix equals its block operator norm.**

Let H be a complex Hilbert space,I finite and X∈CStarMatrix I I B(H). Then
‖CStarMatrix.piLpStarAlgEquiv X‖=‖X‖, using the operator norm on H^I and canonical C-star
matrix norm.
-/
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
