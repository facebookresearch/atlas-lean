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

public import MathlibExt.Analysis.InnerProductSpace.Operator.HilbertAmplification
public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.CuntzFold

import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Positive finite matrix folds of the actual Hilbert Calkin algebra

The frame comes from actual basis-coordinate DATA, not a supplied fold/model.
The existing classStarMap carries both computed Cuntz laws to the same Calkin
carrier, and the existing general Cuntz fold supplies the matrix equivalence.
This is a fixed-H precursor, not the general stable-B/spatial identification
or an Ext/K₁ pairing/descent theorem. The finite index is genuinely positive.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace CalkinAlgebra

universe uI uH

variable {ι : Type uI} {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual quotient coordinate family satisfies every finite Gram relation. -/
theorem finiteClassFamily_orthogonal (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (i j : Fin N) :
    star (classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i)) *
        classStarMap (H := H) (HilbertAmplification.finiteFamily b e N j) =
      if i = j then 1 else 0 := by
  classical
  let q := classStarMap (H := H)
  calc
    _ = q (star (HilbertAmplification.finiteFamily b e N i) *
        HilbertAmplification.finiteFamily b e N j) := by
      rw [map_mul, map_star]
    _ = if i = j then 1 else 0 := by
      rw [(HilbertAmplification.finiteFamily_relations b e N).1 i j]
      split_ifs <;> simp only [map_one, map_zero]

/-- The actual quotient coordinate ranges partition the Calkin unit. -/
theorem finiteClassFamily_partition (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    (∑ i : Fin N,
      classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i) *
        star (classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i))) = 1 := by
  let q := classStarMap (H := H)
  calc
    _ = ∑ i : Fin N, q (HilbertAmplification.finiteFamily b e N i *
        star (HilbertAmplification.finiteFamily b e N i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_star]
    _ = q (∑ i : Fin N, HilbertAmplification.finiteFamily b e N i *
        star (HilbertAmplification.finiteFamily b e N i)) := (map_sum q _ _).symm
    _ = 1 := by rw [(HilbertAmplification.finiteFamily_relations b e N).2, map_one]

/-- The actual positive matrix identification from the computed coordinate family. -/
def finiteMatrixFold (b : HilbertBasis ι ℂ H) (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    CStarMatrix (Fin N) (Fin N) (CalkinAlgebra ℂ H) ≃⋆ₐ[ℂ] CalkinAlgebra ℂ H :=
  CuntzFamily.fold ℂ
    (fun i => classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i))
    (finiteClassFamily_orthogonal b e N) (finiteClassFamily_partition b e N)

/-- Literal ordered sum for the constructed quotient fold. -/
theorem finiteMatrixFold_apply (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+)
    (X : CStarMatrix (Fin N) (Fin N) (CalkinAlgebra ℂ H)) :
    finiteMatrixFold b e N X =
      ∑ i : Fin N, ∑ j : Fin N,
        classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i) *
          X i j *
          star (classStarMap (H := H) (HilbertAmplification.finiteFamily b e N j)) :=
  CuntzFamily.fold_apply ℂ _ _ _ X

/-- The inverse has the actual adjoint/class/operator sandwich entries. -/
theorem finiteMatrixFold_symm_apply_entry (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (z : CalkinAlgebra ℂ H) (i j : Fin N) :
    (finiteMatrixFold b e N).symm z i j =
      star (classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i)) *
        z * classStarMap (H := H) (HilbertAmplification.finiteFamily b e N j) :=
  CuntzFamily.fold_symm_apply_entry ℂ _ _ _ z i j

/-- Quotienting the actual ordered upstairs sum agrees with the constructed matrix fold. -/
theorem finiteMatrixFold_ofMatrix_classes (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (X : Fin N → Fin N → (H →L[ℂ] H)) :
    finiteMatrixFold b e N
        (CStarMatrix.ofMatrix (fun i j => classStarMap (H := H) (X i j))) =
      classStarMap (H := H)
        (∑ i : Fin N, ∑ j : Fin N,
          HilbertAmplification.finiteFamily b e N i * X i j *
            star (HilbertAmplification.finiteFamily b e N j)) := by
  rw [finiteMatrixFold_apply]
  have hEntry (i j : Fin N) :
      (CStarMatrix.ofMatrix (fun i j => classStarMap (H := H) (X i j)) :
        CStarMatrix (Fin N) (Fin N) (CalkinAlgebra ℂ H)) i j =
          classStarMap (H := H) (X i j) := rfl
  simp only [hEntry, map_sum, map_mul, map_star]

/-- The fold uses the actual operator metric under the coefficient's computed spectral order. -/
theorem finiteMatrixFold_isometry (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    letI : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _;
    letI : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _;
    Isometry (finiteMatrixFold b e N) := by
  let : PartialOrder (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CalkinAlgebra ℂ H) := CStarAlgebra.spectralOrderedRing _
  exact NonUnitalStarAlgHom.isometry (finiteMatrixFold b e N)
    (finiteMatrixFold b e N).injective

end CalkinAlgebra
