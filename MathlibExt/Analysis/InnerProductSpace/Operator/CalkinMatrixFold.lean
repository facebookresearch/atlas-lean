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
# Finite matrix folds of a Hilbert-space Calkin algebra

Let `H` be a complete complex Hilbert space with a Hilbert basis `b_i` and an index bijection
`Fin 2 × ι ≃ ι`. For any positive finite size `N`, its coordinate construction gives Cuntz
isometries `S_i`. Their Calkin classes `c_i=[S_i]` satisfy `c_i* c_j=δ_ij I` and `Σ_i c_i
c_i*=I`.

The complex star equivalence `M_N(Q(H)) ≃ Q(H)` has forward formula `X ↦ Σ_i,j c_i X_ij c_j*`
and inverse entries `z ↦ c_i* z c_j`. It preserves the C-star metrics, and quotienting the
corresponding bounded-operator sum agrees with this fold. The index `N` is positive.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace CalkinAlgebra

universe uI uH

variable {ι : Type uI} {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Calkin Gram relations of the finite coordinate family.** Let `H` be a complete complex
Hilbert space with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 ×
ι ≃ ι`, and `N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting
each last leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. for `i,j ∈ Fin N`, `c_i* c_j=I` when `i=j` and zero otherwise. -/
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

/-- **Finite coordinate classes partition the Calkin unit.** Let `H` be a complete complex
Hilbert space with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 ×
ι ≃ ι`, and `N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting
each last leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. `Σ_i∈Fin N c_i c_i*=I_(Q(H))`. -/
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

/-- **Finite matrix star equivalence of the Calkin algebra.** Let `H` be a complete complex
Hilbert space with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 ×
ι ≃ ι`, and `N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting
each last leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. `finiteMatrixFold b e N : M_N(Q(H)) ≃⋆ₐ[ℂ] Q(H)` sends `X` to `Σ_i,j c_i
X_ij c_j*`, with inverse entries `c_i* z c_j`. -/
def finiteMatrixFold (b : HilbertBasis ι ℂ H) (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) :
    CStarMatrix (Fin N) (Fin N) (CalkinAlgebra ℂ H) ≃⋆ₐ[ℂ] CalkinAlgebra ℂ H :=
  CuntzFamily.fold ℂ
    (fun i => classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i))
    (finiteClassFamily_orthogonal b e N) (finiteClassFamily_partition b e N)

/-- **Ordered sum of the finite Calkin matrix fold.** Let `H` be a complete complex Hilbert
space with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 × ι ≃ ι`,
and `N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting each last
leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. for `X ∈ M_N(Q(H))`, `finiteMatrixFold b e N X=Σ_i,j∈Fin N c_i X_ij
c_j*`. -/
theorem finiteMatrixFold_apply (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+)
    (X : CStarMatrix (Fin N) (Fin N) (CalkinAlgebra ℂ H)) :
    finiteMatrixFold b e N X =
      ∑ i : Fin N, ∑ j : Fin N,
        classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i) *
          X i j *
          star (classStarMap (H := H) (HilbertAmplification.finiteFamily b e N j)) :=
  CuntzFamily.fold_apply ℂ _ _ _ X

/-- **Inverse entry of the finite Calkin fold.** Let `H` be a complete complex Hilbert space
with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 × ι ≃ ι`, and
`N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting each last
leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. for `z ∈ Q(H)` and `i,j ∈ Fin N`, `(finiteMatrixFold b e N).symm z i
j=c_i* z c_j`. -/
theorem finiteMatrixFold_symm_apply_entry (b : HilbertBasis ι ℂ H)
    (e : (Fin 2 × ι) ≃ ι) (N : ℕ+) (z : CalkinAlgebra ℂ H) (i j : Fin N) :
    (finiteMatrixFold b e N).symm z i j =
      star (classStarMap (H := H) (HilbertAmplification.finiteFamily b e N i)) *
        z * classStarMap (H := H) (HilbertAmplification.finiteFamily b e N j) :=
  CuntzFamily.fold_symm_apply_entry ℂ _ _ _ z i j

/-- **Calkin fold agrees with quotienting the operator matrix sum.** Let `H` be a complete
complex Hilbert space with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e :
Fin 2 × ι ≃ ι`, and `N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by
splitting each last leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin
quotient and `c_i=q(S_N(i))`. for bounded-operator entries `X_ij ∈ B(H)`, folding the
matrix of classes `[X_ij]` gives `q(Σ_i,j S_N(i) X_ij S_N(j)*)`. -/
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

/-- **Metric preservation of the finite Calkin matrix fold.** Let `H` be a complete complex
Hilbert space with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 ×
ι ≃ ι`, and `N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting
each last leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. `finiteMatrixFold b e N` is an isometry from the C-star matrix metric on
`M_N(Q(H))` to the Calkin quotient-norm metric. -/
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
