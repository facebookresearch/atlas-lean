/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.Matrix.Basis

/-!
# Choi matrix for linear and completely positive maps (finite-dimensional)

This module defines the repository-convention Choi matrix for arbitrary
complex-linear maps `Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ` and the reconstruction
by matrix-unit expansion. It proves application formulas, both inverse laws,
a linear equivalence, injectivity and extensionality, and retains
`CompletelyPositiveMap.choiMatrix` as a thin specialization.

Convention: `J(Φ) ((i,a),(j,b)) = Φ (Matrix.single i j 1) a b`,
indexed by `n × m`. Reconstruction is
`Φ(X) = ∑ i j, X i j • (fun a b => J (i,a) (j,b))`.

## Tags

choi, completely positive map, cstar algebra
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator CStarAlgebra MatrixOrder

namespace LinearMap

variable {n m : Type*} [DecidableEq n]

/-- **Choi matrix of a complex-linear matrix map.** Let `n` be an index type with decidable equality,
let `m` be any index type, and let `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`. Its Choi matrix is indexed
by `n × m` and has entry `J(Φ) ((i,a),(j,b)) = Φ(Eᵢⱼ)(a,b)`, where `Eᵢⱼ` is the complex matrix unit.
Neither index type is required to be finite for this definition. -/
noncomputable def choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    Matrix (n × m) (n × m) ℂ :=
  fun ⟨i, a⟩ ⟨j, b⟩ => Φ (Matrix.single i j (1 : ℂ)) a b

@[simp]
theorem choiMatrix_apply (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (i j : n) (a b : m) :
    choiMatrix Φ (i, a) (j, b) = Φ (Matrix.single i j (1 : ℂ)) a b :=
  rfl

/-- **Choi matrix of the identity.** For an index type `n` with decidable equality, the identity
complex-linear map on `Matrix n n ℂ` has Choi entry `J(id) ((i,a),(j,b)) = 1` when `i = a` and `j =
b`, and zero otherwise. No finiteness assumption on `n` is needed. -/
theorem choiMatrix_id :
    choiMatrix (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) =
      fun ⟨i, a⟩ ⟨j, b⟩ => if i = a ∧ j = b then (1 : ℂ) else 0 :=
  rfl

/-- **Linearity of the Choi construction.** For an index type `n` with decidable equality and any index
type `m`, sending a complex-linear map `Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ` to its Choi matrix defines
a complex-linear map into `Matrix (n × m) (n × m) ℂ`. The entry convention is `Φ(Eᵢⱼ)(a,b)`. -/
noncomputable def choiMatrixHom :
    (Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) →ₗ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun := choiMatrix
  map_add' := by
    intro Φ Ψ
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [choiMatrix]
  map_smul' := by
    intro r Φ
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [choiMatrix, LinearMap.smul_apply]

variable [Fintype n]

/-- **Reconstruction of a linear map from its Choi matrix.** For a finite index type `n` with decidable
equality, any index type `m`, and a complex matrix `J` indexed by `n × m`, reconstruction sends a
complex square matrix `X` indexed by `n` to the matrix with entry `∑ i j, X(i,j) J((i,a),(j,b))`.
This is inverse to the Choi construction. -/
noncomputable def fromChoiMatrix (J : Matrix (n × m) (n × m) ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ :=
  Matrix.liftLinear ℂ (fun i j =>
    { toFun := fun c => c • (Matrix.of fun a b => J (i, a) (j, b))
      map_add' := fun x y => by simp [add_smul]
      map_smul' := fun r x => by simp [smul_smul, mul_comm r x] })

/-- **Choi reconstruction on matrix units.** For finite decidable `n`, any `m`, a complex matrix `J`
indexed by `n × m`, indices `i,j ∈ n`, and `c ∈ ℂ`, reconstruction sends `c Eᵢⱼ` to the matrix with
`(a,b)` entry `c J((i,a),(j,b))`. -/
theorem fromChoiMatrix_single (J : Matrix (n × m) (n × m) ℂ) (i j : n) (c : ℂ) :
    fromChoiMatrix J (Matrix.single i j c) = c • (Matrix.of fun a b => J (i, a) (j, b)) := by
  unfold fromChoiMatrix
  simp [Matrix.liftLinear_single]

@[simp]
theorem fromChoiMatrix_single_one (J : Matrix (n × m) (n × m) ℂ) (i j : n) :
    fromChoiMatrix J (Matrix.single i j (1 : ℂ)) = Matrix.of fun a b => J (i, a) (j, b) := by
  rw [fromChoiMatrix_single, one_smul]

theorem fromChoiMatrix_apply_single (J : Matrix (n × m) (n × m) ℂ) (i j : n) (c : ℂ) (a b : m) :
    fromChoiMatrix J (Matrix.single i j c) a b = c * J (i, a) (j, b) := by
  rw [fromChoiMatrix_single]
  simp [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]

theorem fromChoiMatrix_single_one_apply (J : Matrix (n × m) (n × m) ℂ) (i j : n) (a b : m) :
    fromChoiMatrix J (Matrix.single i j (1 : ℂ)) a b = J (i, a) (j, b) := by
  rw [fromChoiMatrix_single_one]
  rfl

/-- **Entry formula for Choi reconstruction.** For finite decidable `n`, any `m`, `J : Matrix (n × m) (n
× m) ℂ`, and `X : Matrix n n ℂ`, the reconstructed map has `(a,b)` entry `∑ i j, X(i,j)
J((i,a),(j,b))`. -/
theorem fromChoiMatrix_apply (J : Matrix (n × m) (n × m) ℂ) (X : Matrix n n ℂ) (a b : m) :
    fromChoiMatrix J X a b = ∑ i : n, ∑ j : n, X i j * J (i, a) (j, b) := by
  classical
  unfold fromChoiMatrix
  simp [Matrix.liftLinear_apply, Matrix.sum_apply, Matrix.of_apply, smul_eq_mul]

/-- **Choi matrix after reconstruction.** For finite decidable `n`, any index type `m`, and a complex
matrix `J` indexed by `n × m`, the Choi matrix of the reconstructed complex-linear map equals `J`. -/
theorem choiMatrix_fromChoiMatrix (J : Matrix (n × m) (n × m) ℂ) :
    choiMatrix (fromChoiMatrix J) = J := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [choiMatrix, fromChoiMatrix_single_one_apply]

/-- **Reconstruction after the Choi construction.** For finite decidable `n`, any index type `m`, and a
complex-linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`, reconstructing from `J(Φ)` recovers `Φ`. -/
theorem fromChoiMatrix_choiMatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) :
    fromChoiMatrix (choiMatrix Φ) = Φ := by
  classical
  have h_single_smul : ∀ (i j : n) (c : ℂ),
      Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
    intro i j c
    ext p q
    simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : i = p ∧ j = q
    · simp [h]
    · simp [h]
  have h_X : ∀ X : Matrix n n ℂ,
      X = ∑ i : n, ∑ j : n, X i j • Matrix.single i j (1 : ℂ) := by
    intro X
    calc
      X = ∑ i : n, ∑ j : n, Matrix.single i j (X i j) :=
        Matrix.matrix_eq_sum_single X
      _ = ∑ i : n, ∑ j : n, X i j • Matrix.single i j (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [h_single_smul]
  ext X a b
  rw [fromChoiMatrix_apply]
  have hΦ : Φ X = ∑ i : n, ∑ j : n, X i j • Φ (Matrix.single i j (1 : ℂ)) := by
    calc
      Φ X = Φ (∑ i : n, ∑ j : n, X i j • Matrix.single i j (1 : ℂ)) := by rw [← h_X X]
      _ = ∑ i : n, ∑ j : n, Φ (X i j • Matrix.single i j (1 : ℂ)) := by simp [map_sum]
      _ = ∑ i : n, ∑ j : n, X i j • Φ (Matrix.single i j (1 : ℂ)) := by simp_rw [map_smul]
  calc
    (∑ i : n, ∑ j : n, X i j * choiMatrix Φ (i, a) (j, b))
        = (∑ i : n, ∑ j : n, X i j * Φ (Matrix.single i j (1 : ℂ)) a b) := by rfl
    _ = (∑ i : n, ∑ j : n, (X i j • Φ (Matrix.single i j (1 : ℂ)) : Matrix m m ℂ) a b) := by
          simp [Matrix.smul_apply, smul_eq_mul]
    _ = ((∑ i : n, ∑ j : n, X i j • Φ (Matrix.single i j (1 : ℂ)) : Matrix m m ℂ) a b) := by
          simp [Matrix.sum_apply]
    _ = (Φ X) a b := by rw [hΦ]

/-- **Linearity of Choi reconstruction.** For finite decidable `n` and any index type `m`,
reconstruction is a complex-linear map from complex matrices indexed by `n × m` to complex-linear
maps `Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`. -/
noncomputable def fromChoiMatrixHom :
    Matrix (n × m) (n × m) ℂ →ₗ[ℂ] (Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) where
  toFun := fromChoiMatrix
  map_add' := by
    intro J K
    apply Matrix.ext_linearMap
    intro i j
    apply LinearMap.ext
    intro c
    have hJK : (Matrix.of fun a b => (J + K) (i, a) (j, b) : Matrix m m ℂ) =
        (Matrix.of fun a b => J (i, a) (j, b)) + (Matrix.of fun a b => K (i, a) (j, b)) := by
      ext a b
      simp [Matrix.add_apply]
    calc
      fromChoiMatrix (J + K) (Matrix.single i j c)
          = c • (Matrix.of fun a b => (J + K) (i, a) (j, b)) := fromChoiMatrix_single _ i j c
      _ = c • ((Matrix.of fun a b => J (i, a) (j, b)) +
          (Matrix.of fun a b => K (i, a) (j, b))) := by rw [hJK]
      _ = c • (Matrix.of fun a b => J (i, a) (j, b)) +
          c • (Matrix.of fun a b => K (i, a) (j, b)) := smul_add _ _ _
      _ = fromChoiMatrix J (Matrix.single i j c) +
          fromChoiMatrix K (Matrix.single i j c) := by
            rw [← fromChoiMatrix_single, ← fromChoiMatrix_single]
      _ = (fromChoiMatrix J + fromChoiMatrix K) (Matrix.single i j c) := by
            simp [LinearMap.add_apply]
  map_smul' := by
    intro r J
    apply Matrix.ext_linearMap
    intro i j
    apply LinearMap.ext
    intro c
    have hr : (Matrix.of fun a b => (r • J) (i, a) (j, b) : Matrix m m ℂ) =
        r • (Matrix.of fun a b => J (i, a) (j, b)) := by
      ext a b
      simp [Matrix.smul_apply, smul_eq_mul]
    calc
      fromChoiMatrix (r • J) (Matrix.single i j c)
          = c • (Matrix.of fun a b => (r • J) (i, a) (j, b)) := fromChoiMatrix_single _ i j c
      _ = c • (r • (Matrix.of fun a b => J (i, a) (j, b))) := by rw [hr]
      _ = r • (c • (Matrix.of fun a b => J (i, a) (j, b))) := by
            rw [smul_smul, smul_smul, mul_comm]
      _ = r • fromChoiMatrix J (Matrix.single i j c) := by rw [← fromChoiMatrix_single]
      _ = (r • fromChoiMatrix J) (Matrix.single i j c) := by simp [LinearMap.smul_apply]

/-- **Linear equivalence between matrix maps and Choi matrices.** For finite decidable `n` and any index
type `m`, the Choi construction gives a complex-linear equivalence between `Matrix n n ℂ →ₗ[ℂ]
Matrix m m ℂ` and complex matrices indexed by `n × m`. Its inverse is matrix-unit reconstruction,
with entry order `((i,a),(j,b))`. -/
noncomputable def choiMatrixEquiv :
    (Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) ≃ₗ[ℂ] Matrix (n × m) (n × m) ℂ :=
  LinearEquiv.ofLinearMap choiMatrixHom fromChoiMatrixHom
    (by
      apply LinearMap.ext
      intro J
      exact choiMatrix_fromChoiMatrix J)
    (by
      apply LinearMap.ext
      intro Φ
      exact fromChoiMatrix_choiMatrix Φ)

set_option linter.unusedFintypeInType false in
theorem choiMatrix_injective :
    Function.Injective (choiMatrix (n := n) (m := m)) := by
  intro Φ Ψ h
  have h1 : fromChoiMatrix (choiMatrix Φ) = fromChoiMatrix (choiMatrix Ψ) := by rw [h]
  rwa [fromChoiMatrix_choiMatrix, fromChoiMatrix_choiMatrix] at h1

set_option linter.unusedFintypeInType false in
theorem fromChoiMatrix_injective :
    Function.Injective (fromChoiMatrix (n := n) (m := m)) := by
  intro J K h
  have h1 : choiMatrix (fromChoiMatrix J) = choiMatrix (fromChoiMatrix K) := by rw [h]
  rwa [choiMatrix_fromChoiMatrix, choiMatrix_fromChoiMatrix] at h1

set_option linter.unusedFintypeInType false in
theorem choiMatrix_inj {Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    choiMatrix Φ = choiMatrix Ψ ↔ Φ = Ψ :=
  ⟨fun h => choiMatrix_injective h, fun h => by rw [h]⟩

theorem fromChoiMatrix_inj {J K : Matrix (n × m) (n × m) ℂ} :
    fromChoiMatrix J = fromChoiMatrix K ↔ J = K :=
  ⟨fun h => fromChoiMatrix_injective h, fun h => by rw [h]⟩

set_option linter.unusedFintypeInType false in
theorem ext_choiMatrix {Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : choiMatrix Φ = choiMatrix Ψ) : Φ = Ψ :=
  choiMatrix_injective h

set_option linter.unusedFintypeInType false in
theorem choiMatrix_ext_iff {Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ} :
    Φ = Ψ ↔ choiMatrix Φ = choiMatrix Ψ :=
  ⟨fun h => by rw [h], fun h => ext_choiMatrix h⟩

end LinearMap

namespace CompletelyPositiveMap

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **Choi matrix of a completely positive map.** For finite index types `n` and `m` with decidable
equality and a completely positive map `φ : Matrix n n ℂ →CP Matrix m m ℂ`, its Choi matrix is
indexed by `n × m` and has entry `J(φ) ((i,a),(j,b)) = φ(Eᵢⱼ)(a,b)`. -/
noncomputable def choiMatrix (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    Matrix (n × m) (n × m) ℂ :=
  LinearMap.choiMatrix φ.toLinearMap

@[simp]
theorem choiMatrix_apply (φ : Matrix n n ℂ →CP Matrix m m ℂ)
    (i j : n) (a b : m) :
    choiMatrix φ (i, a) (j, b) = φ (Matrix.single i j (1 : ℂ)) a b :=
  rfl

theorem choiMatrix_toLinearMap (φ : Matrix n n ℂ →CP Matrix m m ℂ) :
    choiMatrix φ = LinearMap.choiMatrix φ.toLinearMap :=
  rfl

end CompletelyPositiveMap
