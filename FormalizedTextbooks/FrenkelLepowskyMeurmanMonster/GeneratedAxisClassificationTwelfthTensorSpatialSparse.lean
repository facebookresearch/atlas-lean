/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorCircuitData

/-! Every full original numerator in the first three generators has at most four nonzero
entries per row. Exact sparse expansion avoids evaluating discarded source coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- All four original physical source addresses, including zero padding. -/
def generatedTwelfthTensorSpatialSparseAddress : Fin 3 → Fin 24 → Fin 4 → Fin 24 :=
  ![![![17, 0, 0, 0], ![1, 0, 0, 0], ![19, 0, 0, 0], ![2, 0, 0, 0], ![6, 0, 0, 0], ![7, 0, 0, 0], ![11, 0, 0, 0], ![9, 0, 0, 0], ![15, 0, 0, 0], ![20, 0, 0, 0], ![12, 0, 0, 0], ![21, 0, 0, 0], ![10, 0, 0, 0], ![5, 0, 0, 0], ![4, 0, 0, 0], ![8, 0, 0, 0], ![0, 0, 0, 0], ![16, 0, 0, 0], ![18, 0, 0, 0], ![3, 0, 0, 0], ![22, 0, 0, 0], ![23, 0, 0, 0], ![13, 0, 0, 0], ![14, 0, 0, 0]], ![![0, 1, 16, 17], ![0, 1, 16, 17], ![2, 3, 18, 19], ![2, 3, 18, 19], ![9, 11, 13, 14], ![9, 11, 13, 14], ![4, 5, 20, 21], ![4, 5, 20, 21], ![6, 7, 22, 23], ![8, 10, 12, 15], ![6, 7, 22, 23], ![8, 10, 12, 15], ![6, 7, 22, 23], ![8, 10, 12, 15], ![8, 10, 12, 15], ![6, 7, 22, 23], ![0, 1, 16, 17], ![0, 1, 16, 17], ![2, 3, 18, 19], ![2, 3, 18, 19], ![9, 11, 13, 14], ![9, 11, 13, 14], ![4, 5, 20, 21], ![4, 5, 20, 21]], ![![0, 2, 17, 18], ![1, 3, 16, 19], ![1, 3, 16, 19], ![0, 2, 17, 18], ![6, 7, 12, 15], ![4, 5, 13, 14], ![4, 5, 13, 14], ![6, 7, 12, 15], ![9, 11, 20, 21], ![9, 11, 20, 21], ![8, 10, 22, 23], ![8, 10, 22, 23], ![9, 11, 20, 21], ![8, 10, 22, 23], ![9, 11, 20, 21], ![8, 10, 22, 23], ![0, 2, 17, 18], ![1, 3, 16, 19], ![1, 3, 16, 19], ![0, 2, 17, 18], ![6, 7, 12, 15], ![4, 5, 13, 14], ![4, 5, 13, 14], ![6, 7, 12, 15]]]

/-- The corresponding exact signed integer coefficients, including zero padding. -/
def generatedTwelfthTensorSpatialSparseCoefficient : Fin 3 → Fin 24 → Fin 4 → ℤ :=
  ![![![-1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0]], ![![1, -1, 1, -1], ![-1, 1, 1, -1], ![-1, -1, 1, 1], ![-1, 1, -1, 1], ![1, 1, -1, -1], ![1, -1, 1, -1], ![-1, -1, 1, 1], ![1, -1, -1, 1], ![-1, -1, 1, 1], ![1, -1, -1, 1], ![1, -1, -1, 1], ![-1, -1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, -1, 1, -1], ![1, -1, 1, -1], ![-1, -1, 1, 1], ![-1, -1, -1, -1], ![-1, 1, 1, -1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![-1, 1, 1, -1], ![-1, -1, -1, -1], ![-1, 1, -1, 1]], ![![-1, 1, 1, 1], ![-1, 1, 1, 1], ![1, 1, 1, -1], ![-1, -1, 1, -1], ![1, -1, -1, -1], ![1, -1, 1, 1], ![-1, -1, -1, 1], ![-1, -1, 1, -1], ![1, -1, 1, 1], ![1, 1, -1, 1], ![1, -1, 1, 1], ![-1, -1, -1, 1], ![1, -1, -1, -1], ![-1, -1, 1, -1], ![1, 1, 1, -1], ![1, -1, -1, -1], ![-1, 1, -1, -1], ![-1, 1, -1, -1], ![1, 1, -1, 1], ![-1, -1, -1, 1], ![1, -1, 1, 1], ![1, -1, -1, -1], ![-1, -1, 1, -1], ![-1, -1, -1, 1]]]

/-- All complete entries agree with the sparse row expansion, including every zero. -/
theorem generatedTwelfth_tensor_spatial_sparse_entries :
    ∀ (g : Fin 3) (j k : Fin 24),
      generatedTwelfthSpinTensorSpatialNumerator ⟨g.val, by omega⟩ j k =
        ∑ a : Fin 4, generatedTwelfthTensorSpatialSparseCoefficient g j a *
          if generatedTwelfthTensorSpatialSparseAddress g j a = k then 1 else 0 := by
  decide +kernel

/-- A finite row expansion evaluates exactly the original integer matrix action. -/
theorem generatedTwelfth_integer_matrix_sparse
    (N : Matrix (Fin 24) (Fin 24) ℤ)
    (p : Fin 24 → Fin 4 → Fin 24) (c : Fin 24 → Fin 4 → ℤ)
    (hN : ∀ j k, N j k = ∑ a : Fin 4, c j a * if p j a = k then 1 else 0)
    (v : Fin 24 → ℤ) (j : Fin 24) :
    ∑ k : Fin 24, N j k * v k = ∑ a : Fin 4, c j a * v (p j a) := by
  simp_rw [hN, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- The complete original physical numerator uses its exact four source terms. -/
theorem generatedTwelfth_tensor_spatial_sparse (g : Fin 3) (n : Fin 4096) (j : Fin 24) :
    generatedTwelfthSpinTensorSpatialInteger ⟨g.val, by omega⟩ n j =
      ∑ a : Fin 4, generatedTwelfthTensorSpatialSparseCoefficient g j a *
        generatedTwelfthSpinTensorInputInteger n (generatedTwelfthTensorSpatialSparseAddress g j a) := by
  unfold generatedTwelfthSpinTensorSpatialInteger
  exact generatedTwelfth_integer_matrix_sparse _ _ _
    (generatedTwelfth_tensor_spatial_sparse_entries g) _ j

/-- Original generator 0 retains the complete four-term physical action. -/
theorem generatedTwelfth_tensor_spatial_sparse_00 (n : Fin 4096) (j : Fin 24) :
    generatedTwelfthSpinTensorSpatialInteger 0 n j =
      ∑ a : Fin 4, generatedTwelfthTensorSpatialSparseCoefficient 0 j a *
        generatedTwelfthSpinTensorInputInteger n (generatedTwelfthTensorSpatialSparseAddress 0 j a) :=
  generatedTwelfth_tensor_spatial_sparse 0 n j

/-- Original generator 1 retains the complete four-term physical action. -/
theorem generatedTwelfth_tensor_spatial_sparse_01 (n : Fin 4096) (j : Fin 24) :
    generatedTwelfthSpinTensorSpatialInteger 1 n j =
      ∑ a : Fin 4, generatedTwelfthTensorSpatialSparseCoefficient 1 j a *
        generatedTwelfthSpinTensorInputInteger n (generatedTwelfthTensorSpatialSparseAddress 1 j a) :=
  generatedTwelfth_tensor_spatial_sparse 1 n j

/-- Original generator 2 retains the complete four-term physical action. -/
theorem generatedTwelfth_tensor_spatial_sparse_02 (n : Fin 4096) (j : Fin 24) :
    generatedTwelfthSpinTensorSpatialInteger 2 n j =
      ∑ a : Fin 4, generatedTwelfthTensorSpatialSparseCoefficient 2 j a *
        generatedTwelfthSpinTensorInputInteger n (generatedTwelfthTensorSpatialSparseAddress 2 j a) :=
  generatedTwelfth_tensor_spatial_sparse 2 n j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
