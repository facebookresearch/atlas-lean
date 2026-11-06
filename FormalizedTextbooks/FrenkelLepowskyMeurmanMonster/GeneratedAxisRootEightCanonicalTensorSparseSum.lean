/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveTensorColumns

/-! Sparse summation is justified by every coefficient of the complete original spatial matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Literal nonzero entries of each full original canonical physical row. -/
def generatedRootEightCanonicalTensorSparseRows : Fin 24 → List (Fin 24 × ℤ) :=
  ![[(0, -1), (1, 1), (2, 1), (3, 1), (16, 1), (17, 3), (18, -1), (19, -1)],
    [(0, -1), (1, 1), (2, 1), (3, 1), (16, -3), (17, -1), (18, -1), (19, -1)],
    [(0, 3), (1, 1), (2, 1), (3, 1), (16, 1), (17, -1), (18, -1), (19, -1)],
    [(0, 1), (1, 3), (2, -1), (3, -1), (16, -1), (17, 1), (18, 1), (19, 1)],
    [(0, 1), (1, -1), (2, -1), (3, -1), (16, -1), (17, 1), (18, -3), (19, 1)],
    [(0, -1), (1, 1), (2, 1), (3, -3), (16, 1), (17, -1), (18, -1), (19, -1)],
    [(0, 1), (1, -1), (2, -1), (3, -1), (16, -1), (17, 1), (18, 1), (19, -3)],
    [(0, 1), (1, -1), (2, 3), (3, -1), (16, -1), (17, 1), (18, 1), (19, 1)],
    [(4, 1), (5, -1), (6, 1), (7, 1), (8, 1), (9, 1), (10, -1), (11, 1), (12, 1), (13, 1), (14, 1), (15, -1), (20, 1), (21, -1), (22, 1), (23, 1)],
    [(4, 1), (5, -1), (6, -1), (7, -1), (8, -1), (9, 1), (10, 1), (11, 1), (12, -1), (13, 1), (14, 1), (15, 1), (20, 1), (21, -1), (22, -1), (23, -1)],
    [(4, -1), (5, 1), (6, 1), (7, 1), (8, -1), (9, 1), (10, 1), (11, 1), (12, -1), (13, 1), (14, 1), (15, 1), (20, -1), (21, 1), (22, 1), (23, 1)],
    [(4, 1), (5, -1), (6, 1), (7, 1), (8, -1), (9, -1), (10, 1), (11, -1), (12, -1), (13, -1), (14, -1), (15, 1), (20, 1), (21, -1), (22, 1), (23, 1)],
    [(4, -1), (5, -1), (6, 1), (7, -1), (8, -1), (9, -1), (10, -1), (11, 1), (12, -1), (13, 1), (14, -1), (15, -1), (20, -1), (21, -1), (22, 1), (23, -1)],
    [(4, 1), (5, 1), (6, 1), (7, -1), (8, -1), (9, 1), (10, -1), (11, -1), (12, -1), (13, -1), (14, 1), (15, -1), (20, 1), (21, 1), (22, 1), (23, -1)],
    [(4, 1), (5, 1), (6, 1), (7, -1), (8, 1), (9, -1), (10, 1), (11, 1), (12, 1), (13, 1), (14, -1), (15, 1), (20, 1), (21, 1), (22, 1), (23, -1)],
    [(4, 1), (5, 1), (6, -1), (7, 1), (8, -1), (9, -1), (10, -1), (11, 1), (12, -1), (13, 1), (14, -1), (15, -1), (20, 1), (21, 1), (22, -1), (23, 1)],
    [(4, -1), (5, 1), (6, -1), (7, -1), (8, 1), (9, 1), (10, -1), (11, 1), (12, -1), (13, -1), (14, -1), (15, 1), (20, 1), (21, -1), (22, 1), (23, 1)],
    [(4, -1), (5, 1), (6, 1), (7, 1), (8, -1), (9, 1), (10, 1), (11, 1), (12, 1), (13, -1), (14, -1), (15, -1), (20, 1), (21, -1), (22, -1), (23, -1)],
    [(4, 1), (5, -1), (6, -1), (7, -1), (8, -1), (9, 1), (10, 1), (11, 1), (12, 1), (13, -1), (14, -1), (15, -1), (20, -1), (21, 1), (22, 1), (23, 1)],
    [(4, -1), (5, 1), (6, -1), (7, -1), (8, -1), (9, -1), (10, 1), (11, -1), (12, 1), (13, 1), (14, 1), (15, -1), (20, 1), (21, -1), (22, 1), (23, 1)],
    [(4, 1), (5, 1), (6, -1), (7, 1), (8, -1), (9, -1), (10, -1), (11, 1), (12, 1), (13, -1), (14, 1), (15, 1), (20, -1), (21, -1), (22, 1), (23, -1)],
    [(4, -1), (5, -1), (6, -1), (7, 1), (8, -1), (9, 1), (10, -1), (11, -1), (12, 1), (13, 1), (14, -1), (15, 1), (20, 1), (21, 1), (22, 1), (23, -1)],
    [(4, -1), (5, -1), (6, -1), (7, 1), (8, 1), (9, -1), (10, 1), (11, 1), (12, -1), (13, -1), (14, 1), (15, -1), (20, 1), (21, 1), (22, 1), (23, -1)],
    [(4, -1), (5, -1), (6, 1), (7, -1), (8, -1), (9, -1), (10, -1), (11, 1), (12, 1), (13, -1), (14, 1), (15, 1), (20, 1), (21, 1), (22, -1), (23, 1)]]

set_option maxHeartbeats 4000000 in
/-- Every coefficient, including every omitted zero, equals the complete original spatial matrix. -/
theorem generatedRootEight_canonical_tensor_sparse_coefficients : ∀ i j : Fin 24,
    generatedRootEightCanonicalSpatialNumerator i j =
      ((generatedRootEightCanonicalTensorSparseRows i).map
        (fun p => if p.1 = j then p.2 else 0)).sum := by
  decide +kernel

private theorem sparse_dot (v : Fin 24 → ℤ) (l : List (Fin 24 × ℤ)) :
    (∑ j : Fin 24, v j * (l.map (fun p => if p.1 = j then p.2 else 0)).sum) =
      (l.map (fun p => v p.1 * p.2)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]
    have ht : (∑ j : Fin 24, v j * (if p.1 = j then p.2 else 0)) = v p.1 * p.2 := by
      rw [Finset.sum_eq_single p.1]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro h
        simp at h
    rw [ht]

/-- For every integer source vector, exact sparse rows give the complete original twenty-four-column sum. -/
theorem generatedRootEight_canonical_tensor_sparse_sum (v : Fin 24 → ℤ) (i : Fin 24) :
    (∑ j : Fin 24, v j * generatedRootEightCanonicalSpatialNumerator i j) =
      ((generatedRootEightCanonicalTensorSparseRows i).map (fun p => v p.1 * p.2)).sum := by
  simp_rw [generatedRootEight_canonical_tensor_sparse_coefficients]
  exact sparse_dot v _

/-- The exact sparse evaluation of all genuine original spin columns in a canonical tensor entry. -/
def generatedRootEightCanonicalTensorSparseNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  ((generatedRootEightCanonicalTensorSparseRows i).map
    (fun p => generatedRootEightCanonicalTensorSpinInteger p.1 n * p.2)).sum

/-- Complete original tensor numerators equal the exact sparse row evaluation without a cache premise. -/
theorem generatedRootEight_canonical_tensor_numerator_sparse (n : Fin 4096) (i : Fin 24) :
    generatedRootEightCanonicalPositiveTensorNumerator n i =
      generatedRootEightCanonicalTensorSparseNumerator n i :=
  generatedRootEight_canonical_tensor_sparse_sum _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
