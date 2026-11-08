/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimum condition numbers of sign matrices
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace Matrix.SignConditionNumber

/-- Finite encoding of all square sign matrices of order `n`. -/
abbrev SignMatrix (n : ℕ) := Matrix (Fin n) (Fin n) Bool

/-- Interpret each Boolean entry as a real sign. -/
def SignMatrix.realize {n : ℕ} (A : SignMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if A i j then -1 else 1

/-- Realization produces only the two allowed entries. -/
theorem SignMatrix.realize_entries {n : ℕ} (A : SignMatrix n) (i j : Fin n) :
    A.realize i j = 1 ∨ A.realize i j = -1 := by
  cases h : A i j <;> simp [SignMatrix.realize, h]

/-- The finite Boolean encoding covers exactly all real sign matrices. -/
theorem exists_realize_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∃ A : SignMatrix n, A.realize = M) ↔ ∀ i j, M i j = 1 ∨ M i j = -1 := by
  classical
  constructor
  · rintro ⟨A, rfl⟩
    exact A.realize_entries
  · intro h
    refine ⟨fun i j => decide (M i j = -1), ?_⟩
    ext i j
    by_cases hneg : M i j = -1
    · simp [SignMatrix.realize, hneg]
    · rcases h i j with hpos | hminus
      · simpa [SignMatrix.realize, hneg] using hpos.symm
      · exact (hneg hminus).elim

/-- Largest singular value divided by the smallest of the first `n` singular
values; a zero smallest singular value gives infinity. Zero order is outside
the optimization domain. -/
noncomputable def conditionNumber {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ENNReal :=
  let σ := (Matrix.toEuclideanLin A).singularValues
  if σ (n - 1) = 0 then ⊤ else ENNReal.ofReal (σ 0 / σ (n - 1))

/-- Attained minimum over the nonempty finite set of all sign matrices, at a
positive order. -/
noncomputable def minimumConditionNumber (n : {n : ℕ // 0 < n}) : ENNReal :=
  (Finset.univ : Finset (SignMatrix n.1)).inf' Finset.univ_nonempty
    (fun A => conditionNumber A.realize)

/-- A vanishing smallest singular value selects the infinite branch. -/
theorem conditionNumber_eq_top_of_smallest_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (h : (Matrix.toEuclideanLin A).singularValues (n - 1) = 0) :
    conditionNumber A = ⊤ := by
  simp [conditionNumber, h]

/-- On the nonsingular branch, the definition is exactly the singular-value ratio. -/
theorem conditionNumber_eq_ratio_of_smallest_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (h : (Matrix.toEuclideanLin A).singularValues (n - 1) ≠ 0) :
    conditionNumber A = ENNReal.ofReal
      ((Matrix.toEuclideanLin A).singularValues 0 /
        (Matrix.toEuclideanLin A).singularValues (n - 1)) := by
  simp [conditionNumber, h]

/-- Zero matrices, including the isolated zero-order matrix, have infinite
condition number under the singular convention. -/
@[simp] theorem conditionNumber_zero (n : ℕ) :
    conditionNumber (0 : Matrix (Fin n) (Fin n) ℝ) = ⊤ := by
  simp [conditionNumber]

/-- The finite minimum is attained by an actual sign matrix. -/
theorem minimumConditionNumber_attained (n : {n : ℕ // 0 < n}) :
    ∃ A : SignMatrix n.1, minimumConditionNumber n = conditionNumber A.realize := by
  obtain ⟨A, _, hA⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (SignMatrix n.1)).Nonempty)
    (fun A => conditionNumber A.realize)
  exact ⟨A, hA⟩

/-- Descending, nonnegative singular values make every defined ratio at least one. -/
theorem one_le_conditionNumber {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    1 ≤ conditionNumber A := by
  unfold conditionNumber
  dsimp
  split_ifs with h
  · exact le_top
  · have hp := ((Matrix.toEuclideanLin A).singularValues_pos_iff_ne_zero (n - 1)).mpr h
    have hle := (Matrix.toEuclideanLin A).singularValues_antitone (Nat.zero_le (n - 1))
    simpa using ENNReal.ofReal_le_ofReal ((one_le_div hp).mpr hle)

/-- Every positive-order minimum is at least one. -/
theorem one_le_minimumConditionNumber (n : {n : ℕ // 0 < n}) :
    1 ≤ minimumConditionNumber n := by
  apply Finset.le_inf'
  intro A _
  exact one_le_conditionNumber A.realize

/-- The order-one identity is nonsingular and has condition number one. -/
@[simp] theorem conditionNumber_one_order_one :
    conditionNumber (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
  have hT : Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      (LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) :=
    Matrix.toLpLin_one 2
  have hi : Function.Injective
      (Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    rw [hT]
    exact fun _ _ h => h
  have hp := (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos
    (Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ))).mp hi
  have hpos : 0 < (Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)).singularValues 0 :=
    hp 0 (by simp)
  rw [conditionNumber_eq_ratio_of_smallest_ne_zero _ (ne_of_gt hpos)]
  change ENNReal.ofReal
    ((Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)).singularValues 0 /
      (Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ)).singularValues 0) = 1
  rw [div_self (ne_of_gt hpos)]
  simp

/-- The actual order-one sign-matrix minimum is one. -/
@[simp] theorem minimumConditionNumber_one :
    minimumConditionNumber ⟨1, Nat.zero_lt_one⟩ = 1 := by
  let A : SignMatrix 1 := fun _ _ => false
  have hr : A.realize = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [A, SignMatrix.realize, Matrix.one_apply, Subsingleton.elim i j]
  refine le_antisymm ?_ (one_le_minimumConditionNumber _)
  calc
    minimumConditionNumber ⟨1, Nat.zero_lt_one⟩ ≤ conditionNumber A.realize :=
      Finset.inf'_le (fun B : SignMatrix 1 => conditionNumber B.realize) (Finset.mem_univ A)
    _ = 1 := by rw [hr, conditionNumber_one_order_one]

end Matrix.SignConditionNumber
