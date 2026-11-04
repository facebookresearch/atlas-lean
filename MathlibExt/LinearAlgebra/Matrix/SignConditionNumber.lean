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

/-- **Boolean encoding of sign matrices.** For a natural number $n$, a sign matrix of order $n$ is
encoded as an $n \times n$ matrix with entries in the Booleans $\{\mathrm{true}, \mathrm{false}\}$,
whose rows and columns are indexed by $\{0, \dots, n - 1\}$. -/
abbrev SignMatrix (n : ℕ) := Matrix (Fin n) (Fin n) Bool

/-- **Real sign matrix of a Boolean matrix.** The realization of a Boolean $n \times n$ matrix $A$
is the real $n \times n$ matrix whose $(i, j)$ entry is $-1$ if $A_{ij}$ is true and $1$ if
$A_{ij}$ is false. -/
def SignMatrix.realize {n : ℕ} (A : SignMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if A i j then -1 else 1

/-- **Realized sign matrices have entries $\pm 1$.** For every Boolean $n \times n$ matrix $A$ and
all indices $i, j$, the $(i, j)$ entry of the real realization of $A$ is $1$ or $-1$. -/
theorem SignMatrix.realize_entries {n : ℕ} (A : SignMatrix n) (i j : Fin n) :
    A.realize i j = 1 ∨ A.realize i j = -1 := by
  cases h : A i j <;> simp [SignMatrix.realize, h]

/-- **Boolean matrices realize exactly the sign matrices.** Send each $n \times n$ Boolean
matrix to the real matrix whose entry is $-1$ where the Boolean entry is true and $1$ where it
is false. A real $n \times n$ matrix $M$ arises in this way if and only if every entry of $M$
is $1$ or $-1$. -/
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

/-- **Condition number of a square real matrix.** For a real $n \times n$ matrix $A$, let
$\sigma_0 \ge \sigma_1 \ge \dots$ be the singular values of $A$ acting on Euclidean space
$\mathbb{R}^n$, indexed from $0$ and extended by $\sigma_i = 0$ for $i \ge n$. The condition
number of $A$, an element of $[0, \infty]$, is $\infty$ if $\sigma_{n-1} = 0$ and
$\sigma_0 / \sigma_{n-1}$ otherwise, where $n - 1$ is read as $0$ when $n = 0$.

The minimum over sign matrices is only taken at positive order. -/
noncomputable def conditionNumber {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ENNReal :=
  let σ := (Matrix.toEuclideanLin A).singularValues
  if σ (n - 1) = 0 then ⊤ else ENNReal.ofReal (σ 0 / σ (n - 1))

/-- **Minimum condition number of sign matrices.** For a positive integer $n$, the minimum
condition number of order $n$ is the least condition number of a real $n \times n$ sign matrix,
that is, a matrix all of whose entries are $1$ or $-1$; the minimum is taken over the finitely
many such matrices. -/
noncomputable def minimumConditionNumber (n : {n : ℕ // 0 < n}) : ENNReal :=
  (Finset.univ : Finset (SignMatrix n.1)).inf' Finset.univ_nonempty
    (fun A => conditionNumber A.realize)

/-- **Infinite condition number from a vanishing singular value.** Let $A$ be a real
$n \times n$ matrix with singular values $\sigma_0 \ge \sigma_1 \ge \dots$ on Euclidean space
$\mathbb{R}^n$, indexed from $0$ and extended by zeros, where $n - 1$ is read as $0$ when
$n = 0$. If $\sigma_{n-1} = 0$, then the condition number of $A$ is $\infty$. -/
theorem conditionNumber_eq_top_of_smallest_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (h : (Matrix.toEuclideanLin A).singularValues (n - 1) = 0) :
    conditionNumber A = ⊤ := by
  simp [conditionNumber, h]

/-- **Condition number as a singular-value ratio.** Let $A$ be a real $n \times n$ matrix with
singular values $\sigma_0 \ge \sigma_1 \ge \dots$ on Euclidean space $\mathbb{R}^n$, indexed from
$0$ and extended by zeros, where $n - 1$ is read as $0$ when $n = 0$. If $\sigma_{n-1} \ne 0$,
then the condition number of $A$ equals $\sigma_0 / \sigma_{n-1}$. -/
theorem conditionNumber_eq_ratio_of_smallest_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (h : (Matrix.toEuclideanLin A).singularValues (n - 1) ≠ 0) :
    conditionNumber A = ENNReal.ofReal
      ((Matrix.toEuclideanLin A).singularValues 0 /
        (Matrix.toEuclideanLin A).singularValues (n - 1)) := by
  simp [conditionNumber, h]

/-- **The zero matrix has infinite condition number.** For every natural number $n$, the
condition number of the real $n \times n$ zero matrix is $\infty$; this includes the
$0 \times 0$ matrix. -/
@[simp] theorem conditionNumber_zero (n : ℕ) :
    conditionNumber (0 : Matrix (Fin n) (Fin n) ℝ) = ⊤ := by
  simp [conditionNumber]

/-- **The minimum condition number is attained.** For every positive integer $n$, there is an
$n \times n$ Boolean matrix whose realization as a real sign matrix ($-1$ for true, $1$ for
false) has condition number equal to the minimum condition number of order $n$. -/
theorem minimumConditionNumber_attained (n : {n : ℕ // 0 < n}) :
    ∃ A : SignMatrix n.1, minimumConditionNumber n = conditionNumber A.realize := by
  obtain ⟨A, _, hA⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (SignMatrix n.1)).Nonempty)
    (fun A => conditionNumber A.realize)
  exact ⟨A, hA⟩

/-- **Condition numbers are at least one.** For every natural number $n$ and every real
$n \times n$ matrix $A$, the condition number of $A$ is at least $1$. -/
theorem one_le_conditionNumber {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    1 ≤ conditionNumber A := by
  unfold conditionNumber
  dsimp
  split_ifs with h
  · exact le_top
  · have hp := ((Matrix.toEuclideanLin A).singularValues_pos_iff_ne_zero (n - 1)).mpr h
    have hle := (Matrix.toEuclideanLin A).singularValues_antitone (Nat.zero_le (n - 1))
    simpa using ENNReal.ofReal_le_ofReal ((one_le_div hp).mpr hle)

/-- **The minimum condition number is at least one.** For every positive integer $n$, the minimum
condition number of the real $n \times n$ sign matrices is at least $1$. -/
theorem one_le_minimumConditionNumber (n : {n : ℕ // 0 < n}) :
    1 ≤ minimumConditionNumber n := by
  apply Finset.le_inf'
  intro A _
  exact one_le_conditionNumber A.realize

/-- **Condition number of the order-one identity.** The condition number of the $1 \times 1$
real identity matrix is $1$. -/
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

/-- **Minimum condition number of order one.** The minimum condition number of order $1$ is $1$:
the least condition number of a $1 \times 1$ real sign matrix is $1$. -/
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
