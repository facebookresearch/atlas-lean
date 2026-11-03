/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Partial traces of finite matrices

For a matrix `A` indexed by a product type `m × n`, thought of as an operator
on a tensor product of two finite-dimensional spaces, the **partial traces**
trace out one factor:

* `partialTraceLeft A : Matrix n n 𝕜` has entries
  `(partialTraceLeft A) j j' = ∑ i, A (i, j) (i, j')`;
* `partialTraceRight A : Matrix m m 𝕜` has entries
  `(partialTraceRight A) i i' = ∑ j, A (i, j) (i', j)`.

These are the finite-dimensional instances of the partial-trace maps for
operators on tensor products of Hilbert spaces, the setting of the
Hilbert-space material in `v1/Atlas/IntroductionToFunctionalAnalysis/code/`
(Riesz representation, orthogonal projection, spectral theory). They are
the reduced density matrices of quantum information theory: if `A` is a
density matrix (`PosSemidef` with `trace A = 1`), then each partial trace is
again a density matrix.

Main results:

* `partialTraceLeft_kronecker` / `partialTraceRight_kronecker`: the partial
  trace of a Kronecker product is the trace of the traced-out factor times
  the remaining factor;
* `posSemidef_partialTraceLeft` / `posSemidef_partialTraceRight`: partial
  traces preserve positive semidefiniteness;
* `trace_partialTraceLeft_mul` / `trace_partialTraceRight_mul`: the partial
  trace is adjoint to amplification by the identity, in the trace pairing.
-/

@[expose] public section

open scoped BigOperators ComplexOrder Kronecker Matrix

namespace MathlibExt.LinearAlgebra.Matrix.PartialTrace

variable {m n : Type*} {𝕜 : Type*} [RCLike 𝕜]

/-- The partial trace over the first factor: `∑ i, A (i, j) (i, j')`. -/
def partialTraceLeft [Fintype m] [Fintype n]
    (A : Matrix (m × n) (m × n) 𝕜) : Matrix n n 𝕜 :=
  Matrix.of fun j j' => ∑ i, A (i, j) (i, j')

/-- The partial trace over the second factor: `∑ j, A (i, j) (i', j)`. -/
def partialTraceRight [Fintype m] [Fintype n]
    (A : Matrix (m × n) (m × n) 𝕜) : Matrix m m 𝕜 :=
  Matrix.of fun i i' => ∑ j, A (i, j) (i', j)

@[simp]
theorem partialTraceLeft_apply [Fintype m] [Fintype n]
    (A : Matrix (m × n) (m × n) 𝕜) (j j' : n) :
    partialTraceLeft A j j' = ∑ i, A (i, j) (i, j') :=
  rfl

@[simp]
theorem partialTraceRight_apply [Fintype m] [Fintype n]
    (A : Matrix (m × n) (m × n) 𝕜) (i i' : m) :
    partialTraceRight A i i' = ∑ j, A (i, j) (i', j) :=
  rfl

theorem partialTraceLeft_zero [Fintype m] [Fintype n] :
    partialTraceLeft (0 : Matrix (m × n) (m × n) 𝕜) = 0 := by
  ext j j'
  simp [partialTraceLeft]

theorem partialTraceRight_zero [Fintype m] [Fintype n] :
    partialTraceRight (0 : Matrix (m × n) (m × n) 𝕜) = 0 := by
  ext i i'
  simp [partialTraceRight]

theorem partialTraceLeft_add [Fintype m] [Fintype n] (A B : Matrix (m × n) (m × n) 𝕜) :
    partialTraceLeft (A + B) = partialTraceLeft A + partialTraceLeft B := by
  ext j j'
  simp only [partialTraceLeft, Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

theorem partialTraceRight_add [Fintype m] [Fintype n] (A B : Matrix (m × n) (m × n) 𝕜) :
    partialTraceRight (A + B) = partialTraceRight A + partialTraceRight B := by
  ext i i'
  simp only [partialTraceRight, Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]

theorem partialTraceLeft_smul [Fintype m] [Fintype n] (c : 𝕜)
    (A : Matrix (m × n) (m × n) 𝕜) :
    partialTraceLeft (c • A) = c • partialTraceLeft A := by
  ext j j'
  simp only [partialTraceLeft, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]

theorem partialTraceRight_smul [Fintype m] [Fintype n] (c : 𝕜)
    (A : Matrix (m × n) (m × n) 𝕜) :
    partialTraceRight (c • A) = c • partialTraceRight A := by
  ext i i'
  simp only [partialTraceRight, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]

theorem partialTraceLeft_sum [Fintype m] [Fintype n] {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (m × n) (m × n) 𝕜) :
    partialTraceLeft (∑ k ∈ s, A k) = ∑ k ∈ s, partialTraceLeft (A k) := by
  ext j j'
  simp only [partialTraceLeft, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

theorem partialTraceRight_sum [Fintype m] [Fintype n] {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (m × n) (m × n) 𝕜) :
    partialTraceRight (∑ k ∈ s, A k) = ∑ k ∈ s, partialTraceRight (A k) := by
  ext i i'
  simp only [partialTraceRight, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

theorem partialTraceLeft_conjTranspose [Fintype m] [Fintype n]
    (A : Matrix (m × n) (m × n) 𝕜) :
    partialTraceLeft Aᴴ = (partialTraceLeft A)ᴴ := by
  ext j j'
  simp only [partialTraceLeft, Matrix.of_apply, Matrix.conjTranspose_apply, star_sum]

theorem partialTraceRight_conjTranspose [Fintype m] [Fintype n]
    (A : Matrix (m × n) (m × n) 𝕜) :
    partialTraceRight Aᴴ = (partialTraceRight A)ᴴ := by
  ext i i'
  simp only [partialTraceRight, Matrix.of_apply, Matrix.conjTranspose_apply, star_sum]

theorem trace_partialTraceLeft [Fintype m] [Fintype n] (A : Matrix (m × n) (m × n) 𝕜) :
    Matrix.trace (partialTraceLeft A) = Matrix.trace A := by
  show (∑ j, ∑ i, A (i, j) (i, j)) = ∑ x : m × n, A x x
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem trace_partialTraceRight [Fintype m] [Fintype n] (A : Matrix (m × n) (m × n) 𝕜) :
    Matrix.trace (partialTraceRight A) = Matrix.trace A := by
  show (∑ i, ∑ j, A (i, j) (i, j)) = ∑ x : m × n, A x x
  rw [Fintype.sum_prod_type]

/-- The partial trace of a density matrix has trace `1`. -/
theorem trace_partialTraceLeft_of_trace_eq_one [Fintype m] [Fintype n]
    {A : Matrix (m × n) (m × n) 𝕜}
    (hA : Matrix.trace A = 1) : Matrix.trace (partialTraceLeft A) = 1 := by
  rw [trace_partialTraceLeft, hA]

/-- The partial trace of a density matrix has trace `1`. -/
theorem trace_partialTraceRight_of_trace_eq_one [Fintype m] [Fintype n]
    {A : Matrix (m × n) (m × n) 𝕜}
    (hA : Matrix.trace A = 1) : Matrix.trace (partialTraceRight A) = 1 := by
  rw [trace_partialTraceRight, hA]

theorem partialTraceLeft_kronecker [Fintype m] [Fintype n] (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) :
    partialTraceLeft (A ⊗ₖ B) = Matrix.trace A • B := by
  ext j j'
  simp only [partialTraceLeft, Matrix.of_apply, Matrix.kronecker_apply, Matrix.smul_apply,
    smul_eq_mul]
  show (∑ i, A i i * B j j') = (∑ i, A i i) * B j j'
  rw [Finset.sum_mul]

theorem partialTraceRight_kronecker [Fintype m] [Fintype n] (A : Matrix m m 𝕜)
    (B : Matrix n n 𝕜) :
    partialTraceRight (A ⊗ₖ B) = Matrix.trace B • A := by
  ext i i'
  simp only [partialTraceRight, Matrix.of_apply, Matrix.kronecker_apply, Matrix.smul_apply,
    smul_eq_mul]
  show (∑ j, A i i' * B j j) = (∑ j, B j j) * A i i'
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem partialTraceLeft_one [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    partialTraceLeft (1 : Matrix (m × n) (m × n) 𝕜)
      = (Fintype.card m : 𝕜) • (1 : Matrix n n 𝕜) := by
  ext j j'
  by_cases hj : j = j' <;> simp [partialTraceLeft, hj]

theorem partialTraceRight_one [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    partialTraceRight (1 : Matrix (m × n) (m × n) 𝕜)
      = (Fintype.card n : 𝕜) • (1 : Matrix m m 𝕜) := by
  ext i i'
  by_cases hi : i = i' <;> simp [partialTraceRight, hi]

/-- The partial trace of a rank-one positive semidefinite matrix is the sum
of the rank-one positive semidefinite matrices of its slices. -/
theorem partialTraceLeft_vecMulVec_star [Fintype m] [Fintype n] (u : m × n → 𝕜) :
    partialTraceLeft (Matrix.vecMulVec u (star u)) =
      ∑ i, Matrix.vecMulVec (fun j => u (i, j)) (star fun j => u (i, j)) := by
  ext j j'
  simp [partialTraceLeft, Matrix.vecMulVec_apply, Matrix.sum_apply]

/-- The partial trace of a rank-one positive semidefinite matrix is the sum
of the rank-one positive semidefinite matrices of its slices. -/
theorem partialTraceRight_vecMulVec_star [Fintype m] [Fintype n] (u : m × n → 𝕜) :
    partialTraceRight (Matrix.vecMulVec u (star u)) =
      ∑ j, Matrix.vecMulVec (fun i => u (i, j)) (star fun i => u (i, j)) := by
  ext i i'
  simp [partialTraceRight, Matrix.vecMulVec_apply, Matrix.sum_apply]

/-- The partial trace over the first factor preserves positive semidefiniteness. -/
theorem posSemidef_partialTraceLeft [Fintype m] [Fintype n]
    {A : Matrix (m × n) (m × n) 𝕜}
    (hA : A.PosSemidef) : (partialTraceLeft A).PosSemidef := by
  obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  rw [hv, partialTraceLeft_sum]
  exact Matrix.posSemidef_sum Finset.univ fun k _ => by
    rw [partialTraceLeft_vecMulVec_star]
    exact Matrix.posSemidef_sum Finset.univ fun i _ =>
      Matrix.posSemidef_vecMulVec_self_star _

/-- The partial trace over the second factor preserves positive semidefiniteness. -/
theorem posSemidef_partialTraceRight [Fintype m] [Fintype n]
    {A : Matrix (m × n) (m × n) 𝕜}
    (hA : A.PosSemidef) : (partialTraceRight A).PosSemidef := by
  obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  rw [hv, partialTraceRight_sum]
  exact Matrix.posSemidef_sum Finset.univ fun k _ => by
    rw [partialTraceRight_vecMulVec_star]
    exact Matrix.posSemidef_sum Finset.univ fun j _ =>
      Matrix.posSemidef_vecMulVec_self_star _

/-- The partial trace over the first factor is adjoint to amplification by
the identity, in the trace pairing. -/
theorem trace_partialTraceLeft_mul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix (m × n) (m × n) 𝕜) (B : Matrix n n 𝕜) :
    Matrix.trace (partialTraceLeft A * B)
      = Matrix.trace (A * ((1 : Matrix m m 𝕜) ⊗ₖ B)) := by
  have hL : Matrix.trace (partialTraceLeft A * B)
      = ∑ j, ∑ j', ∑ i, A (i, j) (i, j') * B j' j := by
    show (∑ j, (partialTraceLeft A * B) j j) = _
    simp only [Matrix.mul_apply, partialTraceLeft, Matrix.of_apply, Finset.sum_mul]
  have hR : Matrix.trace (A * ((1 : Matrix m m 𝕜) ⊗ₖ B))
      = ∑ j, ∑ j', ∑ i, A (i, j) (i, j') * B j' j := by
    show (∑ x : m × n, (A * ((1 : Matrix m m 𝕜) ⊗ₖ B)) x x) = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j' _
    simp only [Matrix.one_apply, ite_mul, mul_ite, one_mul, zero_mul, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hL, hR]

/-- The partial trace over the second factor is adjoint to amplification by
the identity, in the trace pairing. -/
theorem trace_partialTraceRight_mul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix (m × n) (m × n) 𝕜) (C : Matrix m m 𝕜) :
    Matrix.trace (partialTraceRight A * C)
      = Matrix.trace (A * (C ⊗ₖ (1 : Matrix n n 𝕜))) := by
  have hL : Matrix.trace (partialTraceRight A * C)
      = ∑ i, ∑ i', ∑ j, A (i, j) (i', j) * C i' i := by
    show (∑ i, (partialTraceRight A * C) i i) = _
    simp only [Matrix.mul_apply, partialTraceRight, Matrix.of_apply, Finset.sum_mul]
  have hR : Matrix.trace (A * (C ⊗ₖ (1 : Matrix n n 𝕜)))
      = ∑ i, ∑ i', ∑ j, A (i, j) (i', j) * C i' i := by
    show (∑ x : m × n, (A * (C ⊗ₖ (1 : Matrix n n 𝕜))) x x) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i' _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hL, hR]

end MathlibExt.LinearAlgebra.Matrix.PartialTrace
