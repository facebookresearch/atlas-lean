/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.UnitaryErrorBudget
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open MathlibExt.Quantum.UnitaryErrorBudget

namespace MathlibExt.Quantum.UnitaryErrorBudgetTests

/-- Equal gate lists have zero total error. -/
example {n : Type*} [Fintype n] [DecidableEq n] {T : ℕ}
    (U : Fin T → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup n ℂ) :
    ‖circuitProd U - circuitProd U‖ ≤ ∑ _i : Fin T, (0 : ℝ) :=
  norm_circuit_sub_le U U hU hU (fun _ => 0) (fun i => by simp)

/-- Replacing one gate by the identity costs at most that gate's distance
from the identity. -/
theorem drop_one_gate {n : Type*} [Fintype n] [DecidableEq n] {T : ℕ}
    (U : Fin T → Matrix n n ℂ)
    (hU : ∀ i, U i ∈ Matrix.unitaryGroup n ℂ) (j : Fin T) :
    ‖circuitProd U - circuitProd (Function.update U j 1)‖ ≤
      ‖U j - 1‖ := by
  have hV : ∀ i, Function.update U j 1 i ∈ Matrix.unitaryGroup n ℂ := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact one_mem _
    · rw [Function.update_of_ne hij]
      exact hU i
  have hε : ∀ i, ‖U i - Function.update U j 1 i‖ ≤
      (if i = j then ‖U j - 1‖ else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      simp
    · simp [hij]
  have h := norm_circuit_sub_le U (Function.update U j 1) hU hV _ hε
  rw [Finset.sum_ite_eq'] at h
  simp only [Finset.mem_univ, ite_true] at h
  exact h

/-- A two-dimensional phase gate is unitary. -/
theorem phase_diagonal_mem_unitaryGroup (φ : ℝ) :
    Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] ∈
      Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have he : (starRingEnd ℂ) (Complex.exp (φ * Complex.I)) *
      Complex.exp (φ * Complex.I) = 1 := by
    rw [RCLike.conj_mul, Complex.norm_exp_ofReal_mul_I φ]
    simp
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  have hw : (fun i : Fin 2 =>
        star (![1, Complex.exp (φ * Complex.I)] : Fin 2 → ℂ) i *
          ![1, Complex.exp (φ * Complex.I)] i) = fun _ => 1 := by
    funext i
    fin_cases i <;> simp [he]
  rw [hw, Matrix.diagonal_one]

/-- The phase-gate distance from the identity is the scalar phase distance. -/
theorem phase_diagonal_sub_one_norm (φ : ℝ) :
    ‖(Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
        Matrix (Fin 2) (Fin 2) ℂ) - 1‖ =
      ‖Complex.exp (φ * Complex.I) - 1‖ := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal (fun _ => 1) := Matrix.diagonal_one.symm
  have hsub : (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
        Matrix (Fin 2) (Fin 2) ℂ) - 1 =
      Matrix.diagonal ![0, Complex.exp (φ * Complex.I) - 1] := by
    rw [h1, Matrix.diagonal_sub]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hsub, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    fin_cases i <;> simp
  · have h1 : (![0, Complex.exp (φ * Complex.I) - 1] : Fin 2 → ℂ) 1 =
        Complex.exp (φ * Complex.I) - 1 := by simp
    rw [← h1]
    exact norm_le_pi_norm _ _

/-- The first-coordinate diagonal matrix is an orthogonal projection. -/
theorem diagonal_one_zero_isStarProjection :
    IsStarProjection
      (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [isStarProjection_iff']
  constructor
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    fin_cases i <;> simp

/-- The first standard basis vector is normalized. -/
theorem single_zero_one_norm :
    ‖EuclideanSpace.single (0 : Fin 2) (1 : ℂ)‖ = 1 := by
  have h := EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)
  exact h.norm_eq_one 0

/-- Applying `norm_inner_conj_sub_le` to the phase-gate and identity fixtures
gives the scalar phase-distance bound. -/
theorem phase_inner_conj_le (φ : ℝ) :
    ‖⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          ((star (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
              Matrix (Fin 2) (Fin 2) ℂ)) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
              Matrix (Fin 2) (Fin 2) ℂ))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ -
      ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          ((star (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * 1)
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ‖ ≤
      2 * ‖Complex.exp (φ * Complex.I) - 1‖ := by
  have h :=
    norm_inner_conj_sub_le
      (U := (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
        Matrix (Fin 2) (Fin 2) ℂ)) (V := 1)
      (P := (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      (phase_diagonal_mem_unitaryGroup φ) (one_mem _)
      diagonal_one_zero_isStarProjection
      (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_one_norm
  rw [phase_diagonal_sub_one_norm] at h
  exact h

/-- `1 / √2` as a complex number. -/
noncomputable def sqrt2inv : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The squared Hadamard entry `(1/√2)²` equals `1/2`. -/
theorem sqrt2_inv_sq : sqrt2inv * sqrt2inv = 1 / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast h2
  simp only [sqrt2inv]
  rw [← mul_inv, hsq, one_div]

/-- `1/√2` is fixed by complex conjugation. -/
theorem star_sqrt2inv : star sqrt2inv = sqrt2inv := by
  simp [sqrt2inv]

/-- Real Hadamard-style gate with entries `±1/√2`. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  !![sqrt2inv, sqrt2inv; sqrt2inv, -sqrt2inv]

/-- The Hadamard-style gate is unitary. -/
theorem hadamard_mem_unitaryGroup :
    hadamard ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, Matrix.mul_apply, Fin.sum_univ_two, star_sqrt2inv, sqrt2_inv_sq] <;>
    simp only [starRingEnd_apply, star_sqrt2inv] <;>
    norm_num [sqrt2_inv_sq]

/-- Pauli-X gate. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-X is unitary. -/
theorem pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

/-- Conjugating the first-coordinate projection by the Hadamard-style gate
yields the all-`1/2` matrix. -/
theorem hadamard_conj_proj :
    star hadamard * (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
        hadamard =
      (!![1 / 2, 1 / 2; 1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      star_sqrt2inv, sqrt2_inv_sq] <;>
    simp only [starRingEnd_apply, star_neg, star_sqrt2inv, mul_neg, neg_mul, sqrt2_inv_sq] <;>
    norm_num

/-- A two-gate chronological circuit applies the first gate first: the total
operator is `B * A`. -/
theorem circuitProd_pair (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    circuitProd ![A, B] = B * A := by
  simp [circuitProd, List.ofFn_succ, List.ofFn_zero, List.reverse_cons,
    List.reverse_nil, List.prod_append, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one]

/-- `X * H` puts the negated entry at `(0, 1)`. -/
theorem pauliX_mul_hadamard :
    pauliX * hadamard =
      (!![sqrt2inv, -sqrt2inv; sqrt2inv, sqrt2inv] :
        Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, hadamard, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

/-- `H * X` puts the negated entry at `(1, 0)`: gate order matters. -/
theorem hadamard_mul_pauliX :
    hadamard * pauliX =
      (!![sqrt2inv, sqrt2inv; -sqrt2inv, sqrt2inv] :
        Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, hadamard, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

/-- The two-gate Hadamard-then-X circuit equals `X * H`. Under the wrong
(list-order) product this would be `H * X`, a different matrix. -/
theorem circuit_two_gate_value :
    circuitProd ![hadamard, pauliX] =
      (!![sqrt2inv, -sqrt2inv; sqrt2inv, sqrt2inv] :
        Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [circuitProd_pair, pauliX_mul_hadamard]

/-- Conjugating the first-coordinate projection by the two-gate circuit. -/
theorem circuit_conj_value :
    star (circuitProd ![hadamard, pauliX]) *
        (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
        (circuitProd ![hadamard, pauliX]) =
      (!![1 / 2, -1 / 2; -1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [circuit_two_gate_value]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      star_sqrt2inv, sqrt2_inv_sq] <;>
    simp only [starRingEnd_apply, star_neg, star_sqrt2inv, mul_neg, neg_mul, sqrt2_inv_sq] <;>
    norm_num

/-- The quadratic form on the first basis vector reads off the `(0, 0)`
entry. -/
theorem inner_single_zero_toEuclideanCLM (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ =
      M 0 0 := by
  rw [EuclideanSpace.inner_single_left, ← ContinuousLinearMap.coe_coe,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.single]

/-- The Hadamard-conjugated form on the first basis vector equals `1/2`. -/
theorem hadamard_inner_eq :
    ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
        (star hadamard * (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
          hadamard)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ =
      1 / 2 := by
  simp [hadamard_conj_proj, inner_single_zero_toEuclideanCLM,
    Matrix.cons_val_zero]

/-- The identity-conjugated form on the first basis vector equals `1`. -/
theorem one_inner_eq :
    ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
        (star (1 : Matrix (Fin 2) (Fin 2) ℂ) *
          (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * 1)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ =
      1 := by
  simp [star_one, one_mul, mul_one, inner_single_zero_toEuclideanCLM,
    Matrix.diagonal_apply, Matrix.cons_val_zero]

/-- The Hadamard quadratic-form change is the nonzero value `-1/2`, so the
bound below is not vacuous. -/
theorem hadamard_inner_sub :
    (⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star hadamard * (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            hadamard)
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ -
      ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (1 : Matrix (Fin 2) (Fin 2) ℂ) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * 1)
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ) =
      (-1 / 2 : ℂ) := by
  rw [hadamard_inner_eq, one_inner_eq]
  ring

/-- Applying `norm_inner_conj_sub_le` to the Hadamard-style and identity
fixtures gives a nonvacuous instance of the bound. -/
theorem hadamard_inner_conj_le :
    ‖⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star hadamard * (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            hadamard)
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ -
      ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (1 : Matrix (Fin 2) (Fin 2) ℂ) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * 1)
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ‖ ≤
      2 * ‖hadamard - 1‖ := by
  have h :=
    norm_inner_conj_sub_le (U := hadamard) (V := 1)
      (P := (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
      hadamard_mem_unitaryGroup (one_mem _)
      diagonal_one_zero_isStarProjection
      (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_one_norm
  exact h

/-- The two-gate circuit form on the first basis vector equals `1/2`. -/
theorem circuit_inner_eq :
    ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
        (star (circuitProd ![hadamard, pauliX]) *
          (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
          (circuitProd ![hadamard, pauliX]))
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ =
      1 / 2 := by
  simp [circuit_conj_value, inner_single_zero_toEuclideanCLM,
    Matrix.cons_val_zero]

/-- The identity-circuit form on the first basis vector equals `1`. -/
theorem circuit_identity_inner_eq :
    ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
        (star (circuitProd ![1, 1]) *
          (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
          (circuitProd ![1, 1]))
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ =
      1 := by
  have hc1 : circuitProd ![1, 1] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [circuitProd_pair, mul_one]
  simp [hc1, star_one, one_mul, mul_one, inner_single_zero_toEuclideanCLM,
    Matrix.diagonal_apply, Matrix.cons_val_zero]

/-- The two-gate circuit change is the nonzero value `-1/2`. -/
theorem circuit_inner_sub :
    (⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (circuitProd ![hadamard, pauliX]) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (circuitProd ![hadamard, pauliX]))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ -
      ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (circuitProd ![1, 1]) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (circuitProd ![1, 1]))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ) =
      (-1 / 2 : ℂ) := by
  rw [circuit_inner_eq, circuit_identity_inner_eq]
  ring

/-- Applying `norm_inner_circuit_conj_sub_le` to the two-gate Hadamard
circuit against the identity circuit. -/
theorem hadamard_circuit_inner_conj_le :
    ‖⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (circuitProd ![hadamard, pauliX]) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (circuitProd ![hadamard, pauliX]))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ -
      ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (circuitProd ![1, 1]) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (circuitProd ![1, 1]))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ‖ ≤
      2 * (‖hadamard - 1‖ + ‖pauliX - 1‖) := by
  have hU : ∀ i : Fin 2,
      ![hadamard, pauliX] i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    intro i
    fin_cases i
    · simpa [Matrix.cons_val_zero] using hadamard_mem_unitaryGroup
    · simpa [Matrix.cons_val_one] using pauliX_mem_unitaryGroup
  have hV : ∀ i : Fin 2,
      (![(1 : Matrix (Fin 2) (Fin 2) ℂ), 1] : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) i ∈
        Matrix.unitaryGroup (Fin 2) ℂ := by
    intro i
    fin_cases i
    · simpa [Matrix.cons_val_zero] using one_mem (Matrix.unitaryGroup (Fin 2) ℂ)
    · simpa [Matrix.cons_val_one] using one_mem (Matrix.unitaryGroup (Fin 2) ℂ)
  have hε : ∀ i : Fin 2, ‖![hadamard, pauliX] i -
      (![(1 : Matrix (Fin 2) (Fin 2) ℂ), 1] : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) i‖ ≤
      ![‖hadamard - 1‖, ‖pauliX - 1‖] i := by
    intro i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      exact le_refl _
  have h := norm_inner_circuit_conj_sub_le ![hadamard, pauliX]
    (![(1 : Matrix (Fin 2) (Fin 2) ℂ), 1] : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    hU hV ![‖hadamard - 1‖, ‖pauliX - 1‖] hε
    diagonal_one_zero_isStarProjection
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) single_zero_one_norm
  rw [Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

/-- Applying `norm_inner_circuit_conj_sub_le` to single-gate phase and identity
circuits gives the scalar phase-distance bound. -/
theorem phase_circuit_inner_conj_le (φ : ℝ) :
    ‖⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (circuitProd fun _ : Fin 1 =>
              (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
                Matrix (Fin 2) (Fin 2) ℂ)) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (circuitProd fun _ : Fin 1 =>
              (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
                Matrix (Fin 2) (Fin 2) ℂ)))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ -
      ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          (star (circuitProd fun _ : Fin 1 =>
              (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (circuitProd fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ‖ ≤
      2 * ‖Complex.exp (φ * Complex.I) - 1‖ := by
  have hU : ∀ i : Fin 1, (fun _ : Fin 1 =>
      (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
        Matrix (Fin 2) (Fin 2) ℂ)) i ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    fun _ => phase_diagonal_mem_unitaryGroup φ
  have hV : ∀ i : Fin 1, (fun _ : Fin 1 =>
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) i ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    fun _ => one_mem _
  have hε : ∀ i : Fin 1, ‖(fun _ : Fin 1 =>
      (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
        Matrix (Fin 2) (Fin 2) ℂ)) i -
        (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)) i‖ ≤
      (fun _ : Fin 1 => ‖Complex.exp (φ * Complex.I) - 1‖) i := by
    intro i
    show ‖(Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
      Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ ‖Complex.exp (φ * Complex.I) - 1‖
    rw [phase_diagonal_sub_one_norm]
  have h := norm_inner_circuit_conj_sub_le
    (fun _ : Fin 1 => (Matrix.diagonal ![1, Complex.exp (φ * Complex.I)] :
      Matrix (Fin 2) (Fin 2) ℂ))
    (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ))
    hU hV (fun _ : Fin 1 => ‖Complex.exp (φ * Complex.I) - 1‖) hε
    diagonal_one_zero_isStarProjection (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))
    single_zero_one_norm
  rw [Fin.sum_univ_one] at h
  exact h

/-- At phase zero the scalar bound computes to zero. -/
example :
    ‖⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          ((star (Matrix.diagonal ![1, Complex.exp ((0 : ℝ) * Complex.I)] :
              Matrix (Fin 2) (Fin 2) ℂ)) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *
            (Matrix.diagonal ![1, Complex.exp ((0 : ℝ) * Complex.I)] :
              Matrix (Fin 2) (Fin 2) ℂ))
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ -
      ⟪EuclideanSpace.single (0 : Fin 2) (1 : ℂ),
        Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
          ((star (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
            (Matrix.diagonal ![1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * 1)
          (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))⟫_ℂ‖ ≤ 0 := by
  have h := phase_inner_conj_le 0
  have h0 : (2 : ℝ) * ‖Complex.exp ((0 : ℝ) * Complex.I) - 1‖ = 0 := by
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, norm_zero,
      mul_zero]
  rw [h0] at h
  exact h

/-- Empty circuits have zero mutual error. -/
example {n : Type*} [Fintype n] [DecidableEq n]
    (U V : Fin 0 → Matrix n n ℂ) :
    ‖(List.ofFn U).prod - (List.ofFn V).prod‖ ≤ (0 : ℝ) := by
  simp only [List.ofFn_zero, List.prod_nil, sub_self, norm_zero, le_refl]

/-- In dimension zero, every pair of unitaries has zero mutual distance. -/
example (U V : Matrix (Fin 0) (Fin 0) ℂ) : ‖U - V‖ = 0 := by
  have h : U = V := Subsingleton.elim _ _
  rw [h, sub_self, norm_zero]

#print axioms norm_list_ofFn_prod_sub_le
#print axioms norm_circuit_sub_le
#print axioms norm_inner_conj_sub_le
#print axioms norm_inner_circuit_conj_sub_le

end MathlibExt.Quantum.UnitaryErrorBudgetTests
