/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Chemistry.Quantum.FinitePostulates
import PhyslibExt.Quantum.FiniteState
import MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional quantum postulate checks

Concrete consumers of `PhyslibExt.Chemistry.Quantum.FinitePostulates`: a two-state Born rule
in the computational basis, the Pauli matrices, a Robertson-inequality instance in a
nondegenerate state, Pauli time evolution, Pauli-`X` eigenvectors, the trace argument, and a
simultaneous diagonalization. The spectral decomposition check uses Mathlib's canonical
spectral theorem.

## i. Overview

These are elaboration and exact-computation checks, not new results. The Pauli matrices are
`σx = !![0, 1; 1, 0]`, `σy = !![0, -I; I, 0]`, and `σz = !![1, 0; 0, -1]` over `ℂ`.

The Born check in section A uses the canonical `Quantum.FiniteState` API: `ψ₊` is a normalized
two-state superposition whose `bornProb` values in the computational basis are both `1 / 2`,
and the sum is `1` by `Chemistry.Quantum.sum_bornProb_unitaryOrthonormalBasis`.

The Robertson check in section C uses the nondegenerate state `ψ₁ = ![(3/5), (4/5)·I]`: the
expectations of `σx`, `σz` are `0`, `-7/25`, the coordinate-sum variances are `1`, `576/625`,
and the commutator expectation is `48·I/25` with squared norm `2304/625`, so both sides of the
checked inequality equal `576/625`. The coordinate-sum variance is proved equal to
`RobertsonUncertainty.variance` on unit states (`variance_matToCLM_eq_coordsum`, via the
matrix-to-`ContinuousLinearMap` bridge `matToCLM`), and the commutator expectation likewise
(`commutatorInner_matToCLM`); the instance is an application of
`MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty.robertson`, not a standalone
computation.

## ii. Key results

Test scaffolding (not new results): `matToCLM`, the matrix-to-`ContinuousLinearMap` bridge,
with `matToCLM_apply`, `isSelfAdjoint_matToCLM`, `meanValue_matToCLM`,
`variance_matToCLM_eq_coordsum`, and `commutatorInner_matToCLM` connecting matrix coordinates
to `RobertsonUncertainty`.

## iii. Table of contents

- A. Born rule for a two-state superposition
- B. Pauli matrices
- C. Robertson inequality for `σx`, `σz`
- D. Pauli time evolution
- E. Pauli-`X` eigenvectors
- F. Trace argument
- G. Simultaneous diagonalization

## iv. References

- `PhyslibExt.Chemistry.Quantum.FinitePostulates`
- `PhyslibExt.Quantum.FiniteState`
- `MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty`
- `Matrix.IsHermitian.spectral_theorem`

## A. Born rule for a two-state superposition
-/

open scoped Matrix

open MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty

local notation "ψ₊" => (WithLp.toLp 2 ![(√2 : ℂ)⁻¹, (√2 : ℂ)⁻¹])

/-- `ψ₊ = ![(√2)⁻¹, (√2)⁻¹]` is normalized. -/
example : Quantum.FiniteState.IsNormalized ψ₊ := by
  rw [Quantum.FiniteState.IsNormalized, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]
  norm_num

/-- In the computational basis, both Born probabilities of `ψ₊` are `1 / 2`. -/
example (i : Fin 2) :
    Quantum.FiniteState.bornProb (EuclideanSpace.basisFun (Fin 2) ℂ) ψ₊ i = 1 / 2 := by
  rw [Quantum.FiniteState.bornProb, EuclideanSpace.basisFun_inner]
  fin_cases i <;> simp

/-- The two Born probabilities of `ψ₊` in the unitary measurement basis `1` sum to `1`, by
`sum_bornProb_unitaryOrthonormalBasis`. -/
example : ∑ i, Quantum.FiniteState.bornProb
    (Chemistry.Quantum.unitaryOrthonormalBasis (1 : Matrix (Fin 2) (Fin 2) ℂ) (one_mem _)) ψ₊ i
    = 1 :=
  Chemistry.Quantum.sum_bornProb_unitaryOrthonormalBasis (1 : Matrix (Fin 2) (Fin 2) ℂ) (one_mem _)
    (by
    rw [Quantum.FiniteState.IsNormalized, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
    norm_num)

/-! ## B. Pauli matrices -/

local notation "σx" => (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
local notation "σy" => (!![0, -Complex.I; Complex.I, 0] : Matrix (Fin 2) (Fin 2) ℂ)
local notation "σz" => (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)

/-- `σx` is Hermitian. -/
example : Matrix.IsHermitian σx :=
  Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- `σz` is Hermitian. -/
example : Matrix.IsHermitian σz :=
  Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- `σy` is Hermitian. -/
example : Matrix.IsHermitian σy :=
  Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

/-- The commutator `[σx, σz] = σx * σz - σz * σx` is `-2 i σy`, with the scalar `-2 * I`. -/
example : σx * σz - σz * σx = (-2 * Complex.I) • σy := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mul_assoc]

/-- The same identity in the literal form `-2 * Complex.I • σy`, which Lean parses as the
matrix product `(-2 : Matrix (Fin 2) (Fin 2) ℂ) * (Complex.I • σy)`. -/
example : σx * σz - σz * σx = -2 * Complex.I • σy := by
  rw [neg_mul, two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-! ## C. Robertson inequality for `σx`, `σz` -/

/-- The nondegenerate test state `ψ₁ = ![(3/5), (4/5)·I]`. -/
noncomputable def ψ₁ : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(3 / 5 : ℂ), (4 / 5 : ℂ) * Complex.I]

/-- A complex `2 × 2` matrix as a continuous linear map on `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def matToCLM (A : Matrix (Fin 2) (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

/-- Application of `matToCLM` is matrix-vector multiplication. -/
lemma matToCLM_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
    matToCLM A x = WithLp.toLp 2 (A *ᵥ x.ofLp) := rfl

/-- `matToCLM` of a Hermitian matrix is self-adjoint. -/
lemma isSelfAdjoint_matToCLM {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian) :
    IsSelfAdjoint (matToCLM A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show inner ℂ (matToCLM A x) y = inner ℂ x (matToCLM A y)
  rw [matToCLM_apply, matToCLM_apply]
  exact Quantum.FiniteState.inner_mulVec_left_of_isHermitian hA _ _

/-- On unit states, the `meanValue` of `matToCLM A` is the real part of the coordinate
expectation. -/
lemma meanValue_matToCLM (A : Matrix (Fin 2) (Fin 2) ℂ) (x : EuclideanSpace ℂ (Fin 2))
    (hx : ‖x‖ = 1) :
    meanValue (matToCLM A) x = (star (A *ᵥ x.ofLp) ⬝ᵥ x.ofLp).re := by
  rw [meanValue_of_norm_eq_one _ hx]
  congr 1
  rw [matToCLM_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp]
  exact dotProduct_comm _ _

/-- Bridge: the coordinate-sum variance equals `RobertsonUncertainty.variance` on unit states
(for Hermitian `A`). -/
lemma variance_matToCLM_eq_coordsum {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin 2)) (hx : ‖x‖ = 1) :
    variance (matToCLM A) x =
      ∑ i, ‖(A *ᵥ x.ofLp - (star (A *ᵥ x.ofLp) ⬝ᵥ x.ofLp) • x.ofLp) i‖ ^ 2 := by
  have hAmv : star (A *ᵥ x.ofLp) ⬝ᵥ x.ofLp = star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
    rw [Matrix.star_mulVec, hA.eq, ← Matrix.dotProduct_mulVec]
  have hexp : ((meanValue (matToCLM A) x : ℝ) : ℂ) = star (A *ᵥ x.ofLp) ⬝ᵥ x.ofLp := by
    rw [meanValue_matToCLM _ _ hx, hAmv]
    refine Complex.ext rfl ?_
    rw [Complex.ofReal_im]
    exact (hA.im_star_dotProduct_mulVec_self _).symm
  rw [variance_of_norm_eq_one _ hx, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ‖(matToCLM A x - ((meanValue (matToCLM A) x : ℝ) : ℂ) • x) i‖ ^ 2 = _
  rw [hexp, matToCLM_apply]
  rfl

/-- Bridge: the commutator expectation of `matToCLM` maps equals the coordinate commutator
expectation. -/
lemma commutatorInner_matToCLM (A B : Matrix (Fin 2) (Fin 2) ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ ((matToCLM A ∘L matToCLM B - matToCLM B ∘L matToCLM A) x) x =
      star ((A * B - B * A) *ᵥ x.ofLp) ⬝ᵥ x.ofLp := by
  rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    matToCLM_apply, matToCLM_apply, matToCLM_apply, matToCLM_apply,
    EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_sub, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp, WithLp.ofLp_toLp, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.sub_mulVec]
  exact dotProduct_comm _ _

/-- `ψ₁ = ![(3/5), (4/5)·I]` is a unit vector. -/
example : star ψ₁.ofLp ⬝ᵥ ψ₁.ofLp = 1 := by
  simp [ψ₁, WithLp.ofLp_toLp, dotProduct, Fin.sum_univ_two, Complex.conj_ofNat, Complex.conj_I,
    mul_comm, mul_left_comm]
  ring_nf
  norm_num

/-- Expectation of `σx` in `ψ₁` is `0`; variance is `1`. -/
example :
    star (σx *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp = 0 ∧
      ∑ i, ‖(σx *ᵥ ψ₁.ofLp - (star (σx *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp) • ψ₁.ofLp) i‖ ^ 2 = 1 := by
  have hE : star (σx *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp = 0 := by
    simp [ψ₁, WithLp.ofLp_toLp, dotProduct, Fin.sum_univ_two, Complex.conj_I, mul_assoc,
      mul_comm, mul_left_comm]
  refine ⟨hE, ?_⟩
  rw [hE]
  simp [ψ₁, WithLp.ofLp_toLp, Fin.sum_univ_two]
  norm_num

/-- Expectation of `σz` in `ψ₁` is `-7/25`; variance is `576/625`. -/
example :
    star (σz *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp = (-7 / 25 : ℂ) ∧
      ∑ i, ‖(σz *ᵥ ψ₁.ofLp - (star (σz *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp) • ψ₁.ofLp) i‖ ^ 2
        = 576 / 625 := by
  have hE : star (σz *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp = (-7 / 25 : ℂ) := by
    simp [ψ₁, WithLp.ofLp_toLp, dotProduct, Fin.sum_univ_two, Complex.conj_I, mul_assoc,
      mul_comm, mul_left_comm]
    ring_nf
    norm_num
  refine ⟨hE, ?_⟩
  rw [hE]
  have hvec : σz *ᵥ ψ₁.ofLp - (-7 / 25 : ℂ) • ψ₁.ofLp
      = ![(96 / 125 : ℂ), (-72 / 125 : ℂ) * Complex.I] := by
    ext i
    fin_cases i <;>
      simp [ψ₁, WithLp.ofLp_toLp, mul_assoc, mul_comm, mul_left_comm] <;> ring_nf
  rw [Fin.sum_univ_two, hvec]
  simp [Complex.norm_I]
  norm_num

/-- The commutator expectation `⟪[σx, σz] ψ₁, ψ₁⟫` is `48·I/25`, with squared norm `2304/625`. -/
example :
    star ((σx * σz - σz * σx) *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp = 48 / 25 * Complex.I ∧
      ‖star ((σx * σz - σz * σx) *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp‖ ^ 2 = 2304 / 625 := by
  have hC : star ((σx * σz - σz * σx) *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp = 48 / 25 * Complex.I := by
    simp [ψ₁, WithLp.ofLp_toLp, dotProduct, Fin.sum_univ_two, Complex.conj_I, mul_assoc,
      mul_comm, mul_left_comm]
    ring_nf
  refine ⟨hC, ?_⟩
  rw [hC]
  simp
  norm_num

/-- `ψ₁` has norm `1`. -/
example : ‖ψ₁‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ψ₁, Fin.sum_univ_two]
  norm_num

/-- Robertson inequality instance for `σx`, `σz` in the nondegenerate state `ψ₁`, as an
application of `robertson`: both variances (`1`, `576/625`) and the commutator bound
(`(1/4) * (2304/625) = 576/625`) are nonzero. -/
example :
    (1 / 4 : ℝ) * ‖star ((σx * σz - σz * σx) *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp‖ ^ 2 ≤
      (∑ i, ‖(σx *ᵥ ψ₁.ofLp - (star (σx *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp) • ψ₁.ofLp) i‖ ^ 2) *
        ∑ i, ‖(σz *ᵥ ψ₁.ofLp - (star (σz *ᵥ ψ₁.ofLp) ⬝ᵥ ψ₁.ofLp) • ψ₁.ofLp) i‖ ^ 2 := by
  have hX : Matrix.IsHermitian σx :=
    Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp
  have hZ : Matrix.IsHermitian σz :=
    Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp
  have hnorm : ‖ψ₁‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [ψ₁, Fin.sum_univ_two]
    norm_num
  rw [← variance_matToCLM_eq_coordsum hX _ hnorm,
    ← variance_matToCLM_eq_coordsum hZ _ hnorm, ← commutatorInner_matToCLM]
  exact robertson (isSelfAdjoint_matToCLM hX) (isSelfAdjoint_matToCLM hZ) hnorm

/-! ## D. Pauli time evolution -/

/-- `exp (-(t / ħ) • (I • σz))` is unitary for every real `t` and `ħ ≠ 0`, by
`unitary_time_evolution`. -/
example (t ħ : ℝ) (hħ : ħ ≠ 0) :
    NormedSpace.exp (-(t / ħ) • (Complex.I • σz)) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  Chemistry.Quantum.unitary_time_evolution _
    (Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp) t ħ hħ

/-- At `t = π * ħ / 2`, Mathlib's `Matrix.exp_diagonal` gives the diagonal matrix with entries
`exp (-(I * π / 2))` and `exp (I * π / 2)`, that is `!![-I, 0; 0, I]`. -/
example (ħ : ℝ) (hħ : ħ ≠ 0) :
    NormedSpace.exp (-((Real.pi * ħ / 2) / ħ) • (Complex.I • σz)) =
        Matrix.diagonal
          ![Complex.exp (-(Complex.I * Real.pi / 2)), Complex.exp (Complex.I * Real.pi / 2)] ∧
      NormedSpace.exp (-((Real.pi * ħ / 2) / ħ) • (Complex.I • σz)) =
        !![-Complex.I, 0; 0, Complex.I] := by
  have hdiag : NormedSpace.exp (-((Real.pi * ħ / 2) / ħ) • (Complex.I • σz)) =
      Matrix.diagonal
        ![Complex.exp (-(Complex.I * Real.pi / 2)), Complex.exp (Complex.I * Real.pi / 2)] := by
    have hθ : (Real.pi * ħ / 2) / ħ = Real.pi / 2 := by field_simp
    have hσz : σz = Matrix.diagonal ![1, -1] := by
      rw [Matrix.diagonal_fin_two]
      rfl
    have hvec : -(Real.pi / 2) • Complex.I • ![(1 : ℂ), -1] =
        ![-(Complex.I * Real.pi / 2), Complex.I * Real.pi / 2] := by
      ext i
      fin_cases i <;> simp [Complex.real_smul] <;> ring
    rw [hθ, hσz, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.exp_diagonal, hvec]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    fin_cases i <;> rfl
  refine ⟨hdiag, ?_⟩
  have hneg : Complex.exp (-(Complex.I * Real.pi / 2)) = -Complex.I := by
    rw [show -(Complex.I * Real.pi / 2) = -Real.pi / 2 * Complex.I by ring]
    exact Complex.exp_neg_pi_div_two_mul_I
  have hpos : Complex.exp (Complex.I * Real.pi / 2) = Complex.I := by
    rw [show Complex.I * Real.pi / 2 = Real.pi / 2 * Complex.I by ring]
    exact Complex.exp_pi_div_two_mul_I
  rw [hdiag, hneg, hpos, Matrix.diagonal_fin_two]
  rfl

/-! ## E. Pauli-`X` eigenvectors -/

/-- `![1, 1]` is an eigenvector of `σx` with eigenvalue `1`. -/
example : σx *ᵥ ![1, 1] = (1 : ℂ) • ![1, 1] := by
  ext i
  fin_cases i <;> simp

/-- `![1, -1]` is an eigenvector of `σx` with eigenvalue `-1`. -/
example : σx *ᵥ ![1, -1] = (-1 : ℂ) • ![1, -1] := by
  ext i
  fin_cases i <;> simp

/-- The two eigenvectors of `σx` are orthogonal. -/
example : star (![1, 1] : Fin 2 → ℂ) ⬝ᵥ ![1, -1] = 0 := by
  simp [dotProduct]

/-- Mathlib's spectral theorem decomposes `σx` using a unitary eigenbasis and real eigenvalues. -/
example :
    ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ d : Fin 2 → ℝ,
      σx = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ := by
  have hX : Matrix.IsHermitian σx :=
    Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp
  refine ⟨hX.eigenvectorUnitary, hX.eigenvectorUnitary.2, hX.eigenvalues, ?_⟩
  refine hX.spectral_theorem.trans ?_
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

/-! ## F. Trace argument -/

/-- The trace of the commutator `[σx, σz]` vanishes. -/
example : Matrix.trace (σx * σz - σz * σx) = 0 := by
  simp [Matrix.trace_fin_two]

/-- The trace of `(I * ħ) • 1` on `ℂ²` is `2 * I * ħ`, which is nonzero for `ħ ≠ 0`. -/
example (ħ : ℝ) (hħ : ħ ≠ 0) :
    Matrix.trace ((Complex.I * (ħ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        2 * Complex.I * ħ ∧
      (2 * Complex.I * ħ : ℂ) ≠ 0 := by
  refine ⟨?_, by simp [hħ]⟩
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- `no_finite_dim_canonical_commutator` on `ℂ²`: no `X`, `P` satisfy `[X, P] = I • ħ • 1`. -/
example (ħ : ℝ) (hħ : ħ ≠ 0) :
    ¬ ∃ X P : Matrix (Fin 2) (Fin 2) ℂ, X * P - P * X = Complex.I • (ħ : ℂ) • 1 :=
  fun ⟨X, P, h⟩ => Chemistry.Quantum.no_finite_dim_canonical_commutator two_pos ħ hħ X P h

/-! ## G. Simultaneous diagonalization -/

/-- `simultaneous_orthonormal_eigenbasis` applies to the commuting, non-diagonal Hermitian pair
`σx` and `!![2, 1; 1, 2]`. -/
example :
    ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ a b : Fin 2 → ℝ,
      Uᴴ * σx * U = Matrix.diagonal (fun i => (a i : ℂ)) ∧
        Uᴴ * !![2, 1; 1, 2] * U = Matrix.diagonal (fun i => (b i : ℂ)) :=
  Chemistry.Quantum.simultaneous_orthonormal_eigenbasis _ _
    (Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp)
    (Matrix.IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp)
    (by
      change σx * !![2, 1; 1, 2] = !![2, 1; 1, 2] * σx
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num)
