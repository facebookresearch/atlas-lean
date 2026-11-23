/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PosSemidefDeterminant
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Order

/-!
# Factored semidefinite-programming lower bound

For a complex SDP with data matrices and a factored certificate
of the form `Y = F Fᴴ` (positive semidefinite by construction),
any feasible `W` has objective at least the certificate value.
The key positivity input is the canonical
`Matrix.PosSemidef.trace_mul_nonneg_re`. A two-dimensional
example attains the bound `1/2`, and perturbed multipliers and a
wrong factorization are shown to break it.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.FactoredSDPLowerBound

open scoped Matrix ComplexOrder MatrixOrder

/-- PSD trace nonnegativity from a factorization: for `W` positive semidefinite and any
`F`, `Re(trace(F Fᴴ W)) ≥ 0`. -/
theorem re_trace_factor_mul_nonneg (n k : ℕ) (F : Matrix (Fin n) (Fin k) ℂ)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.PosSemidef) :
    0 ≤ ((F * Fᴴ * W).trace).re := by
  have hFF : (F * Fᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose F
  exact Matrix.PosSemidef.trace_mul_nonneg_re hFF hW

/-- Linearity of `Re ∘ trace` over the certificate matrix:
`Re tr((C + Σ λᵢ Aᵢ + Σ νⱼ Eⱼ) W) = Re tr(C W) + Σ λᵢ Re tr(Aᵢ W) + Σ νⱼ Re tr(Eⱼ W)`. -/
theorem re_trace_certificate_mul (n m p : ℕ) (C : Matrix (Fin n) (Fin n) ℂ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (E : Fin p → Matrix (Fin n) (Fin n) ℂ)
    (lam : Fin m → ℝ) (nu : Fin p → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    (((C + ∑ i, (lam i : ℂ) • A i + ∑ j, (nu j : ℂ) • E j) * W).trace).re =
      ((C * W).trace).re + ∑ i, lam i * ((A i * W).trace).re +
        ∑ j, nu j * ((E j * W).trace).re := by
  rw [add_mul, add_mul, Matrix.trace_add, Matrix.trace_add]
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [Matrix.trace_sum, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Complex.add_re, Complex.add_re, Complex.re_sum, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

/-- **Factored dual certificate lower bound.** For the Hermitian PSD matrix problem
minimizing `Re(trace(C W)) + c0` subject to `Re(trace(Aᵢ W)) ≤ bᵢ` and `Re(trace(Eⱼ W)) = dⱼ`,
if `λ ≥ 0` and `C + Σ λᵢ Aᵢ + Σ νⱼ Eⱼ = F Fᴴ`, then every feasible `W` has objective at least
`c0 - Σ λᵢ bᵢ - Σ νⱼ dⱼ`. -/
theorem factored_certificate_lower_bound (n m p k : ℕ) (C : Matrix (Fin n) (Fin n) ℂ)
    (c0 : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (E : Fin p → Matrix (Fin n) (Fin n) ℂ) (d : Fin p → ℝ)
    (hC : C.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hE : ∀ j, (E j).IsHermitian)
    (lam : Fin m → ℝ) (nu : Fin p → ℝ) (F : Matrix (Fin n) (Fin k) ℂ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hcert : C + ∑ i, (lam i : ℂ) • A i + ∑ j, (nu j : ℂ) • E j = F * Fᴴ)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.PosSemidef)
    (hineq : ∀ i, ((A i * W).trace).re ≤ b i)
    (heq : ∀ j, ((E j * W).trace).re = d j) :
    c0 - ∑ i, lam i * b i - ∑ j, nu j * d j ≤ ((C * W).trace).re + c0 := by
  have hlin := re_trace_certificate_mul n m p C A E lam nu W
  have hnonneg := re_trace_factor_mul_nonneg n k F W hW
  rw [← hcert] at hnonneg
  rw [hlin] at hnonneg
  have hle : ∑ i, lam i * ((A i * W).trace).re ≤ ∑ i, lam i * b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hineq i) (hlam i)
  have heq' : ∑ j, nu j * ((E j * W).trace).re = ∑ j, nu j * d j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [heq j]
  linarith

/-- The same certificate, stated as a lower bound for the whole problem: the bound lies in
`lowerBounds` of the objective values of the feasible set. -/
theorem factored_certificate_mem_lowerBounds (n m p k : ℕ) (C : Matrix (Fin n) (Fin n) ℂ)
    (c0 : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (b : Fin m → ℝ)
    (E : Fin p → Matrix (Fin n) (Fin n) ℂ) (d : Fin p → ℝ)
    (hC : C.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (hE : ∀ j, (E j).IsHermitian)
    (lam : Fin m → ℝ) (nu : Fin p → ℝ) (F : Matrix (Fin n) (Fin k) ℂ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hcert : C + ∑ i, (lam i : ℂ) • A i + ∑ j, (nu j : ℂ) • E j = F * Fᴴ) :
    c0 - ∑ i, lam i * b i - ∑ j, nu j * d j ∈
      lowerBounds ((fun W : Matrix (Fin n) (Fin n) ℂ => ((C * W).trace).re + c0) ''
        {W | W.PosSemidef ∧ (∀ i, ((A i * W).trace).re ≤ b i) ∧
          ∀ j, ((E j * W).trace).re = d j}) := by
  intro y hy
  obtain ⟨W, ⟨hW, hineq, heq⟩, rfl⟩ := hy
  exact factored_certificate_lower_bound n m p k C c0 A b E d hC hA hE lam nu F
    hlam hcert W hW hineq heq

/-! ### Validation instance (complex-rational, both constraint kinds) -/

/-- Example cost `C = [[1, -i], [i, 2]]`. -/
def exampleC : Matrix (Fin 2) (Fin 2) ℂ := !![1, -Complex.I; Complex.I, 2]

/-- Example inequality matrix `A = diag(1, 0)` (with `b = 1/2`: `W₁₁ ≤ 1/2`). -/
def exampleA : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- Example equality matrix `E = I` (with `d = 1`: `trace W = 1`). -/
def exampleE : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- Example factor `F = [1, i]ᵀ`, so `F Fᴴ = [[1, -i], [i, 1]]`. -/
def exampleF : Matrix (Fin 2) (Fin 1) ℂ := !![1; Complex.I]

/-- Example optimizer `W = (1/2) [[1, i], [-i, 1]] = v vᴴ` with `v = [1, -i]ᵀ / √2`. -/
noncomputable def exampleW : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2]

/-- Validation: the example coefficient matrices are Hermitian. -/
theorem example_coefficients_hermitian :
    exampleC.IsHermitian ∧ exampleA.IsHermitian ∧ exampleE.IsHermitian := by
  refine ⟨?_, ?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [exampleC, Complex.conj_I]
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [exampleA]
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [exampleE]

/-- Validation: exact complex-rational certificate identity with `λ = 1 ≥ 0` and the
sign-free equality multiplier `ν = -1`: `C + 1 • A + (-1) • E = F Fᴴ`. -/
theorem example_certificate_identity :
    exampleC + ∑ i : Fin 1, (((fun _ => (1 : ℝ)) i : ℝ) : ℂ) • (fun _ => exampleA) i +
        ∑ j : Fin 1, (((fun _ => (-1 : ℝ)) j : ℝ) : ℂ) • (fun _ => exampleE) j =
      exampleF * exampleFᴴ := by
  simp only [Fin.sum_univ_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exampleC, exampleA, exampleE, exampleF,
    Matrix.mul_apply]
  all_goals ring

/-- Validation: the certified bound `0 - 1 * (1/2) - (-1) * 1 = 1/2` holds for every PSD `W`
with `W₁₁ ≤ 1/2` and `trace W = 1`. -/
theorem example_lower_bound (W : Matrix (Fin 2) (Fin 2) ℂ) (hW : W.PosSemidef)
    (hineq : ((exampleA * W).trace).re ≤ 1 / 2)
    (heq : ((exampleE * W).trace).re = 1) :
    (1 / 2 : ℝ) ≤ ((exampleC * W).trace).re + 0 := by
  have hH := example_coefficients_hermitian
  have hcert := example_certificate_identity
  have h := factored_certificate_lower_bound 2 1 1 1 exampleC 0
    (fun _ => exampleA) (fun _ => 1 / 2) (fun _ => exampleE) (fun _ => 1)
    hH.1 (fun _ => hH.2.1) (fun _ => hH.2.2)
    (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) exampleF
    (by intro i; fin_cases i; norm_num) hcert W hW
    (by intro i; fin_cases i; simpa using hineq)
    (by intro j; fin_cases j; simpa using heq)
  simp only [Fin.sum_univ_one, one_mul, mul_one] at h
  linarith

/-- Validation (boundary): `exampleW` is feasible, its inequality constraint is active, and
it attains the certified bound `1/2`, so the bound is sharp here. -/
theorem example_bound_attained :
    exampleW.PosSemidef ∧ ((exampleA * exampleW).trace).re = 1 / 2 ∧
      ((exampleE * exampleW).trace).re = 1 ∧ ((exampleC * exampleW).trace).re + 0 = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hF : exampleW = (1 / 2 : ℝ) •
        ((!![(1 : ℂ); -Complex.I] : Matrix (Fin 2) (Fin 1) ℂ) *
          (!![(1 : ℂ); -Complex.I])ᴴ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [exampleW, Matrix.mul_apply,
        -Matrix.cons_mul]
      all_goals ring
    rw [hF]
    exact Matrix.PosSemidef.smul (Matrix.posSemidef_self_mul_conjTranspose _)
      (by norm_num)
  · simp [exampleA, exampleW, Matrix.trace_fin_two]
  · simp [exampleE, exampleW, Matrix.trace_fin_two]; norm_num
  · simp [exampleC, exampleW, Matrix.trace_fin_two]; ring

/-! ### Violated premises -/

/-- Violated premise: the hypothesis `λ ≥ 0` cannot be dropped. With `n = m = k = 1`, no
equality constraints and `c0 = 0`, take `C = [2]`, `A = [1]`, `b = 1`, `λ = -1`, `F = [1]`:
the identity `C + λ A = F Fᴴ` holds and `W = 0` is feasible, yet the claimed bound `1`
exceeds the objective `0`. -/
theorem nonneg_multiplier_necessary :
    ¬ ∀ (C : Matrix (Fin 1) (Fin 1) ℂ) (A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ)
        (b lam : Fin 1 → ℝ) (F : Matrix (Fin 1) (Fin 1) ℂ) (W : Matrix (Fin 1) (Fin 1) ℂ),
        C.IsHermitian → (∀ i, (A i).IsHermitian) →
        C + ∑ i, (lam i : ℂ) • A i = F * Fᴴ → W.PosSemidef →
        (∀ i, ((A i * W).trace).re ≤ b i) →
        0 - ∑ i, lam i * b i ≤ ((C * W).trace).re + 0 := by
  intro h
  have hC : (!![2] : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i; fin_cases j; simp
  have hA : ∀ i : Fin 1, ((fun _ => (!![1] : Matrix (Fin 1) (Fin 1) ℂ)) i).IsHermitian := by
    intro i
    fin_cases i
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i; fin_cases j; simp
  have hcert : (!![2] : Matrix (Fin 1) (Fin 1) ℂ) +
      ∑ i : Fin 1, (((fun _ => (-1 : ℝ)) i : ℝ) : ℂ) •
        (fun _ => (!![1] : Matrix (Fin 1) (Fin 1) ℂ)) i =
      (!![1] : Matrix (Fin 1) (Fin 1) ℂ) * (!![1] : Matrix (Fin 1) (Fin 1) ℂ)ᴴ := by
    simp only [Fin.sum_univ_one]
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.mul_apply]
    all_goals ring
  have hW : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef := Matrix.PosSemidef.zero
  have hfeas : ∀ i : Fin 1, ((((fun _ => (!![1] : Matrix (Fin 1) (Fin 1) ℂ)) i) * 0).trace).re ≤
      (fun _ => (1 : ℝ)) i := by
    intro i
    fin_cases i
    simp
  have hconcl := h (!![2]) (fun _ => !![1]) (fun _ => 1) (fun _ => -1) (!![1]) 0
    hC hA hcert hW hfeas
  simp only [Fin.sum_univ_one, mul_zero, Matrix.trace_zero, Complex.zero_re,
    zero_add, mul_one] at hconcl
  norm_num at hconcl

/-- Violated premise: an incorrect slack factorization invalidates the certificate. With
`n = 1`, `C = 0`, one equality `E = [1]`, `d = 1`, and `ν = -2`, the slack
`C + ν E = [-2]` equals no `F Fᴴ` (any width `k`), and the claimed bound `0 - (-2) * 1 = 2`
exceeds the objective `0` of the feasible point `W = [1]`. -/
theorem wrong_factorization_bound_fails (k : ℕ) :
    (∀ F : Matrix (Fin 1) (Fin k) ℂ,
        (0 : Matrix (Fin 1) (Fin 1) ℂ) + ((-2 : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠
          F * Fᴴ) ∧
      (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef ∧
      (((1 : Matrix (Fin 1) (Fin 1) ℂ) * 1).trace).re = 1 ∧
      (((0 : Matrix (Fin 1) (Fin 1) ℂ) * 1).trace).re + 0 < 0 - (-2) * 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F hcon
    have h00 : ((0 : Matrix (Fin 1) (Fin 1) ℂ) + ((-2 : ℝ) : ℂ) • 1) 0 0 =
        (F * Fᴴ) 0 0 := by rw [hcon]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
      Matrix.one_apply_eq, mul_one, zero_add] at h00
    have hre : (((-2 : ℝ) : ℂ)).re = ((F * Fᴴ) 0 0).re := by rw [← h00]
    rw [Matrix.mul_apply, Complex.re_sum] at hre
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re] at hre
    have hnn : 0 ≤ ∑ j, Complex.normSq (F 0 j) :=
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    linarith
  · exact Matrix.PosSemidef.one
  · simp
  · simp

end MathlibExt.Analysis.Convex.FactoredSDPLowerBound
