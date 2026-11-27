/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Field.GeomSum

/-!
# The quantum Fourier transform matrix

The quantum Fourier transform on `q` basis states is the matrix `A_q` whose `(a, c)` entry is
`q ^ (-1/2) * exp (2 π i a c / q)`: it maps the basis state `|a⟩` to
`q ^ (-1/2) * ∑_c exp (2 π i a c / q) |c⟩` (Shor 1997, Section 4, equation (4.1)). This file
defines it and proves that it is a unitary matrix, which is what makes it a legitimate quantum
operation. Mathlib's `ZMod.dft` is the unnormalised discrete Fourier transform on functions
`ZMod q → E`; this file states the normalised matrix form used in quantum computing.

## Main results

* `qftMatrix q`: the `q × q` quantum Fourier transform matrix.
* `qftMatrix_mem_unitaryGroup`: `qftMatrix q` is unitary.
* `qftMatrix_transpose`: `qftMatrix q` is symmetric.

## Source

P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a
quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509 (arXiv:quant-ph/9508027), Section 4,
equation (4.1).
-/

@[expose] public section

open Complex Matrix
open scoped Real ComplexConjugate

namespace MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

/-- **Quantum Fourier transform matrix.** For a natural number `q`, the `q × q` complex matrix
`A_q` with `(a, c)` entry `q ^ (-1/2) * exp (2 π i a c / q)`, rows and columns indexed by
`0, …, q - 1`. It maps the basis state `|a⟩` to `q ^ (-1/2) ∑_c exp (2 π i a c / q) |c⟩`
(P. W. Shor, SIAM J. Comput. 26 (1997), Section 4, equation (4.1)). -/
noncomputable def qftMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.of fun a c => ((Real.sqrt q : ℝ) : ℂ)⁻¹ * exp (2 * π * I * a * c / q)

theorem qftMatrix_apply (q : ℕ) (a c : Fin q) :
    qftMatrix q a c = ((Real.sqrt q : ℝ) : ℂ)⁻¹ * exp (2 * π * I * a * c / q) := rfl

/-- **The quantum Fourier transform matrix is symmetric.** `(A_q)ᵀ = A_q`, since its `(a, c)`
entry depends on `a * c` only (P. W. Shor, SIAM J. Comput. 26 (1997), equation (4.1)). -/
theorem qftMatrix_transpose (q : ℕ) : (qftMatrix q)ᵀ = qftMatrix q := by
  ext a c
  simp only [transpose_apply, qftMatrix_apply]
  ring_nf

/-- The geometric sum behind unitarity: for `a, b < q`,
`∑_{c < q} exp (2 π i (a - b) c / q)` is `q` when `a = b` and `0` otherwise. -/
private theorem sum_exp_eq (q : ℕ) (a b : Fin q) :
    ∑ c : Fin q, exp (2 * π * I * ((a : ℂ) - b) / q) ^ (c : ℕ) =
      if a = b then (q : ℂ) else 0 := by
  have hq : (q : ℂ) ≠ 0 := by
    have : 0 < q := Fin.pos a
    exact_mod_cast this.ne'
  set w := exp (2 * π * I * ((a : ℂ) - b) / q) with hw
  rw [Fin.sum_univ_eq_sum_range (fun c => w ^ c) q]
  split_ifs with hab
  · subst hab
    simp [hw]
  · have hwq : w ^ q = 1 := by
      rw [hw, ← exp_nat_mul]
      rw [exp_eq_one_iff]
      refine ⟨(a : ℤ) - b, ?_⟩
      field_simp
      push_cast
      ring
    have hw1 : w ≠ 1 := by
      intro h1
      rw [hw, exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have key : ((a : ℂ) - b) = n * q := by
        field_simp at hn
        linear_combination hn
      have keyZ : ((a : ℤ) - b) = n * q := by exact_mod_cast key
      have ha : (a : ℤ) < q := by exact_mod_cast a.isLt
      have hb : (b : ℤ) < q := by exact_mod_cast b.isLt
      have ha0 : (0 : ℤ) ≤ a := by positivity
      have hb0 : (0 : ℤ) ≤ b := by positivity
      have hn0 : n = 0 := by
        rcases lt_trichotomy n 0 with h | h | h
        · have : n * (q : ℤ) ≤ -q := by nlinarith
          omega
        · exact h
        · have : (q : ℤ) ≤ n * q := by nlinarith
          omega
      subst hn0
      apply hab
      apply Fin.ext
      omega
    rw [geom_sum_eq hw1, hwq, sub_self, zero_div]

/-- **The quantum Fourier transform is unitary.** For every natural number `q`, the matrix
`A_q` with `(a, c)` entry `q ^ (-1/2) * exp (2 π i a c / q)` is unitary: `A_q * A_qᴴ = 1`.
This is what makes the transformation (4.1) of P. W. Shor, SIAM J. Comput. 26 (1997),
Section 4 a quantum operation; the proof is the orthogonality of the characters
`c ↦ exp (2 π i a c / q)`. -/
theorem qftMatrix_mem_unitaryGroup (q : ℕ) : qftMatrix q ∈ Matrix.unitaryGroup (Fin q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  have hq0 : 0 < q := Fin.pos a
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hsq : ((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹ = (q : ℂ)⁻¹ := by
    rw [← mul_inv, ← ofReal_mul, Real.mul_self_sqrt hqR.le]
    simp
  have hterm : ∀ c : Fin q, qftMatrix q a c * star (qftMatrix q b c) =
      (q : ℂ)⁻¹ * exp (2 * π * I * ((a : ℂ) - b) / q) ^ (c : ℕ) := by
    intro c
    rw [qftMatrix_apply, qftMatrix_apply, star_mul', ← exp_nat_mul]
    have hs : star (((Real.sqrt q : ℝ) : ℂ)⁻¹) = ((Real.sqrt q : ℝ) : ℂ)⁻¹ := by
      rw [star_inv₀]; exact congrArg _ (conj_ofReal _)
    have he : star (exp (2 * π * I * b * c / q)) = exp (-(2 * π * I * b * c / q)) := by
      change (starRingEnd ℂ) _ = _
      rw [← exp_conj]
      congr 1
      simp only [map_div₀, map_mul, conj_ofReal, conj_I, conj_natCast, map_ofNat]
      ring
    rw [hs, he]
    calc ((Real.sqrt q : ℝ) : ℂ)⁻¹ * exp (2 * π * I * a * c / q) *
          (((Real.sqrt q : ℝ) : ℂ)⁻¹ * exp (-(2 * π * I * b * c / q)))
        = (((Real.sqrt q : ℝ) : ℂ)⁻¹ * ((Real.sqrt q : ℝ) : ℂ)⁻¹) *
            (exp (2 * π * I * a * c / q) * exp (-(2 * π * I * b * c / q))) := by ring
      _ = (q : ℂ)⁻¹ * exp ((c : ℕ) * (2 * π * I * ((a : ℂ) - b) / q)) := by
        rw [hsq, ← exp_add]
        congr 2
        ring
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), ← Finset.mul_sum, sum_exp_eq q a b,
    Matrix.one_apply]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  split_ifs <;> simp [hq]

end MathlibExt.QuantumInformation.Finite.QuantumFourierTransform
