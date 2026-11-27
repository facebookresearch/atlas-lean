/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import MathlibExt.NumberTheory.GeneralizedMarkovCharacteristic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# A product identity for generalized Cohn matrices

Generalized Markov numbers (`IsGenMarkovNumber`), generalized Cohn matrices
(`IsGenCohnMatrix`), and the product identity `IsGenCohnMatrix.mul_E_mul` relating `M * E * M`
and `M⁻¹ * E * M⁻¹` to `(tr M + k) • M + E` and `-(tr M⁻¹ + k) • M⁻¹ + E`.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.7.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Markov number.** Let $k$ be a natural number. A natural number $b$ is a
$k$-generalized Markov number when there are natural numbers $a$ and $c$ such that
$(a, b, c)$ is a $k$-generalized Markov triple.

Since the $k$-generalized Markov equation is symmetric in its three variables, this is the same
as $b$ being an entry, in any position, of some $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public def IsGenMarkovNumber (k b : ℕ) : Prop :=
  ∃ a c, IsGenMarkovTriple k a b c

/-- **Generalized Cohn matrices.** Let $k$ be a natural number. An integer $2 \times 2$ matrix
$P = (p_{ij})$ is a $k$-generalized Cohn matrix if $\det P = 1$, its entry $p_{12}$ is a
$k$-generalized Markov number, and its trace equals $(3 + 3k) p_{12} - k$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.1. -/
public def IsGenCohnMatrix (k : ℕ) (P : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  P.det = 1 ∧ ∃ n : ℕ, P 0 1 = n ∧ IsGenMarkovNumber k n ∧ P.trace = (3 + 3 * k) * n - k

/-- **A product identity for generalized Cohn matrices.** Let $k$ be a natural number, let $M$
be a $k$-generalized Cohn matrix, and let $E$ be the $2 \times 2$ integer matrix whose only
nonzero entry is $3 + 3k$, in row $2$ and column $1$. Then $MEM = (\operatorname{tr} M + k)M + E$
and $M^{-1} E M^{-1} = -(\operatorname{tr} M^{-1} + k)M^{-1} + E$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.7. -/
public theorem IsGenCohnMatrix.mul_E_mul {k : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : IsGenCohnMatrix k M) :
    M * !![0, 0; 3 + 3 * (k : ℤ), 0] * M =
        (M.trace + (k : ℤ)) • M + !![0, 0; 3 + 3 * (k : ℤ), 0] ∧
      M⁻¹ * !![0, 0; 3 + 3 * (k : ℤ), 0] * M⁻¹ =
        (-(M⁻¹.trace + (k : ℤ))) • M⁻¹ + !![0, 0; 3 + 3 * (k : ℤ), 0] := by
  obtain ⟨hdet, n, hb, -, htr⟩ := hM
  have hkey : (3 + 3 * (k : ℤ)) * M 0 1 - M.trace - (k : ℤ) = 0 := by
    rw [hb]
    linear_combination -htr
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hdet
  have hE00 : (!![0, 0; 3 + 3 * (k : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := rfl
  have hE01 : (!![0, 0; 3 + 3 * (k : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := rfl
  have hE10 : (!![0, 0; 3 + 3 * (k : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = 3 + 3 * (k : ℤ) := rfl
  have hE11 : (!![0, 0; 3 + 3 * (k : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := rfl
  have hMinv : M⁻¹ = !![M 1 1, -M 0 1; -M 1 0, M 0 0] := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  have htrInv : M⁻¹.trace = M.trace := by
    rw [hMinv, Matrix.trace_fin_two_of, Matrix.trace_fin_two, add_comm]
  have i00 : M⁻¹ 0 0 = M 1 1 := by simp [hMinv]
  have i01 : M⁻¹ 0 1 = -M 0 1 := by simp [hMinv]
  have i10 : M⁻¹ 1 0 = -M 1 0 := by simp [hMinv]
  have i11 : M⁻¹ 1 1 = M 0 0 := by simp [hMinv]
  constructor
  · rw [← Matrix.ext_iff]
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, hE00, hE01, hE10, hE11]
      linear_combination (M 0 0) * hkey
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, hE00, hE01, hE10, hE11]
      linear_combination (M 0 1) * hkey
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, hE00, hE01, hE10, hE11]
      linear_combination (3 + 3 * (k : ℤ)) * hdet' + (M 1 0) * hkey
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, hE00, hE01, hE10, hE11]
      linear_combination (M 1 1) * hkey
  · rw [← Matrix.ext_iff]
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, htrInv, hE00, hE01, hE10, hE11, i00, i01,
        i10]
      linear_combination (-(M 1 1)) * hkey
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, htrInv, hE00, hE01, hE10, hE11, i00, i01,
        i11]
      linear_combination (M 0 1) * hkey
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, htrInv, hE00, hE01, hE10, hE11, i00, i10,
        i11]
      linear_combination (3 + 3 * (k : ℤ)) * hdet' + (M 1 0) * hkey
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, htrInv, hE00, hE01, hE10, hE11, i01, i10,
        i11]
      linear_combination (-(M 0 0)) * hkey

end

end MetaMathlibExt
