/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularForm_AtkinLehnerDatum.lean` and
`Theorems/Thm_ModularForm_alSlash_mul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

open UpperHalfPlane
open scoped ModularForm

namespace ModularForm

/-- Datum for an Atkin-Lehner involution at an exact divisor `q` of `M`.

The fields record a factorisation `M = q * R` and integers `a, b` with
`q * a - R * b = 1`, so the matrix `!![q * a, b; q * R, q]` has
determinant `q`. -/
structure AtkinLehnerDatum (M q : ℕ) : Type where
  /-- The complementary factor of `M`. -/
  R : ℕ
  /-- The factorisation `M = q * R`. -/
  hM : M = q * R
  /-- First Bezout coefficient. -/
  a : ℤ
  /-- Second Bezout coefficient. -/
  b : ℤ
  /-- The Bezout identity `q * a - R * b = 1`. -/
  bezout : (q : ℤ) * a - (R : ℤ) * b = 1

namespace AtkinLehnerDatum

variable {M q : ℕ}

/-- The factorisation `M = q * R` over the integers. -/
lemma hM_int (W : AtkinLehnerDatum M q) : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := by exact_mod_cast W.hM

/-- If `M` is nonzero then `q` is positive. -/
lemma q_pos (W : AtkinLehnerDatum M q) [NeZero M] : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inl h))) (NeZero.ne M)
  · exact h

/-- The Atkin-Lehner matrix `!![q * a, b; q * R, q]`. -/
def mat (W : AtkinLehnerDatum M q) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a, W.b; (q : ℤ) * (W.R : ℤ), (q : ℤ)]

/-- The Atkin-Lehner matrix has determinant `q`. -/
@[simp] lemma det_mat (W : AtkinLehnerDatum M q) : W.mat.det = (q : ℤ) := by
  rw [mat, Matrix.det_fin_two_of]
  linear_combination (q : ℤ) * W.bezout

/-- The Atkin-Lehner matrix viewed in `GL (Fin 2) ℝ`. -/
noncomputable def alGL (W : AtkinLehnerDatum M q) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℝ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using (W.q_pos).ne')

@[simp] lemma alGL_coe (W : AtkinLehnerDatum M q) [NeZero M] :
    (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) = (W.mat).map (algebraMap ℤ ℝ) := rfl

/-- The determinant of the Atkin-Lehner matrix in `GL (Fin 2) ℝ` is `q`. -/
lemma val_det_alGL (W : AtkinLehnerDatum M q) [NeZero M] : ((W.alGL).det : ℝ) = (q : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, alGL_coe]
  have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, W.det_mat]
  simp

end AtkinLehnerDatum

/-- The Atkin-Lehner slash action of weight `k`: slash by the
Atkin-Lehner matrix of `W`. -/
noncomputable def alSlash {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M]
    (f : ℍ → ℂ) : ℍ → ℂ :=
  f ∣[k] W.alGL

/-- The Atkin-Lehner slash action is the slash action by `W.alGL`. -/
lemma alSlash_def {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M]
    (f : ℍ → ℂ) : alSlash W k f = f ∣[k] W.alGL := rfl

/-- Product rule for the Atkin-Lehner slash operator: slashing a product
in weight `k₁ + k₂` is `q` times the product of the slashes, the factor
`q` being the determinant of the Atkin-Lehner matrix. -/
public theorem alSlash_mul {M q : ℕ} [NeZero M] (W : AtkinLehnerDatum M q)
    (k₁ k₂ : ℤ) (F G : ℍ → ℂ) :
    alSlash W (k₁ + k₂) (F * G) =
      (q : ℂ) • (alSlash W k₁ F * alSlash W k₂ G) := by
  simp only [alSlash_def, ModularForm.mul_slash, W.val_det_alGL, Nat.abs_cast]
  ext τ
  simp [Complex.real_smul]

end ModularForm
