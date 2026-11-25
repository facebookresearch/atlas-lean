/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_ComplexIwasawa.lean`,
`Theorems/Thm_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean`
and
`P2M/Sol/S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup.lean`
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

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.UnitaryGroup
public import MathlibExt.LinearAlgebra.Matrix.SpecialUnitaryFinTwo

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

@[expose] public section

open ComplexConjugate

namespace AutomorphicForm
namespace ComplexIwasawa

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

/-- The lower-left entry of `g` after the unipotent coordinate `z` is applied. -/
noncomputable def botP (z : ℂ) : ℂ := g 0 0 + z * g 1 0

/-- The lower-right entry of `g` after the unipotent coordinate `z` is applied. -/
noncomputable def botQ (z : ℂ) : ℂ := g 0 1 + z * g 1 1

/-- The normalizing radius of the bottom row in complex Iwasawa coordinates. -/
noncomputable def radC (z : ℂ) : ℝ :=
  Real.sqrt (Complex.normSq (botP g z) + Complex.normSq (botQ g z))

/-- The compact `SU(2)` factor in complex Iwasawa coordinates. -/
noncomputable def kC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![conj (botQ g z) / (radC g z : ℂ), -conj (botP g z) / (radC g z : ℂ);
     botP g z / (radC g z : ℂ), botQ g z / (radC g z : ℂ)]

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

/-- The squared radius is the sum of the squared norms of the bottom entries. -/
theorem radC_sq (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

/-- The radius is positive when `g` has nonzero determinant: vanishing of both
bottom entries would make the two rows of `g` proportional. -/
theorem radC_pos (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := by
  rw [radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (botP g z))
    (Complex.normSq_nonneg (botQ g z))).lt_or_eq with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hQ : Complex.normSq (botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [botP] at hP0
    rw [botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

/-- The compact factor in complex `GL(2)` Iwasawa coordinates belongs to
`SU(2)`, provided `g` has nonzero determinant. -/
public theorem kC_mem_specialUnitaryGroup (hg : g.det ≠ 0) (z : ℂ) :
    kC g z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hr : 0 < radC g z := radC_pos hg z
  rw [Matrix.mem_specialUnitaryGroup_fin_two_iff]
  refine ⟨conj (botQ g z) / (radC g z : ℂ), -conj (botP g z) / (radC g z : ℂ), ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kC, map_div₀, map_neg, Complex.conj_ofReal] <;> ring
  · have hsum : Complex.normSq (botQ g z) + Complex.normSq (botP g z) = radC g z ^ 2 := by
      rw [add_comm]
      exact (radC_sq (g := g) z).symm
    simp only [Complex.normSq_div, Complex.normSq_conj, Complex.normSq_neg,
      Complex.normSq_ofReal]
    rw [← add_div, hsum, pow_two, div_self (mul_ne_zero hr.ne' hr.ne')]

/-- The conjugate transpose of the compact factor is its inverse on the left. -/
theorem conjTranspose_mul_kC (hg : g.det ≠ 0) (z : ℂ) :
    (kC g z).conjTranspose * kC g z = 1 := by
  have h := (Matrix.mem_specialUnitaryGroup_iff.1 (kC_mem_specialUnitaryGroup hg z)).1
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  exact h

/-- The compact factor has determinant `1`. -/
theorem det_kC (hg : g.det ≠ 0) (z : ℂ) : (kC g z).det = 1 :=
  (Matrix.mem_specialUnitaryGroup_iff.1 (kC_mem_specialUnitaryGroup hg z)).2

end ComplexIwasawa
end AutomorphicForm
