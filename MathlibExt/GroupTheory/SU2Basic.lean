/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.SpecialUnitaryFinTwo
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Basic structure of `SU₂`

An element of `SU₂`, the special unitary group of `2 × 2` complex matrices,
has the form `!![α, β; -conj β, conj α]` with `‖α‖² + ‖β‖² = 1`. Its center
is `{1, -1}`, its trace is real, and its trace has norm at most `2`.

The membership witnesses and proper-center result support the conjugacy development.

Source: `v1/Atlas/AlgebraNotes/code/SimpleGroups.lean` (theorems
`su2_matrix_form`, `su2_center_mem_iff`, `su2_trace_real`, and
`su2_trace_bound`, with the auxiliary membership lemmas `D_mem_SU2` and
`W_mem_SU2`). The `SU₂` simplicity material in that file, which depends on
the unproved `su2_normal_contains_all_traces` and `longitude_iso`, is not
ported here; see `MathlibExt/GroupTheory/SU2Conjugacy.lean` for the
fully proved conjugacy-by-trace results from the same file.
-/

@[expose] public section

namespace SU2

open Matrix

/-- **The matrix $\operatorname{diag}(i, -i)$ is special unitary.** The complex diagonal matrix
$\operatorname{diag}(i, -i)$, where $i$ is the imaginary unit, lies in the special unitary group
$\mathrm{SU}(2)$ of complex $2 \times 2$ matrices. -/
theorem diag_I_mem :
    !![Complex.I, (0 : ℂ); 0, -Complex.I] ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
          Matrix.map, Complex.I] <;>
    first | (apply Complex.ext <;> simp) | left; (apply Complex.ext <;> simp)
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two,
          Matrix.map, Complex.I] <;>
    first | (apply Complex.ext <;> simp) | right; (apply Complex.ext <;> simp)
  · simp [Matrix.detMonoidHom, Matrix.det_fin_two, Complex.I]
    apply Complex.ext <;> simp

/-- **The matrix with rows $(0, 1)$ and $(-1, 0)$ is special unitary.** The complex $2 \times 2$
matrix with rows $(0, 1)$ and $(-1, 0)$ lies in the special unitary group $\mathrm{SU}(2)$ of
complex $2 \times 2$ matrices. -/
theorem antidiag_mem :
    !![(0 : ℂ), 1; -1, 0] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  simp only [Matrix.specialUnitaryGroup, Submonoid.mem_inf, MonoidHom.mem_mker]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
    (apply Complex.ext <;> simp)
  · ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, star, Matrix.conjTranspose, Fin.sum_univ_two, Matrix.map] <;>
    (apply Complex.ext <;> simp)
  · simp [Matrix.detMonoidHom, Matrix.det_fin_two]

/-- **The center of $\mathrm{SU}(2)$ is proper.** The center of the special unitary group
$\mathrm{SU}(2)$ of complex $2 \times 2$ matrices is not all of $\mathrm{SU}(2)$.

The matrix $\operatorname{diag}(i, -i)$, where $i$ is the imaginary unit, lies in
$\mathrm{SU}(2)$ but is not central. -/
theorem su2_center_ne_top :
    Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) ≠ ⊤ := by
  intro heq
  have hmem : (⟨!![Complex.I, (0 : ℂ); 0, -Complex.I], diag_I_mem⟩ :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
      Subgroup.center ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    heq ▸ Subgroup.mem_top _
  rw [Matrix.mem_center_specialUnitaryGroup_fin_two_iff] at hmem
  rcases hmem with h | h
  · have h00 := congr_fun (congr_fun h 0) 0
    simp at h00
    have him := congr_arg Complex.im h00
    simp at him
  · have h00 := congr_fun (congr_fun h 0) 0
    simp at h00
    have him := congr_arg Complex.im h00
    simp at him

end SU2
