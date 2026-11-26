/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Perturbation theory for linear systems: the condition number

For an invertible `A` with inverse `Z = A⁻¹` in a complete normed ring (for instance bounded
operators on a Banach space, or square matrices with an operator norm), the number
`κ(A) = ‖A‖ ‖A⁻¹‖` governs how much the inverse of `A` and the solution of `A x = b` move when
`A` and `b` are perturbed. These are the first results of the perturbation theory of linear
systems as taught in J. W. Demmel's graduate numerical linear algebra course (Math 221, UC
Berkeley, Lecture 3 notes of 10 September 2024,
https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_03.txt; the course text is
J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997):

* `isUnit_sub` and `norm_inverse_sub_le`: if `‖E‖ ‖Z‖ < 1`, then `A - E` is invertible and
  `‖(A - E)⁻¹‖ ≤ ‖Z‖ / (1 - ‖E‖ ‖Z‖)`;
* `norm_inverse_sub_sub_le`: `‖(A - E)⁻¹ - Z‖ ≤ ‖Z‖² ‖E‖ / (1 - ‖E‖ ‖Z‖)`, so the relative change
  of the inverse is at most `κ(A) / (1 - ‖E‖ ‖Z‖)` times the relative change `‖E‖ / ‖A‖`;
* `one_le_norm_mul_norm_inv`: `κ(A) ≥ 1`;
* `norm_sub_div_norm_le`: **the condition number bound for linear systems**: if `A x = b ≠ 0` and
  `(A - E)(x + δx) = b + f`, then
  `‖δx‖ / ‖x‖ ≤ κ(A) / (1 - ‖E‖ ‖Z‖) · (‖f‖ / ‖b‖ + ‖E‖ / ‖A‖)`;
* `norm_sub_div_norm_le_of_rhs`: the case `E = 0`, `‖δx‖ / ‖x‖ ≤ κ(A) ‖f‖ / ‖b‖`.

The proofs avoid the Neumann series: `(A - E)⁻¹ = Z + Z E (A - E)⁻¹` gives the norm bound
directly.
-/

@[expose] public section

namespace MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation

section Ring

variable {R : Type*} [NormedRing R] [CompleteSpace R]

/-- **Small perturbations of an invertible element stay invertible.** If `‖E‖ ‖A⁻¹‖ < 1`, then
`A - E` is invertible (Demmel, Math 221 Lecture 3 notes, 2024, the lemma "`A - E` invertible if
`norm(E) < 1/norm(inv(A))`"). It restates Mathlib's `Units.add` (built from the Neumann series)
in the form used in perturbation theory. -/
theorem isUnit_sub (A : Rˣ) (E : R) (h : ‖E‖ * ‖(↑A⁻¹ : R)‖ < 1) : IsUnit ((A : R) - E) := by
  nontriviality R
  have hpos : 0 < ‖(↑A⁻¹ : R)‖ := Units.norm_pos A⁻¹
  have h' : ‖-E‖ < ‖(↑A⁻¹ : R)‖⁻¹ := by
    calc ‖-E‖ = ‖E‖ * ‖(↑A⁻¹ : R)‖ / ‖(↑A⁻¹ : R)‖ := by
          rw [norm_neg, mul_div_assoc, div_self hpos.ne', mul_one]
      _ < 1 / ‖(↑A⁻¹ : R)‖ := by gcongr
      _ = ‖(↑A⁻¹ : R)‖⁻¹ := one_div _
  have := (A.add (-E) h').isUnit
  simpa [sub_eq_add_neg] using this

omit [CompleteSpace R] in
/-- The identity `(A - E)⁻¹ = Z + Z E (A - E)⁻¹` for `Z = A⁻¹`, when `A - E` is invertible. -/
private theorem inverse_sub_eq (A : Rˣ) (E : R) (hu : IsUnit ((A : R) - E)) :
    Ring.inverse ((A : R) - E) =
      (↑A⁻¹ : R) + (↑A⁻¹ : R) * E * Ring.inverse ((A : R) - E) := by
  obtain ⟨B, hB⟩ := hu
  rw [← hB, Ring.inverse_unit]
  have hBv : (A : R) - E = B := hB.symm
  have : (↑A⁻¹ : R) = (↑A⁻¹ : R) * ((A : R) - E) * (↑B⁻¹ : R) := by
    rw [hBv, mul_assoc, Units.mul_inv, mul_one]
  calc (↑B⁻¹ : R) = (↑A⁻¹ : R) * (A : R) * (↑B⁻¹ : R) := by rw [Units.inv_mul, one_mul]
    _ = (↑A⁻¹ : R) * ((A : R) - E) * (↑B⁻¹ : R) + (↑A⁻¹ : R) * E * (↑B⁻¹ : R) := by
        noncomm_ring
    _ = _ := by rw [← this]

/-- **Norm of the inverse under perturbation.** If `‖E‖ ‖Z‖ < 1` for `Z = A⁻¹`, then
`‖(A - E)⁻¹‖ ≤ ‖Z‖ / (1 - ‖E‖ ‖Z‖)` (Demmel, Math 221 Lecture 3 notes, 2024:
"`norm(inv(A-E)) <= norm(Z)/(1-norm(E)*norm(Z))`"). -/
theorem norm_inverse_sub_le (A : Rˣ) (E : R) (h : ‖E‖ * ‖(↑A⁻¹ : R)‖ < 1) :
    ‖Ring.inverse ((A : R) - E)‖ ≤ ‖(↑A⁻¹ : R)‖ / (1 - ‖E‖ * ‖(↑A⁻¹ : R)‖) := by
  set Z : R := ↑A⁻¹
  set B := Ring.inverse ((A : R) - E)
  have hid := inverse_sub_eq A E (isUnit_sub A E h)
  have hle : ‖B‖ ≤ ‖Z‖ + ‖Z‖ * ‖E‖ * ‖B‖ := by
    calc ‖B‖ = ‖Z + Z * E * B‖ := by rw [← hid]
      _ ≤ ‖Z‖ + ‖Z * E * B‖ := norm_add_le _ _
      _ ≤ ‖Z‖ + ‖Z‖ * ‖E‖ * ‖B‖ := by
          gcongr
          exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **Change of the inverse.** If `‖E‖ ‖Z‖ < 1` for `Z = A⁻¹`, then
`‖(A - E)⁻¹ - Z‖ ≤ ‖Z‖² ‖E‖ / (1 - ‖E‖ ‖Z‖)` (Demmel, Math 221 Lecture 3 notes, 2024:
"`norm(inv(A-E)-Z) <= norm(Z)^2*norm(E)/(1-norm(E)*norm(Z))`"). -/
theorem norm_inverse_sub_sub_le (A : Rˣ) (E : R) (h : ‖E‖ * ‖(↑A⁻¹ : R)‖ < 1) :
    ‖Ring.inverse ((A : R) - E) - ↑A⁻¹‖ ≤
      ‖(↑A⁻¹ : R)‖ ^ 2 * ‖E‖ / (1 - ‖E‖ * ‖(↑A⁻¹ : R)‖) := by
  set Z : R := ↑A⁻¹
  have hid := inverse_sub_eq A E (isUnit_sub A E h)
  have hB := norm_inverse_sub_le A E h
  set B := Ring.inverse ((A : R) - E)
  have hpos : 0 < 1 - ‖E‖ * ‖Z‖ := by linarith
  have hsub : B - Z = Z * E * B := sub_eq_iff_eq_add'.2 hid
  calc ‖B - Z‖ = ‖Z * E * B‖ := by rw [hsub]
    _ ≤ ‖Z‖ * ‖E‖ * ‖B‖ :=
        (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ ‖Z‖ * ‖E‖ * (‖Z‖ / (1 - ‖E‖ * ‖Z‖)) := by gcongr
    _ = ‖Z‖ ^ 2 * ‖E‖ / (1 - ‖E‖ * ‖Z‖) := by ring

omit [CompleteSpace R] in
/-- **The condition number is at least one.** In a normed ring with `‖1‖ = 1`,
`1 ≤ ‖A‖ ‖A⁻¹‖` (Demmel, Math 221 Lecture 3 notes, 2024: "`kappa(A) >= 1`", from
`1 = norm(I) = norm(A*Z) <= norm(A)*norm(Z)`). For continuous linear equivalences between
normed spaces, Mathlib's `ContinuousLinearEquiv.one_le_norm_mul_norm_symm` is the analogue. -/
theorem one_le_norm_mul_norm_inv [NormOneClass R] (A : Rˣ) :
    1 ≤ ‖(A : R)‖ * ‖(↑A⁻¹ : R)‖ := by
  calc (1 : ℝ) = ‖((A : R) * ↑A⁻¹)‖ := by rw [Units.mul_inv, norm_one]
    _ ≤ _ := norm_mul_le _ _

end Ring

section LinearSystem

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

/-- **Condition number bound for linear systems.** Let `A` be an invertible bounded operator on
a Banach space with `A x = b ≠ 0`, and let `(A - E)(x + δx) = b + f` with `‖E‖ ‖A⁻¹‖ < 1`. Then
`‖δx‖ / ‖x‖ ≤ ‖A‖ ‖A⁻¹‖ / (1 - ‖E‖ ‖A⁻¹‖) · (‖f‖ / ‖b‖ + ‖E‖ / ‖A‖)` (Demmel, Math 221
Lecture 3 notes, 2024: "`norm(dx)/norm(x) <= norm(Z)*norm(A) * 1/(1-norm(E)*norm(Z)) *(
norm(f)/norm(b) + norm(E)/norm(A) )`"). -/
theorem norm_sub_div_norm_le (A : (F →L[𝕜] F)ˣ) (E : F →L[𝕜] F) {x δx b f : F}
    (hAx : (A : F →L[𝕜] F) x = b) (hb : b ≠ 0)
    (hpert : ((A : F →L[𝕜] F) - E) (x + δx) = b + f)
    (h : ‖E‖ * ‖(↑A⁻¹ : F →L[𝕜] F)‖ < 1) :
    ‖δx‖ / ‖x‖ ≤ ‖(A : F →L[𝕜] F)‖ * ‖(↑A⁻¹ : F →L[𝕜] F)‖ / (1 - ‖E‖ * ‖(↑A⁻¹ : F →L[𝕜] F)‖) *
      (‖f‖ / ‖b‖ + ‖E‖ / ‖(A : F →L[𝕜] F)‖) := by
  set A' : F →L[𝕜] F := (↑A : F →L[𝕜] F)
  set Z : F →L[𝕜] F := ↑A⁻¹
  obtain ⟨B, hB⟩ := isUnit_sub A E h
  have hBnorm : ‖(↑B⁻¹ : F →L[𝕜] F)‖ ≤ ‖Z‖ / (1 - ‖E‖ * ‖Z‖) := by
    have := norm_inverse_sub_le A E h
    rwa [← hB, Ring.inverse_unit] at this
  have hpos : 0 < 1 - ‖E‖ * ‖Z‖ := by linarith
  -- `(A - E) δx = f + E x`
  have hdx_eq : (B : F →L[𝕜] F) δx = f + E x := by
    rw [hB]
    have := hpert
    rw [map_add, sub_apply, sub_apply, hAx] at this
    rw [sub_apply]
    calc A' δx - E δx = (b - E x + (A' δx - E δx)) - b + E x := by abel
      _ = (b + f) - b + E x := by rw [this]
      _ = f + E x := by abel
  have hdx : δx = (↑B⁻¹ : F →L[𝕜] F) (f + E x) := by
    rw [← hdx_eq]
    change δx = ((↑B⁻¹ : F →L[𝕜] F) * ↑B) δx
    rw [Units.inv_mul]
    rfl
  have hx : x ≠ 0 := by rintro rfl; exact hb (by rw [← hAx, map_zero])
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hApos : 0 < ‖A'‖ := by
    refine norm_pos_iff.2 fun h0 => hb ?_
    rw [← hAx, h0, zero_apply]
  have hbA : ‖b‖ ≤ ‖A'‖ * ‖x‖ := by rw [← hAx]; exact A'.le_opNorm x
  have hnormdx : ‖δx‖ ≤ ‖Z‖ / (1 - ‖E‖ * ‖Z‖) * (‖f‖ + ‖E‖ * ‖x‖) := by
    rw [hdx]
    calc ‖(↑B⁻¹ : F →L[𝕜] F) (f + E x)‖ ≤ ‖(↑B⁻¹ : F →L[𝕜] F)‖ * ‖f + E x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Z‖ / (1 - ‖E‖ * ‖Z‖) * (‖f‖ + ‖E‖ * ‖x‖) := by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact E.le_opNorm x)
  have hf : ‖f‖ / ‖x‖ ≤ ‖A'‖ * (‖f‖ / ‖b‖) := by
    rw [div_le_iff₀ hxpos, mul_comm ‖A'‖, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hbpos]
    calc ‖f‖ * ‖b‖ ≤ ‖f‖ * (‖A'‖ * ‖x‖) := by gcongr
      _ = _ := by ring
  rw [div_le_iff₀ hxpos]
  calc ‖δx‖ ≤ ‖Z‖ / (1 - ‖E‖ * ‖Z‖) * (‖f‖ + ‖E‖ * ‖x‖) := hnormdx
    _ = ‖Z‖ / (1 - ‖E‖ * ‖Z‖) * (‖f‖ / ‖x‖ + ‖E‖) * ‖x‖ := by field_simp
    _ ≤ ‖Z‖ / (1 - ‖E‖ * ‖Z‖) * (‖A'‖ * (‖f‖ / ‖b‖) + ‖E‖) * ‖x‖ := by gcongr
    _ = _ := by field_simp

/-- **Condition number bound, right-hand side perturbed only.** If `A x = b ≠ 0` and
`A (x + δx) = b + f`, then `‖δx‖ / ‖x‖ ≤ ‖A‖ ‖A⁻¹‖ ‖f‖ / ‖b‖` (Demmel, Math 221 Lecture 3 notes,
2024, the case `E = 0` of the bound for `A x = b`). -/
theorem norm_sub_div_norm_le_of_rhs (A : (F →L[𝕜] F)ˣ) {x δx b f : F}
    (hAx : (A : F →L[𝕜] F) x = b) (hb : b ≠ 0)
    (hpert : (A : F →L[𝕜] F) (x + δx) = b + f) :
    ‖δx‖ / ‖x‖ ≤ ‖(A : F →L[𝕜] F)‖ * ‖(↑A⁻¹ : F →L[𝕜] F)‖ * (‖f‖ / ‖b‖) := by
  have := norm_sub_div_norm_le A 0 hAx hb (by simpa using hpert) (by simp)
  simpa using this

end LinearSystem

end MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation
