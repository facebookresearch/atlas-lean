/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.ProperIdealConj

/-!
# Tests for a proper ideal times its conjugate

The form $x^2 + y^2$, with root $i$ and order $\mathbb{Z}[i]$: the lattice $(1 + i)\mathbb{Z}[i]$
times its conjugate is $2\mathbb{Z}[i]$, it has index $2$ in $\mathbb{Z}[i]$, and
$\mathbb{Z}[i]$ times its conjugate is $\mathbb{Z}[i]$.
-/

namespace BinaryQuadraticForm.ProperIdealConjTest

open Complex

open scoped Pointwise

theorem root_I : ((1 : ℤ) : ℂ) * I ^ 2 + ((0 : ℤ) : ℂ) * I + ((1 : ℤ) : ℂ) = 0 := by
  simp

theorem gcd_one_zero_one : Int.gcd (Int.gcd 1 0 : ℤ) 1 = 1 := by decide

theorem discrim_neg : discrim (1 : ℤ) 0 1 < 0 := by decide

theorem span_le : Submodule.span ℤ {1 + I, (1 + I) * I} ≤
    Submodule.span ℤ {(1 : ℂ), ((1 : ℤ) : ℂ) * I} := by
  rw [Submodule.span_le]
  rintro _ (rfl | rfl)
  · exact Submodule.mem_span_pair.mpr ⟨1, 1, by simp⟩
  · exact Submodule.mem_span_pair.mpr ⟨-1, 1, by simp; ring_nf; simp; ring⟩

/-- $(1 + i)\mathbb{Z}[i] \cdot \overline{(1 + i)\mathbb{Z}[i]} = 2\,\mathbb{Z}[i]$. -/
example : Submodule.span ℤ {1 + I, (1 + I) * I} *
      (Submodule.span ℤ {1 + I, (1 + I) * I}).map (starRingEnd ℂ).toIntAlgHom.toLinearMap =
    ((2 : ℝ) : ℂ) • Submodule.span ℤ {(1 : ℂ), ((1 : ℤ) : ℂ) * I} := by
  have h := span_mul_map_conj_span (α := 1 + I) gcd_one_zero_one one_pos discrim_neg root_I
  have h2 : normSq (1 + I) / ((1 : ℤ) : ℝ) = 2 := by simp [normSq_apply]; norm_num
  rwa [h2] at h

/-- The index of $(1 + i)\mathbb{Z}[i]$ in $\mathbb{Z}[i]$ is $2$. -/
example : ((Submodule.span ℤ {1 + I, (1 + I) * I}).toAddSubgroup.relIndex
    (Submodule.span ℤ {(1 : ℂ), ((1 : ℤ) : ℂ) * I}).toAddSubgroup : ℝ) = 2 := by
  rw [(relIndex_span_pair_eq one_pos discrim_neg root_I (by simp [Complex.ext_iff]) span_le).1]
  simp [normSq_apply]
  norm_num

/-- $\mathbb{Z}[i]$, as the lattice of the period pair $(1, i)$, is invertible with inverse its
conjugate. -/
example : (PeriodPair.ofTau I (by simp)).lattice *
    (((PeriodPair.ofTau I (by simp)).lattice.toAddSubgroup.relIndex
      (Submodule.span ℤ {(1 : ℂ), ((1 : ℤ) : ℂ) * I}).toAddSubgroup : ℕ) : ℂ)⁻¹ •
      (PeriodPair.ofTau I (by simp)).lattice.map (starRingEnd ℂ).toIntAlgHom.toLinearMap =
    Submodule.span ℤ {(1 : ℂ), ((1 : ℤ) : ℂ) * I} :=
  (PeriodPair.lattice_mul_map_conj_eq_relIndex_smul gcd_one_zero_one one_pos discrim_neg root_I
    one_ne_zero _ (by rw [one_mul]; rfl) (by rw [Int.cast_one, one_mul]; exact le_rfl)).2.2

end BinaryQuadraticForm.ProperIdealConjTest
