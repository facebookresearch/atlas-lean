/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Contrapose

/-! Rank-one sums of real vector squares have support on a single line.

The statements are generic real linear algebra and do not assume any
centralizer recognition or properties of the Griess construction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

variable {ι n : Type*} [Fintype ι]

/-- A rank-one sum of outer squares forces each active vector to satisfy
every collinearity equation with the vector on the right. -/
theorem rankOneSquareSupport_coordinate
    (u : ι → n → ℝ) (c : ι → ℝ) (v : n → ℝ)
    (h : (∑ r, c r ^ 2 • Matrix.vecMulVec (u r) (u r)) = Matrix.vecMulVec v v)
    (r : ι) (hr : c r ≠ 0) (i j : n) :
    v i * u r j = v j * u r i := by
  have hentry (i j : n) : (∑ r, c r ^ 2 * (u r i * u r j)) = v i * v j := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
      using congrFun (congrFun h i) j
  have hsum : (∑ r, (c r * (v i * u r j - v j * u r i)) ^ 2) = 0 := by
    calc
      _ = v i ^ 2 * (∑ r, c r ^ 2 * (u r j * u r j)) -
          (2 * v i * v j) * (∑ r, c r ^ 2 * (u r i * u r j)) +
          v j ^ 2 * (∑ r, c r ^ 2 * (u r i * u r i)) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = 0 := by rw [hentry j j, hentry i j, hentry i i]; ring
  have hzero : c r * (v i * u r j - v j * u r i) = 0 :=
    ((Finset.sum_sq_eq_zero_iff Finset.univ
      (fun s => c s * (v i * u s j - v j * u s i))).mp hsum) r (Finset.mem_univ r)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hr)

/-- Every active vector in a rank-one sum is a scalar multiple of the
nonzero vector on the right. -/
theorem rankOneSquareSupport_scalar
    (u : ι → n → ℝ) (c : ι → ℝ) (v : n → ℝ)
    (hv : v ≠ 0)
    (h : (∑ r, c r ^ 2 • Matrix.vecMulVec (u r) (u r)) = Matrix.vecMulVec v v)
    (r : ι) (hr : c r ≠ 0) : ∃ a : ℝ, u r = a • v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  refine ⟨u r i / v i, ?_⟩
  funext j
  change u r j = (u r i / v i) * v j
  calc
    u r j = (v i * u r j) / v i := by field_simp [hi]
    _ = (v j * u r i) / v i := by rw [rankOneSquareSupport_coordinate u c v h r hr i j]
    _ = (u r i / v i) * v j := by ring

/-- The requested span formulation of rank-one support. -/
theorem rankOneSquareSupport_mem_span
    (u : ι → n → ℝ) (c : ι → ℝ) (v : n → ℝ)
    (hv : v ≠ 0)
    (h : (∑ r, c r ^ 2 • Matrix.vecMulVec (u r) (u r)) = Matrix.vecMulVec v v)
    (r : ι) (hr : c r ≠ 0) : u r ∈ Submodule.span ℝ {v} := by
  obtain ⟨a, ha⟩ := rankOneSquareSupport_scalar u c v hv h r hr
  exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩

/-- Nonzero vectors on distinct lines admit at most one active coefficient
in a rank-one sum of squares. Equal nonzero norms are sufficient for the
nonzero-vector hypothesis in applications, but are not required here. -/
theorem rankOneSquareSupport_at_most_one
    (u : ι → n → ℝ) (c : ι → ℝ) (v : n → ℝ)
    (hv : v ≠ 0) (hu : ∀ r, u r ≠ 0)
    (hlines : ∀ r s (a : ℝ), a ≠ 0 → u r = a • u s → r = s)
    (h : (∑ r, c r ^ 2 • Matrix.vecMulVec (u r) (u r)) = Matrix.vecMulVec v v)
    (r s : ι) (hr : c r ≠ 0) (hs : c s ≠ 0) : r = s := by
  obtain ⟨a, ha⟩ := rankOneSquareSupport_scalar u c v hv h r hr
  obtain ⟨b, hb⟩ := rankOneSquareSupport_scalar u c v hv h s hs
  have ha0 : a ≠ 0 := by intro hzero; apply hu r; rw [ha, hzero, zero_smul]
  have hb0 : b ≠ 0 := by intro hzero; apply hu s; rw [hb, hzero, zero_smul]
  apply hlines r s (a / b) (div_ne_zero ha0 hb0)
  rw [ha, hb, smul_smul, div_mul_cancel₀ _ hb0]

/-- Normalized square coefficients on distinct nonzero lines have exactly
one nonzero coefficient, and it is either one or minus one. -/
theorem rankOneSquareSupport_normalized_singleton
    (u : ι → n → ℝ) (c : ι → ℝ) (v : n → ℝ)
    (hv : v ≠ 0) (hu : ∀ r, u r ≠ 0)
    (hlines : ∀ r s (a : ℝ), a ≠ 0 → u r = a • u s → r = s)
    (h : (∑ r, c r ^ 2 • Matrix.vecMulVec (u r) (u r)) = Matrix.vecMulVec v v)
    (hnorm : (∑ r, c r ^ 2) = 1) :
    ∃ r : ι, (c r = 1 ∨ c r = -1) ∧ ∀ s, s ≠ r → c s = 0 := by
  classical
  have hex : ∃ r : ι, c r ≠ 0 := by
    by_contra! hzero
    simp only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨r, hr⟩ := hex
  have hs : ∀ s, s ≠ r → c s = 0 := by
    intro s hsr
    by_contra hcs
    exact hsr (rankOneSquareSupport_at_most_one u c v hv hu hlines h s r hcs hr)
  have hsum : (∑ s, c s ^ 2) = c r ^ 2 := by
    apply Finset.sum_eq_single r
    · intro s hmem hsr
      rw [hs s hsr, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    · intro hmem
      exact (hmem (Finset.mem_univ r)).elim
  rw [hsum] at hnorm
  exact ⟨r, sq_eq_one_iff.mp hnorm, hs⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
