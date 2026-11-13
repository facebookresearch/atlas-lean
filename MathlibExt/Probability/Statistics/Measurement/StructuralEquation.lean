/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import MathlibExt.LinearAlgebra.Matrix.LogDetTrace

/-!
# Structural equations for DAG models and Gaussian covariance-fit discrepancy

Nilpotency of DAG-supported coefficient matrices with the finite geometric
series inverse of `1 - B` (D07.2), and nonnegativity with the equality case
of the Gaussian covariance-fit discrepancy (D07.3). The discrepancy results are
corollaries of the log-determinant/trace inequality
`Matrix.PosDef.log_det_mul_le_trace` and its equality case
`Matrix.PosDef.mul_eq_one_of_log_det_eq_trace`, applied to `S` and `C⁻¹`.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

/-- Path-counting estimate: a nonzero entry of `B ^ k` spans at least `k`
topological levels (Drton, arXiv:1612.05994). -/
private theorem pow_entry_ne_zero_le_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) (k : ℕ) (i j : V) :
    (B ^ k) i j ≠ 0 → ord j + k ≤ ord i := by
  induction k generalizing i j with
  | zero =>
    intro h
    rw [pow_zero, Matrix.one_apply] at h
    have hij : i = j := by
      by_contra hne
      simp [hne] at h
    subst hij
    omega
  | succ k ih =>
    intro h
    rw [pow_succ, Matrix.mul_apply] at h
    have hex : ∃ l ∈ (Finset.univ : Finset V), (B ^ k) i l * B l j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (Finset.sum_eq_zero hc)
    obtain ⟨l, _, hl⟩ := hex
    have h1 : (B ^ k) i l ≠ 0 := fun hz => hl (by rw [hz, zero_mul])
    have h2 : B l j ≠ 0 := fun hz => hl (by rw [hz, mul_zero])
    have g1 := hB l j h2
    have g2 := ih i l h1
    omega

/-- Nilpotency of DAG-supported coefficient matrices: `B ^ Fintype.card V = 0`
when parents precede children in `ord` (Drton, arXiv:1612.05994). -/
theorem pow_card_eq_zero_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    B ^ Fintype.card V = 0 := by
  ext i j
  simp only [Matrix.zero_apply]
  by_contra h
  have hle := pow_entry_ne_zero_le_of_topologicalOrder B ord hB _ i j h
  have hi := hord i
  omega

/-- Higher powers vanish too: `B ^ m = 0` for `Fintype.card V ≤ m`
(Drton, arXiv:1612.05994). -/
theorem pow_eq_zero_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) (m : ℕ)
    (hm : Fintype.card V ≤ m) :
    B ^ m = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, pow_card_eq_zero_of_topologicalOrder B ord hord hB, zero_mul]

/-- The finite geometric series `∑ k ∈ Finset.range (Fintype.card V), B ^ k` is a
two-sided inverse of `1 - B` (Drton, arXiv:1612.05994). -/
theorem one_sub_mul_sum_pow_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    (1 - B) * ∑ k ∈ Finset.range (Fintype.card V), B ^ k = 1 ∧
      (∑ k ∈ Finset.range (Fintype.card V), B ^ k) * (1 - B) = 1 := by
  have hcard : B ^ Fintype.card V = 0 :=
    pow_card_eq_zero_of_topologicalOrder B ord hord hB
  have hsum : (∑ k ∈ Finset.range (Fintype.card V), B ^ k) =
      ∑ i ∈ Finset.range (Fintype.card V),
        (1 : Matrix V V R) ^ i * B ^ (Fintype.card V - 1 - i) := by
    rw [← Finset.sum_range_reflect (fun k => B ^ k) (Fintype.card V)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  have hcomm : Commute (1 : Matrix V V R) B := Commute.one_left B
  have hmul := Commute.mul_geom_sum₂ hcomm (Fintype.card V)
  have hgeom := Commute.geom_sum₂_mul hcomm (Fintype.card V)
  rw [hsum]
  rw [hcard, one_pow, sub_zero] at hmul hgeom
  exact ⟨hmul, hgeom⟩

/-- `(1 - B).det` is a unit when `B` is DAG-supported
(Drton, arXiv:1612.05994). -/
theorem isUnit_det_one_sub_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    IsUnit (1 - B).det :=
  Matrix.isUnit_det_of_right_inverse
    (one_sub_mul_sum_pow_of_topologicalOrder B ord hord hB).1

/-- `(1 - B)⁻¹` is the finite geometric series for DAG-supported `B`
(Drton, arXiv:1612.05994). -/
theorem inv_one_sub_eq_sum_pow_of_topologicalOrder
    {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]
    (B : Matrix V V R) (ord : V → ℕ)
    (hord : ∀ v, ord v < Fintype.card V)
    (hB : ∀ i j, B i j ≠ 0 → ord j < ord i) :
    (1 - B)⁻¹ = ∑ k ∈ Finset.range (Fintype.card V), B ^ k :=
  Matrix.inv_eq_right_inv
    (one_sub_mul_sum_pow_of_topologicalOrder B ord hord hB).1

/-- Gaussian covariance-fit discrepancy for sample `S` and model `C`
(Bartlett, STAT 241A (2007), Lemma 2). Values outside `Matrix.PosDef` are
meaningless: the definition is total via `Real.log` of a nonpositive determinant
and `C⁻¹` of a singular matrix. -/
noncomputable def gaussianDiscrepancy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S C : Matrix ι ι ℝ) : ℝ :=
  Real.log C.det + (S * C⁻¹).trace - Real.log S.det - Fintype.card ι

/-- The discrepancy is nonnegative for positive definite `S`, `C`
(Bartlett, STAT 241A (2007), Lemma 2). -/
theorem gaussianDiscrepancy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S C : Matrix ι ι ℝ} (hS : S.PosDef) (hC : C.PosDef) :
    0 ≤ gaussianDiscrepancy S C := by
  have h := hS.log_det_mul_le_trace hC.inv
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    Real.log_mul hS.det_pos.ne' (inv_ne_zero hC.det_pos.ne'), Real.log_inv] at h
  unfold gaussianDiscrepancy
  linarith

/-- The discrepancy vanishes at the fit when `C.det` is a unit. -/
theorem gaussianDiscrepancy_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Matrix ι ι ℝ} (hC : IsUnit C.det) :
    gaussianDiscrepancy C C = 0 := by
  unfold gaussianDiscrepancy
  rw [Matrix.mul_nonsing_inv C hC, Matrix.trace_one]
  ring

/-- The discrepancy is zero exactly at `S = C`
(Bartlett, STAT 241A (2007), Lemma 2). -/
theorem gaussianDiscrepancy_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S C : Matrix ι ι ℝ} (hS : S.PosDef) (hC : C.PosDef) :
    (gaussianDiscrepancy S C = 0 ↔ S = C) := by
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC.det_pos.ne'
  constructor
  · intro hzero
    have hlog : Real.log (S.det * C⁻¹.det) = (S * C⁻¹).trace - Fintype.card ι := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
        Real.log_mul hS.det_pos.ne' (inv_ne_zero hC.det_pos.ne'), Real.log_inv]
      unfold gaussianDiscrepancy at hzero
      linarith
    have h := congrArg (C * ·) (hS.mul_eq_one_of_log_det_eq_trace hC.inv hlog)
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv C hCu, Matrix.one_mul,
      Matrix.mul_one] using h
  · intro hSC
    rw [hSC]
    exact gaussianDiscrepancy_self hCu

end MathlibExt.Probability.Statistics.Measurement

end
