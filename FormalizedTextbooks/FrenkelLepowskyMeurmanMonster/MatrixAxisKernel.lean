/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The matrix/axis coupling excludes the midpoint eigenvalue.
This is finite-dimensional linear algebra with an explicit rank-one vector.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The coupled rank-one Jordan equation has trivial kernel once its axial
contraction vanishes. It covers both physical and integer pair coordinates. -/
theorem matrix_axis_midpoint_kernel {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (M : Matrix ι ι ℝ) (a N α β : ℝ)
    (hN : N ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hnorm : (∑ i, d i * d i) = N)
    (hsym : ∀ i j, M i j = M j i)
    (hcontract : (∑ i, ∑ j, d i * M i j * d j) = 0)
    (heq : ∀ i j,
      α * (d i * (∑ k, d k * M k j) + (∑ k, M i k * d k) * d j) -
        β * a * d i * d j = 2 * α * N * M i j) :
    a = 0 ∧ M = 0 := by
  classical
  let b : ι → ℝ := fun j => ∑ k, d k * M k j
  have hleft (i : ι) : (∑ k, M i k * d k) = b i := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hsym i k, mul_comm]
  have hc : (∑ i, d i * b i) = 0 := by
    change (∑ i, d i * ∑ j, d j * M j i) = 0
    simp_rw [Finset.mul_sum]
    have hh : (∑ i, ∑ j, d i * (d j * M j i)) =
        ∑ i, ∑ j, d i * M i j * d j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsym j i]
      ring
    rw [hh, hcontract]
  have hrow (j : ι) : α * N * b j = -(β * a * N * d j) := by
    have he : (∑ i, d i *
        (α * (d i * b j + b i * d j) - β * a * d i * d j)) =
        ∑ i, d i * (2 * α * N * M i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hleft i]
      exact congrArg (fun z : ℝ => d i * z) (heq i j)
    have hl : (∑ i, d i *
        (α * (d i * b j + b i * d j) - β * a * d i * d j)) =
        α * N * b j - β * a * N * d j := by
      have ht (i : ι) : d i *
          (α * (d i * b j + b i * d j) - β * a * d i * d j) =
          α * b j * (d i * d i) + α * d j * (d i * b i) -
            β * a * d j * (d i * d i) := by ring
      simp_rw [ht]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hnorm, hc]
      ring
    have hr : (∑ i, d i * (2 * α * N * M i j)) = 2 * α * N * b j := by
      change _ = 2 * α * N * ∑ i, d i * M i j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hl, hr] at he
    linarith
  have ha : a = 0 := by
    have he : (∑ j, d j * (α * N * b j)) =
        ∑ j, d j * -(β * a * N * d j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrow]
    have hl : (∑ j, d j * (α * N * b j)) = 0 := by
      calc
        _ = α * N * ∑ j, d j * b j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [hc]; ring
    have hr : (∑ j, d j * -(β * a * N * d j)) = -(β * a * N * N) := by
      calc
        _ = -(β * a * N) * ∑ j, d j * d j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hnorm]; ring
    rw [hl, hr] at he
    have hz : β * a * N * N = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact (mul_eq_zero.mp h).resolve_left hβ
      · exact False.elim (hN h)
    · exact False.elim (hN h)
  have hb : ∀ j, b j = 0 := by
    intro j
    have h := hrow j
    rw [ha] at h
    have hz : (α * N) * b j = 0 := by simpa using h
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hα hN)
  refine ⟨ha, ?_⟩
  ext i j
  have h := heq i j
  change α * (d i * b j + (∑ k, M i k * d k) * d j) -
    β * a * d i * d j = 2 * α * N * M i j at h
  rw [hleft, hb, hb, ha] at h
  have hz : (2 * α * N) * M i j = 0 := by simpa using h.symm
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hα) hN)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
