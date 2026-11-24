/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.IntegralCayleyGraphs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases

/-! # Tests for `MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.IntegralCayleyGraphs` -/

namespace MathlibExtTest.IntegralCayleyGraphs

open MathlibExt.GroupTheory.IntegralCayleyGraphsKourovka19Problem50Wanted Polynomial

/-- Transpositions are involutions. -/
private theorem isSwap_sq_eq_one_and_ne_one {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : σ.IsSwap) :
    σ ^ 2 = 1 ∧ σ ≠ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := h
  refine ⟨by rw [sq, Equiv.swap_mul_self], fun h1 => hxy ?_⟩
  simpa using (congrArg (· x) h1).symm

/-- A conjugate of a transposition is a transposition. -/
private theorem isSwap_conj {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : σ.IsSwap)
    (g : Equiv.Perm (Fin n)) : (g * σ * g⁻¹).IsSwap := by
  obtain ⟨x, y, hxy, rfl⟩ := h
  exact ⟨g x, g y, g.injective.ne hxy, (Equiv.swap_apply_apply g x y).symm⟩

open Classical in
-- The Cayley graph of the symmetric group `S_n` on the set of all transpositions is integral:
-- the transpositions are involutions, closed under conjugation, and they generate `S_n`.
example (n : ℕ) : HasIntegralSpectrum
    ((SimpleGraph.mulCayley {σ : Equiv.Perm (Fin n) | σ.IsSwap}).adjMatrix ℤ) :=
  involutionCayleyGraphIntegral_holds _ _ (fun _ h => isSwap_sq_eq_one_and_ne_one h)
    (fun _ h g => isSwap_conj h g) Equiv.Perm.closure_isSwap

-- The general form needs no generation hypothesis: for `R = ∅` the Cayley graph has no edges.
example (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    HasIntegralSpectrum ((SimpleGraph.mulCayley (∅ : Set G)).adjMatrix ℤ) :=
  hasIntegralSpectrum_adjMatrix_mulCayley_of_involutions _ (by simp) (by simp)

-- `HasIntegralSpectrum` is not vacuous: the eigenvalues `±√2` of `!![0, 2; 1, 0]` are not
-- integers.
example : ¬ HasIntegralSpectrum !![(0 : ℤ), 2; 1, 0] := by
  intro h
  have hchar : (!![(0 : ℤ), 2; 1, 0].map (Int.castRingHom ℂ)).charpoly = X ^ 2 - C 2 := by
    rw [Matrix.charpoly_fin_two]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, sub_eq_add_neg]
  obtain ⟨μ, hμ⟩ := Complex.exists_root
    (f := (!![(0 : ℤ), 2; 1, 0].map (Int.castRingHom ℂ)).charpoly)
    (by rw [hchar, degree_X_pow_sub_C two_pos]; norm_num)
  obtain ⟨k, rfl⟩ := h μ hμ
  rw [hchar] at hμ
  have hk : k ^ 2 = 2 := by
    have : (k : ℂ) ^ 2 - 2 = 0 := by simpa using hμ
    exact_mod_cast sub_eq_zero.mp this
  have h1 : k ≤ 1 := by nlinarith
  have h2 : -1 ≤ k := by nlinarith
  interval_cases k <;> simp at hk

end MathlibExtTest.IntegralCayleyGraphs
