/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.SpectralSparsification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.LinearAlgebra.Matrix.SpectralSparsification` -/

namespace MathlibExtTest.SpectralSparsification

open Matrix MathlibExt.GraphTheory.SpectralSparsificationWanted

-- Test section: the hypotheses are satisfiable. The standard basis decomposes the identity.
private theorem sum_vecMulVec_single (n : ℕ) :
    ∑ i : Fin n, vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i 1) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]
  · simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply, h]

-- For `d = 4` the constant is `κ = (4 + 1 + 2 · 2) / (4 + 1 - 2 · 2) = 9`.
private theorem kappa_four :
    ((4 : ℝ) + 1 + 2 * Real.sqrt 4) / (4 + 1 - 2 * Real.sqrt 4) = 9 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

-- With `d = 4`, the standard basis of `ℝⁿ` has a reweighting with at most `4 n` nonzero weights
-- and `I ≼ ∑ sᵢ eᵢ eᵢᵀ ≼ 9 I`.
example (n : ℕ) : ∃ s : Fin n → ℝ, 0 ≤ s ∧
    ((Finset.univ.filter fun i => s i ≠ 0).card : ℝ) ≤ 4 * n ∧
    (∑ i, s i • vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i 1) - 1).PosSemidef ∧
    ((9 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      ∑ i, s i • vecMulVec (Pi.single i (1 : ℝ)) (Pi.single i 1)).PosSemidef := by
  have h := exists_sparse_reweighting (d := 4) (by norm_num) _ (sum_vecMulVec_single n)
  rwa [kappa_four] at h

-- Test section: `d n` need not be an integer. In dimension one, with `d = 3 / 2`, the two vectors
-- `3 / 5` and `4 / 5` decompose the identity, and at most `⌊3 / 2⌋ = 1` weight is nonzero.
private noncomputable def w : Fin 2 → Fin 1 → ℝ := ![![3 / 5], ![4 / 5]]

private theorem sum_vecMulVec_w : ∑ i, vecMulVec (w i) (w i) = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  simp [w, Matrix.sum_apply, vecMulVec_apply, Fin.sum_univ_two]
  norm_num

example : ∃ s : Fin 2 → ℝ, 0 ≤ s ∧ (Finset.univ.filter fun i => s i ≠ 0).card ≤ 1 ∧
    (∑ i, s i • vecMulVec (w i) (w i) - 1).PosSemidef := by
  obtain ⟨s, hs, hcard, hlo, -⟩ :=
    exists_sparse_reweighting (d := 3 / 2) (by norm_num) _ sum_vecMulVec_w
  refine ⟨s, hs, ?_, hlo⟩
  have hlt : ((Finset.univ.filter fun i => s i ≠ 0).card : ℝ) < 2 := by
    push_cast at hcard
    linarith
  exact Nat.lt_succ_iff.1 (by exact_mod_cast hlt)

-- Test section: the edge case `n = 0`. Every family decomposes the identity of `ℝ⁰`, and the
-- theorem then allows no nonzero weight at all.
example (m : ℕ) (v : Fin m → Fin 0 → ℝ) {d : ℝ} (hd : 1 < d) :
    ∃ s : Fin m → ℝ, 0 ≤ s ∧ (Finset.univ.filter fun i => s i ≠ 0).card = 0 := by
  obtain ⟨s, hs, hcard, -⟩ := exists_sparse_reweighting hd v (Subsingleton.elim _ _)
  refine ⟨s, hs, ?_⟩
  exact_mod_cast le_antisymm (by simpa using hcard) (Nat.cast_nonneg _)

end MathlibExtTest.SpectralSparsification
