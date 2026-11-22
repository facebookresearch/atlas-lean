/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.ClusterAlgebra.LaurentPhenomenon
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the Laurent phenomenon in rank two
-/

namespace MathlibExtTest.RingTheory.ClusterAlgebra.LaurentPhenomenon

open MathlibExt.RingTheory.ClusterAlgebra
open MathlibExt.RingTheory.ClusterAlgebra.LaurentPhenomenonWanted

/-- The generators of the Laurent ring and their inverses lie in it. -/
example (i : Fin 2) : initialCluster (Fin 2) i ∈ laurentSubalgebra (Fin 2) ∧
    (initialCluster (Fin 2) i)⁻¹ ∈ laurentSubalgebra (Fin 2) :=
  ⟨Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩), Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)⟩

/-- A wild type, `bc = 9 > 4`: the cluster variables are still Laurent polynomials. -/
example (k : ℕ) :
    rankTwoSeq 3 3 (initialCluster (Fin 2) 0) (initialCluster (Fin 2) 1) k ∈
      laurentSubalgebra (Fin 2) :=
  rankTwoSeq_mem_laurentSubalgebra (by norm_num) (by norm_num) k

/-- Specializing at `x = y = 1`: every term of the recurrence is an integer. -/
example {b c : ℕ} (hb : 0 < b) (hc : 0 < c) (k : ℕ) : ∃ m : ℤ, rankTwoSeq b c (1 : ℚ) 1 k = m := by
  have h1 : (1 : ℚ) ∈ (Int.castRingHom ℚ).range := one_mem _
  have h1' : (1 : ℚ)⁻¹ ∈ (Int.castRingHom ℚ).range := by rw [inv_one]; exact h1
  obtain ⟨m, hm⟩ := RingHom.mem_range.mp (rankTwoSeq_mem hb hc h1 h1 h1' h1' k)
  exact ⟨m, hm.symm⟩

/-- With `x = 2` and `y = 1` the denominators are powers of `2`. -/
example (k : ℕ) : rankTwoSeq 1 4 (2 : ℚ) 1 k ∈ Subring.closure ({2, 2⁻¹, 1} : Set ℚ) :=
  rankTwoSeq_mem one_pos (by norm_num) (Subring.subset_closure (by simp))
    (Subring.subset_closure (by simp)) (Subring.subset_closure (by simp))
    (Subring.subset_closure (by simp)) k

/-- No term needs to be nonzero: at `x = 1, y = -1` the term `rankTwoSeq 1 1 1 (-1) 2` vanishes,
and the terms after it are still integers. -/
example : rankTwoSeq 1 1 (1 : ℚ) (-1) 2 = 0 := by norm_num [rankTwoSeq]

example (k : ℕ) : ∃ m : ℤ, rankTwoSeq 1 1 (1 : ℚ) (-1) k = m := by
  have h1 : (1 : ℚ) ∈ (Int.castRingHom ℚ).range := one_mem _
  have h1' : (1 : ℚ)⁻¹ ∈ (Int.castRingHom ℚ).range := by rw [inv_one]; exact h1
  have hm1 : (-1 : ℚ) ∈ (Int.castRingHom ℚ).range := neg_mem h1
  have hm1' : (-1 : ℚ)⁻¹ ∈ (Int.castRingHom ℚ).range := by rw [inv_neg, inv_one]; exact hm1
  obtain ⟨m, hm⟩ := RingHom.mem_range.mp (rankTwoSeq_mem one_pos one_pos h1 hm1 h1' hm1' k)
  exact ⟨m, hm.symm⟩

/-- The hypothesis `0 < b` is needed: for `b = 0, c = 1` and `x = y = 1` the terms start
`1, 1, 2, 2, 3 / 2`. -/
example : ¬ ∃ m : ℤ, rankTwoSeq 0 1 (1 : ℚ) 1 4 = m := by
  rintro ⟨m, hm⟩
  have h : rankTwoSeq 0 1 (1 : ℚ) 1 4 = 3 / 2 := by norm_num [rankTwoSeq]
  rw [h] at hm
  have h2 : (3 : ℚ) = 2 * m := by linarith
  have h3 : (3 : ℤ) = 2 * m := by exact_mod_cast h2
  omega

end MathlibExtTest.RingTheory.ClusterAlgebra.LaurentPhenomenon
