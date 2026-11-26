/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.EuclideanRamsey

/-! # Tests for indexed Euclidean Ramsey configurations -/

namespace EuclideanRamseyTests

-- The empty configuration still requires a positive host dimension and a palette witness.
example (a : Fin 0 → EuclideanSpace ℝ (Fin 0)) : IsEuclideanRamsey a := by
  intro r hr
  refine ⟨1, le_rfl, fun _ ↦ ⟨Fin.elim0, ?_, ⟨0, by omega⟩, ?_⟩⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

-- Indexing need not be injective: two coincident points can have a coincident copy.
example : IsEuclideanRamsey (fun _ : Fin 2 ↦ (0 : EuclideanSpace ℝ (Fin 0))) := by
  intro r _
  refine ⟨1, le_rfl, fun color ↦ ⟨fun _ ↦ 0, ?_, color 0, fun _ ↦ rfl⟩⟩
  intro i j
  simp

private theorem dist_basis_sq {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    dist (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1) ^ 2 = 2 := by
  have h := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin n)
  rw [dist_eq_norm, norm_sub_sq_real, h.norm_eq_one i, h.norm_eq_one j, h.inner_eq_zero hij]
  norm_num

-- For each palette, two of the r+1 coordinate unit vectors share a color. Their distance
-- is exactly that of the original pair, so the witness cannot just collapse both labels.
example : IsEuclideanRamsey (fun i : Fin 2 ↦ EuclideanSpace.single i (1 : ℝ)) := by
  intro r _
  refine ⟨r + 1, Nat.succ_pos r, fun color ↦ ?_⟩
  obtain ⟨u, v, huv, hcolor⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j : Fin (r + 1) ↦ color (EuclideanSpace.single j (1 : ℝ))) (by simp)
  let j : Fin 2 → Fin (r + 1) := fun i ↦ if i = 0 then u else v
  have hj : Function.Injective j := by
    intro i k heq
    fin_cases i <;> fin_cases k <;> simp_all [j, Ne.symm huv]
  refine ⟨fun i ↦ EuclideanSpace.single (j i) 1, ?_, color (EuclideanSpace.single u 1), ?_⟩
  · intro i k
    by_cases hik : i = k
    · subst k
      simp
    · apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      exact (dist_basis_sq (hj.ne hik)).trans (dist_basis_sq hik).symm
  · intro i
    fin_cases i <;> simp [j, hcolor]

end EuclideanRamseyTests
