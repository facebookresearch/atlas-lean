/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DeterminantalTangentMemTangentIff
import MathlibExt.LinearAlgebra.Matrix.RankManifold
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Tests for the kernel-to-image description of determinantal tangent spaces: the zero
matrix is always tangent, and a rank-one `2 × 2` example over an arbitrary field. -/

namespace MathlibExtTest.AlgebraicGeometry.DeterminantalTangentMemTangentIff

open MathlibExt.AlgebraicGeometry.DeterminantalTangent
open WantedExt.AlgebraicGeometry.DeterminantalTangentWanted
open scoped Matrix

theorem zero_mem_tangent {K : Type*} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Matrix.rank A = r)
    (hrm : r < m) (hrn : r < n) :
    (fun ij ↦ (0 : Matrix (Fin m) (Fin n) K) ij.1 ij.2) ∈ tangent r A := by
  rw [mem_tangent_iff A 0 hA hrm hrn]
  intro v _
  simp

theorem rank_one_mem_tangent {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K)
    (hA : A = !![1, 0; 0, 0]) (hB : B = !![0, 1; 0, 0]) :
    (fun ij ↦ B ij.1 ij.2) ∈ tangent 1 A := by
  have hA1 : Matrix.rank A = 1 := by
    have hAvv : A = Matrix.vecMulVec ![1, 0] ![1, 0] := by
      rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply]
    have hAle : Matrix.rank A ≤ 1 := by
      rw [hAvv]
      exact Matrix.rank_vecMulVec_le _ _
    have hAne : A ≠ 0 := by
      intro hcon
      have h00 : A 0 0 = (0 : Matrix (Fin 2) (Fin 2) K) 0 0 := by rw [hcon]
      rw [hA] at h00
      simp at h00
    have hne : Matrix.rank A ≠ 0 := by
      intro hz
      exact hAne ((Matrix.rank_eq_zero_iff A).mp hz)
    omega
  rw [mem_tangent_iff A B hA1 (by norm_num) (by norm_num)]
  intro v hv
  have hv0 : v 0 = 0 := by
    have h0 := congrFun hv 0
    rw [Matrix.toLin'_apply] at h0
    simp only [hA] at h0
    -- h0 : (!![1,0;0,0] *ᵥ v) 0 = 0; LHS = v 0
    have hentry : (!![1, 0; 0, 0] *ᵥ v) 0 = v 0 := by
      change ∑ j, !![1, 0; 0, 0] 0 j * v j = v 0
      simp [Fin.sum_univ_two]
    rw [hentry] at h0
    exact h0
  -- goal: toLin' B v ∈ range (toLin' A); witness u = Pi.single 0 (v 1)
  set u : Fin 2 → K := Pi.single 0 (v 1) with hu
  have hu0 : u 0 = v 1 := by
    simp [hu]
  have hu1 : u 1 = 0 := by
    rw [hu]
    exact Pi.single_eq_of_ne (by decide) _
  rw [LinearMap.mem_range]
  refine ⟨u, ?_⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  ext i
  change ∑ j, A i j * u j = ∑ j, B i j * v j
  fin_cases i <;> simp [hA, hB, Fin.sum_univ_two, hu0, hu1]

end MathlibExtTest.AlgebraicGeometry.DeterminantalTangentMemTangentIff
