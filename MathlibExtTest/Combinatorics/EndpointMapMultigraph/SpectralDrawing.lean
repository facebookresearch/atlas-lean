/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.SpectralDrawing

@[expose] public section

namespace EndpointMapMultigraphSpectralDrawingTest

open EndpointMapMultigraph Matrix

/-- The unit vector `(1, -1)/√2` is orthonormal and orthogonal to the constants on `Fin 2`. -/
theorem drawing_orthonormal :
    ∀ i j : Fin 1, (![![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]] : Fin 1 → Fin 2 → ℝ) i ⬝ᵥ
      (![![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]] : Fin 1 → Fin 2 → ℝ) j =
        if i = j then 1 else 0 := by
  intro i j
  fin_cases i; fin_cases j
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp [dotProduct, Fin.sum_univ_two, h2]
  norm_num

/-- For one edge of weight `3`, the one-dimensional drawing `(1, -1)/√2` has energy at least
`λ₂`. -/
example :
    ∑ j : Fin 1, (isSymmetric_toEuclideanLin_laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1)
        (fun _ => 3)).eigenvalues finrank_euclideanSpace
          ⟨Fintype.card (Fin 2) - 2 - j, by have := j.isLt; simp⟩ ≤
      ∑ i, (![![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]] : Fin 1 → Fin 2 → ℝ) i ⬝ᵥ
        (laplacian (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => 3) *ᵥ
          (![![(Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]] : Fin 1 → Fin 2 → ℝ) i) :=
  sum_eigenvalues_le_sum_quadratic_form _ _ (fun _ => by norm_num) (by simp) _
    drawing_orthonormal (fun i => by fin_cases i; simp [dotProduct, Fin.sum_univ_two])

end EndpointMapMultigraphSpectralDrawingTest
