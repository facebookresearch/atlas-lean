/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.IndexOneElimination

@[expose] public section

open PhyslibExt.Circuits.IndexOneElimination

namespace PhyslibExtTest.Circuits.IndexOneElimination

/-- Scalar reconstruction with nonzero forcing: state `2` and
forcing `5` with unit blocks reconstruct to `-7`, so the forcing is
retained by the reconstruction. -/
private lemma scalar_reconstruction_with_nonzeroForcing :
    @algebraicReconstruction (Fin 1) (Fin 1) _ _ _ (1 : Matrix (Fin 1) (Fin 1) ℝ)
        invertibleOne (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 2) (fun _ => 5) =
      (fun _ => -7) := by
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = 1 :=
    Matrix.inv_eq_left_inv (by simp)
  simp only [algebraicReconstruction, h1, Matrix.one_mulVec]
  funext i
  simp only [Pi.neg_apply, Pi.add_apply]
  norm_num

/-- The value `0` is not consistent with state `2` and forcing `5`
for unit blocks, checked directly from the algebraic equation. -/
example :
    ¬ consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 5) (fun _ => 2) (fun _ => 0) := by
  intro hcon
  simp only [consistentPair, Matrix.one_mulVec] at hcon
  have h0 := congrFun hcon 0
  simp only [Pi.add_apply, Pi.zero_apply] at h0
  norm_num at h0

/-- The reconstructed value `-7` is consistent with state `2` and
forcing `5` for unit blocks. -/
example :
    consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 5) (fun _ => 2) (fun _ => -7) := by
  apply (@consistentPair_iff_eq_algebraicReconstruction (Fin 1) (Fin 1) _ _ _
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
    (fun _ => 5) (fun _ => 2) (fun _ => -7)).mpr
  exact scalar_reconstruction_with_nonzeroForcing.symm

/-- A value different from the reconstruction, here `0`, is excluded
by the consistency criterion for state `2` and forcing `5`. -/
example :
    ¬ consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 5) (fun _ => 2) (fun _ => 0) := by
  apply @not_consistentPair_of_ne_algebraicReconstruction (Fin 1) (Fin 1) _ _ _
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
    (fun _ => 5) (fun _ => 2) (fun _ => 0)
  intro hcon
  have hrec := scalar_reconstruction_with_nonzeroForcing
  rw [← hcon] at hrec
  have h0 := congrFun hrec 0
  norm_num at h0

/-- The zero scalar block admits no invertible instance, so a
singular algebraic block is outside the reduction. -/
example : ¬ Nonempty (Invertible (0 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  intro hne
  obtain ⟨h⟩ := hne
  have h2 := h.mul_invOf_self
  rw [Matrix.zero_mul] at h2
  have h3 := congrFun (congrFun h2 0) 0
  simp at h3

/-- Descriptor satisfaction can be stated for a singular algebraic
block: the predicate itself needs no invertibility instance. -/
example : Prop :=
  satisfiesDescriptorSystem (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 2) (fun _ _ => -2)

/-- Concrete reduced dynamics: with unit blocks `A = B = C = D = 1`
and zero forcing, the constant state `x = 2` and algebraic value
`y = -2` satisfy the descriptor system, hence the reduced system,
and the reconstruction at every time is the value `-2`. -/
example :
    @satisfiesReducedSystem (Fin 1) (Fin 1) _ _ _
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 2) (fun _ _ => -2) ∧
      @algebraicReconstruction (Fin 1) (Fin 1) _ _ _
          (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
          (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 2) (fun _ => 0) 0 = -2 := by
  have hdesc : satisfiesDescriptorSystem (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 2) (fun _ _ => -2) := by
    refine ⟨differentiable_const _, ?_, ?_⟩
    · intro t
      have hderiv : deriv (fun _ : ℝ => (fun _ : Fin 1 => (2 : ℝ))) t = 0 := by
        simp
      rw [hderiv]
      funext i
      simp [Matrix.one_mulVec]
    · intro t
      funext i
      simp [Matrix.one_mulVec]
  have hred := (@satisfiesDescriptorSystem_iff_satisfiesReducedSystem
    (Fin 1) (Fin 1) _ _ _ (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 2) (fun _ _ => -2)).mp hdesc
  refine ⟨hred, ?_⟩
  have hrec := hred.2.2 0
  have h0 := congrFun hrec 0
  exact h0.symm

end PhyslibExtTest.Circuits.IndexOneElimination
