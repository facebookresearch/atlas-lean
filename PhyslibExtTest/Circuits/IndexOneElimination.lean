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
forcing `5` with unit blocks reconstruct to `-7`. -/
example :
    @algebraicReconstruction (Fin 1) (Fin 1) _ _ _ (1 : Matrix (Fin 1) (Fin 1) ℝ)
        invertibleOne (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 2) (fun _ => 5) =
      (fun _ => -7) :=
  scalar_reconstruction_with_nonzeroForcing.1

/-- The value `0` is not consistent with state `2` and forcing `5`
for unit blocks. -/
example :
    ¬ consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 5) (fun _ => 2) (fun _ => 0) :=
  scalar_reconstruction_with_nonzeroForcing.2

/-- The reconstructed value `-7` is consistent with state `2` and
forcing `5` for unit blocks. -/
example :
    consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 5) (fun _ => 2) (fun _ => -7) := by
  apply (@consistentPair_iff_eq_algebraicReconstruction (Fin 1) (Fin 1) _ _ _
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
    (fun _ => 5) (fun _ => 2) (fun _ => -7)).mpr
  exact scalar_reconstruction_with_nonzeroForcing.1.symm

/-- A value different from the reconstruction, here `0`, is excluded
by the consistency criterion for state `2` and forcing `5`. -/
example :
    ¬ consistentPair (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 5) (fun _ => 2) (fun _ => 0) := by
  apply @not_consistentPair_of_ne_algebraicReconstruction (Fin 1) (Fin 1) _ _ _
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) invertibleOne
    (fun _ => 5) (fun _ => 2) (fun _ => 0)
  intro hcon
  have hrec := scalar_reconstruction_with_nonzeroForcing.1
  rw [← hcon] at hrec
  have h0 := congrFun hrec 0
  norm_num at h0

/-- The zero scalar block admits no invertible instance. -/
example : ¬ Nonempty (Invertible (0 : Matrix (Fin 1) (Fin 1) ℝ)) :=
  not_nonempty_invertible_zero_scalar

end PhyslibExtTest.Circuits.IndexOneElimination
