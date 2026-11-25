/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.Combinatorics.KuniskyKomlosLowerBound
import Mathlib.Data.Matrix.Block

open scoped ENNReal
open MatrixDiscrepancy KomlosDiscrepancyWanted

namespace MathlibExtTest.KuniskyKomlosLowerBound

example : ENNReal.ofReal (1 + Real.sqrt 2) ≤ komlosConstant :=
  kunisky2023LowerBound_holds

private noncomputable def firstHaar : Matrix (Fin 2) (Fin 2) ℝ :=
  haarStep (fun _ _ : Fin 1 => 1)

example : ColumnAdmissible firstHaar :=
  haarStep_admissible columnAdmissible_unit

-- Equal signs cancel the second row, and opposite signs cancel the first row.
example :
    firstHaar.mulVec (fun _ => signValue 1) 0 = Real.sqrt 2 ∧
      firstHaar.mulVec (fun _ => signValue 1) 1 = 0 ∧
      firstHaar.mulVec (fun j => signValue j) 0 = 0 ∧
      firstHaar.mulVec (fun j => signValue j) 1 = -Real.sqrt 2 := by
  have h0 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = Sum.inl 0 :=
    finSumFinEquiv_symm_apply_castAdd (0 : Fin 1)
  have h1 : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 1 = Sum.inr 0 :=
    finSumFinEquiv_symm_apply_natAdd (0 : Fin 1)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [firstHaar, Matrix.mulVec, dotProduct, Fin.sum_univ_two, haarStep, h0, h1,
      Matrix.fromBlocks, signValue, haarScale, Matrix.one_apply_eq]
  ring

end MathlibExtTest.KuniskyKomlosLowerBound
