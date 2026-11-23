/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.BanachNecasBabuska
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.BanachNecasBabuska

namespace MathlibExtTest.Analysis.InnerProductSpace.BanachNecasBabuskaBanachTests

-- The trial space has its standard supremum norm; the test space has its Euclidean norm.
private noncomputable def supForm :
    (Fin 2 → ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
  (InnerProductSpace.toDual ℝ _).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap

private theorem supForm_apply (x : Fin 2 → ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    supForm x y = ⟪WithLp.toLp 2 x, y⟫_ℝ := by
  simp [supForm, EuclideanSpace.equiv, InnerProductSpace.toDual_apply_apply]

-- The coordinate embedding gives the actual inf-sup constant beta=1.
private theorem supForm_lower_bound (x : Fin 2 → ℝ) : ‖x‖ ≤ ‖supForm x‖ := by
  have hnorm : ‖supForm x‖ = ‖WithLp.toLp 2 x‖ := by
    simp [supForm, EuclideanSpace.equiv]
  rw [hnorm]
  apply (pi_norm_le_iff_of_nonempty x).mpr
  intro i
  exact PiLp.norm_apply_le (WithLp.toLp 2 x) i

private theorem supForm_nondegenerate :
    ∀ y : EuclideanSpace ℝ (Fin 2),
      (∀ x : Fin 2 → ℝ, supForm x y = 0) → y = 0 := by
  intro y hy
  have h := hy (WithLp.ofLp y)
  rw [supForm_apply, WithLp.toLp_ofLp] at h
  exact inner_self_eq_zero.mp h

-- A concrete caller proves both hypotheses and invokes the actual BNB solution theorem.
example :
    ∃! x : Fin 2 → ℝ, ∀ y : EuclideanSpace ℝ (Fin 2),
      supForm x y =
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))
          (WithLp.toLp 2 ![3, 4]) y :=
  exists_unique_apply_eq (E := Fin 2 → ℝ) (F := EuclideanSpace ℝ (Fin 2))
    (B := supForm) ⟨1, one_pos, fun x => by simpa using supForm_lower_bound x⟩
    supForm_nondegenerate _

example :
    ∃ x : Fin 2 → ℝ,
      (∀ y : EuclideanSpace ℝ (Fin 2), supForm x y =
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))
          (WithLp.toLp 2 ![3, 4]) y) ∧
      ‖x‖ ≤ (1 : ℝ)⁻¹ *
        ‖InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))
          (WithLp.toLp 2 ![3, 4])‖ :=
  exists_apply_eq_and_norm_le (E := Fin 2 → ℝ) (F := EuclideanSpace ℝ (Fin 2))
    (B := supForm) one_pos (fun x => by simpa using supForm_lower_bound x)
    supForm_nondegenerate _

private theorem norm_sup_two (x : Fin 2 → ℝ) : ‖x‖ = max ‖x 0‖ ‖x 1‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonempty x).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (norm_le_pi_norm x 0) (norm_le_pi_norm x 1)

-- This norm fails the parallelogram identity, so it is not an inner-product norm.
example :
    ‖(![1, 0] + ![0, 1] : Fin 2 → ℝ)‖ ^ 2 +
      ‖(![1, 0] - ![0, 1] : Fin 2 → ℝ)‖ ^ 2 ≠
        2 * (‖(![1, 0] : Fin 2 → ℝ)‖ ^ 2 + ‖(![0, 1] : Fin 2 → ℝ)‖ ^ 2) := by
  norm_num [norm_sup_two]

-- Generic interface coverage: neither space needs an inner product for the dual-norm API.
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] F →L[ℝ] ℝ) (x : E) :
    ‖B x‖ = ⨆ y : {y : F // ‖y‖ ≤ 1}, ‖B x y‖ :=
  norm_apply_eq_iSup (E := E) (F := F) B x

-- Conditional API coverage for arbitrary Banach trial space, with the BNB witnesses explicit.
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (B : E →L[ℝ] F →L[ℝ] ℝ) (hInf : IsInfSup (E := E) (F := F) B)
    (hNondeg : IsNondegenerate (E := E) (F := F) B)
    (φ : F →L[ℝ] ℝ) :
    ∃! x : E, ∀ y : F, B x y = φ y :=
  exists_unique_apply_eq (E := E) (F := F) hInf hNondeg φ

end MathlibExtTest.Analysis.InnerProductSpace.BanachNecasBabuskaBanachTests
