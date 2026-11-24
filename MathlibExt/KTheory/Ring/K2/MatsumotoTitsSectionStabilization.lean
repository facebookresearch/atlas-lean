/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsMonomialStabilization

/-!
# Stabilization of Tits sections

The chosen sections of the Tits monomial extensions commute with successor
stabilization, both for the ambient monomial group and for its determinant-one
subgroup.
-/

@[expose] public section

universe u

open PermutationBilinearCocycle
open PermutationBilinearTitsStabilization
open Matrix.GeneralLinearGroup

namespace MatsumotoTitsMonomialExtension

theorem titsMonomialLiftSuccHom_titsMonomialSection
    (F : Type u) [Field F] (n : ℕ)
    (b : MonomialBase Fˣ (Fin n)) :
    titsMonomialLiftSuccHom F n (titsMonomialSection F n b) =
      titsMonomialSection F (n + 1) (monomialSuccHom b) := by
  apply TitsMonomialLift.ext_base_coeff_right
  · simp
  · simp
  · simp

theorem HMTitsSuccHom_HMTitsSection
    (F : Type u) [Field F] (n : ℕ) (m : M F n) :
    HMTitsSuccHom F n (HMTitsSection F n m) =
      HMTitsSection F (n + 1) (monomialSLSuccHom (R := F) m) := by
  apply Subtype.ext
  apply Prod.ext
  · calc ambientLiftHom F (n + 1)
          (HMTitsSuccHom F n (HMTitsSection F n m))
        = titsMonomialLiftSuccHom F n
            (ambientLiftHom F n (HMTitsSection F n m)) :=
          HMTitsSuccHom_ambient F n (HMTitsSection F n m)
      _ = titsMonomialLiftSuccHom F n
            (titsMonomialSection F n
              (monomialSLToMonomialBase F (Fin n) m)) := by
          rw [HMTitsSection_ambient]
      _ = titsMonomialSection F (n + 1)
            (monomialSuccHom
              (monomialSLToMonomialBase F (Fin n) m)) := by
          rw [titsMonomialLiftSuccHom_titsMonomialSection]
      _ = titsMonomialSection F (n + 1)
            (monomialSLToMonomialBase F (Fin (n + 1))
              (monomialSLSuccHom (R := F) m)) := by
          -- `coe_monomialSLSuccHom` uses `↑`
          have h :
              (monomialSLSuccHom (R := F) m :
                MonomialBase Fˣ (Fin (n + 1))) =
              monomialSuccHom (m : MonomialBase Fˣ (Fin n)) :=
            coe_monomialSLSuccHom (R := F) m
          have h1 :
              (m : MonomialBase Fˣ (Fin n)) =
              monomialSLToMonomialBase F (Fin n) m := rfl
          have h2 :
              (monomialSLSuccHom (R := F) m :
                MonomialBase Fˣ (Fin (n + 1))) =
              monomialSLToMonomialBase F (Fin (n + 1))
                (monomialSLSuccHom (R := F) m) := rfl
          rw [h1] at h
          rw [h2] at h
          rw [← h]
      _ = ambientLiftHom F (n + 1)
            (HMTitsSection F (n + 1)
              (monomialSLSuccHom (R := F) m)) := by
          rw [HMTitsSection_ambient]
  · calc projHom F (n + 1)
          (HMTitsSuccHom F n (HMTitsSection F n m))
        = monomialSLSuccHom (R := F)
            (projHom F n (HMTitsSection F n m)) :=
          HMTitsSuccHom_proj F n (HMTitsSection F n m)
      _ = monomialSLSuccHom (R := F) m := by
          rw [HMTitsSection_proj]
      _ = projHom F (n + 1)
            (HMTitsSection F (n + 1)
              (monomialSLSuccHom (R := F) m)) := by
          rw [HMTitsSection_proj]

end MatsumotoTitsMonomialExtension
