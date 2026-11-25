/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.DominantRootPosCoeffCharPoly

open Polynomial

-- For `x ^ 2 - x - 1`, the dominant root satisfies the golden-ratio equation.
example :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ^ 2 = ρ + 1 ∧
      (∀ x : ℝ, 0 < x → x ^ 2 = x + 1 → x = ρ) := by
  have hφ : (X ^ 2 - X - 1 : ℤ[X])
      = X ^ 2 - ∑ i : Fin 2, C ((fun _ : Fin 2 => 1) i : ℤ) * X ^ (2 - 1 - (i : ℕ)) := by
    simp [Fin.sum_univ_two]
    ring
  obtain ⟨ρ, hρ1, huniq, s, hroots, hnorm⟩ :=
    MetaMathlibExt.exists_dominant_root_of_pos_coeff_charPoly 2 (by norm_num)
      (fun _ => 1) (fun _ => by norm_num) (X ^ 2 - X - 1 : ℤ[X]) hφ
  have hρroot : eval (ρ : ℂ) ((X ^ 2 - X - 1 : ℤ[X]).map (Int.castRingHom ℂ)) = 0 := by
    have hmem : (ρ : ℂ) ∈ ((X ^ 2 - X - 1 : ℤ[X]).map (Int.castRingHom ℂ)).roots := by
      rw [hroots]
      exact Multiset.mem_cons_self _ _
    exact (Polynomial.mem_roots'.mp hmem).2
  have hρeq : (ρ : ℂ) ^ 2 = (ρ : ℂ) + 1 := by
    have h : (ρ : ℂ) ^ 2 - (ρ : ℂ) - 1 = 0 := by
      simpa using hρroot
    linear_combination h
  have hρeqR : ρ ^ 2 = ρ + 1 := by exact_mod_cast hρeq
  refine ⟨ρ, hρ1, hρeqR, ?_⟩
  intro x hx hxeq
  apply huniq x hx
  have h : aeval x (X ^ 2 - X - 1 : ℤ[X]) = 0 := by
    have hx2 : x ^ 2 = x + 1 := hxeq
    simp [hx2]
  exact h

-- For `x ^ 2 - 2 * x - 3`, the dominant root is the explicit root `3`.
example :
    ∃ ρ : ℝ, ρ = 3 ∧
      ∃ s : Multiset ℂ, ((X ^ 2 - 2 * X - 3 : ℤ[X]).map (Int.castRingHom ℂ)).roots
          = (ρ : ℂ) ::ₘ s ∧ ∀ z ∈ s, ‖z‖ < ρ := by
  have hφ : (X ^ 2 - 2 * X - 3 : ℤ[X])
      = X ^ 2 - ∑ i : Fin 2, C ((![2, 3] : Fin 2 → ℕ) i : ℤ) * X ^ (2 - 1 - (i : ℕ)) := by
    simp [Fin.sum_univ_two]
    ring
  obtain ⟨ρ, hρ1, huniq, s, hroots, hnorm⟩ :=
    MetaMathlibExt.exists_dominant_root_of_pos_coeff_charPoly 2 (by norm_num)
      ![2, 3] (by decide) (X ^ 2 - 2 * X - 3 : ℤ[X]) hφ
  have h3 : aeval (3 : ℝ) (X ^ 2 - 2 * X - 3 : ℤ[X]) = 0 := by
    norm_num [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hρ3 : ρ = 3 := (huniq 3 (by norm_num) h3).symm
  exact ⟨ρ, hρ3, s, hroots, hnorm⟩
