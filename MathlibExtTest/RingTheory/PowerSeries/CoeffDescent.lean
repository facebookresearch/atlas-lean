/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.CoeffDescent
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

-- Consumer with the original binders.
example {L : Type} [Field L] (K₀ : Subfield L) {n : ℕ} (g : Fin n → PowerSeries L)
    (hg : ∀ (i : Fin n) (m : ℕ), (g i).coeff m ∈ K₀)
    (c : Fin n → L) (h : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀) :
    ∃ c' : Fin n → L, (∀ i, c' i ∈ K₀) ∧ ∑ i, c' i • g i = ∑ i, c i • g i :=
  PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem K₀ g hg c h

-- The coefficient hypothesis matters: for `K₀ = ℚ` in `ℝ`, `g = 1` and
-- `c = √2`, no descended scalars exist, since that would force `√2 ∈ ℚ`.
example : ¬ ∃ c' : Fin 1 → ℝ, (∀ i, c' i ∈ (⊥ : Subfield ℝ)) ∧
    (∑ i : Fin 1, c' i • (1 : PowerSeries ℝ)) =
      ∑ i : Fin 1, (fun _ => Real.sqrt 2) i • (1 : PowerSeries ℝ) := by
  rintro ⟨c', hc', hsum⟩
  have h0 : c' 0 = Real.sqrt 2 := by
    have hcoeff := congrArg (PowerSeries.coeff (R := ℝ) 0) hsum
    simpa using hcoeff
  have hmem := hc' 0
  rw [h0] at hmem
  rw [Subfield.bot_eq_of_charZero] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact irrational_sqrt_two ⟨q, by simpa using hq⟩
