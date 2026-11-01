/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic

/-!
# Tests for the uncertainty principle on a finite abelian group

* The delta function on `ZMod 2` has Fourier transform identically `1`,
  so its supports have cards `1` and `2` and the Donoho–Stark bound is
  an equality: `1 * 2 = 2`.
* The constant function on `ZMod 3` has Fourier transform supported
  only at the trivial character, so its supports have cards `3` and `1`
  and the bound is again an equality: `3 * 1 = 3`.
* No nonzero function on `ZMod 2` is supported in `{0}` with Fourier
  transform supported in `{0}` (the nonvanishing corollary, since
  `1 * 1 < 2`).
* Concentration bounds for the delta function on `ZMod 2`, and the
  character norm bound.
-/

open scoped BigOperators
open MathlibExt.Analysis.Fourier.FiniteAbelianUncertainty
open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted

namespace MathlibExtTest.Analysis.Fourier.FiniteAbelianUncertaintyTests

/-- The delta function at `0` on `ZMod 2`. -/
private def deltaTwo : ZMod 2 → ℂ := fun x => if x = 0 then 1 else 0

/-- The Fourier transform of the delta function is identically `1`. -/
private theorem dftFun_deltaTwo (ψ : AddChar (ZMod 2) ℂ) :
    dftFun deltaTwo ψ = 1 := by
  simp only [deltaTwo, dftFun]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The support of the delta function on `ZMod 2` is `{0}`. -/
private theorem filter_deltaTwo :
    Finset.univ.filter (fun x : ZMod 2 => deltaTwo x ≠ 0) = {0} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  constructor
  · simp [deltaTwo]
  · intro x hx
    rw [Finset.mem_filter] at hx
    by_contra hne
    exact hx.2 (by simp [deltaTwo, hne])

/-- The Fourier support of the delta function on `ZMod 2` is everything. -/
private theorem filter_dftFun_deltaTwo :
    Finset.univ.filter (fun ψ : AddChar (ZMod 2) ℂ => dftFun deltaTwo ψ ≠ 0) =
      Finset.univ := by
  apply Finset.filter_true_of_mem
  intro ψ _
  rw [dftFun_deltaTwo ψ]
  exact one_ne_zero

/-- Donoho–Stark is sharp for the delta function on `ZMod 2`: `1 * 2 = 2`. -/
example :
    (Finset.univ.filter (fun x : ZMod 2 => deltaTwo x ≠ 0)).card *
      (Finset.univ.filter (fun ψ : AddChar (ZMod 2) ℂ => dftFun deltaTwo ψ ≠ 0)).card =
      Fintype.card (ZMod 2) := by
  rw [filter_deltaTwo, filter_dftFun_deltaTwo, Finset.card_singleton,
    Finset.card_univ, AddChar.card_eq]
  simp

/-- The Donoho–Stark lower bound holds for the delta function on `ZMod 2`. -/
example : Fintype.card (ZMod 2) ≤
    (Finset.univ.filter (fun x : ZMod 2 => deltaTwo x ≠ 0)).card *
      (Finset.univ.filter (fun ψ : AddChar (ZMod 2) ℂ => dftFun deltaTwo ψ ≠ 0)).card :=
  card_le_mul_card_filter_support (f := deltaTwo) (by
    intro h
    have := congrFun h 0
    simp [deltaTwo] at this)

/-- The Fourier transform of the constant function on `ZMod 3` is `3`
at the trivial character and `0` elsewhere. -/
private theorem dftFun_const_zmod_three (ψ : AddChar (ZMod 3) ℂ) :
    dftFun (fun _ : ZMod 3 => (1 : ℂ)) ψ = if ψ = 0 then 3 else 0 := by
  simp only [dftFun, mul_one]
  rw [AddChar.sum_eq_ite]
  split_ifs with h
  · simp [ZMod.card]
  · simp

/-- The Fourier support of the constant function on `ZMod 3` is `{0}`. -/
private theorem filter_dftFun_const_zmod_three :
    Finset.univ.filter (fun ψ : AddChar (ZMod 3) ℂ =>
      dftFun (fun _ : ZMod 3 => (1 : ℂ)) ψ ≠ 0) = {0} := by
  ext ψ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [dftFun_const_zmod_three ψ]
  by_cases h : ψ = 0 <;> simp [h]

/-- Donoho–Stark is sharp for the constant function on `ZMod 3`: `3 * 1 = 3`. -/
example :
    (Finset.univ.filter (fun _x : ZMod 3 => (1 : ℂ) ≠ 0)).card *
      (Finset.univ.filter (fun ψ : AddChar (ZMod 3) ℂ =>
        dftFun (fun _ : ZMod 3 => (1 : ℂ)) ψ ≠ 0)).card =
      Fintype.card (ZMod 3) := by
  rw [filter_dftFun_const_zmod_three, Finset.card_singleton,
    Finset.filter_true_of_mem (fun _ _ => one_ne_zero), Finset.card_univ]
  simp

/-- No nonzero function on `ZMod 2` lives in `{0}` with Fourier
transform living in `{0}`. -/
example (f : ZMod 2 → ℂ) (hA : ∀ x, x ∉ ({0} : Finset (ZMod 2)) → f x = 0)
    (hB : ∀ ψ, ψ ∉ ({0} : Finset (AddChar (ZMod 2) ℂ)) → dftFun f ψ = 0) :
    f = 0 := by
  apply eq_zero_of_card_mul_card_lt_card hA hB
  simp

/-- Concentration of the delta function on `ZMod 2`: its mass on `{0}`
is its total mass, since its Fourier transform lives everywhere and
`1 * 2 / 2 = 1`. -/
example :
    ∑ x ∈ ({0} : Finset (ZMod 2)), ‖deltaTwo x‖ ^ 2 ≤
      (({0} : Finset (ZMod 2)).card *
        (Finset.univ : Finset (AddChar (ZMod 2) ℂ)).card / Fintype.card (ZMod 2)) *
        ∑ x : ZMod 2, ‖deltaTwo x‖ ^ 2 :=
  sum_norm_sq_le_of_dftFun_eq_zero_of_notMem (f := deltaTwo)
    (fun ψ hψ => (hψ (Finset.mem_univ ψ)).elim)

/-- Dual concentration for the delta function on `ZMod 2`, with `A = {0}`. -/
example :
    ∑ ψ : AddChar (ZMod 2) ℂ, ‖dftFun deltaTwo ψ‖ ^ 2 ≤
      (({0} : Finset (ZMod 2)).card *
        (Finset.univ : Finset (AddChar (ZMod 2) ℂ)).card / Fintype.card (ZMod 2)) *
        ∑ ψ : AddChar (ZMod 2) ℂ, ‖dftFun deltaTwo ψ‖ ^ 2 :=
  sum_norm_sq_dftFun_le_of_eq_zero_of_notMem (f := deltaTwo) (B := Finset.univ)
    (fun x hx => by
      have hne : x ≠ 0 := Finset.notMem_singleton.mp hx
      simp [deltaTwo, hne])

/-- Characters take values on the unit circle, at the trivial character
of `ZMod 2` evaluated at `1`. -/
example : ‖(0 : AddChar (ZMod 2) ℂ) 1‖ = 1 :=
  norm_addChar_apply 0 1

/-- Plancherel for the delta function on `ZMod 2`: both sides are `2`. -/
example : ∑ ψ : AddChar (ZMod 2) ℂ, ‖dftFun deltaTwo ψ‖ ^ 2 =
    (Fintype.card (ZMod 2) : ℝ) * ∑ x : ZMod 2, ‖deltaTwo x‖ ^ 2 :=
  sum_norm_sq_dftFun deltaTwo

end MathlibExtTest.Analysis.Fourier.FiniteAbelianUncertaintyTests
