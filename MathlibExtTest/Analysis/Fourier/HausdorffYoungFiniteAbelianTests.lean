/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.HausdorffYoungFiniteAbelian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.NormNum

/-!
# Tests for the Hausdorff–Young inequality on a finite abelian group

The sharp case is a delta function: for `f = Pi.single a 1`, one has
`dftFun f ψ = ψ a`, whose norm is `1` for every character, so the left
side of the Hausdorff–Young inequality is exactly `(card G) ^ (1 / q)`
and the bound is attained. The concrete instance is `G = ZMod 2` at
`p = 2`, where the bound is `√2`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Fourier.HausdorffYoungFiniteAbelianTests

open MathlibExt.Analysis.Fourier.HausdorffYoungFiniteAbelian
open MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted

/-- The Fourier transform of a delta function is the character itself. -/
theorem dftFun_single_apply {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (a : G) (ψ : AddChar G ℂ) :
    dftFun (Pi.single a 1) ψ = ψ a := by
  show ∑ x : G, ψ x * (Pi.single a (1 : ℂ) : G → ℂ) x = ψ a
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_eq_same]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

/-- The Hausdorff–Young bound applied to a delta function. -/
theorem hausdorffYoung_dft_single_le {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (a : G) {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    (∑ ψ : AddChar G ℂ, ‖dftFun (Pi.single a 1) ψ‖ ^ (p / (p - 1))) ^
        (1 / (p / (p - 1))) ≤
      (Fintype.card G : ℝ) ^ (1 / (p / (p - 1))) := by
  have hp0 : 0 < p := by linarith
  have h := @hausdorffYoung_dft G _ _ ⊤ ⊤ _ _ p hp1 hp2 (Pi.single a 1)
  have hsum : (∑ x : G, ‖(Pi.single a (1 : ℂ) : G → ℂ) x‖ ^ p) = 1 := by
    rw [Finset.sum_eq_single a]
    · simp [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, norm_zero, Real.zero_rpow hp0.ne']
    · simp
  rw [hsum, Real.one_rpow, mul_one] at h
  exact h

/-- The Hausdorff–Young bound is sharp: for a delta function the left
side equals `(card G) ^ (1 / q)`. -/
theorem hausdorffYoung_dft_single_eq {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (a : G) {p : ℝ} (_hp1 : 1 < p) (_hp2 : p ≤ 2) :
    (∑ ψ : AddChar G ℂ, ‖dftFun (Pi.single a 1) ψ‖ ^ (p / (p - 1))) ^
        (1 / (p / (p - 1))) =
      (Fintype.card G : ℝ) ^ (1 / (p / (p - 1))) := by
  have hsum : (∑ ψ : AddChar G ℂ, ‖dftFun (Pi.single a 1) ψ‖ ^ (p / (p - 1))) =
      (Fintype.card G : ℝ) := by
    have h1 : ∀ ψ : AddChar G ℂ,
        ‖dftFun (Pi.single a 1) ψ‖ ^ (p / (p - 1)) = 1 := by
      intro ψ
      rw [dftFun_single_apply, AddChar.norm_apply, Real.one_rpow]
    rw [Finset.sum_congr rfl (fun ψ _ => h1 ψ), Finset.sum_const, Finset.card_univ,
      AddChar.card_eq, nsmul_eq_mul, mul_one]
  rw [hsum]

/-- Plancherel for a delta function: the sum of the squared norms of the
Fourier coefficients is the group order. -/
theorem sum_norm_sq_dftFun_single {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (a : G) :
    (∑ ψ : AddChar G ℂ, ‖dftFun (Pi.single a 1) ψ‖ ^ 2) =
      (Fintype.card G : ℝ) := by
  have h := sum_norm_sq_dftFun (G := G) (Pi.single a (1 : ℂ))
  have hsum : (∑ x : G, ‖(Pi.single a (1 : ℂ) : G → ℂ) x‖ ^ 2) = 1 := by
    rw [Finset.sum_eq_single a]
    · simp [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, norm_zero]
      norm_num
    · simp
  rw [hsum, mul_one] at h
  exact h

/-- The concrete instance `G = ZMod 2`, `p = 2`: the Hausdorff–Young
bound for a delta function is `√2`. -/
theorem hausdorffYoung_zmod2_p2 :
    (∑ ψ : AddChar (ZMod 2) ℂ,
        ‖dftFun (Pi.single (1 : ZMod 2) 1) ψ‖ ^ (2:ℝ)) ^ (1 / 2 : ℝ) =
      Real.sqrt 2 := by
  have h := hausdorffYoung_dft_single_eq (G := ZMod 2) (a := (1 : ZMod 2)) (p := 2)
    (by norm_num) (by norm_num)
  have h2 : (2:ℝ) / (2 - 1) = 2 := by norm_num
  rw [h2] at h
  rw [h, Real.sqrt_eq_rpow, ZMod.card]
  norm_num

end MathlibExtTest.Analysis.Fourier.HausdorffYoungFiniteAbelianTests
