/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.DirichletNontrivialZeros
import MathlibExt.NumberTheory.LSeries.RiemannXi

import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Tests for the nontrivial zeros of Dirichlet `L`-functions

Boundary probes for `DirichletCharacter.nontrivialZeros`: the point `s = 0` is excluded, the
pole `s = 1` of the trivial character is not a zero, the character mod `1` recovers
`riemannZetaNontrivialZeros`, and for an imprimitive character the zeros of the Euler factors on
the line `Re s = 0` are not members, so that the trivial character mod `2` has the same nontrivial
zeros as `ζ`. Also boundary probes for `DirichletCharacter.zeroCount`.
-/

@[expose] public section

open Complex

namespace DirichletNontrivialZerosTest

/-- `s = 0` is never a nontrivial zero. -/
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : (0 : ℂ) ∉ χ.nontrivialZeros :=
  fun h => DirichletCharacter.ne_zero_of_mem_nontrivialZeros h rfl

/-- Points to the right of the critical strip are not nontrivial zeros. -/
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : (2 : ℂ) ∉ χ.nontrivialZeros :=
  fun h => by have := h.2.2; norm_num at this

/-- Trivial zeros (here `s = -2`) are excluded by the strip condition. -/
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : (-2 : ℂ) ∉ χ.nontrivialZeros :=
  fun h => by have := h.2.1; norm_num at this

/-- The pole of the trivial character mod `1` is not a nontrivial zero (Mathlib's junk value
`ζ(1) = (γ - log 4π) / 2` is nonzero). -/
example : (1 : ℂ) ∉ (1 : DirichletCharacter ℂ 1).nontrivialZeros := fun h =>
  riemannZeta_one_ne_zero (by simpa using h.1)

/-- For the character mod `1`, the nontrivial zeros are exactly those of `ζ` (the open and the
closed strip agree, as `ζ` has no zeros on `Re s = 0` or `Re s = 1`). -/
private theorem nontrivialZeros_modOne (χ : DirichletCharacter ℂ 1) :
    χ.nontrivialZeros = riemannZetaNontrivialZeros := by
  ext s
  simp only [DirichletCharacter.mem_nontrivialZeros, DirichletCharacter.LFunction_modOne_eq]
  constructor
  · rintro ⟨h, h0, h1⟩
    exact ⟨h, h0.le, h1.le⟩
  · intro hs
    have hξ := (RiemannXi.riemannXi_eq_zero_iff s).mpr hs
    exact ⟨hs.1, RiemannXi.re_pos_of_riemannXi_eq_zero hξ,
      RiemannXi.re_lt_one_of_riemannXi_eq_zero hξ⟩

/-- Nontrivial zeros lie in `Re s < 1`, for every character. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s : ℂ} (hs : s ∈ χ.nontrivialZeros) :
    s.re < 1 :=
  DirichletCharacter.re_lt_one_of_mem_nontrivialZeros hs

/-- **Imprimitive characters.** For the trivial character mod `2`,
`L(s, χ) = (1 - 2⁻ˢ) ζ(s)` vanishes at `s = 2πi / log 2`, on the line `Re s = 0`. This zero of an
Euler factor is trivial: it is not a member of `nontrivialZeros`. -/
example : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 2)
      (2 * Real.pi * I / Real.log 2) = 0 ∧
    (2 * Real.pi * I / Real.log 2 : ℂ) ∉ (1 : DirichletCharacter ℂ 2).nontrivialZeros := by
  set s : ℂ := 2 * Real.pi * I / Real.log 2 with hs
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hre : s.re = 0 := by
    rw [hs, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    simp
  have hs1 : s ≠ 1 := fun h => by rw [h] at hre; simp at hre
  have hpow : (2 : ℂ) ^ (-s) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), ← Complex.ofReal_ofNat,
      ← Complex.ofReal_log (by norm_num), hs]
    rw [show (Real.log 2 : ℂ) * -(2 * Real.pi * I / Real.log 2) = -(2 * Real.pi * I) by
      field_simp]
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  refine ⟨?_, fun h => by have := h.2.1; rw [hre] at this; exact lt_irrefl _ this⟩
  have h := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hs1
  rw [DirichletCharacter.LFunctionTrivChar] at h
  rw [h, Nat.Prime.primeFactors Nat.prime_two, Finset.prod_singleton]
  push_cast
  rw [hpow, sub_self, zero_mul]

/-- The trivial character mod `2` has the same nontrivial zeros as `ζ`: it is induced by the
character mod `1`. -/
example : (1 : DirichletCharacter ℂ 2).nontrivialZeros = riemannZetaNontrivialZeros := by
  rw [← DirichletCharacter.changeLevel_one (one_dvd 2),
    DirichletCharacter.nontrivialZeros_changeLevel, nontrivialZeros_modOne]

/-- The same, through the primitive character. -/
example (χ : DirichletCharacter ℂ 4) [NeZero χ.conductor] :
    χ.primitiveCharacter.nontrivialZeros = χ.nontrivialZeros :=
  DirichletCharacter.nontrivialZeros_primitiveCharacter χ

/-- `N(T, χ) = 0` for `T ≤ 0`. -/
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : χ.zeroCount 0 = 0 :=
  DirichletCharacter.zeroCount_of_nonpos le_rfl

end DirichletNontrivialZerosTest
