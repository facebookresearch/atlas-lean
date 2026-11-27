/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GcdLucasTheoremGcdSqrtExpansionCoeffs
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Tests for gcds of square-root expansion coefficients

Concrete coefficient families for `(1 + √v) ^ n` exercise all four congruence cases.
-/

namespace MathlibExtTest.NumberTheory.GcdLucasTheoremGcdSqrtExpansionCoeffs

private def coords (v n : ℕ) : Zsqrtd v := (⟨1, 1⟩ : Zsqrtd v) ^ n

private theorem expansion (v n : ℕ) :
    (((1 : ℕ) : ℝ) + Real.sqrt v) ^ n = (coords v n).re + (coords v n).im * Real.sqrt v := by
  let root : {r : ℝ // r * r = ((v : ℤ) : ℝ)} :=
    ⟨Real.sqrt v, by simp [← pow_two, Real.sq_sqrt (Nat.cast_nonneg v)]⟩
  simpa [coords, Zsqrtd.lift_apply_apply, root] using
    ((Zsqrtd.lift root).map_pow (⟨1, 1⟩ : Zsqrtd v) n).symm

example (n : ℕ) (hn : 1 ≤ n) : Int.gcd (coords 2 n).re (coords 2 n).im = 1 := by
  have h := MetaMathlibExt.gcd_sqrt_expansion_coeffs (u := 1) (v := 2)
    (by decide) (by decide) (by decide) Nat.prime_two.irrational_sqrt
    (fun m ↦ (coords 2 m).re) (fun m ↦ (coords 2 m).im) (fun m _ ↦ expansion 2 m)
  exact h.1 (by norm_num [Int.odd_iff]) n hn

example : Int.gcd (coords 3 3).re (coords 3 3).im = 2 ∧
    Int.gcd (coords 3 4).re (coords 3 4).im = 4 := by
  have h := MetaMathlibExt.gcd_sqrt_expansion_coeffs (u := 1) (v := 3)
    (by decide) (by decide) (by decide) (Nat.Prime.irrational_sqrt (by decide))
    (fun m ↦ (coords 3 m).re) (fun m ↦ (coords 3 m).im) (fun m _ ↦ expansion 3 m)
  simpa using h.2.1 (by norm_num) 2 (by decide)

example : Int.gcd (coords 5 4).re (coords 5 4).im = 8 ∧
    Int.gcd (coords 5 5).re (coords 5 5).im = 16 ∧
    Int.gcd (coords 5 6).re (coords 5 6).im = 64 := by
  have h := MetaMathlibExt.gcd_sqrt_expansion_coeffs (u := 1) (v := 5)
    (by decide) (by decide) (by decide) (Nat.Prime.irrational_sqrt (by decide))
    (fun m ↦ (coords 5 m).re) (fun m ↦ (coords 5 m).im) (fun m _ ↦ expansion 5 m)
  simpa using h.2.2.1 (by norm_num) 2 (by decide)

example (n : ℕ) (hn : 1 ≤ n) :
    Int.gcd (coords 17 n).re (coords 17 n).im = 2 ^ (n - 1) := by
  have h := MetaMathlibExt.gcd_sqrt_expansion_coeffs (u := 1) (v := 17)
    (by decide) (by decide) (by decide) (Nat.Prime.irrational_sqrt (by decide))
    (fun m ↦ (coords 17 m).re) (fun m ↦ (coords 17 m).im) (fun m _ ↦ expansion 17 m)
  exact h.2.2.2 (by norm_num) n hn

example : Int.gcd (coords 2 7).re (coords 2 7).im = 1 := by
  let a : ℕ → ℤ := fun m ↦ if m = 0 then 37 else (coords 2 m).re
  let b : ℕ → ℤ := fun m ↦ if m = 0 then -23 else (coords 2 m).im
  have hab (m : ℕ) (hm : 1 ≤ m) :
      (((1 : ℕ) : ℝ) + Real.sqrt 2) ^ m = a m + b m * Real.sqrt 2 := by
    simpa [a, b, show m ≠ 0 by omega] using expansion 2 m
  have h := MetaMathlibExt.gcd_sqrt_expansion_coeffs (u := 1) (v := 2)
    (by decide) (by decide) (by decide) Nat.prime_two.irrational_sqrt a b hab
  simpa [a, b] using h.1 (by norm_num [Int.odd_iff]) 7 (by decide)

end MathlibExtTest.NumberTheory.GcdLucasTheoremGcdSqrtExpansionCoeffs
