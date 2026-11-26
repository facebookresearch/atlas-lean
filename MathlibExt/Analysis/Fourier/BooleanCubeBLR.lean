/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeConvolution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Blum–Luby–Rubinfeld linearity test

The BLR test queries a function `F : 𝔽₂ⁿ → 𝔽₂` at uniform independent `x, y` and at `x + y`, and
accepts when `F(x) + F(y) = F(x + y)`. Encoding outputs by `±1` and `𝔽₂ⁿ` as the multiplicative
cube `{-1, 1}ⁿ`, a function becomes `f : BoolCube n → ℝ` with values `±1`, the linear functions
become the characters `χ_S`, and the test accepts when `f(x) f(y) = f(x y)`. This is the encoding
in which O'Donnell proves the test (proof of Theorem 1.30).

## Main definitions

* `BooleanCube.blrAcceptProb f`: the probability `Pr_{x,y}[f(x) f(y) = f(x y)]`.
* `BooleanCube.boolDist f g`: the relative Hamming distance `Pr_x[f(x) ≠ g(x)]`.

## Main statements

* `BooleanCube.blrAcceptProb_eq`: for `±1`-valued `f`,
  `Pr[accept] = 1/2 + 1/2 ∑_S f̂(S)³` (equation (1.10)).
* `BooleanCube.boolDist_cubeChi_eq`: `dist(f, χ_S) = 1/2 - 1/2 f̂(S)` (Proposition 1.9).
* `BooleanCube.blr_test`: if the test accepts with probability at least `1 - ε`, then `f` is
  `ε`-close to some character `χ_S` (Theorem 1.30).

## Relation to `MathlibExt.Complexity.LinearityTest`

That module proves the same theorem for `f : (Fin n → ZMod 2) → ZMod 2` as `blr_soundness`, with
completeness (`blr_complete`), from private character sums. `blr_test` states it in the `±1`
encoding on `BoolCube n`, derived from the Boolean-cube Fourier API (`boolFourierCoeff`,
`boolConv`).

## References

* M. Blum, M. Luby and R. Rubinfeld, "Self-testing/correcting with applications to numerical
  problems", J. Comput. Syst. Sci. 47 (1993), 549-595.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Section 1.6 (Theorem 1.30).
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators

variable {n : ℕ}

/-- **Acceptance probability of the BLR test.** For `f : BoolCube n → ℝ`, the probability over
uniform independent `x, y` that `f(x) f(y) = f(x y)`, where `x y` is the coordinatewise product
`cubeMul` (R. O'Donnell, *Analysis of Boolean Functions*, 2014, Section 1.6). -/
noncomputable def blrAcceptProb (f : BoolCube n → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, if f x * f y = f (cubeMul x y) then (1 : ℝ) else 0

/-- **Relative Hamming distance on the Boolean cube.** For `f, g : BoolCube n → ℝ`,
`dist(f, g) = Pr_x[f(x) ≠ g(x)]` for uniform `x` (R. O'Donnell, *Analysis of Boolean
Functions*, 2014, Definition 1.10). -/
noncomputable def boolDist (f g : BoolCube n → ℝ) : ℝ :=
  𝔼 x, if f x ≠ g x then (1 : ℝ) else 0

/-- **Characters are `±1`-valued.** Every character `χ_S` takes only the values `1` and `-1`. -/
theorem cubeChi_eq_one_or_neg_one (S : Finset (Fin n)) (x : BoolCube n) :
    cubeChi n S x = 1 ∨ cubeChi n S x = -1 :=
  mul_self_eq_one_iff.mp (cubeChi_mul_self n S x)

/-- **Acceptance probability of the BLR test in Fourier form.** For `f : BoolCube n → ℝ` with
values `±1`, `Pr_{x,y}[f(x) f(y) = f(x y)] = 1/2 + 1/2 ∑_S f̂(S)³` (R. O'Donnell, *Analysis of
Boolean Functions*, 2014, equation (1.10) in the proof of Theorem 1.30). -/
theorem blrAcceptProb_eq {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1) :
    blrAcceptProb f = 1 / 2 + 1 / 2 * ∑ S, boolFourierCoeff n f S ^ 3 := by
  have hind (x y : BoolCube n) :
      (if f x * f y = f (cubeMul x y) then (1 : ℝ) else 0) =
        1 / 2 + 1 / 2 * (f x * (f y * f (cubeMul x y))) := by
    rcases hf x with h1 | h1 <;> rcases hf y with h2 | h2 <;>
      rcases hf (cubeMul x y) with h3 | h3 <;> norm_num [h1, h2, h3]
  have hconv : 𝔼 x, f x * boolConv f f x = ∑ S, boolFourierCoeff n f S ^ 3 := by
    rw [expect_mul_eq_sum_boolFourierCoeff_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [boolFourierCoeff_boolConv]
    ring
  simp_rw [blrAcceptProb, hind, Finset.expect_add_distrib, Fintype.expect_const,
    ← Finset.mul_expect]
  rw [← hconv]
  simp [boolConv]

/-- **Distance to a character.** For `f : BoolCube n → ℝ` with values `±1` and every `S`,
`dist(f, χ_S) = 1/2 - 1/2 f̂(S)` (R. O'Donnell, *Analysis of Boolean Functions*, 2014,
Proposition 1.9 with `g = χ_S`, and Proposition 1.8). -/
theorem boolDist_cubeChi_eq {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (S : Finset (Fin n)) :
    boolDist f (cubeChi n S) = 1 / 2 - 1 / 2 * boolFourierCoeff n f S := by
  have hind (x : BoolCube n) :
      (if f x ≠ cubeChi n S x then (1 : ℝ) else 0) = 1 / 2 - 1 / 2 * (f x * cubeChi n S x) := by
    rcases hf x with h1 | h1 <;> rcases cubeChi_eq_one_or_neg_one S x with h2 | h2 <;>
      norm_num [h1, h2]
  simp_rw [boolDist, hind, Finset.expect_sub_distrib, Fintype.expect_const,
    ← Finset.mul_expect, ← boolFourierCoeff_eq_expect]

/-- **Blum–Luby–Rubinfeld linearity test.** Let `f : BoolCube n → ℝ` take values `±1` (a
function `𝔽₂ⁿ → 𝔽₂` in the `±1` encoding). If the BLR test accepts `f` with probability at least
`1 - ε`, then `f` is `ε`-close to a linear function: `dist(f, χ_S) ≤ ε` for some character `χ_S`
(M. Blum, M. Luby and R. Rubinfeld, J. Comput. Syst. Sci. 47 (1993); R. O'Donnell, *Analysis of
Boolean Functions*, 2014, Theorem 1.30, stated there for acceptance probability exactly
`1 - ε`). -/
theorem blr_test {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1) {ε : ℝ}
    (hacc : 1 - ε ≤ blrAcceptProb f) :
    ∃ S : Finset (Fin n), boolDist f (cubeChi n S) ≤ ε := by
  obtain ⟨S, -, hS⟩ := Finset.exists_max_image Finset.univ (boolFourierCoeff n f)
    Finset.univ_nonempty
  refine ⟨S, ?_⟩
  have hsq : ∑ T, boolFourierCoeff n f T ^ 2 = 1 := by
    rw [← expect_sq_eq_sum_boolFourierCoeff_sq]
    have h1 : ∀ x, f x ^ 2 = 1 := fun x => by rcases hf x with h | h <;> simp [h]
    simp [h1]
  have hcube : ∑ T, boolFourierCoeff n f T ^ 3 ≤ boolFourierCoeff n f S := by
    calc ∑ T, boolFourierCoeff n f T ^ 3
        = ∑ T, boolFourierCoeff n f T * boolFourierCoeff n f T ^ 2 :=
          Finset.sum_congr rfl fun T _ => by ring
      _ ≤ ∑ T, boolFourierCoeff n f S * boolFourierCoeff n f T ^ 2 :=
          Finset.sum_le_sum fun T hT =>
            mul_le_mul_of_nonneg_right (hS T hT) (sq_nonneg _)
      _ = boolFourierCoeff n f S := by rw [← Finset.mul_sum, hsq, mul_one]
  rw [blrAcceptProb_eq hf] at hacc
  rw [boolDist_cubeChi_eq hf]
  linarith

end BooleanCube
