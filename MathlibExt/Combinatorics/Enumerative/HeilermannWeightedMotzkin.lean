/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HankelTransform
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Abel

@[expose] public section

namespace MetaMathlibExt

section

private noncomputable def motzkinH {K : Type*} [Ring K] (F : ℕ → PowerSeries K) :
    ℕ → PowerSeries K
  | 0 => F 0
  | (j + 1) => F (j + 1) * motzkinH F j * PowerSeries.X

private noncomputable def motzkinM {K : Type*} [Ring K] (F : ℕ → PowerSeries K) :
    ℕ → ℕ → K :=
  fun n j => PowerSeries.coeff n (motzkinH F j)

private theorem F_expand {K : Type*} [Ring K]
    {a alpha beta : ℕ → K} {mu0 : K} {F : ℕ → PowerSeries K}
    (h : HasJacobiFraction a alpha beta mu0 F) (j : ℕ) :
    F j = 1 + PowerSeries.C (alpha j) * PowerSeries.X * F j +
      PowerSeries.C (beta (j + 1)) * PowerSeries.X ^ 2 * F (j + 1) * F j := by
  have hi := h.2 j
  have hdist : (1 - PowerSeries.C (alpha j) * PowerSeries.X -
        PowerSeries.C (beta (j + 1)) * PowerSeries.X ^ 2 * F (j + 1)) * F j
        = F j - PowerSeries.C (alpha j) * PowerSeries.X * F j -
      PowerSeries.C (beta (j + 1)) * PowerSeries.X ^ 2 * F (j + 1) * F j := by
    rw [sub_mul, sub_mul, one_mul, mul_assoc, mul_assoc]
  have hexpand : F j - PowerSeries.C (alpha j) * PowerSeries.X * F j -
      PowerSeries.C (beta (j + 1)) * PowerSeries.X ^ 2 * F (j + 1) * F j = 1 := by
    rw [← hdist, hi]
  calc F j = (F j - PowerSeries.C (alpha j) * PowerSeries.X * F j -
        PowerSeries.C (beta (j + 1)) * PowerSeries.X ^ 2 * F (j + 1) * F j) +
        PowerSeries.C (alpha j) * PowerSeries.X * F j +
        PowerSeries.C (beta (j + 1)) * PowerSeries.X ^ 2 * F (j + 1) * F j := by abel
    _ = 1 + PowerSeries.C (alpha j) * PowerSeries.X * F j +
        PowerSeries.C (beta (j + 1)) * PowerSeries.X ^ 2 * F (j + 1) * F j := by rw [hexpand]

private theorem central_move {K : Type*} [Ring K] (c : K) (G H : PowerSeries K) :
    PowerSeries.C c * PowerSeries.X ^ 2 * G * H = PowerSeries.C c * PowerSeries.X *
        (G * H * PowerSeries.X) := by
  have hXH : (PowerSeries.X : PowerSeries K) * (G * H) = (G * H) * PowerSeries.X :=
      PowerSeries.X_mul
  calc PowerSeries.C c * PowerSeries.X ^ 2 * G * H
      = PowerSeries.C c * PowerSeries.X *
          (PowerSeries.X * (G * H)) := by rw [pow_two]; simp only [mul_assoc]
    _ = PowerSeries.C c * PowerSeries.X * ((G * H) * PowerSeries.X) := by rw [hXH]
    _ = PowerSeries.C c * PowerSeries.X * (G * H * PowerSeries.X) := by rw [mul_assoc]

private theorem H0_eq {K : Type*} [Ring K]
    {a alpha beta : ℕ → K} {mu0 : K} {F : ℕ → PowerSeries K}
    (h : HasJacobiFraction a alpha beta mu0 F) :
    motzkinH F 0 = 1 + PowerSeries.C (alpha 0) * PowerSeries.X * motzkinH F 0 +
      PowerSeries.C (beta 1) * PowerSeries.X * motzkinH F 1 := by
  have hF := F_expand h 0
  have hmove := central_move (beta (0 + 1)) (F (0 + 1)) (motzkinH F 0)
  have hH1 : motzkinH F 1 = F (0 + 1) * motzkinH F 0 * PowerSeries.X := rfl
  calc motzkinH F 0 = F 0 := rfl
    _ = 1 + PowerSeries.C (alpha 0) * PowerSeries.X * F 0 +
      PowerSeries.C (beta (0 + 1)) * PowerSeries.X ^ 2 * F (0 + 1) * F 0 := hF
    _ = 1 + PowerSeries.C (alpha 0) * PowerSeries.X * motzkinH F 0 +
      PowerSeries.C (beta (0 + 1)) * PowerSeries.X ^ 2 * F (0 + 1) * motzkinH F 0 := rfl
    _ = 1 + PowerSeries.C (alpha 0) * PowerSeries.X * motzkinH F 0 +
      PowerSeries.C (beta 1) * PowerSeries.X * motzkinH F 1 := by rw [hmove, hH1]

private theorem Hsucc_eq {K : Type*} [Ring K]
    {a alpha beta : ℕ → K} {mu0 : K} {F : ℕ → PowerSeries K}
    (h : HasJacobiFraction a alpha beta mu0 F) (j : ℕ) :
    motzkinH F (j + 1) = motzkinH F j * PowerSeries.X +
      PowerSeries.C (alpha (j + 1)) * PowerSeries.X * motzkinH F (j + 1) +
      PowerSeries.C (beta (j + 2)) * PowerSeries.X * motzkinH F (j + 2) := by
  have hF := F_expand h (j + 1)
  have hH : motzkinH F (j + 1) = F (j + 1) * (motzkinH F j * PowerSeries.X) := by
    change F (j + 1) * motzkinH F j * PowerSeries.X = _
    rw [mul_assoc]
  have hH2 : motzkinH F (j + 2) = F (j + 2) * motzkinH F (j + 1) * PowerSeries.X := rfl
  have e1 : (PowerSeries.C (alpha (j + 1)) * PowerSeries.X * F (j + 1)) *
      (motzkinH F j * PowerSeries.X)
    = PowerSeries.C (alpha (j + 1)) * PowerSeries.X * motzkinH F (j + 1) := by
    rw [mul_assoc, mul_assoc, mul_assoc, ← hH]
  have e2 : (PowerSeries.C (beta (j + 1 + 1)) * PowerSeries.X ^ 2 * F (j + 1 + 1) * F (j + 1)) *
      (motzkinH F j * PowerSeries.X)
    = PowerSeries.C (beta (j + 2)) * PowerSeries.X * motzkinH F (j + 2) := by
    have hm := central_move (beta (j + 1 + 1)) (F (j + 1 + 1)) (motzkinH F (j + 1))
    have lhs : (PowerSeries.C (beta (j + 1 + 1)) * PowerSeries.X ^ 2 * F (j + 1 + 1) * F (j + 1)) *
        (motzkinH F j * PowerSeries.X)
      = PowerSeries.C (beta (j + 1 + 1)) * PowerSeries.X ^ 2 * F (j + 1 + 1) * motzkinH F
          (j + 1) := by
      rw [mul_assoc, mul_assoc, hH]
      simp only [mul_assoc]
    rw [lhs, hm]
    change PowerSeries.C (beta (j + 1 + 1)) * PowerSeries.X *
        (F (j + 1 + 1) * motzkinH F (j + 1) * PowerSeries.X)
      = PowerSeries.C (beta (j + 2)) * PowerSeries.X * motzkinH F (j + 2)
    rw [← hH2]
  calc motzkinH F (j + 1)
      = F (j + 1) * (motzkinH F j * PowerSeries.X) := hH
    _ = (1 + PowerSeries.C (alpha (j + 1)) * PowerSeries.X * F (j + 1) +
        PowerSeries.C (beta (j + 1 + 1)) * PowerSeries.X ^ 2 * F (j + 1 + 1) * F (j + 1)) *
        (motzkinH F j * PowerSeries.X) := by conv_lhs => rw [hF]
    _ = motzkinH F j * PowerSeries.X +
        PowerSeries.C (alpha (j + 1)) * PowerSeries.X * motzkinH F (j + 1) +
        PowerSeries.C (beta (j + 2)) * PowerSeries.X * motzkinH F (j + 2) := by
          rw [add_mul, add_mul, one_mul, e1, e2]

private theorem coeff_CX_succ {K : Type*} [Ring K] (c : K) (H : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.C c * PowerSeries.X * H) = c * PowerSeries.coeff n
        H := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]

private theorem coeffF_zero {K : Type*} [Ring K]
    {a alpha beta : ℕ → K} {mu0 : K} {F : ℕ → PowerSeries K}
    (h : HasJacobiFraction a alpha beta mu0 F) (i : ℕ) :
    PowerSeries.coeff 0 (F i) = 1 := by
  have hi := h.2 i
  have hcc : PowerSeries.constantCoeff ((1 - PowerSeries.C (alpha i) * PowerSeries.X -
        PowerSeries.C (beta (i + 1)) * PowerSeries.X ^ 2 * F (i + 1)) * F i)
      = PowerSeries.constantCoeff 1 := by rw [hi]
  simp at hcc
  simpa using hcc

private theorem head_coeff {K : Type*} [Ring K]
    {a alpha beta : ℕ → K} {mu0 : K} {F : ℕ → PowerSeries K}
    (h : HasJacobiFraction a alpha beta mu0 F) (n : ℕ) :
    a n = mu0 * PowerSeries.coeff n (F 0) := by
  have h1 := h.1
  have hc : PowerSeries.coeff n (PowerSeries.mk a) = PowerSeries.coeff n
      (PowerSeries.C mu0 * F 0) := by rw [h1]
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul] at hc
  exact hc

/-- **Weighted Motzkin recurrence for the coefficients of a Jacobi fraction.** Let $K$ be a ring,
let $a$, $\alpha$, $\beta$ be sequences in $K$ and let $\mu_0 \in K$. Suppose that $a$ has Jacobi
fraction data $(\alpha, \beta, \mu_0)$: there are power series $F_0, F_1, \dots$ over $K$ with
$\sum_{n \ge 0} a_n x^n = \mu_0 F_0$ and $(1 - \alpha_i x - \beta_{i+1} x^2 F_{i+1}) F_i = 1$ for
every $i \ge 0$. Then there is an array $(M_{n,j})_{n, j \ge 0}$ in $K$ with $M_{0,0} = 1$ and,
for all $n, j \ge 0$, $M_{0,j+1} = 0$, $M_{n+1,0} = \alpha_0 M_{n,0} + \beta_1 M_{n,1}$ and
$M_{n+1,j+1} = M_{n,j} + \alpha_{j+1} M_{n,j+1} + \beta_{j+2} M_{n,j+2}$, such that
$a_n = \mu_0 M_{n,0}$ for every $n \ge 0$.

Source: Paul Barry, *From Fibonacci to Robbins: Series Reversion and Hankel Transforms*,
Journal of Integer Sequences 24 (2021), Article 21.10.2, lines 110–117,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex.
Source SHA-256
`9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`.
Normalized line-span SHA-256
`a838e5996f223ba9e45347f17ad864912efc392f5c3d56ea749bcf62d3289825`.
Concept `jis_dep_heilermann_049f63eb`.
Grounded `jis_grounded_049f63eb8aadf7377777a597`.
Barry does not explicitly state this auxiliary tableau lemma; it is a
coefficientwise bridge for the displayed fraction.

Proves `Wanted` entry `exists_weightedMotzkin_coefficients_of_hasJacobiFraction`.
-/
theorem exists_weightedMotzkin_coefficients_of_hasJacobiFraction
    {K : Type*} [Ring K]
    {a alpha beta : ℕ → K} {mu0 : K} {F : ℕ → PowerSeries K}
    (h : HasJacobiFraction a alpha beta mu0 F) :
    ∃ M : ℕ → ℕ → K, M 0 0 = 1 ∧
      (∀ j, M 0 (j + 1) = 0) ∧
      (∀ n, M (n + 1) 0 = alpha 0 * M n 0 + beta 1 * M n 1) ∧
      (∀ n j, M (n + 1) (j + 1) =
        M n j + alpha (j + 1) * M n (j + 1) +
          beta (j + 2) * M n (j + 2)) ∧
      ∀ n, a n = mu0 * M n 0 := by
  refine ⟨motzkinM F, ?_, ?_, ?_, ?_, ?_⟩
  · change PowerSeries.coeff 0 (motzkinH F 0) = 1
    change PowerSeries.coeff 0 (F 0) = 1
    exact coeffF_zero h 0
  · intro j
    change PowerSeries.coeff 0 (motzkinH F (j + 1)) = 0
    change PowerSeries.coeff 0 (F (j + 1) * motzkinH F j * PowerSeries.X) = 0
    exact PowerSeries.coeff_zero_mul_X (F (j + 1) * motzkinH F j)
  · intro n
    change PowerSeries.coeff (n + 1) (motzkinH F 0)
      = alpha 0 * PowerSeries.coeff n (motzkinH F 0) + beta 1 * PowerSeries.coeff n (motzkinH F 1)
    have hH := H0_eq h
    conv_lhs => rw [hH]
    simp only [map_add, coeff_CX_succ]
    simp
  · intro n j
    change PowerSeries.coeff (n + 1) (motzkinH F (j + 1))
      = PowerSeries.coeff n (motzkinH F j) + alpha (j + 1) * PowerSeries.coeff n
          (motzkinH F (j + 1)) +
        beta (j + 2) * PowerSeries.coeff n (motzkinH F (j + 2))
    have hH := Hsucc_eq h j
    conv_lhs => rw [hH]
    simp only [map_add, PowerSeries.coeff_succ_mul_X, coeff_CX_succ]
  · intro n
    change a n = mu0 * PowerSeries.coeff n (motzkinH F 0)
    change a n = mu0 * PowerSeries.coeff n (F 0)
    exact head_coeff h n

end

end MetaMathlibExt
