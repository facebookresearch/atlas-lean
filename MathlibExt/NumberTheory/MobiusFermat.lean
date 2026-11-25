/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The Möbius–Fermat and von Mangoldt–Fermat functions

We define the Fermat unit function and prove that its Dirichlet inverse and the corresponding
von Mangoldt–Fermat function vanish outside the Fermat semigroup. Their values at one are
respectively one and zero.
-/

open ArithmeticFunction

@[expose] public section

namespace MetaMathlibExt

/-- **Fermat unit function.** The Fermat unit function $u_M$ is the integer-valued arithmetic
function with $u_M(l) = 1$ when $l = 2^n - 1$ for some integer $n \ge 1$, and $u_M(l) = 0$
otherwise (in particular $u_M(0) = 0$). Equivalently, $u_M(l) = 1$ exactly when $l \ge 1$ and
$l + 1$ is a power of $2$.

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, equation (7). -/
def fermatUnitFunction : ArithmeticFunction ℤ :=
  ⟨fun l => if l ≠ 0 ∧ 2 ^ Nat.log 2 (l + 1) = l + 1 then 1 else 0, by simp⟩

/-- **The Fermat unit function at $2^n - 1$.** For every integer $n \ge 1$, the Fermat unit
function $u_M$ satisfies $u_M(2^n - 1) = 1$.

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, equation (7). -/
theorem fermatUnitFunction_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) :
    fermatUnitFunction (2 ^ n - 1) = 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hs : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel h1
  change (if 2 ^ n - 1 ≠ 0 ∧ 2 ^ Nat.log 2 (2 ^ n - 1 + 1) = 2 ^ n - 1 + 1
    then (1 : ℤ) else 0) = 1
  rw [hs, Nat.log_pow (by norm_num)]
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, rfl⟩)

/-- **Small values of the Fermat unit function.** The Fermat unit function $u_M$ satisfies
$u_M(1) = u_M(3) = u_M(7) = u_M(63) = 1$ and $u_M(2) = u_M(9) = 0$.

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, equation (7). -/
theorem fermatUnitFunction_small_values :
    fermatUnitFunction 1 = 1 ∧ fermatUnitFunction 3 = 1 ∧ fermatUnitFunction 7 = 1 ∧
      fermatUnitFunction 63 = 1 ∧ fermatUnitFunction 2 = 0 ∧ fermatUnitFunction 9 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The Möbius–Fermat and von Mangoldt–Fermat functions at $1$ and off the Fermat
semigroup.** Let $u_M$ be the Fermat unit function
and let $\mu_M$ be an integer-valued arithmetic function with $\mu_M * u_M = \varepsilon$, where
$*$ is Dirichlet convolution and $\varepsilon$ is its identity, with $\varepsilon(1) = 1$ and
$\varepsilon(l) = 0$ for $l \ne 1$; thus $\mu_M$ is the Dirichlet inverse of $u_M$, the
Möbius–Fermat function.
Let $\Lambda_M = \mu_M * u_M'$, computed with real values, where
$u_M'(l) = u_M(l) \log l$.
Then $\mu_M(1) = 1$ and $\Lambda_M(1) = 0$, and $\mu_M(l) = \Lambda_M(l) = 0$ for every natural
number $l$ outside the Fermat semigroup, the multiplicative submonoid of $\mathbb{N}$ generated
by the numbers $2^n - 1$ with $n \ge 2$.

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, Proposition 2. -/
theorem mobiusFermat_one_and_vanishing (μ : ArithmeticFunction ℤ)
    (hμ : μ * fermatUnitFunction = 1) :
    μ 1 = 1 ∧
      ((μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log) 1 = 0 ∧
      ∀ l : ℕ, l ∉ Submonoid.closure {x : ℕ | ∃ n, 2 ≤ n ∧ x = 2 ^ n - 1} →
        μ l = 0 ∧
          ((μ : ArithmeticFunction ℝ) * (fermatUnitFunction : ArithmeticFunction ℝ).pmul log) l
            = 0 := by
  let S := Submonoid.closure {x : ℕ | ∃ n, 2 ≤ n ∧ x = 2 ^ n - 1}
  have hu (d : ℕ) (hd : d ∉ S) : fermatUnitFunction d = 0 := by
    apply ite_eq_right
    rintro ⟨hd0, hpow⟩
    apply hd
    generalize Nat.log 2 (d + 1) = n at hpow
    match n with
    | 0 => simp_all
    | 1 =>
      have : d = 1 := by simpa using hpow.symm
      exact this ▸ S.one_mem
    | n + 2 =>
      exact Submonoid.subset_closure ⟨n + 2, by omega, by omega⟩
  have hu1 := fermatUnitFunction_small_values.1
  have hμ0 (l : ℕ) (hl : l ∉ S) : μ l = 0 := by
    induction l using Nat.strong_induction_on with
    | ind l ih =>
      obtain rfl | hl0 := eq_or_ne l 0
      · exact ArithmeticFunction.map_zero
      have hl1 : l ≠ 1 := fun h => hl (h ▸ S.one_mem)
      have hsum : ∑ d ∈ l.properDivisors, μ d * fermatUnitFunction (l / d) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp hd
        by_cases hmem : d ∈ S
        · have hout : l / d ∉ S := fun h => hl (Nat.mul_div_cancel' hdvd ▸ S.mul_mem hmem h)
          rw [hu _ hout, mul_zero]
        · rw [ih d hlt hmem, zero_mul]
      have h := DFunLike.congr_fun hμ l
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
        (fun a b => μ a * fermatUnitFunction b), ← Nat.cons_self_properDivisors hl0,
        Finset.sum_cons] at h
      simpa [Nat.div_self (Nat.pos_of_ne_zero hl0), hu1, hsum, hl1] using h
  refine ⟨?_, ?_, fun l hl => ⟨hμ0 l hl, ?_⟩⟩
  · simpa [mul_apply_one, hu1] using DFunLike.congr_fun hμ 1
  · simp [pmul_apply]
  · rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hab).1
    by_cases ha : a ∈ S
    · have hb : b ∉ S := fun h => hl (hprod ▸ S.mul_mem ha h)
      simp [pmul_apply, hu b hb]
    · simp [hμ0 a ha]

end MetaMathlibExt
