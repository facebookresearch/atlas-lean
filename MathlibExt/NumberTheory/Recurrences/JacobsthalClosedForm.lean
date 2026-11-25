/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Init
import MathlibExt.NumberTheory.BinetClosedForm

@[expose] public section

namespace MetaMathlibExt

/--
**Jacobsthal closed form.** Let $J : \mathbb{N} \to \mathbb{N}$ satisfy $J(0) = J(1) = 1$ and
$J(n+2) = J(n+1) + 2J(n)$ for every $n \in \mathbb{N}$. Then for every $m \in \mathbb{N}$,
$$J(m) = \frac{2^{m+1} + (-1)^m}{3}.$$

The source cites A. Tucker, "Applied Combinatorics," 3rd edition, for this formula. The proof
applies Binet's formula for second-order linear recurrences; the characteristic polynomial
$x^2 - x - 2$ has roots $2$ and $-1$.

Source: Darrin D. Frey and James A. Sellers, "Jacobsthal Numbers and
Alternating Sign Matrices," Journal of Integer Sequences 3 (2000),
Article 00.2.3, recurrence (label jacrecur) with initial values,
lines 260–266, and Theorem, equation (Eq4a), lines 329–335,
https://cs.uwaterloo.ca/journals/JIS/VOL3/SELLERS/sellers.tex
-/
theorem jacobsthal_closedForm
    (J : ℕ → ℕ)
    (h_zero : J 0 = 1)
    (h_one : J 1 = 1)
    (h_rec : ∀ n : ℕ, J (n + 2) = J (n + 1) + 2 * J n)
    (m : ℕ) :
    (J m : ℚ) = ((2 : ℚ) ^ (m + 1) + (-1 : ℚ) ^ m) / 3 := by
  have h := binet_closed_form_second_order (fun n => (J n : ℚ)) 1 (-2) 2 (-1)
    (by norm_num) (by norm_num) (by norm_num) (fun n => by simp [h_rec n]) m
  simp only [h_zero, h_one] at h
  rw [h, pow_succ]
  ring

end MetaMathlibExt
