/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Parity interpolation

The theorem `parity_interpolation` recovers a real sequence from its even and odd subsequences.
-/

namespace MetaMathlibExt.BridgeTorchGeneralizations

/-- **Parity interpolation.** Let $f, g, a : \mathbb{N} \to \mathbb{R}$ be sequences with
$a_{2m} = f(m)$ and $a_{2m+1} = g(m)$ for every $m \in \mathbb{N}$. Then for every
$n \in \mathbb{N}$,

$$a_n = \frac{1 + (-1)^n}{2} f(\lfloor n/2 \rfloor) + \frac{1 - (-1)^n}{2} g(\lfloor n/2 \rfloor).$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 2 (`jis-2026-26.5.6-lem-2`). -/
public theorem parity_interpolation (f g a : ℕ → ℝ)
    (heven : ∀ m, a (2 * m) = f m) (hodd : ∀ m, a (2 * m + 1) = g m) (n : ℕ) :
    a n = (1 + (-1 : ℝ) ^ n) / 2 * f (n / 2) + (1 - (-1 : ℝ) ^ n) / 2 * g (n / 2) := by
  rcases Nat.even_or_odd n with h | h
  · simpa [h.neg_one_pow, one_add_one_eq_two, Nat.two_mul_div_two_of_even h] using heven (n / 2)
  · simpa [h.neg_one_pow, one_add_one_eq_two, Nat.two_mul_div_two_add_one_of_odd h] using
      hodd (n / 2)

end MetaMathlibExt.BridgeTorchGeneralizations
