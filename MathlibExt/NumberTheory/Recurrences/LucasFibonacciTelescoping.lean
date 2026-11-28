/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Fib.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two telescoping relations between Lucas and Fibonacci numbers

The Lucas number at an odd index, divided by the corresponding Fibonacci square plus one,
is a difference of neighboring even-index ratios. Clearing factors gives a reciprocal form.
-/

namespace MetaMathlibExt

/-- **Two telescoping relations between Lucas and Fibonacci numbers.** Let $F_m$ be the Fibonacci
numbers extended to all integers $m$ ($F_0 = 0$, $F_1 = 1$, $F_{m+2} = F_{m+1} + F_m$) and
$L_m = F_{m-1} + F_{m+1}$ the Lucas numbers. Then for every integer $k$,
$$\frac{L_{2k+1}}{F_{2k+1}^2 + 1} = \frac{L_{2k}}{F_{2k}^2 + 1} - \frac{L_{2k+2}}{F_{2k+2}^2 + 1}$$
and
$$\frac{L_{2k+1}}{L_{2k} L_{2k+2}} \cdot \frac{(F_{2k}^2 + 1)(F_{2k+2}^2 + 1)}{F_{2k+1}^2 + 1}
= \frac{F_{2k+2}^2 + 1}{L_{2k+2}} - \frac{F_{2k}^2 + 1}{L_{2k}}.$$

Source: Kunle Adegoke, *Fibonacci Identities via Fibonacci Functions*, Journal of
Integer Sequences 27 (2024), Article 24.6.2, Proposition 3
(`jis-2024-24.6.2-prop-3`). -/
public theorem lucas_div_fib_sq_add_one_telescoping
    (L : ℤ → ℝ) (hL : ∀ m : ℤ, L m = Int.fib (m - 1) + Int.fib (m + 1)) (k : ℤ) :
    L (2 * k + 1) / ((Int.fib (2 * k + 1) : ℝ) ^ 2 + 1) =
        L (2 * k) / ((Int.fib (2 * k) : ℝ) ^ 2 + 1) -
          L (2 * k + 2) / ((Int.fib (2 * k + 2) : ℝ) ^ 2 + 1) ∧
      L (2 * k + 1) / (L (2 * k) * L (2 * k + 2)) *
          (((Int.fib (2 * k) : ℝ) ^ 2 + 1) * ((Int.fib (2 * k + 2) : ℝ) ^ 2 + 1) /
            ((Int.fib (2 * k + 1) : ℝ) ^ 2 + 1)) =
        ((Int.fib (2 * k + 2) : ℝ) ^ 2 + 1) / L (2 * k + 2) -
          ((Int.fib (2 * k) : ℝ) ^ 2 + 1) / L (2 * k) := by
  let F (i : ℤ) : ℝ := Int.fib i
  set n := 2 * k with hn
  have he : Even n := ⟨k, by omega⟩
  have ho : Odd (n - 1) := ⟨k - 1, by omega⟩
  -- At even indices, Cassini factors the denominator into its two odd neighbors.
  have even_sq (i : ℤ) (hi : Even i) : F i ^ 2 + 1 = F (i - 1) * F (i + 1) := by
    have h := Int.fib_succ_mul_fib_pred_sub_fib_sq i
    rw [hi.natAbs.neg_one_pow] at h
    dsimp only [F]
    norm_cast
    linear_combination -h
  have next_sq : F (n + 2) ^ 2 + 1 = F (n + 1) * F (n + 3) := by
    simpa only [show n + 2 - 1 = n + 1 by omega, show n + 2 + 1 = n + 3 by omega]
      using even_sq (n + 2) (he.add even_two)
  -- Catalan's identity at distance two gives the remaining denominator.
  have odd_sq : F (n + 1) ^ 2 + 1 = F (n - 1) * F (n + 3) := by
    have h := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul (n - 1) 2
    rw [ho.natAbs.neg_one_pow, Int.fib_two] at h
    dsimp only [F]
    norm_cast
    linear_combination (norm := ring1_nf) h
  have lucas_odd : L (n + 1) = F (n + 3) - F (n - 1) := by
    rw [hL]
    dsimp only [F]
    norm_cast
    linear_combination (norm := ring1_nf) -Int.fib_add_two (n - 1) - Int.fib_add_two (n + 1)
  have lucas_next : L (n + 2) = F (n + 1) + F (n + 3) := by
    rw [hL, show n + 2 - 1 = n + 1 by omega, show n + 2 + 1 = n + 3 by omega]
  have odd_pos (j : ℤ) : 0 < F (2 * j + 1) := by
    dsimp only [F]
    exact_mod_cast Int.fib_two_mul_add_one_pos (n := j)
  have ha : 0 < F (n - 1) := by
    simpa only [show 2 * (k - 1) + 1 = n - 1 by omega] using odd_pos (k - 1)
  have hb : 0 < F (n + 1) := odd_pos k
  have hc : 0 < F (n + 3) := by
    simpa only [show 2 * (k + 1) + 1 = n + 3 by omega] using odd_pos (k + 1)
  have lucas_even : L n = F (n - 1) + F (n + 1) := hL n
  rw [odd_sq, even_sq n he, next_sq, lucas_odd, lucas_even, lucas_next]
  constructor <;> field_simp <;> ring

end MetaMathlibExt
