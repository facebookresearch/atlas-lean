/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# Triangular numbers near squares along `⌊n√2⌋`

For a natural number `n` let `a = ⌊n√2⌋` (OEIS A001951) and `T_a = a(a+1)/2`. The distance from
`T_a` to the nearest perfect square is at most `⌊a/2⌋`
(`MetaMathlibExt.exists_sq_near_triangular_beatty_sqrt_two`): the square `n²` already lies that
close to `T_a`.

## Proof outline

Since `n√2 = √(2n²)`, the floor `a` is the integer square root of `2n²`, so
`a² ≤ 2n² < (a + 1)²`, that is `a² ≤ 2n² ≤ a² + 2a`. Hence `2(T_a - n²) = a² + a - 2n²` lies
between `-a` and `a`, and as `T_a - n²` is an integer, `|T_a - n²| ≤ ⌊a/2⌋`.

## Implementation notes

`exists_sq_near_triangular_beatty_sqrt_two` keeps the full name, the statement and the docstring
it had as a wanted theorem in `WantedExt.Combinatorics.Enumerative.TenOeisConjecturesWanted`.

## References

The theorem's docstring cites its source, Sela Fried's *Proofs of Ten Conjectures From the OEIS*
(Journal of Integer Sequences, 2026). The proof here is self-contained.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Triangular numbers near squares along $\lfloor n\sqrt{2} \rfloor$.** For a natural number
$n$ let $a = \lfloor n\sqrt{2} \rfloor$ (A001951) and $T_a = a(a+1)/2$. Then some integer $k$
satisfies $|T_a - k^2| \le \lfloor a/2 \rfloor$; that is, the distance from $T_a$ to the nearest
perfect square is at most $\lfloor a/2 \rfloor$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 3 (`jis-2026-26.1.8-thm-3`). -/
theorem exists_sq_near_triangular_beatty_sqrt_two (n : ℕ) :
    let a : ℕ := ⌊(n : ℝ) * Real.sqrt 2⌋₊
    ∃ k : ℤ, |((a * (a + 1) / 2 : ℕ) : ℤ) - k ^ 2| ≤ (a / 2 : ℕ) := by
  intro a
  -- `a = ⌊√(2n²)⌋` is the integer square root of `2n²`.
  have ha : a = Nat.sqrt (2 * n ^ 2) := by
    rw [← Real.nat_floor_real_sqrt_eq_nat_sqrt, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n), mul_comm]
  have hlo : a ^ 2 ≤ 2 * n ^ 2 := ha ▸ Nat.sqrt_le' _
  have hhi : 2 * n ^ 2 < (a + 1) ^ 2 := ha ▸ Nat.lt_succ_sqrt' _
  clear_value a
  -- So `2 (T_a - n²) = a² + a - 2n²` lies between `-a` and `a`; take `k = n`. The evenness of
  -- `a (a + 1)` makes the division exact, which the lower bound needs.
  have hdvd : 2 ∣ a * (a + 1) := (Nat.even_mul_succ_self a).two_dvd
  have hT : a * (a + 1) = a ^ 2 + a := by ring
  have hsucc : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
  have hcast : ((n ^ 2 : ℕ) : ℤ) = (n : ℤ) ^ 2 := Nat.cast_pow n 2
  refine ⟨n, ?_⟩
  rw [abs_le]
  omega

end

end MetaMathlibExt
