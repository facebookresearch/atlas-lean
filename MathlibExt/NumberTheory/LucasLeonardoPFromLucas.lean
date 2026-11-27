/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LeonardoPTilings
import Mathlib.Tactic.Ring

/-!
# Lucas–Leonardo `p`-numbers in terms of Lucas `p`-numbers

The affine transform of the Lucas `p`-numbers has the initial values and recurrence of the
Lucas–Leonardo `p`-numbers. This gives an inductive proof of the identity.

## References

- Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
  Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, pp. 1–17, Proposition 13
  and Section 1, equations (5)–(6).
- Jingyang Zhong, Jialing Yao, and Chan-Liang Chung, *A Note on Incomplete Fibonacci–Lucas
  Relations*, Symmetry 15 (12) (2023), Article 2113, Section 4, Proposition 8, equation (16).
  This is the original recurrence proof.
- Alexey Stakhov and Boris Rozin, *Theory of Binet formulas for Fibonacci and Lucas p-numbers*,
  Chaos, Solitons & Fractals 27 (5) (2006), pp. 1162–1177 (Lucas `p`-numbers).
-/

namespace MetaMathlibExt

/-- **Lucas-Leonardo $p$-numbers from Lucas $p$-numbers.** For every $p \ge 1$ and every
natural number $n$, the Lucas-Leonardo $p$-number $R_{p,n}$ and the Lucas $p$-number $L_{p,n}$
satisfy $R_{p,n} = (p + 1) L_{p,n} - p$.

Source: Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and
Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 13. -/
public theorem lucasLeonardoP_eq_lucasP (p n : ℕ) (hp : 1 ≤ p) :
    lucasLeonardoP p n = ((p : ℤ) + 1) * lucasP p n - p := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hzero : n = 0
    · subst n
      rw [lucasLeonardoP_zero, lucasP_zero, Nat.cast_add, Nat.cast_one]
      ring
    by_cases hn : n ≤ p
    · have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hzero
      rw [lucasLeonardoP_of_le p hn₁ hn, lucasP_of_le p hn₁ hn, Nat.cast_one]
      ring
    · have hpn : p < n := Nat.lt_of_not_ge hn
      have hp₀ : 0 < p := hp
      rw [lucasLeonardoP_of_lt p hpn, lucasP_of_lt p hpn,
        ih (n - 1) (Nat.sub_lt (hp₀.trans hpn) Nat.one_pos),
        ih (n - p - 1) (by omega), Nat.cast_add]
      ring

end MetaMathlibExt
