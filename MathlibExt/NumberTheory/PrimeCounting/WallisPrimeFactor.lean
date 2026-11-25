/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Wallis-type prime factors

The character modulo four is either `1` or `-1` at an odd prime. Its square is therefore
`1`, so the two conjugate linear factors of the prime multiply to its square minus one.
-/

namespace MetaMathlibExt

/-- **Factor identity for Wallis-type prime products.** For every odd prime $p$,
$$\frac{p - \chi_4(p)}{p + \chi_4(p)} = \frac{(1 - \chi_4(p)/p)^2}{1 - 1/p^2},$$
where $\chi_4$ is the nontrivial Dirichlet character modulo $4$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Lemma 1 (`integers-2026-A90-lem-1`). -/
public theorem wallis_prime_factor_eq
    (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)) =
      (1 - (ZMod.χ₄ (p : ZMod 4) : ℝ) / p) ^ 2 / (1 - 1 / (p : ℝ) ^ 2) := by
  let x : ℝ := p
  let c : ℝ := ZMod.χ₄ (p : ZMod 4)
  change (x - c) / (x + c) = (1 - c / x) ^ 2 / (1 - 1 / x ^ 2)
  have hx : 2 ≤ x := by
    change (2 : ℝ) ≤ (p : ℝ)
    exact_mod_cast hp.two_le
  have hx0 : x ≠ 0 := by linarith
  have hs : c = 1 ∨ c = -1 := by
    have hm : p % 2 ≠ 0 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    dsimp [c]
    rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right hm]
    split <;> simp
  have hsq : c ^ 2 = 1 := by rcases hs with hc | hc <;> norm_num [hc]
  have hplus : x + c ≠ 0 := by rcases hs with hc | hc <;> rw [hc] <;> linarith
  have hminus : x - c ≠ 0 := by rcases hs with hc | hc <;> rw [hc] <;> linarith
  have hfactor : x ^ 2 - 1 = (x - c) * (x + c) := by
    linear_combination hsq
  rw [show 1 - c / x = (x - c) / x by field_simp [hx0],
    show 1 - 1 / x ^ 2 = (x ^ 2 - 1) / x ^ 2 by field_simp [hx0], hfactor]
  field_simp [hx0, hplus, hminus]

end MetaMathlibExt
