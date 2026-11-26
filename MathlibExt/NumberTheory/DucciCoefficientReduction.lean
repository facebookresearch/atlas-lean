/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DucciSequence
import Mathlib.Algebra.Polynomial.Expand

/-!
# Reduction of Ducci coefficients

In characteristic `p`, the polynomial `(X + 1) ^ (c * p ^ k)` is obtained from
`(X + 1) ^ c` by substituting `X ^ (p ^ k)` for `X`. This identifies the
indices that can contribute to the Ducci coefficient modulo `p`.
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.DucciWanted

open Polynomial in
-- Retain the source's bounds, although the coefficient argument does not need them.
set_option linter.unusedVariables false in
/-- **Reduction of Ducci coefficients modulo $p$.** For integers $N \ge 1$, $r \ge 0$ and $s \ge 1$
write $a^{(N)}_{r,s} = \sum_{0 \le j \le r,\ j \equiv s - 1 \ (\mathrm{mod}\ N)} \binom{r}{j}$ for
the Ducci coefficients of length $N$. Let $p$ be a prime, let $k \ge 0$ and $n_1 \ge 2$ be
integers, and let $n = p^k n_1$. Then for every integer $c \ge 1$ and every integer $b$ with
$0 \le b < n_1$,
$a^{(n)}_{c p^k,\, b p^k + 1} \equiv a^{(n_1)}_{c,\, b + 1} \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 4. -/
theorem ducciCoeff_reduce_mod (p k n1 c b : ℕ)
    (hp : p.Prime) (hn1 : 2 ≤ n1) (hc : 1 ≤ c) (hb : b < n1) :
    ((ducciCoeff (p ^ k * n1) (c * p ^ k) (b * p ^ k + 1) : ℤ) :
      ZMod p) =
      ((ducciCoeff n1 c (b + 1) : ℤ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  let q := p ^ k
  have hq : 0 < q := pow_pos hp.pos _
  have hexpand : (X + 1 : (ZMod p)[X]) ^ (c * q) =
      expand (ZMod p) q ((X + 1) ^ c) := by
    simp [q, Nat.mul_comm c, pow_mul, add_pow_char_pow]
  let S := (Finset.range (c * q + 1)).filter (fun j => j % (q * n1) = (b * q) % (q * n1))
  let T := (Finset.range (c + 1)).filter (fun i => i % n1 = b % n1)
  -- Both the range bound and the congruence cancel the same positive factor `q`.
  have hmem (i : ℕ) : q * i ∈ S ↔ i ∈ T := by
    simp only [S, T, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
      Nat.mul_comm c q, Nat.mul_comm b q, Nat.mul_mod_mul_left,
      Nat.mul_left_cancel_iff hq, Nat.mul_le_mul_left_iff hq]
  simp only [Int.cast_natCast]
  simp only [ducciCoeff, Nat.cast_sum, Nat.add_sub_cancel]
  change (∑ j ∈ S, (Nat.choose (c * q) j : ZMod p)) = ∑ i ∈ T, (Nat.choose c i : ZMod p)
  symm
  refine Finset.sum_bij (fun i _ => q * i) (fun i hi => (hmem i).2 hi) ?_ ?_ ?_
  · intro i _ i' _ hii'
    exact Nat.mul_left_cancel hq hii'
  · intro j hj
    -- The large residue class itself forces `q ∣ j`, since `q ∣ q * n1`.
    have hmod := (Finset.mem_filter.mp hj).2
    have hqmod : q ∣ q * n1 := dvd_mul_right q n1
    have hdiv : q ∣ j := by
      apply Nat.dvd_of_mod_eq_zero
      rw [← Nat.mod_mod_of_dvd j hqmod, hmod, Nat.mod_mod_of_dvd _ hqmod]
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_left q b)
    obtain ⟨i, rfl⟩ := hdiv
    exact ⟨i, (hmem i).1 hj, rfl⟩
  · intro i _
    rw [← coeff_X_add_one_pow (ZMod p) (c * q), hexpand, coeff_expand_mul' hq,
      coeff_X_add_one_pow]

end MathlibExt.NumberTheory.DucciWanted
