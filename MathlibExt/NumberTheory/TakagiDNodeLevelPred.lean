/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TakagiDyadicIdentities
import Mathlib.Algebra.Ring.Parity

/-!
# Consecutive level counts of D-nodes

Subtracting one from an odd leaf count changes the level count by one in magnitude. The
binary digit at that level determines the sign.

## References

* Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
  Sequences 27 (2024), Article 24.2.7, pp. 1–14, Lemma 17 (p. 7) and the level-count
  formula in Theorem 11 (p. 6).
* Tomás M. Coronado, Mareike Fischer, Lina Herbst, Francesc Rosselló, and Kristina Wicke,
  *On the minimum value of the Colless index and the bifurcating trees that achieve it*,
  Journal of Mathematical Biology 80 (2020), pp. 1993–2054, §3.1 (the underlying
  divide-and-conquer count).
-/

namespace MetaMathlibExt

-- The arithmetic does not need the upper bound on `r`; retain the published hypotheses.
set_option linter.unusedVariables false in
/-- **Level counts of D-nodes at consecutive integers.** Let $k$, $r$ and $i$ be natural numbers
with $r$ odd, $r < 2^k$ and $0 < i < k$, and let $n = 2^k + r$. Then the level counts of
D-nodes satisfy $\lambda_i(n) - \lambda_i(n-1) = 1$ if the binary digit $n_i$ of $n$ is $0$,
and $\lambda_i(n) - \lambda_i(n-1) = -1$ if $n_i = 1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 17 (`jis-2024-24.2.7-lem-17`). -/
public theorem dcLevelDNodes_sub_pred (k r i : ℕ) (hodd : Odd r) (hr : r < 2 ^ k)
    (hi0 : 0 < i) (hik : i < k) :
    (dcLevelDNodes (2 ^ k + r) i : ℤ) - dcLevelDNodes (2 ^ k + r - 1) i =
      if (2 ^ k + r) / 2 ^ i % 2 = 0 then 1 else -1 := by
  let n : ℕ := 2 ^ k + r
  change (dcLevelDNodes n i : ℤ) - dcLevelDNodes (n - 1) i =
    if n / 2 ^ i % 2 = 0 then 1 else -1
  have hdvd (j : ℕ) (hj : 0 < j) : 2 ∣ (2 : ℕ) ^ j :=
    Nat.pow_dvd_pow 2 hj
  have hnodd : Odd n := (even_iff_two_dvd.mpr (hdvd k (hi0.trans hik))).add_odd hodd
  have hrem_pos : 0 < n % 2 ^ i := by
    have h := (Nat.mod_mod_of_dvd n (hdvd i hi0)).trans (Nat.odd_iff.mp hnodd)
    omega
  have hpow := Nat.two_pow_pos i
  have hrem_lt := Nat.mod_lt n hpow
  have hsplit := Nat.div_add_mod' n (2 ^ i)
  -- There is no borrow across the boundary at bit `i`.
  have hdiv : (n - 1) / 2 ^ i = n / 2 ^ i := by
    apply (Nat.div_eq_iff hpow).mpr
    omega
  have hmod : (n - 1) % 2 ^ i = n % 2 ^ i - 1 := by
    rw [Nat.mod_eq_sub_div_mul, hdiv]
    omega
  have hcast : (((n - 1) % 2 ^ i : ℕ) : ℤ) = (n % 2 ^ i : ℕ) - (1 : ℤ) := by
    rw [hmod, Int.ofNat_sub hrem_pos, Int.ofNat_one]
  have hdigit := congrArg (· % 2) hdiv
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with hzero | hone
  · rw [ite_eq_left hzero, dcLevelDNodes_of_digit_eq_zero hzero,
      dcLevelDNodes_of_digit_eq_zero (hdigit.trans hzero), hcast]
    omega
  · have hprev_le : (n - 1) % 2 ^ i ≤ 2 ^ i := (Nat.mod_lt _ hpow).le
    have hne : n / 2 ^ i % 2 ≠ 0 := hone.trans_ne Nat.one_ne_zero
    rw [ite_eq_right hne,
      dcLevelDNodes_of_digit_eq_one hone, dcLevelDNodes_of_digit_eq_one (hdigit.trans hone),
      Int.ofNat_sub hrem_lt.le, Int.ofNat_sub hprev_le, hcast]
    omega

end MetaMathlibExt
