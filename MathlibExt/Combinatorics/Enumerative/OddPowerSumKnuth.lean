/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Knuth's binomial formula for odd power sums

Normalize the even power-sum expansion and use Knuth's correspondence to obtain
its odd counterpart in the same binomial basis.

## References

* José L. Cereceda, *Sums of Powers of Integers and the Sequence A304330*, Journal of
  Integer Sequences 28 (2025), Article 25.1.3, pp. 1–21, Propositions 2 and 3, equations (5)–(6).
* Donald E. Knuth, *Johann Faulhaber and Sums of Powers*, Mathematics of Computation
  61 (1993), 277–294, pp. 284–286 (the odd formula and the even–odd correspondence).
* P. L. Butzer, M. Schmidt, E. L. Stark, and L. Vogt,
  *Central factorial numbers; their main properties and some applications*, Numerical Functional
  Analysis and Optimization 10 (1989), 419–488, Propositions 2.3 and 2.4(xiii) (the central
  factorial identities behind the even expansion).
* M. Z. Spivey, *The Art of Proving Binomial Identities*, CRC Press, 2019, Identity 58
  (cited in Cereceda's alternative derivation of the odd formula in §2.2).
-/

set_option autoImplicit false

public section

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

/-- **Knuth's binomial formula for the odd power sums.** For all natural numbers $k \ge 1$ and
$n$, the power sum $S_{2k-1}(n) = 1^{2k-1} + 2^{2k-1} + \cdots + n^{2k-1}$ satisfies
$$S_{2k-1}(n) = \sum_{m=1}^{k} R(k, m) \cdot \frac{1}{m} \binom{n + m}{2m},$$
where $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$ is the array of OEIS A304330.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 3. -/
theorem powerSum_odd_eq_sum (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    powerSum (2 * k - 1) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) * (1 / (m : ℚ)) *
          (Nat.choose (n + m) (2 * m) : ℚ) := by
  let a (m : ℕ) : ℝ := (arrayR k m : ℝ) / (2 * (m : ℝ) + 1)
  have heven (j : ℕ) : (powerSum (2 * k) j : ℝ) / (2 * (j : ℝ) + 1) =
      ∑ m ∈ Finset.Icc 1 k, a m * (Nat.choose (j + m) (2 * m) : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (powerSum_even_eq_sum k hk j)
    push_cast at h
    rw [div_eq_iff (by positivity), h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp [a]
    ring
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [(powerSum_even_div_iff_odd k hk a).mp heven n]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm₀ : (m : ℝ) ≠ 0 := by
    have hm₁ : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    positivity
  have hd : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  dsimp [a]
  field_simp [hm₀, hd]

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
