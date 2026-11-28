/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Knuth's binomial formula for odd power sums

Normalize the even power-sum expansion and use Knuth's correspondence to obtain
its odd counterpart in the same binomial basis. For `k ≥ 1` and natural `n`, the signed
Legendre–Stirling expansion in that basis gives the Faulhaber form of `S_{2k+1}(n)`,
including the empty sum at `n = 0`. The alternating factorial identity removes the linear term
in `S₁(n)` without differentiation.

## References

* José L. Cereceda, *Sums of Powers of Integers and the Sequence A304330*, Journal of
  Integer Sequences 28 (2025), Article 25.1.3, pp. 1–21, Propositions 2 and 3, equations (5)–(6),
  and Propositions 12 and 15.
* G. E. Andrews, W. Gawronski, and L. L. Littlejohn, *The Legendre-Stirling numbers*,
  Discrete Mathematics 311 (2011), 1255–1272, Theorem 5.5.
* M. W. Coffey and M. C. Lettington, *On Fibonacci Polynomial Expressions for Sums of mth
  Powers, their implications for Faulhaber's Formula and some Theorems of Fermat*,
  arXiv:1510.05402 (2015), Equation (5.1).
* Donald E. Knuth, *Johann Faulhaber and Sums of Powers*, Mathematics of Computation
  61 (1993), 277–294, pp. 284–286 (the odd formula and the even–odd correspondence).
* P. L. Butzer, M. Schmidt, E. L. Stark, and L. Vogt,
  *Central factorial numbers; their main properties and some applications*, Numerical Functional
  Analysis and Optimization 10 (1989), 419–488, Propositions 2.3 and 2.4(xiii) (the central
  factorial identities behind the even expansion).
* M. Z. Spivey, *The Art of Proving Binomial Identities*, CRC Press, 2019, Identity 58
  (cited in Cereceda's alternative derivation of the odd formula in §2.2).
* `MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330`, `powerSum_even_faulhaber`,
  for the corresponding change of basis and sum exchange in Lean.
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

open Finset MetaMathlibExt

/-- **The Faulhaber coefficients $c_{k,r}$.** For natural numbers $p$ and $q$, let
$R(p, q) = \sum_{j=0}^{q} (-1)^j \binom{2q}{j} (q - j)^{2p}$, and for natural numbers $q$
and $s$ let $\mathrm{Ps}_q^{(s)}$ be the Legendre–Stirling number of the first kind, the
coefficient of $x^s$ in $\prod_{i=0}^{q-1} (x - i(i+1))$. For natural numbers $k$ and $r$,
$c_{k,r}$ is the rational number
$\sum_{m=r}^{k} \frac{2^{r+1}}{(2m+2)!\,(m+1)}\, R(k+1, m+1)\, \mathrm{Ps}_{m+1}^{(r+1)}$. -/
@[expose] noncomputable def faulhaberC (k r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Icc r k,
    (2 ^ (r + 1) / ((Nat.factorial (2 * m + 2) : ℚ) * (m + 1))) *
      (arrayR (k + 1) (m + 1) : ℚ) * (MetaMathlibExt.legendreStirlingFirst (m + 1) (r + 1) : ℚ)

/-- **Odd Faulhaber coefficients with unshifted column indices.** For all natural numbers $k$
and $r$, the Faulhaber coefficient $c_{k,r}$ satisfies

$$c_{k,r} = \sum_{m=r+1}^{k+1} \frac{2^{r+1}}{(2m)!\,m}\,R(k+1,m)\,\mathrm{Ps}_m^{(r+1)}.$$

Here $R(p,m) = \sum_{j=0}^{m}(-1)^j\binom{2m}{j}(m-j)^{2p}$ is the A304330 array and
$\mathrm{Ps}_m^{(s)}$ is the coefficient of $X^s$ in $\prod_{j=0}^{m-1}(X-j(j+1))$.
The sum is empty when $r > k$. This reindexes equation (19) of José L. Cereceda's
*Sums of Powers of Integers and the Sequence A304330*. -/
theorem faulhaberC_eq_sum_succ (k r : ℕ) :
    faulhaberC k r = ∑ m ∈ Icc (r + 1) (k + 1),
      (2 ^ (r + 1) / (((2 * m).factorial : ℚ) * m)) *
        (arrayR (k + 1) m : ℚ) * (legendreStirlingFirst m (r + 1) : ℚ) := by
  rw [faulhaberC, ← map_add_right_Icc r k 1, sum_map]
  refine sum_congr rfl fun m _ ↦ ?_
  rw [addRightEmbedding_apply, show 2 * (m + 1) = 2 * m + 2 by omega, Nat.cast_add, Nat.cast_one]

/-- **Faulhaber form of the odd power sums.** For all natural numbers $k \ge 1$ and $n$,
writing $S_j(n) = 1^j + 2^j + \cdots + n^j$ for the power sums and $c_{k,r}$ for the Faulhaber
coefficients of Proposition 12, the rational numbers satisfy
$S_{2k+1}(n) = S_1(n)^2 \sum_{r=1}^{k} c_{k,r} \, S_1(n)^{r-1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 12. -/
theorem powerSum_odd_faulhaber (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    powerSum (2 * k + 1) n =
      (powerSum 1 n) ^ 2 * ∑ r ∈ Finset.Icc 1 k,
        faulhaberC k r * (powerSum 1 n) ^ (r - 1) := by
  let s := powerSum 1 n
  let a (m r : ℕ) : ℚ := (1 / (((2 * m).factorial : ℚ) * m)) *
    (arrayR (k + 1) m : ℚ) * (legendreStirlingFirst m r : ℚ)
  let term (m r : ℕ) : ℚ := a m r * (2 * s) ^ r
  rw [← show 2 * (k + 1) - 1 = 2 * k + 1 by omega, powerSum_odd_eq_sum (k + 1) (by omega) n]
  calc
    _ = ∑ m ∈ Icc 1 (k + 1), ∑ r ∈ Icc 1 m, term m r := by
      refine sum_congr rfl fun m hm ↦ ?_
      have hm₁ := (mem_Icc.mp hm).1
      rw [choose_eq_legendreStirlingFirst_sum n m hm₁, sum_div, mul_sum]
      refine sum_congr rfl fun r _ ↦ ?_
      dsimp only [term, a, s]
      field_simp
    _ = ∑ r ∈ Icc 1 (k + 1), ∑ m ∈ Icc r (k + 1), term m r := by
      apply sum_comm'
      intro m r
      simp only [mem_Icc]
      omega
    _ = ∑ r ∈ Icc 2 (k + 1), ∑ m ∈ Icc r (k + 1), term m r := by
      have hsplit : insert 1 (Icc 2 (k + 1)) = Icc 1 (k + 1) :=
        insert_Icc_add_one_left_eq_Icc (by omega)
      have hlinear : ∑ m ∈ Icc 1 (k + 1), term m 1 = 0 := by
        simp only [term, ← sum_mul, a]
        rw [sum_arrayR_legendreStirlingFirst_one_eq_zero (k + 1) (by omega), zero_mul]
      rw [← hsplit, sum_insert (by simp), hlinear, zero_add]
    _ = _ := by
      rw [mul_sum, ← map_add_right_Icc 1 k 1, sum_map]
      refine sum_congr rfl fun r hr ↦ ?_
      have hr₁ := (mem_Icc.mp hr).1
      rw [addRightEmbedding_apply, faulhaberC_eq_sum_succ, sum_mul, mul_sum]
      refine sum_congr rfl fun m _ ↦ ?_
      have hs : s ^ (r + 1) = s ^ 2 * s ^ (r - 1) := by
        rw [← pow_add, show 2 + (r - 1) = r + 1 by omega]
      dsimp only [term, a, s] at hs ⊢
      rw [mul_pow, hs]
      ring

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
