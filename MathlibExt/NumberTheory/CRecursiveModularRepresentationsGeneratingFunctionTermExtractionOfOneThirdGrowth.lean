/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Term extraction from the generating function under cube-root growth

For a sequence of natural numbers whose generating function converges at the reciprocal
of a base `c ≥ 8`, and whose terms grow slower than `c ^ (n / 3)`, each term `t n` with
`n ≥ 1` is the remainder modulo `c ^ n` of the floor of `c ^ (n ^ 2)` times the generating
function evaluated at `(c ^ n)⁻¹`.

## Main results

* `MetaMathlibExt.generating_function_term_extraction_of_one_third_growth`: the term
  extraction formula above.

## References

* M. Prunescu and L. Sauras-Altuzarra, *On the representation of C-recursive integer sequences
  by arithmetic terms*, Journal of Difference Equations and Applications 31 (2025), 1263–1285,
  arXiv:2405.04083, Theorems 1 and 2.
* M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
  Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 2, second part, which
  restates the result of the first reference.
-/

public section

namespace MetaMathlibExt

namespace generating_function_term_extraction

private theorem self_cancel (c n : ℕ) (hc : 8 ≤ c) :
    (c : ℝ) ^ (n ^ 2) * (((c : ℝ) ^ n)⁻¹) ^ n = 1 := by
  have hxc0 : (c : ℝ) ≠ 0 := by
    have hcR : (8 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    have hc0 : (0 : ℝ) < (c : ℝ) := by linarith
    exact ne_of_gt hc0
  rw [inv_pow, pow_two n, pow_mul]
  exact mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hxc0))

private theorem summable_shifted (t : ℕ → ℕ) (c n : ℕ) (hc : 8 ≤ c) (hn : 1 ≤ n)
    (hconv : Summable (fun k : ℕ => (t k : ℝ) * ((c : ℝ)⁻¹) ^ k)) :
    Summable (fun k : ℕ => (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k) := by
  have hcR : (8 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hx1 : (1 : ℝ) ≤ (c : ℝ) := by linarith
  have hx0 : (0 : ℝ) < (c : ℝ) := by linarith
  have hpow : (c : ℝ) ≤ (c : ℝ) ^ n := le_self_pow₀ hx1 (by omega)
  have hbase : (((c : ℝ) ^ n)⁻¹) ≤ (c : ℝ)⁻¹ :=
    (inv_le_inv₀ (pow_pos hx0 n) hx0).mpr hpow
  have hbase0 : (0 : ℝ) ≤ (((c : ℝ) ^ n)⁻¹) := (inv_pos.mpr (pow_pos hx0 n)).le
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbase0 _))
    (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase k)
      (Nat.cast_nonneg _))
    hconv

private theorem hasSum_half_pow_succ : HasSum (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) 1 := by
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hg := hasSum_geometric_of_lt_one h0 h1
  have hval : (1 / 2 : ℝ) * (1 - 1 / 2)⁻¹ = 1 := by norm_num
  have hm := hg.mul_left (1 / 2)
  rw [hval] at hm
  exact hm.congr_fun (fun i => pow_succ' _ _)

private theorem rpow_eight_third (i : ℕ) : (8 : ℝ) ^ (((i : ℝ) + 1) / 3) = (2 : ℝ) ^ (i + 1) := by
  have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
  conv_lhs => rw [h8, ← Real.rpow_natCast 2 3, ← Real.rpow_mul (by norm_num)]
  have hexp : ((3 : ℕ) : ℝ) * (((i : ℝ) + 1) / 3) = (i : ℝ) + 1 := by
    rw [Nat.cast_ofNat]
    ring
  rw [hexp]
  have hcast : (i : ℝ) + 1 = ((i + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast, Real.rpow_natCast]

private theorem tail_term_lt (t : ℕ → ℕ) (c n i : ℕ) (hc : 8 ≤ c) (hn : 1 ≤ n)
    (hbound : ∀ m, 1 ≤ m → (t m : ℝ) < (c : ℝ) ^ ((m : ℝ) / 3)) :
    (c : ℝ) ^ (n ^ 2) * ((t (i + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (i + (n + 1)))
      < (1 / 2 : ℝ) ^ (i + 1) := by
  have hcR : (8 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hx0 : (0 : ℝ) < (c : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ (c : ℝ) := by linarith
  have hxc0 : (c : ℝ) ≠ 0 := ne_of_gt hx0
  have hcancel := self_cancel c n hc
  have hT : (c : ℝ) ^ (n ^ 2) * ((t (i + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (i + (n + 1)))
      = (t (i + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (i + 1) := by
    have hsplit : i + (n + 1) = n + (i + 1) := by omega
    have ering : ∀ (a b d f : ℝ), a * (b * (d * f)) = b * ((a * d) * f) :=
      fun a b d f => by ring
    rw [hsplit, pow_add, ering, hcancel, one_mul]
  have hpos : (0 : ℝ) < (((c : ℝ) ^ n)⁻¹) ^ (i + 1) :=
    pow_pos (inv_pos.mpr (pow_pos hx0 n)) _
  have hbound_m : (t (i + (n + 1)) : ℝ) < (c : ℝ) ^ ((((i + (n + 1) : ℕ)) : ℝ) / 3) :=
    hbound _ (by omega)
  have hstep1 : (c : ℝ) ^ (n ^ 2) * ((t (i + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (i + (n + 1)))
      < (c : ℝ) ^ ((((i + (n + 1) : ℕ)) : ℝ) / 3) * (((c : ℝ) ^ n)⁻¹) ^ (i + 1) := by
    rw [hT]
    exact mul_lt_mul_of_pos_right hbound_m hpos
  have hC : (c : ℝ) ^ ((((i + (n + 1) : ℕ)) : ℝ) / 3) * (((c : ℝ) ^ n)⁻¹) ^ (i + 1)
      = (c : ℝ) ^ (((((i + (n + 1) : ℕ)) : ℝ) / 3 - (n : ℝ) * ((i : ℝ) + 1))) := by
    rw [inv_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hexp_le : ((((i + (n + 1) : ℕ)) : ℝ) / 3 - (n : ℝ) * ((i : ℝ) + 1))
      ≤ -(((i : ℝ) + 1) / 3) := by
    have hn3 : 2 ≤ 3 * n := by omega
    have h1 : 2 * i ≤ 3 * n * i := mul_le_mul_of_nonneg_right hn3 (Nat.zero_le i)
    have h2 : n + 2 ≤ 3 * n := by omega
    have hni : n + 2 * i + 2 ≤ 3 * n * (i + 1) := by
      calc n + 2 * i + 2 = (2 * i) + (n + 2) := by ring
      _ ≤ 3 * n * i + 3 * n := add_le_add h1 h2
      _ = 3 * n * (i + 1) := by ring
    have hR : (n : ℝ) + 2 * (i : ℝ) + 2 ≤ 3 * (n : ℝ) * ((i : ℝ) + 1) := by
      exact_mod_cast hni
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [hR]
  have hstep2 : (c : ℝ) ^ ((((i + (n + 1) : ℕ)) : ℝ) / 3) * (((c : ℝ) ^ n)⁻¹) ^ (i + 1)
      ≤ (c : ℝ) ^ (-(((i : ℝ) + 1) / 3)) := by
    rw [hC]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hexp_le
  have hle83 : ((2 ^ (i + 1) : ℕ) : ℝ) ≤ (c : ℝ) ^ (((i : ℝ) + 1) / 3) := by
    have hcR : (8 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    have hu : (0 : ℝ) ≤ ((i : ℝ) + 1) / 3 := by positivity
    have h80 : (0 : ℝ) ≤ 8 := by norm_num
    have h8 := Real.rpow_le_rpow h80 hcR hu
    rw [rpow_eight_third] at h8
    have hcast : ((2 ^ (i + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (i + 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast]
    exact h8
  have hstep3 : (c : ℝ) ^ (-(((i : ℝ) + 1) / 3)) ≤ (1 / 2 : ℝ) ^ (i + 1) := by
    have h2pos : (0 : ℕ) < 2 := by norm_num
    have hX0 : (0 : ℝ) < ((2 ^ (i + 1) : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (pow_pos h2pos _)
    have hcu0 : (0 : ℝ) < (c : ℝ) ^ (((i : ℝ) + 1) / 3) := Real.rpow_pos_of_pos hx0 _
    have hinv : ((c : ℝ) ^ (((i : ℝ) + 1) / 3))⁻¹ ≤ (((2 ^ (i + 1) : ℕ) : ℝ))⁻¹ :=
      (inv_le_inv₀ hcu0 hX0).mpr hle83
    have hcast : ((2 ^ (i + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (i + 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    have h2inv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    have hinv2 : (((2 ^ (i + 1) : ℕ) : ℝ))⁻¹ = (1 / 2 : ℝ) ^ (i + 1) := by
      rw [hcast, ← inv_pow, h2inv]
    rw [Real.rpow_neg hx0.le]
    exact hinv.trans hinv2.le
  calc (c : ℝ) ^ (n ^ 2) * ((t (i + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (i + (n + 1)))
        < (c : ℝ) ^ ((((i + (n + 1) : ℕ)) : ℝ) / 3) * (((c : ℝ) ^ n)⁻¹) ^ (i + 1) := hstep1
    _ ≤ (c : ℝ) ^ (-(((i : ℝ) + 1) / 3)) := hstep2
    _ ≤ (1 / 2 : ℝ) ^ (i + 1) := hstep3

private theorem head_term_eq (t : ℕ → ℕ) (c n k : ℕ) (hc : 8 ≤ c) (hkn : k ≤ n) :
    (c : ℝ) ^ (n ^ 2) * ((t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)
      = ((t k * c ^ (n * (n - k)) : ℕ) : ℝ) := by
  have hx0 : (0 : ℝ) < (c : ℝ) := by
    have hcR : (8 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    linarith
  have hxc0 : (c : ℝ) ≠ 0 := ne_of_gt hx0
  have hle : n * k ≤ n ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul le_rfl hkn
  have hsplit : (c : ℝ) ^ (n ^ 2) = (c : ℝ) ^ (n * k) * (c : ℝ) ^ (n ^ 2 - n * k) := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle, pow_add]
  have hcancel : (c : ℝ) ^ (n * k) * ((c : ℝ) ^ (n * k))⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hxc0)
  have hexp : n ^ 2 - n * k = n * (n - k) := by
    rw [pow_two, mul_tsub]
  rw [inv_pow, ← pow_mul, hsplit, hexp, Nat.cast_mul, Nat.cast_pow]
  calc ((c : ℝ) ^ (n * k) * (c : ℝ) ^ (n * (n - k))) * ((t k : ℝ) * ((c : ℝ) ^ (n * k))⁻¹)
        = (t k : ℝ) * (c : ℝ) ^ (n * (n - k))
          * ((c : ℝ) ^ (n * k) * ((c : ℝ) ^ (n * k))⁻¹) := by ring
    _ = (t k : ℝ) * (c : ℝ) ^ (n * (n - k)) := by rw [hcancel, mul_one]

private theorem mid_term_eq (t : ℕ → ℕ) (c n : ℕ) (hc : 8 ≤ c) :
    (c : ℝ) ^ (n ^ 2) * ((t n : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ n) = (t n : ℝ) := by
  have hcancel := self_cancel c n hc
  calc (c : ℝ) ^ (n ^ 2) * ((t n : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ n)
        = (t n : ℝ) * ((c : ℝ) ^ (n ^ 2) * (((c : ℝ) ^ n)⁻¹) ^ n) := by ring
    _ = (t n : ℝ) := by rw [hcancel, mul_one]

private theorem term_lt_pow (t : ℕ → ℕ) (c n : ℕ) (hc : 8 ≤ c) (hn : 1 ≤ n)
    (hbound : ∀ m, 1 ≤ m → (t m : ℝ) < (c : ℝ) ^ ((m : ℝ) / 3)) :
    t n < c ^ n := by
  have hcR : (8 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hx1 : (1 : ℝ) ≤ (c : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hexp : (n : ℝ) / 3 ≤ (n : ℝ) := by linarith
  have h := (hbound n hn).trans_le (Real.rpow_le_rpow_of_exponent_le hx1 hexp)
  rw [Real.rpow_natCast] at h
  have hcast : ((c ^ n : ℕ) : ℝ) = (c : ℝ) ^ n := Nat.cast_pow c n
  rw [← hcast] at h
  exact_mod_cast h

end generating_function_term_extraction

open generating_function_term_extraction in
/--
**Term extraction from the generating function under cube-root growth.** Let
$t_0, t_1, t_2, \dots$ be natural numbers and let $c \ge 8$ be a natural number. Suppose that
the real series $\sum_{k \ge 0} t_k c^{-k}$ is summable and that $t_n < c^{n/3}$, a real power,
for every $n \ge 1$. Then for every $n \ge 1$,

$$t_n = \Bigl\lfloor c^{n^2} \sum_{k \ge 0} t_k \, (c^{-n})^k \Bigr\rfloor \bmod c^n.$$

The Lean statement assumes summability at $c^{-1}$ in place of the papers' hypothesis that
$c^{-1}$ lies inside the radius of convergence of the generating function; summability is the
condition the proof uses. Neither statement is stronger: under the growth bound the series
converges absolutely for $|z| < c^{-1/3}$, so its radius of convergence is at least
$c^{-1/3} > c^{-1}$ and both conditions hold.

Source: M. Prunescu and L. Sauras-Altuzarra, *On the representation of C-recursive integer
sequences by arithmetic terms*, Journal of Difference Equations and Applications 31 (2025),
1263–1285, arXiv:2405.04083, Theorems 1 and 2; restated in M. Prunescu and J. M. Shunia,
*On Modular Representations of C-Recursive Integer Sequences*, Journal of Integer Sequences 28
(2025), Article 25.5.3, Theorem 2, second part.
-/
theorem generating_function_term_extraction_of_one_third_growth
    (t : ℕ → ℕ) (c : ℕ)
    (hc : 8 ≤ c)
    (hconv : Summable (fun k : ℕ => (t k : ℝ) * ((c : ℝ)⁻¹) ^ k))
    (hbound : ∀ n, 1 ≤ n → (t n : ℝ) < (c : ℝ) ^ ((n : ℝ) / 3))
    (n : ℕ) (hn : 1 ≤ n) :
    t n = Nat.floor ((c : ℝ) ^ (n ^ 2) *
      (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)) % c ^ n := by
  have hs : Summable (fun k : ℕ => (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k) :=
    summable_shifted t c n hc hn hconv
  have h1 : (∑ k ∈ Finset.range n, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)
      + (∑' b : ℕ, (t (b + n) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + n))
      = ∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k :=
    hs.sum_add_tsum_nat_add n
  have hg : Summable (fun i : ℕ => (t (i + n) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (i + n)) :=
    (summable_nat_add_iff n).mpr hs
  have h2' : (∑' b : ℕ, (t (b + n) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + n))
      = ((t (0 + n) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (0 + n))
        + ∑' b : ℕ, (t ((b + 1) + n) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ ((b + 1) + n) :=
    hg.tsum_eq_zero_add
  have e1 : (0 : ℕ) + n = n := zero_add n
  have e2 : ∀ b : ℕ, (b + 1) + n = b + (n + 1) := fun b => by omega
  rw [e1] at h2'
  simp only [e2] at h2'
  have hdecomp : (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)
      = (∑ k ∈ Finset.range n, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)
        + ((t n : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ n
          + ∑' b : ℕ, (t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1))) := by
    rw [← h1, h2']
  have hhead : (c : ℝ) ^ (n ^ 2) * (∑ k ∈ Finset.range n, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)
      = ((∑ k ∈ Finset.range n, t k * c ^ (n * (n - k)) : ℕ) : ℝ) := by
    simp only [Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact head_term_eq t c n k hc (Finset.mem_range.mp hk).le
  have htail_eq : (c : ℝ) ^ (n ^ 2)
      * (∑' b : ℕ, (t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1)))
      = ∑' b : ℕ, (c : ℝ) ^ (n ^ 2)
        * ((t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1))) :=
    tsum_mul_left.symm
  have hTnonneg : ∀ b : ℕ, 0 ≤ (c : ℝ) ^ (n ^ 2)
      * ((t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1))) := by
    intro b
    positivity
  have hTle : ∀ b : ℕ, (c : ℝ) ^ (n ^ 2)
      * ((t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1)))
      ≤ (1 / 2 : ℝ) ^ (b + 1) :=
    fun b => (tail_term_lt t c n b hc hn hbound).le
  have hTlt0 : (c : ℝ) ^ (n ^ 2)
      * ((t (0 + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (0 + (n + 1)))
      < (1 / 2 : ℝ) ^ (0 + 1) :=
    tail_term_lt t c n 0 hc hn hbound
  have hgeomsum : Summable (fun b : ℕ => (1 / 2 : ℝ) ^ (b + 1)) :=
    hasSum_half_pow_succ.summable
  have htail_lt : (∑' b : ℕ, (c : ℝ) ^ (n ^ 2)
      * ((t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1)))) < 1 := by
    have h := Summable.tsum_lt_tsum_of_nonneg (i := 0) hTnonneg hTle hTlt0 hgeomsum
    have hval : (∑' b : ℕ, (1 / 2 : ℝ) ^ (b + 1)) = 1 := hasSum_half_pow_succ.tsum_eq
    calc (∑' b : ℕ, (c : ℝ) ^ (n ^ 2)
          * ((t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1))))
          < ∑' b : ℕ, (1 / 2 : ℝ) ^ (b + 1) := h
      _ = 1 := hval
  have htail_nonneg : 0 ≤ ∑' b : ℕ, (c : ℝ) ^ (n ^ 2)
      * ((t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1))) :=
    tsum_nonneg hTnonneg
  have hV : (c : ℝ) ^ (n ^ 2) * (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)
      = ((∑ k ∈ Finset.range n, t k * c ^ (n * (n - k)) : ℕ) : ℝ) + ((t n : ℝ)
        + ∑' b : ℕ, (c : ℝ) ^ (n ^ 2)
          * ((t (b + (n + 1)) : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ (b + (n + 1)))) := by
    rw [hdecomp, mul_add, mul_add, hhead, mid_term_eq t c n hc, htail_eq]
  have hVnonneg : 0 ≤ (c : ℝ) ^ (n ^ 2)
      * (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k) := by
    rw [hV]
    exact add_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) htail_nonneg)
  have hfloor : Nat.floor ((c : ℝ) ^ (n ^ 2)
      * (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k))
      = (∑ k ∈ Finset.range n, t k * c ^ (n * (n - k))) + t n := by
    rw [Nat.floor_eq_iff hVnonneg, hV, Nat.cast_add]
    constructor
    · have h0 := htail_nonneg
      linarith
    · have h1 := htail_lt
      linarith
  have hdvd : c ^ n ∣ (∑ k ∈ Finset.range n, t k * c ^ (n * (n - k))) := by
    apply Finset.dvd_sum
    intro k hk
    have hle : n ≤ n * (n - k) := by
      have h1 : 1 ≤ n - k := by
        have hk' : k < n := Finset.mem_range.mp hk
        omega
      calc n = n * 1 := (mul_one n).symm
      _ ≤ n * (n - k) := Nat.mul_le_mul le_rfl h1
    exact (pow_dvd_pow c hle).trans (dvd_mul_left _ _)
  obtain ⟨K, hK⟩ := hdvd
  have hlt : t n < c ^ n := term_lt_pow t c n hc hn hbound
  rw [hfloor, hK, add_comm (c ^ n * K) (t n), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end MetaMathlibExt
