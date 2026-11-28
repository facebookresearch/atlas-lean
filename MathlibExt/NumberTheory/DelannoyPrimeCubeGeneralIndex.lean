/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.OrdinaryRiordanPascalLikeMatrix
public import MathlibExt.NumberTheory.FermatQuotient
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.DelannoyConstructions
import all MathlibExt.NumberTheory.DelannoyHarmonicCongruence
import all MathlibExt.NumberTheory.DelannoyPrimeCube

/-!
# Delannoy triangle entries in row `n * p - 1` modulo a prime cube

For a prime `p ≥ 5` and a natural number `n ≥ 1`, the Delannoy triangle entry
in row `n * p - 1` and column `p - 1`, minus one, is linear in `n - 1` modulo `p³`.
The coefficient is determined by the case `n = 2`, using the Fermat quotient of two
(with the coprimality proof `IsCoprime (2 : ℤ) (p : ℤ)` required by `Int.fermatQuotient`).

## References

* Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle
  Coefficients*, Journal of Integer Sequences 29 (2026), Article 26.5.2, Theorem 4
  (using Lemma 5 for the binomial expansion and Theorem 1 for the case `n = 2`).
* Paul Barry, *On Integer-Sequence-Based Constructions of Generalized Pascal Triangles*,
  Journal of Integer Sequences 9 (2006), Article 06.2.4, Example 16 (the Delannoy sum).
  We use `delannoy_eq_sum_choose_mul_choose_two_pow` from `DelannoyConstructions`, which
  formalizes the same sum from Steven Edwards and William Griffiths, *Delannoy Constructions*,
  Journal of Integer Sequences 27 (2024), Article 24.1.8, Theorem 8.
* The lagged harmonic sum vanishes by `finiteHarmonic_eq_neg_comp` and `finiteDilog_eval_neg_one`
  from `DelannoyHarmonicCongruence`. The case `n = 2` is `delannoy_two_mul.2` (the second
  congruence of `delannoy_two_mul`) in `DelannoyPrimeCube`, which also supplies `cube_zero`
  and `unit_of_lt`.
-/

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

open Finset

-- Convert the falling factorial in the generalized binomial expansion to `Nat.choose`.
private theorem choose_cast_eq_expansion {p s k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 0 < s) (hk : k < p) :
    ((s * p - 1).choose k : R p) =
      (-1) ^ k * (1 - (s : R p) * (p : R p) * harmonicMod (p ^ 3) k +
        (s : R p) ^ 2 * (p : R p) ^ 2 * (2 : R p)⁻¹ *
          (harmonicMod (p ^ 3) k ^ 2 - harmonic2Mod (p ^ 3) k)) := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [harmonicMod, harmonic2Mod]
  have hsp : p ≤ s * p := Nat.le_mul_of_pos_left p hs
  have hprod : ∏ i ∈ Icc 1 k, ((s : R p) * p - (i : R p)) =
      ((s * p - 1).descFactorial k : R p) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, ← Ico_add_one_right_eq_Icc,
      prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    rw [Nat.cast_sub (show i ≤ s * p - 1 by omega), Nat.cast_sub (show 1 ≤ s * p by omega)]
    push_cast
    ring
  have h := choose_mul_sub_one_mod p hp (by omega) (s : ℤ) k (by omega)
  simp only [Int.cast_natCast] at h
  have hfac := ZMod.coe_mul_inv_eq_one k.factorial
    ((hp.coprime_factorial_of_lt hk).symm.pow_right 3)
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_right_comm,
    hfac, one_mul] at h
  exact h

private def delannoyWeight (p j : ℕ) : R p := 2 ^ (j + 1) * ((j + 1 : ℕ) : R p)⁻¹

-- The factor `s * p` from binomial absorption lets us discard all cubic terms.
private theorem summand_expansion {p s j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 0 < s) (hj : j < p - 1) :
    ((p - 1).choose (j + 1) : R p) * ((s * p).choose (j + 1) : R p) * 2 ^ (j + 1) =
      (s : R p) * ((-(p : R p) + (p : R p) ^ 2 * harmonicMod (p ^ 3) (j + 1)) *
        delannoyWeight p j) +
      ((s : R p) ^ 2 * (p : R p) ^ 2) * (harmonicMod (p ^ 3) j * delannoyWeight p j) := by
  have hu := unit_of_lt hp (Nat.succ_pos j) (show j + 1 < p by omega)
  have hchoose : ((s * p).choose (j + 1) : R p) =
      (s : R p) * p * ((j + 1 : ℕ) : R p)⁻¹ * ((s * p - 1).choose j : R p) := by
    have h := congrArg (Nat.cast : ℕ → R p) (Nat.add_one_mul_choose_eq (s * p - 1) j)
    rw [Nat.sub_add_cancel (Nat.mul_pos hs hp.pos)] at h
    simp only [Nat.cast_mul] at h
    rw [mul_right_comm, h, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]
  let H := harmonicMod (p ^ 3) (j + 1)
  let J := harmonicMod (p ^ 3) j
  let A := (2 : R p)⁻¹ * (H ^ 2 - harmonic2Mod (p ^ 3) (j + 1))
  let B := (s : R p) ^ 2 * (2 : R p)⁻¹ * (J ^ 2 - harmonic2Mod (p ^ 3) j)
  have hA : ((p - 1).choose (j + 1) : R p) =
      (-1) ^ (j + 1) * (1 - (p : R p) * H + (p : R p) ^ 2 * A) := by
    simpa only [one_mul, Nat.cast_one, one_pow, H, A, mul_assoc] using
      choose_cast_eq_expansion hp hp5 (s := 1) Nat.one_pos (k := j + 1) (by omega)
  have hB : ((s * p - 1).choose j : R p) =
      (-1) ^ j * (1 - (s : R p) * p * J + (p : R p) ^ 2 * B) := by
    rw [choose_cast_eq_expansion hp hp5 hs (by omega : j < p)]
    dsimp [B, J]
    ring
  have hsign : (-1 : R p) ^ (j + 1) * (-1) ^ j = -1 := by
    rw [pow_succ (-1 : R p) j, mul_right_comm _ (-1 : R p), ← mul_pow]
    simp
  rw [hchoose, hA, hB]
  calc
    _ = ((-1 : R p) ^ (j + 1) * (-1) ^ j) * ((s : R p) * delannoyWeight p j * p *
        ((1 - (p : R p) * H + (p : R p) ^ 2 * A) *
          (1 - (s : R p) * p * J + (p : R p) ^ 2 * B))) := by
      unfold delannoyWeight
      ring
    _ = _ := by
      rw [hsign]
      change _ = (s : R p) * ((-p + (p : R p) ^ 2 * H) * delannoyWeight p j) +
        ((s : R p) ^ 2 * (p : R p) ^ 2) * (J * delannoyWeight p j)
      linear_combination -(s : R p) * delannoyWeight p j *
        (A + B + H * s * J - p * (H * B + s * J * A) + (p : R p) ^ 2 * A * B) * cube_zero p

-- After reduction modulo `p`, the lagged sum is the negative finite dilogarithm at `-1`.
private theorem lagged_sum_zero {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : R p) ^ 2 * ∑ j ∈ range (p - 1), harmonicMod (p ^ 3) j * delannoyWeight p j = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  let f : R p →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide : (3 : ℕ) ≠ 0)) _
  have hf (k : ℕ) (hk : 0 < k) (hkp : k < p) :
      f ((k : R p)⁻¹) = (k : ZMod p)⁻¹ := by
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    simpa only [map_mul, map_natCast, map_one] using
      congrArg f (ZMod.mul_inv_of_unit _ (unit_of_lt hp hk hkp))
  let x := ∑ j ∈ range (p - 1), harmonicMod (p ^ 3) j * delannoyWeight p j
  have hx : f x = (finiteHarmonic p).eval 2 := by
    simp only [x, map_sum, finiteHarmonic, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, delannoyWeight, map_mul,
      map_pow, map_ofNat]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    have hh : f (harmonicMod (p ^ 3) j) = harmonicMod p j := by
      simp only [harmonicMod, map_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_Icc.mp hi
      exact hf i (by omega) (by omega)
    rw [hh, hf (j + 1) (by omega) (by omega)]
    ring
  have hz : f x = 0 := by
    rw [hx, finiteHarmonic_eq_neg_comp p hp5, Polynomial.eval_neg, Polynomial.eval_comp]
    simp [show (1 : ZMod p) - 2 = -1 by ring, finiteDilog_eval_neg_one p hp5]
  -- A residue in the kernel is a multiple of `p`, so multiplication by `p²` kills it.
  have hv : (x.val : ZMod p) = 0 := by
    rwa [← map_natCast f, ZMod.natCast_zmod_val]
  obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hv
  change (p : R p) ^ 2 * x = 0
  rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_mul, ← mul_assoc, ← pow_succ, cube_zero p,
    zero_mul]

private theorem entry_affine {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (s : ℕ) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix (p - 1 + s * p) (p - 1) 1 : R p) =
      1 + (s : R p) * ∑ j ∈ range (p - 1),
        (-(p : R p) + (p : R p) ^ 2 * harmonicMod (p ^ 3) (j + 1)) * delannoyWeight p j := by
  rw [MetaMathlibExt.DelannoyConstructions.delannoy_eq_sum_choose_mul_choose_two_pow]
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hs' := Nat.pos_of_ne_zero hs
  have hsp : p ≤ s * p := Nat.le_mul_of_pos_left p hs'
  rw [min_eq_left (show p - 1 ≤ s * p by omega), Int.cast_sum, sum_range_succ']
  simp only [Nat.choose_zero_right, Int.cast_mul, Int.cast_natCast, Int.cast_pow,
    Int.cast_ofNat, pow_zero, Nat.cast_one, mul_one]
  rw [sum_congr rfl (fun j hj => summand_expansion hp hp5 hs' (mem_range.mp hj)),
    sum_add_distrib, ← mul_sum, ← mul_sum, mul_assoc, lagged_sum_zero hp hp5, mul_zero, add_zero]
  simp [add_comm]

/-- **Delannoy triangle entry $T(np-1, p-1; 1)$ modulo $p^3$.** Let $p \ge 5$ be a prime and
$n \ge 1$ a natural number, let $q_p(2) = (2^{p-1} - 1)/p$ be the Fermat quotient of $2$, and
let $T(a, b; 1)$ denote the entry of the ordinary Riordan Pascal-like triangle with $r = 1$
(the Delannoy triangle). Then
$$T(np - 1, p - 1; 1) \equiv 1 + (n - 1)\,p\,q_p(2)\,\bigl(2 - p\,q_p(2)\bigr) \pmod{p^3}.$$

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Theorem 4. -/
public theorem delannoy_mul_sub_one (p n : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (h2p : IsCoprime (2 : ℤ) (p : ℤ)) :
    (MetaMathlibExt.ordinaryRiordanPascalLikeMatrix
          (n * p - 1) (p - 1) 1 : ZMod (p ^ 3)) =
      1 + ((n : ZMod (p ^ 3)) - 1) * (p : ZMod (p ^ 3)) *
          (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3)) *
        (2 - (p : ZMod (p ^ 3)) *
          (Int.fermatQuotient p hp 2 h2p : ZMod (p ^ 3))) := by
  have hrow : n * p - 1 = p - 1 + (n - 1) * p := by
    have hsplit : n * p = (n - 1) * p + p := by
      simpa only [Nat.add_mul, one_mul] using congrArg (· * p) (Nat.sub_add_cancel hn).symm
    omega
  have htwo := entry_affine hp hp5 1
  simp only [Nat.cast_one, one_mul] at htwo
  rw [show p - 1 + p = 2 * p - 1 by omega] at htwo
  rw [(delannoy_two_mul p hp hp5 h2p).2, add_sub_assoc] at htwo
  have hcoef := add_left_cancel htwo
  rw [hrow, entry_affine hp hp5, ← hcoef, Nat.cast_sub hn, Nat.cast_one]
  ring

end MathlibExt.NumberTheory.DelannoyTriangleWanted
