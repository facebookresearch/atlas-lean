/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination

/-!
# A binomial expansion modulo a prime cube

The harmonic sums of orders one and two give the linear and quadratic terms of
`choose_mul_sub_one_mod`, the expansion modulo `p ^ 3` for odd primes `p`, integer
multipliers `s`, and coefficient indices `1 ≤ k ≤ p - 1`.

## References

* Chahinaze Djadi and Hacène Belbachir, *Congruence Properties for the Delannoy Triangle
  Coefficients*, Journal of Integer Sequences 29 (2026), Article 26.5.2, Lemma 5.
-/

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

/-- **Harmonic numbers modulo $m$.** For natural numbers $m$ and $k$, the harmonic number
$H_k$ modulo $m$ is the residue $\sum_{i=1}^{k} i^{-1}$ in $\mathbb{Z}/m\mathbb{Z}$, where
$i^{-1}$ is the inverse of $i$ modulo $m$ when $i$ is coprime to $m$; for other $i$ it is the
conventional value that Mathlib assigns to the inverse of a non-unit. -/
@[expose] public def harmonicMod (m k : ℕ) : ZMod m :=
  ∑ i ∈ Finset.Icc 1 k, (i : ZMod m)⁻¹

/-- **Finite sum for a harmonic number modulo $m$.** For natural numbers $m$ and $k$,
$H_k$ modulo $m$ is the sum of the inverses of $1, \ldots, k$ in $\mathbb{Z}/m\mathbb{Z}$,
using the inverse convention of `ZMod` for nonunits. -/
public theorem harmonicMod_eq_sum (m k : ℕ) :
    harmonicMod m k = ∑ i ∈ Finset.Icc 1 k, (i : ZMod m)⁻¹ := rfl

/-- **Harmonic numbers of order two modulo $m$.** For natural numbers $m$ and $k$, the
harmonic number $H_{k,2}$ of order two modulo $m$ is the residue $\sum_{i=1}^{k} (i^2)^{-1}$
in $\mathbb{Z}/m\mathbb{Z}$, where $(i^2)^{-1}$ is the inverse of $i^2$ modulo $m$ when $i$ is
coprime to $m$; for other $i$ it is the conventional value that Mathlib assigns to the
inverse of a non-unit. -/
@[expose] public def harmonic2Mod (m k : ℕ) : ZMod m :=
  ∑ i ∈ Finset.Icc 1 k, ((i : ZMod m) ^ 2)⁻¹

-- Inserting one factor updates both power sums. The only discarded term is cubic in x.
private theorem prod_one_sub_of_cube_eq_zero {R ι : Type*} [CommRing R]
    (x b : R) (hx : x ^ 3 = 0) (hb : 2 * b = 1) (t : Finset ι) (f : ι → R) :
    ∏ i ∈ t, (1 - x * f i) = 1 - x * ∑ i ∈ t, f i +
      x ^ 2 * b * ((∑ i ∈ t, f i) ^ 2 - ∑ i ∈ t, f i ^ 2) := by
  induction t using Finset.cons_induction_on with
  | empty => simp
  | cons a t ha ih =>
    simp only [Finset.prod_cons, Finset.sum_cons, ih]
    linear_combination
      -(b * f a * ((∑ i ∈ t, f i) ^ 2 - ∑ i ∈ t, f i ^ 2)) * hx -
      x ^ 2 * f a * (∑ i ∈ t, f i) * hb

/-- **Expansion of $\binom{sp-1}{k}$ modulo $p^3$.** Let $p$ be an odd prime, $s$ an integer
and $k$ a natural number with $1 \le k \le p - 1$, and let $H_k = \sum_{i=1}^{k} i^{-1}$ and
$H_{k,2} = \sum_{i=1}^{k} (i^2)^{-1}$ be the harmonic numbers of orders one and two in
$\mathbb{Z}/p^3\mathbb{Z}$. Then in $\mathbb{Z}/p^3\mathbb{Z}$
$$
\frac{1}{k!} \prod_{i=1}^{k} (sp - i) =
(-1)^k \Bigl(1 - sp\,H_k + \frac{s^2 p^2}{2} \bigl(H_k^2 - H_{k,2}\bigr)\Bigr),
$$
where $1/k!$ and $1/2$ are inverses in $\mathbb{Z}/p^3\mathbb{Z}$; the left side is the
binomial coefficient $\binom{sp-1}{k}$.

Source: Chahinaze Djadi and Hacène Belbachir,
"Congruence Properties for the Delannoy Triangle
Coefficients", Lemma 5. -/
public theorem choose_mul_sub_one_mod (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (s : ℤ) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ p - 1) :
    (∏ i ∈ Finset.Icc 1 k,
        ((s * (p : ℤ) - (i : ℤ)) : ZMod (p ^ 3))) *
        ((Nat.factorial k : ZMod (p ^ 3)))⁻¹ =
      (-1) ^ k * (1 - (s : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) *
          harmonicMod (p ^ 3) k +
        (s : ZMod (p ^ 3)) ^ 2 * (p : ZMod (p ^ 3)) ^ 2 *
          (2 : ZMod (p ^ 3))⁻¹ *
          (harmonicMod (p ^ 3) k ^ 2 - harmonic2Mod (p ^ 3) k)) := by
  let x : ZMod (p ^ 3) := s * p
  let t := Finset.Icc 1 k
  have hp3 : 2 < p := Nat.two_lt_of_ne hp.ne_zero hp.ne_one hp2
  have hkp : k < p := by omega
  have unit_of_lt (i : ℕ) (hi : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ 3)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).2 (Nat.not_dvd_of_pos_of_lt hi hip)
  have unit_mem (i : ℕ) (hi : i ∈ t) : IsUnit (i : ZMod (p ^ 3)) :=
    unit_of_lt i (Finset.mem_Icc.mp hi).1 (lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 hkp)
  have htwo : (2 : ZMod (p ^ 3)) * 2⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ (unit_of_lt 2 (by decide) hp3)
  have hx : x ^ 3 = 0 := by simp [x, mul_pow, ← Nat.cast_pow]
  have hprod : ∏ i ∈ t, (x - i) =
      (∏ i ∈ t, -(i : ZMod (p ^ 3))) * ∏ i ∈ t, (1 - x * (i : ZMod (p ^ 3))⁻¹) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    linear_combination -x * ZMod.mul_inv_of_unit _ (unit_mem i hi)
  have hfac : ∏ i ∈ t, i = k.factorial := by
    dsimp only [t]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    simp [Nat.add_comm 1]
  have hfinv := ZMod.coe_mul_inv_eq_one k.factorial
    ((hp.coprime_factorial_of_lt hkp).symm.pow_right 3)
  have hsquares : (∑ i ∈ t, ((i : ZMod (p ^ 3))⁻¹) ^ 2) = harmonic2Mod (p ^ 3) k := by
    apply Finset.sum_congr rfl
    intro i hi
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    rw [← mul_pow, ZMod.mul_inv_of_unit _ (unit_mem i hi), one_pow]
  simp only [Int.cast_natCast]
  change (∏ i ∈ t, (x - i)) * _ = _
  rw [hprod, Finset.prod_neg, ← Nat.cast_prod, hfac,
    prod_one_sub_of_cube_eq_zero x _ hx htwo, hsquares]
  have hcard : t.card = k := by simp [t]
  rw [hcard, mul_right_comm (_ * _) _ (_⁻¹), mul_assoc _ _ (_⁻¹), hfinv, mul_one]
  simp only [x, mul_pow]
  rfl

end MathlibExt.NumberTheory.DelannoyTriangleWanted
