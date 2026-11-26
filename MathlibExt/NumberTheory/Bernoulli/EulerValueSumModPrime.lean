/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPolynomialBinomialAverage
public import MathlibExt.NumberTheory.RatResidue
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.Integers

/-!
# A sum of Euler polynomial values modulo a prime

The shift identity for Euler polynomials gives integrality at an odd prime by descending
coefficient comparison. After reduction, its alternating sum telescopes. Swapping the two
finite sums then leaves a geometric sum, with one exceptional term.

## References

* Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli Numbers and Its
  Applications*, INTEGERS 26 (2026), Article A120, pp. 1–15, Corollary 4, equation (25).
  We give a proof via the shift identity rather than the paper's Bernoulli number argument.
* NIST Digital Library of Mathematical Functions, §24.4(i), equation (24.4.2), for the
  Euler polynomial shift identity.
-/

namespace MetaMathlibExt

open Finset Polynomial MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

namespace sum_euler_eval_zero_mod_prime

variable {p : ℕ} [Fact p.Prime]

private noncomputable abbrev primeIntegral (p : ℕ) [Fact p.Prime] : Subring ℚ :=
  (Rat.padicValuation p).integer

private lemma not_dvd_two (hp2 : p ≠ 2) : ¬p ∣ 2 :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)

private lemma half_mem (hp2 : p ≠ 2) : (1 / 2 : ℚ) ∈ primeIntegral p := by
  rw [Valuation.mem_integer_iff, Rat.padicValuation_le_one_iff,
    show (1 / 2 : ℚ).den = 2 by norm_num]
  exact not_dvd_two hp2

/-- On `p`-integral rationals the rational cast is a ring homomorphism. -/
private noncomputable def reduce (p : ℕ) [Fact p.Prime] : primeIntegral p →+* ZMod p where
  toFun x := ((x : ℚ) : ZMod p)
  map_zero' := Rat.cast_zero
  map_one' := Rat.cast_one
  map_add' x y := Rat.cast_add_of_ne_zero (den_ne_zero x) (den_ne_zero y)
  map_mul' x y := Rat.cast_mul_of_ne_zero (den_ne_zero x) (den_ne_zero y)
where
  den_ne_zero (x : primeIntegral p) : ((x : ℚ).den : ZMod p) ≠ 0 :=
    mt (ZMod.natCast_eq_zero_iff _ _).mp (Rat.padicValuation_le_one_iff.mp x.property)

private lemma ratResidue_eq_ratCast (x : ℚ) : ratResidue p x = (x : ZMod p) := by
  rw [Rat.cast_def, div_eq_mul_inv]
  rfl

-- In the coefficient of index k, the translation contributes the original coefficient
-- plus a sum involving only strictly higher indices.
private lemma coeff_taylor_one (f : ℚ[X]) (k : ℕ) :
    (taylor 1 f).coeff k = f.coeff k + ∑ i ∈ range f.natDegree,
      ((k + (i + 1)).choose k : ℚ) * f.coeff (k + (i + 1)) := by
  have hdeg : (hasseDeriv k f).natDegree < f.natDegree + 1 :=
    (natDegree_hasseDeriv_le f k).trans_lt (by omega)
  rw [taylor_coeff, eval_eq_sum_range' hdeg, sum_range_succ']
  simp only [one_pow, mul_one, hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun i _ => by rw [Nat.add_comm (i + 1) k]

private lemma coeff_eulerPoly_mem (hp2 : p ≠ 2) (n k : ℕ) :
    (eulerPoly n).coeff k ∈ primeIntegral p := by
  let f := eulerPoly n
  suffices ∀ d k, f.natDegree < k + d → f.coeff k ∈ primeIntegral p from
    this (f.natDegree + 1) k (by omega)
  intro d
  induction d with
  | zero =>
    intro k hk
    rw [coeff_eq_zero_of_natDegree_lt (by simpa using hk)]
    exact (primeIntegral p).zero_mem
  | succ d ih =>
    intro k hk
    have hs := congrArg (fun g : ℚ[X] => g.coeff k) (eulerPoly_shift n)
    change (taylor 1 f + f).coeff k = _ at hs
    rw [coeff_add, coeff_taylor_one] at hs
    have hcoeff : f.coeff k = (1 / 2 : ℚ) * (((2 : ℚ) • (X ^ n : ℚ[X])).coeff k -
        ∑ i ∈ range f.natDegree, ((k + (i + 1)).choose k : ℚ) * f.coeff (k + (i + 1))) := by
      linarith only [hs]
    rw [hcoeff]
    refine (primeIntegral p).mul_mem (half_mem hp2) ((primeIntegral p).sub_mem ?_ ?_)
    · rw [smul_eq_C_mul, coeff_C_mul_X_pow]
      split <;> simp
    · exact (primeIntegral p).sum_mem fun i _ => (primeIntegral p).mul_mem
        (natCast_mem _ _) (ih _ (by omega))

private lemma exists_eulerPoly_lift (hp2 : p ≠ 2) (n : ℕ) :
    ∃ f : (primeIntegral p)[X], f.map (primeIntegral p).subtype = eulerPoly n := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  exact fun k => ⟨⟨_, coeff_eulerPoly_mem hp2 n k⟩, rfl⟩

private lemma sum_alternating_adjacent {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    ∑ a ∈ range n, (-1 : R) ^ a * (f (a + 1) + f a) = f 0 - (-1) ^ n * f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring

private lemma eval_zero_eq_alternating_powers (h2 : (2 : ZMod p) ≠ 0) (hodd : Odd p)
    {f : (ZMod p)[X]} {n : ℕ} (hf : taylor 1 f + f = C 2 * X ^ n) :
    f.eval 0 = ∑ a ∈ range p, (-1 : ZMod p) ^ a * (a : ZMod p) ^ n := by
  have hstep (a : ℕ) : f.eval ((a + 1 : ℕ) : ZMod p) + f.eval (a : ZMod p) =
      2 * (a : ZMod p) ^ n := by
    simpa only [eval_add, taylor_eval, Nat.cast_succ, eval_mul, eval_C, eval_pow, eval_X]
      using congrArg (eval (a : ZMod p)) hf
  have ht := sum_alternating_adjacent (fun a => f.eval (a : ZMod p)) p
  simp only [hstep, ZMod.natCast_self, Nat.cast_zero, hodd.neg_one_pow] at ht
  rw [show (∑ a ∈ range p, (-1 : ZMod p) ^ a * (2 * (a : ZMod p) ^ n)) =
    2 * ∑ a ∈ range p, (-1 : ZMod p) ^ a * (a : ZMod p) ^ n by
      rw [mul_sum]; exact sum_congr rfl fun a _ => by ring] at ht
  exact mul_left_cancel₀ h2 (by linear_combination -ht)

private lemma sum_alternating_linear (h2 : (2 : ZMod p) ≠ 0) (hodd : Odd p) :
    ∑ a ∈ range p, (-1 : ZMod p) ^ a * ((a : ZMod p) + 1) = 1 / 2 := by
  let f (a : ℕ) : ZMod p := ((a : ZMod p) + 1 / 2) / 2
  have hstep (a : ℕ) : f (a + 1) + f a = (a : ZMod p) + 1 := by
    simp only [f, Nat.cast_succ]
    field_simp
    ring
  have ht := sum_alternating_adjacent f p
  rw [show f p = f 0 by simp [f], hodd.neg_one_pow] at ht
  simp only [hstep] at ht
  rw [ht]
  simp only [f, Nat.cast_zero, zero_add]
  field_simp
  ring

private lemma sum_alternating_geom (h2 : (2 : ZMod p) ≠ 0) (hodd : Odd p) :
    ∑ a ∈ range p, (-1 : ZMod p) ^ a * (∑ j ∈ range (p + 1), (a : ZMod p) ^ j) = 3 / 2 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hterm (a : ℕ) (ha : a ∈ range p) :
      (-1 : ZMod p) ^ a * (∑ j ∈ range (p + 1), (a : ZMod p) ^ j) =
        (-1 : ZMod p) ^ a * ((a : ZMod p) + 1) + if a = 1 then 1 else 0 := by
    by_cases ha1 : a = 1
    · subst a
      simp [Nat.cast_add]
    · have ha1' : (a : ZMod p) ≠ 1 := by
        intro h
        apply ha1
        simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha), ← Nat.cast_one (R := ZMod p),
          ZMod.val_natCast_of_lt hp1] using congrArg ZMod.val h
      rw [geom_sum_eq ha1', pow_succ, ZMod.pow_card, ite_eq_right ha1, add_zero]
      congr 1
      apply (div_eq_iff (sub_ne_zero.mpr ha1')).2
      ring
  calc
    _ = ∑ a ∈ range p, ((-1 : ZMod p) ^ a * ((a : ZMod p) + 1) +
        if a = 1 then 1 else 0) := sum_congr rfl hterm
    _ = _ := by
      rw [sum_add_distrib, sum_alternating_linear h2 hodd]
      simp only [sum_ite_eq', mem_range.mpr hp1, ite_true]
      field_simp
      ring

end sum_euler_eval_zero_mod_prime

open sum_euler_eval_zero_mod_prime

/--
**The congruence $\sum_{j=0}^{p} E_j(0) \equiv 3/2 \pmod p$.** Let $E_j(x)$ denote the Euler
polynomials. For every odd prime $p$, the rational number $S = E_0(0) + E_1(0) + \dots + E_p(0)$
has denominator not divisible by $p$, and its residue modulo $p$ (its numerator times the
inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $3 \cdot 2^{-1}$.

The values $E_j(0)$ are the Euler numbers of the source; they come from the generating function
$2e^{xt}/(e^t + 1)$ and begin $1, -\tfrac12, 0, \tfrac14$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (25).
-/
public theorem sum_euler_eval_zero_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0).den ∧
      ratResidue p (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0) =
        ratResidue p (3 / 2) := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff 2 p).mp (not_dvd_two hp2)
  have hodd := hp.odd_of_ne_two hp2
  choose F hF using exists_eulerPoly_lift hp2
  let S : primeIntegral p := ∑ j ∈ range (p + 1), (F j).eval 0
  have hS : (S : ℚ) = ∑ j ∈ range (p + 1), (eulerPoly j).eval 0 := by
    change (primeIntegral p).subtype (∑ j ∈ range (p + 1), (F j).eval 0) = _
    rw [map_sum]
    exact sum_congr rfl fun j _ => by rw [← eval_map_apply, hF, map_zero]
  rw [← hS, ratResidue_eq_ratCast, ratResidue_eq_ratCast]
  refine ⟨Rat.padicValuation_le_one_iff.mp S.property, ?_⟩
  have hshift (j : ℕ) : taylor 1 (F j) + F j = 2 * X ^ j := by
    apply Polynomial.map_injective (primeIntegral p).subtype Subtype.val_injective
    simpa [hF, smul_eq_C_mul, C_ofNat] using eulerPoly_shift j
  have hmod (j : ℕ) : taylor 1 ((F j).map (reduce p)) + (F j).map (reduce p) = C 2 * X ^ j := by
    simpa [C_ofNat] using congrArg (Polynomial.map (reduce p)) (hshift j)
  change reduce p S = ((3 / 2 : ℚ) : ZMod p)
  rw [Rat.cast_div_of_ne_zero (by simp) (by simpa using h2)]
  simp only [Rat.cast_ofNat, S, map_sum]
  calc
    _ = ∑ j ∈ range (p + 1), ((F j).map (reduce p)).eval 0 :=
      sum_congr rfl fun j _ => by simpa only [map_zero] using (eval_map_apply (reduce p) 0).symm
    _ = ∑ j ∈ range (p + 1), ∑ a ∈ range p, (-1 : ZMod p) ^ a * (a : ZMod p) ^ j :=
      sum_congr rfl fun j _ => eval_zero_eq_alternating_powers h2 hodd (hmod j)
    _ = _ := by
      rw [sum_comm]
      simp only [← mul_sum]
      exact sum_alternating_geom h2 hodd

end MetaMathlibExt
