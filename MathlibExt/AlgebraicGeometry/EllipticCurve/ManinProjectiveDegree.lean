/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.RatFunc.Degree

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Projective numerator degrees for Manin's proof

This file isolates the characteristic-free commutative algebra used to recover the numerator
degrees of two rational functions from primitive projective product and sum coordinates.
-/

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

noncomputable section

open Polynomial

universe u

variable {K : Type u} [Field K]

private local instance : DecidableEq K := Classical.decEq K
private local instance : DecidableEq K[X] := Classical.decEq K[X]

/-- **Primitive triple of polynomials.** Let $K$ be a field. Polynomials $a, b, c \in K[X]$
form a primitive triple when they generate the unit ideal of $K[X]$, that is, when there are
$u, v, w \in K[X]$ with $ua + vb + wc = 1$. -/
def PrimitiveTriple (a b c : K[X]) : Prop :=
  ∃ u v w : K[X], u * a + v * b + w * c = 1

private lemma common_dvd_isUnit_of_isCoprime {p a b : K[X]}
    (hab : IsCoprime a b) (hpa : p ∣ a) (hpb : p ∣ b) : IsUnit p := by
  rcases hpa with ⟨a', ha⟩
  rcases hpb with ⟨b', hb⟩
  rcases hab with ⟨u, v, huv⟩
  refine isUnit_iff_exists_inv.mpr ⟨u * a' + v * b', ?_⟩
  calc
    p * (u * a' + v * b') = u * (p * a') + v * (p * b') := by ring
    _ = 1 := by rw [← ha, ← hb, huv]

private lemma gcd_three_isUnit_of_no_common_irreducible {a b c : K[X]}
    (hc : c ≠ 0)
    (h : ∀ p : K[X], Irreducible p → p ∣ a → p ∣ b → p ∣ c → False) :
    IsUnit (EuclideanDomain.gcd a (EuclideanDomain.gcd b c)) := by
  by_contra hunit
  have hg0 : EuclideanDomain.gcd a (EuclideanDomain.gcd b c) ≠ 0 := by
    simp only [ne_eq, EuclideanDomain.gcd_eq_zero_iff]
    tauto
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor hunit hg0
  apply h p hp
  · exact hpg.trans (EuclideanDomain.gcd_dvd_left _ _)
  · exact hpg.trans ((EuclideanDomain.gcd_dvd_right _ _).trans
      (EuclideanDomain.gcd_dvd_left _ _))
  · exact hpg.trans ((EuclideanDomain.gcd_dvd_right _ _).trans
      (EuclideanDomain.gcd_dvd_right _ _))

/-- **Polynomials with no common irreducible factor form a primitive triple.** Let $K$ be a
field and let $a, b, c \in K[X]$ with $c \neq 0$. If no irreducible polynomial in $K[X]$
divides all of $a$, $b$ and $c$, then $a, b, c$ form a primitive triple: there are
$u, v, w \in K[X]$ with $ua + vb + wc = 1$. -/
theorem primitiveTriple_of_no_common_irreducible {a b c : K[X]}
    (hc : c ≠ 0)
    (h : ∀ p : K[X], Irreducible p → p ∣ a → p ∣ b → p ∣ c → False) :
    PrimitiveTriple a b c := by
  have hgcd := gcd_three_isUnit_of_no_common_irreducible hc h
  rcases isUnit_iff_exists_inv.mp hgcd with ⟨z, hz⟩
  refine ⟨EuclideanDomain.gcdA a (EuclideanDomain.gcd b c) * z,
    EuclideanDomain.gcdA b c *
      EuclideanDomain.gcdB a (EuclideanDomain.gcd b c) * z,
    EuclideanDomain.gcdB b c *
      EuclideanDomain.gcdB a (EuclideanDomain.gcd b c) * z, ?_⟩
  rw [← hz]
  rw [EuclideanDomain.gcd_eq_gcd_ab a (EuclideanDomain.gcd b c),
    EuclideanDomain.gcd_eq_gcd_ab b c]
  ring

private lemma primitiveTriple_linearCombination {a b c : K[X]}
    (h : PrimitiveTriple a b c) :
    ∃ u v w : K[X], u * a + v * b + w * c = 1 := by
  exact h

private lemma dvd_of_primitiveTriple {a b c p x : K[X]}
    (h : PrimitiveTriple a b c)
    (ha : p ∣ x * a) (hb : p ∣ x * b) (hc : p ∣ x * c) : p ∣ x := by
  obtain ⟨u, v, w, huv⟩ := primitiveTriple_linearCombination h
  have hdvd : p ∣ u * (x * a) + v * (x * b) + w * (x * c) :=
    ((ha.mul_left u).add (hb.mul_left v)).add (hc.mul_left w)
  have heq : u * (x * a) + v * (x * b) + w * (x * c) = x := by
    calc
      u * (x * a) + v * (x * b) + w * (x * c) =
          x * (u * a + v * b + w * c) := by ring
      _ = x := by rw [huv, mul_one]
  rwa [heq] at hdvd

private lemma primitive_numeratorTriple {a b c d : K[X]}
    (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hb : b ≠ 0) (hd : d ≠ 0) :
    PrimitiveTriple (a * c) (a * d + b * c) (b * d) := by
  apply primitiveTriple_of_no_common_irreducible (mul_ne_zero hb hd)
  intro p hp hpac hpsum hpbd
  have hprime := hp.prime
  rcases hprime.dvd_mul.mp hpac with hpa | hpc
  · rcases hprime.dvd_mul.mp hpbd with hpb | hpd
    · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
    · have hpad : p ∣ a * d := hpa.mul_right d
      have hpbc : p ∣ b * c := by
        have hdvd := hpsum.sub hpad
        have heq : (a * d + b * c) - a * d = b * c := by ring
        rwa [heq] at hdvd
      rcases hprime.dvd_mul.mp hpbc with hpb | hpc
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)
  · rcases hprime.dvd_mul.mp hpbd with hpb | hpd
    · have hpbc : p ∣ b * c := hpb.mul_right c
      have hpad : p ∣ a * d := by
        have hdvd := hpsum.sub hpbc
        have heq : (a * d + b * c) - b * c = a * d := by ring
        rwa [heq] at hdvd
      rcases hprime.dvd_mul.mp hpad with hpa | hpd
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hab hpa hpb)
      · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)
    · exact hp.not_isUnit (common_dvd_isUnit_of_isCoprime hcd hpc hpd)

private lemma ratFunc_num_denom_mul (x y : RatFunc K) :
    algebraMap K[X] (RatFunc K) (x.num * y.num) /
        algebraMap K[X] (RatFunc K) (x.denom * y.denom) = x * y := by
  rw [map_mul, map_mul, ← div_mul_div_comm]
  rw [RatFunc.num_div_denom, RatFunc.num_div_denom]

private lemma ratFunc_num_denom_add (x y : RatFunc K) :
    algebraMap K[X] (RatFunc K)
          (x.num * y.denom + x.denom * y.num) /
        algebraMap K[X] (RatFunc K) (x.denom * y.denom) = x + y := by
  rw [map_add, map_mul, map_mul, map_mul]
  calc
    _ = algebraMap K[X] (RatFunc K) x.num /
          algebraMap K[X] (RatFunc K) x.denom +
        algebraMap K[X] (RatFunc K) y.num /
          algebraMap K[X] (RatFunc K) y.denom := by
      field_simp [RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x),
        RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero y)]
    _ = x + y := by
      rw [RatFunc.num_div_denom, RatFunc.num_div_denom]

/-- **Numerator degrees from a primitive presentation of product and sum.** Let $K$ be a field,
let $u, v, h \in K[X]$ form a primitive triple with $h \neq 0$, and let $x, y \in K(X)$ be
nonzero rational functions with $u/h = xy$ and $v/h = x + y$ in $K(X)$. Then
$\deg u = \deg \operatorname{num}(x) + \deg \operatorname{num}(y)$, where $\operatorname{num}$
denotes the numerator of a rational function written in lowest terms. -/
theorem projective_first_natDegree {u v h : K[X]}
    (hprimitive : PrimitiveTriple u v h)
    (hh : h ≠ 0) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hprod : algebraMap K[X] (RatFunc K) u /
      algebraMap K[X] (RatFunc K) h = x * y)
    (hsum : algebraMap K[X] (RatFunc K) v /
      algebraMap K[X] (RatFunc K) h = x + y) :
    u.natDegree = x.num.natDegree + y.num.natDegree := by
  let a := x.num
  let b := x.denom
  let c := y.num
  let d := y.denom
  have ha : a ≠ 0 := RatFunc.num_ne_zero hx
  have hb : b ≠ 0 := RatFunc.denom_ne_zero x
  have hc : c ≠ 0 := RatFunc.num_ne_zero hy
  have hd : d ≠ 0 := RatFunc.denom_ne_zero y
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  have hfractionProd :
      algebraMap K[X] (RatFunc K) (a * c) /
          algebraMap K[X] (RatFunc K) (b * d) =
        algebraMap K[X] (RatFunc K) u /
          algebraMap K[X] (RatFunc K) h := by
    rw [ratFunc_num_denom_mul]
    exact hprod.symm
  have hfractionSum :
      algebraMap K[X] (RatFunc K) (a * d + b * c) /
          algebraMap K[X] (RatFunc K) (b * d) =
        algebraMap K[X] (RatFunc K) v /
          algebraMap K[X] (RatFunc K) h := by
    rw [ratFunc_num_denom_add]
    exact hsum.symm
  have hcross0 : (a * c) * h = u * (b * d) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul] using
      (div_eq_div_iff (RatFunc.algebraMap_ne_zero hbd)
        (RatFunc.algebraMap_ne_zero hh)).mp hfractionProd
  have hcross1 : (a * d + b * c) * h = v * (b * d) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul] using
      (div_eq_div_iff (RatFunc.algebraMap_ne_zero hbd)
        (RatFunc.algebraMap_ne_zero hh)).mp hfractionSum
  have hnumPrimitive :
      PrimitiveTriple (a * c) (a * d + b * c) (b * d) :=
    primitive_numeratorTriple (RatFunc.isCoprime_num_denom x)
      (RatFunc.isCoprime_num_denom y) hb hd
  have hh_dvd_bd : h ∣ b * d := by
    apply dvd_of_primitiveTriple hprimitive
    · refine ⟨a * c, ?_⟩
      calc
        (b * d) * u = u * (b * d) := by ring
        _ = (a * c) * h := hcross0.symm
        _ = h * (a * c) := by ring
    · refine ⟨a * d + b * c, ?_⟩
      calc
        (b * d) * v = v * (b * d) := by ring
        _ = (a * d + b * c) * h := hcross1.symm
        _ = h * (a * d + b * c) := by ring
    · exact ⟨b * d, by ring⟩
  have hbd_dvd_h : b * d ∣ h := by
    apply dvd_of_primitiveTriple hnumPrimitive
    · refine ⟨u, ?_⟩
      calc
        h * (a * c) = (a * c) * h := by ring
        _ = u * (b * d) := hcross0
        _ = (b * d) * u := by ring
    · refine ⟨v, ?_⟩
      calc
        h * (a * d + b * c) = (a * d + b * c) * h := by ring
        _ = v * (b * d) := hcross1
        _ = (b * d) * v := by ring
    · exact ⟨h, by ring⟩
  have hdegreeH : h.natDegree = (b * d).natDegree := by
    have hdegree := Polynomial.degree_eq_degree_of_associated
      (associated_of_dvd_dvd hh_dvd_bd hbd_dvd_h)
    rw [degree_eq_natDegree hh, degree_eq_natDegree hbd] at hdegree
    exact WithBot.coe_eq_coe.mp hdegree
  have hu : u ≠ 0 := by
    intro hu
    rw [hu, zero_mul] at hcross0
    exact mul_ne_zero (mul_ne_zero ha hc) hh hcross0
  have hdegreeCross := congrArg Polynomial.natDegree hcross0
  rw [Polynomial.natDegree_mul (mul_ne_zero ha hc) hh,
    Polynomial.natDegree_mul hu hbd,
    Polynomial.natDegree_mul ha hc,
    Polynomial.natDegree_mul hb hd] at hdegreeCross
  rw [Polynomial.natDegree_mul hb hd] at hdegreeH
  dsimp only [a, b, c, d] at hdegreeCross hdegreeH ⊢
  omega

end

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
