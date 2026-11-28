/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Ring

/-!
# Square compositions of zero-one polynomials

This file defines zero-one polynomials and proves the modulo four congruence
for a reducible square composition of an irreducible zero-one polynomial.
-/

set_option autoImplicit false

@[expose] public section

open Polynomial

namespace MathlibExt.Algebra.PalindromicZeroOneWanted

/-- **0,1-polynomial.** A polynomial $f \in \mathbb{Z}[x]$ is a *$0,1$-polynomial* if every
coefficient of $f$ is $0$ or $1$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
def IsZeroOnePoly (f : ℤ[X]) : Prop :=
  ∀ n : ℕ, f.coeff n = 0 ∨ f.coeff n = 1

/-- **Characterization of 0,1-polynomials.** A polynomial $f \in \mathbb{Z}[x]$ is a
$0,1$-polynomial if and only if, for every $n \ge 0$, the coefficient of $x^n$ in $f$ is
$0$ or $1$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Section 1
(terminology). -/
theorem isZeroOnePoly_iff (f : ℤ[X]) :
    IsZeroOnePoly f ↔ ∀ n : ℕ, f.coeff n = 0 ∨ f.coeff n = 1 :=
  Iff.rfl

/-- Over a characteristic-zero domain, a polynomial fixed by `X ↦ -X` has only even powers.
Thus contracting by two and expanding again recovers the polynomial. -/
theorem _root_.Polynomial.expand_contract_of_comp_neg_X_eq {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {p : R[X]} (hp : p.comp (-X) = p) : expand R 2 (p.contract 2) = p := by
  ext n
  rw [coeff_expand (by decide : 0 < 2), coeff_contract two_ne_zero]
  split_ifs with hn
  · rw [Nat.div_mul_cancel hn]
  · have hodd : Odd n := Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp hn)
    have h := congrArg (fun q : R[X] => q.coeff n) hp
    rw [show (-X : R[X]) = C (-1) * X by simp, comp_C_mul_X_coeff,
      hodd.neg_one_pow, mul_neg_one] at h
    have hzero : (2 : R) * p.coeff n = 0 := by
      simpa [two_mul] using congrArg (fun r : R => r + p.coeff n) h.symm
    exact ((mul_eq_zero.mp hzero).resolve_left two_ne_zero).symm

private theorem eq_of_dvd_of_sq_eq_mul {f a b : ℤ[X]} (hirr : Irreducible f)
    (hf0 : f.coeff 0 = 1) (ha0 : a.coeff 0 = 1) (hb : ¬ IsUnit b)
    (hab : f ^ 2 = a * b) (hdiv : f ∣ a) : a = f := by
  obtain ⟨u, rfl⟩ := hdiv
  have hfu : f = u * b :=
    mul_left_cancel₀ hirr.ne_zero (by simpa only [pow_two, mul_assoc] using hab)
  have hu := (hirr.isUnit_or_isUnit hfu).resolve_right hb
  obtain ⟨z, -, rfl⟩ := Polynomial.isUnit_iff.mp hu
  have hz : z = 1 := by simpa [coeff_mul_C, hf0] using ha0
  simp [hz]

private theorem exists_comp_neg_X_factor {f : ℤ[X]} (hirr : Irreducible f)
    (hf0 : f.coeff 0 = 1) (hpos : 0 < f.natDegree)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    ∃ g : ℤ[X], f.comp (X ^ 2) = g * g.comp (-X) := by
  have hnonunit : ¬ IsUnit (f.comp (X ^ 2)) := by
    rw [← expand_eq_comp_X_pow]
    apply not_isUnit_of_natDegree_pos
    rw [natDegree_expand]
    exact Nat.mul_pos hpos (by decide)
  obtain ⟨a, b, ha, hb, hab⟩ := (irreducible_or_factor hnonunit).resolve_left hred
  have hab0 : a.coeff 0 * b.coeff 0 = 1 := by
    simpa [← expand_eq_comp_X_pow, coeff_expand (by decide : 0 < 2), mul_coeff_zero, hf0]
      using (congrArg (fun p : ℤ[X] => p.coeff 0) hab).symm
  have hunit : IsUnit (a.coeff 0 * b.coeff 0) := hab0.symm ▸ isUnit_one
  let N (p : ℤ[X]) : ℤ[X] := (p * p.comp (-X)).contract 2
  have hN (p : ℤ[X]) : expand ℤ 2 (N p) = p * p.comp (-X) := by
    apply expand_contract_of_comp_neg_X_eq
    rw [mul_comp, comp_neg_X_comp_neg_X, mul_comm]
  have hN0 (p : ℤ[X]) (hp : IsUnit (p.coeff 0)) : (N p).coeff 0 = 1 := by
    have hconst : (p.comp (-X)).coeff 0 = p.coeff 0 := by
      simp [coeff_zero_eq_eval_zero, eval_comp]
    change ((p * p.comp (-X)).contract 2).coeff 0 = 1
    rw [coeff_contract (by decide : 2 ≠ 0), zero_mul, mul_coeff_zero, hconst, ← pow_two]
    exact Int.isUnit_sq hp
  have hNnonunit (p : ℤ[X]) (hp : ¬ IsUnit p) : ¬ IsUnit (N p) := by
    intro hu
    have hu' := hu.map (expand ℤ 2)
    rw [hN] at hu'
    exact hp (isUnit_of_mul_isUnit_left hu')
  -- The norms of the factors descend under the square substitution.
  have hsq : f ^ 2 = N a * N b := by
    apply expand_injective (R := ℤ) (by decide : 0 < 2)
    rw [map_pow, map_mul, hN a, hN b, expand_eq_comp_X_pow]
    have hfixed : (f.comp (X ^ 2)).comp (-X) = f.comp (X ^ 2) := by
      rw [comp_assoc, pow_comp, X_comp, neg_sq]
    calc
      (f.comp (X ^ 2)) ^ 2 = f.comp (X ^ 2) * (f.comp (X ^ 2)).comp (-X) := by
        rw [hfixed, pow_two]
      _ = _ := by rw [hab, mul_comp]; ring
  have hdiv : f ∣ N a * N b := hsq ▸ dvd_pow_self f (by decide : 2 ≠ 0)
  rcases hirr.prime.dvd_mul.mp hdiv with h | h
  · have heq := eq_of_dvd_of_sq_eq_mul hirr hf0
      (hN0 a (isUnit_of_mul_isUnit_left hunit)) (hNnonunit b hb) hsq h
    exact ⟨a, by rw [← hN, heq, expand_eq_comp_X_pow]⟩
  · have heq := eq_of_dvd_of_sq_eq_mul hirr hf0
      (hN0 b (isUnit_of_mul_isUnit_right hunit)) (hNnonunit a ha)
      (by rw [mul_comm, ← hsq]) h
    exact ⟨b, by rw [← hN, heq, expand_eq_comp_X_pow]⟩

private theorem map_modTwo_comp_neg_X (p : ℤ[X]) :
    (p.comp (-X)).map (Int.castRingHom (ZMod 2)) = p.map (Int.castRingHom (ZMod 2)) := by
  rw [map_comp, Polynomial.map_neg, map_X, CharTwo.neg_eq, comp_X]

private theorem two_mul_comp_neg_X (p : (ZMod 4)[X]) :
    2 * p.comp (-X) = 2 * p := by
  ext n
  have hsign : (2 : ZMod 4) * (-1) ^ n = 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih]
      decide
  rw [← C_ofNat 2, coeff_C_mul, coeff_C_mul,
    show (-X : (ZMod 4)[X]) = C (-1) * X by simp, comp_C_mul_X_coeff]
  calc
    _ = p.coeff n * (2 * (-1) ^ n) := mul_left_comm _ _ _
    _ = _ := by rw [hsign, mul_comm]

private theorem map_modFour_mul_comp_neg_X_eq_of_map_modTwo_eq {f g : ℤ[X]}
    (h : g.map (Int.castRingHom (ZMod 2)) = f.map (Int.castRingHom (ZMod 2))) :
    (g * g.comp (-X)).map (Int.castRingHom (ZMod 4)) =
      (f * f.comp (-X)).map (Int.castRingHom (ZMod 4)) := by
  have hdvd : C (2 : ℤ) ∣ g - f := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    rw [coeff_sub]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [Int.cast_sub, sub_eq_zero]
    change Int.castRingHom (ZMod 2) (g.coeff n) = Int.castRingHom (ZMod 2) (f.coeff n)
    simpa only [coeff_map] using
      congrArg (fun p : (ZMod 2)[X] => p.coeff n) h
  obtain ⟨r, hr⟩ := hdvd
  have hgr : g = f + C 2 * r := by rw [← hr]; ring
  let φ : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  have h4 : (4 : (ZMod 4)[X]) = 0 := by
    rw [← C_ofNat 4, show (4 : ZMod 4) = 0 by decide, map_zero]
  simp only [Polynomial.map_mul, map_comp, Polynomial.map_neg, map_X]
  change g.map φ * (g.map φ).comp (-X) = f.map φ * (f.map φ).comp (-X)
  have hg : g.map φ = f.map φ + 2 * r.map φ := by
    rw [hgr, Polynomial.map_add, Polynomial.map_mul, map_C, map_ofNat, C_ofNat]
  rw [hg, add_comp, mul_comp, ← C_ofNat 2, C_comp, C_ofNat, two_mul_comp_neg_X]
  calc
    _ = f.map φ * (f.map φ).comp (-X) +
        (2 * f.map φ + 2 * (f.map φ).comp (-X)) * r.map φ + 4 * (r.map φ) ^ 2 := by ring
    _ = _ := by
      rw [two_mul_comp_neg_X, ← add_mul]
      norm_num
      simp [h4]

/-- **Square compositions of $0,1$-polynomials modulo $4$.** Let $f \in \mathbb{Z}[x]$ be
irreducible in $\mathbb{Z}[x]$, with every coefficient equal to $0$ or $1$ and with constant
term $f(0) = 1$. If $f(x^2)$ is not irreducible in $\mathbb{Z}[x]$, then
$f(x^2) \equiv f(x)\,f(-x) \pmod 4$ as polynomials, that is, the two polynomials have the
same image in $(\mathbb{Z}/4\mathbb{Z})[x]$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", Theorem 1.3. -/
theorem map_comp_sq_eq_mul (f : ℤ[X])
    (h01 : IsZeroOnePoly f) (hirr : Irreducible f) (hf0 : f.coeff 0 = 1)
    (hred : ¬ Irreducible (f.comp (X ^ 2))) :
    (f.comp (X ^ 2)).map (Int.castRingHom (ZMod 4)) =
      (f * f.comp (-X)).map (Int.castRingHom (ZMod 4)) := by
  have hmonic : f.Monic :=
    (h01 f.natDegree).resolve_left (leadingCoeff_ne_zero.mpr hirr.ne_zero)
  obtain ⟨g, hg⟩ := exists_comp_neg_X_factor hirr hf0
    (hmonic.natDegree_pos_of_not_isUnit hirr.not_isUnit) hred
  have hfg : g.map (Int.castRingHom (ZMod 2)) = f.map (Int.castRingHom (ZMod 2)) := by
    apply expand_injective (R := ZMod 2) (by decide : 0 < 2)
    rw [ZMod.expand_card, ← map_expand, expand_eq_comp_X_pow, hg,
      Polynomial.map_mul, map_modTwo_comp_neg_X, pow_two]
  rw [hg]
  exact map_modFour_mul_comp_neg_X_eq_of_map_modTwo_eq hfg

end MathlibExt.Algebra.PalindromicZeroOneWanted
