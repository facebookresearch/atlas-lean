/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ManinSequence
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
import MathlibExt.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Manin's elementary proof in characteristic two

This file packages the ordinary and supersingular normal-form cases, following
Chahal--Soomro--Top, *Rocky Mountain J. Math.* 44 (2014).
-/

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

noncomputable section

open Polynomial
open scoped CharTwo
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree

universe u

variable {F : Type u} [Field F]

private lemma ratFunc_ne_zero_of_num_degree_gt {r : RatFunc F}
    (hdegree : r.denom.natDegree < r.num.natDegree) : r ≠ 0 := by
  intro hzero
  rw [hzero] at hdegree
  simp at hdegree

private lemma intDegree_pow {x : RatFunc F} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      ring

private lemma intDegree_pow_le_zero {x : RatFunc F} (hx : x.intDegree ≤ 0)
    (n : ℕ) : (x ^ n).intDegree ≤ 0 := by
  by_cases hx0 : x = 0
  · cases n <;> simp [hx0]
  rw [intDegree_pow hx0]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hx

private lemma intDegree_add_le_of_le {x y : RatFunc F} {m : ℤ}
    (hm : 0 ≤ m) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ m) :
    (x + y).intDegree ≤ m := by
  by_cases hxy : x + y = 0
  · simp [hxy, hm]
  by_cases hy0 : y = 0
  · simpa [hy0] using hx
  exact (RatFunc.intDegree_add_le hy0 hxy).trans (max_le hx hy)

private lemma intDegree_mul_le_of_le {x y : RatFunc F} {m n : ℤ}
    (hmn : 0 ≤ m + n) (hx : x.intDegree ≤ m) (hy : y.intDegree ≤ n) :
    (x * y).intDegree ≤ m + n := by
  by_cases hx0 : x = 0
  · simp [hx0, hmn]
  by_cases hy0 : y = 0
  · simp [hy0, hmn]
  rw [RatFunc.intDegree_mul hx0 hy0]
  exact add_le_add hx hy

private lemma intDegree_add_eq_left_of_lt {x y : RatFunc F}
    (hx0 : x ≠ 0) (hdegree : y.intDegree < x.intDegree) :
    (x + y).intDegree = x.intDegree := by
  by_cases hy0 : y = 0
  · simp [hy0]
  have hsum0 : x + y ≠ 0 := by
    intro hzero
    have hxy : x = -y := by linear_combination hzero
    have hdegrees := congrArg RatFunc.intDegree hxy
    rw [RatFunc.intDegree_neg] at hdegrees
    omega
  apply le_antisymm
  · exact (RatFunc.intDegree_add_le hy0 hsum0).trans
      (max_le le_rfl hdegree.le)
  · have hneg : -y ≠ 0 := neg_ne_zero.mpr hy0
    have hrecover : (x + y) + -y = x := by ring
    have hrecover0 : (x + y) + -y ≠ 0 := by rw [hrecover]; exact hx0
    have hbound := RatFunc.intDegree_add_le hneg hrecover0
    rw [hrecover, RatFunc.intDegree_neg] at hbound
    by_contra hnot
    have hlt : (x + y).intDegree < x.intDegree := lt_of_not_ge hnot
    omega

private def quadraticDegree (q : ℕ) (a n : ℤ) : ℤ :=
  n ^ 2 + a * n + q

private def nonnegativeQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ))
    (hnonneg : ∀ n, 0 ≤ quadraticDegree q a n)
    (hnoAdjacent : ∀ n, quadraticDegree q a n = 0 →
      quadraticDegree q a (n + 1) = 0 → False) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData.ofQuadratic q N a ha
    (by simpa only [quadraticDegree] using hnonneg)
    (by simpa only [quadraticDegree] using hnoAdjacent)

private def positiveQuadraticDegreeData (q N : ℕ) (a : ℤ)
    (ha : a = (q : ℤ) + 1 - (N : ℤ)) (hpos : ∀ n, 0 < quadraticDegree q a n) :
    MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData q N :=
  nonnegativeQuadraticDegreeData q N a ha (fun n ↦ (hpos n).le)
    (fun n hn _ ↦ by nlinarith [hpos n])

private lemma degreeDataAtTwo_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 5) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 2 N) := by
  have hcases : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨positiveQuadraticDegreeData 2 1 2 (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (n + 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 2 1 (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (2 * n + 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 3 0 (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg n])⟩
  · exact ⟨positiveQuadraticDegreeData 2 4 (-1) (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (2 * n - 1)])⟩
  · exact ⟨positiveQuadraticDegreeData 2 5 (-2) (by norm_num) (by
      intro n
      norm_num [quadraticDegree]
      nlinarith [sq_nonneg (n - 1)])⟩

private lemma degreeDataAtFour_of_pointCount_bounds (N : ℕ) (hpos : 1 ≤ N) (hle : N ≤ 9) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData 4 N) := by
  let a : ℤ := 5 - N
  have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast hpos
  have hNle : (N : ℤ) ≤ 9 := by exact_mod_cast hle
  have hdisc : a ^ 2 ≤ 16 := by
    dsimp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNpos) (sub_nonneg.mpr hNle)]
  refine ⟨nonnegativeQuadraticDegreeData 4 N a (by simp [a]) ?_ ?_⟩
  · intro n
    norm_num [quadraticDegree]
    nlinarith [sq_nonneg (2 * n + a)]
  · intro n hn hn1
    norm_num [quadraticDegree] at hn hn1
    nlinarith [sq_nonneg (2 * n + a)]

/-- **Manin degree data over the field with two elements.** Let $F$ be a field with exactly
two elements, let $W$ be any Weierstrass curve over $F$, and let $N$ be the number of
nonsingular points of $W$ over $F$, including the point at infinity. Then there is Manin degree
data for $(2, N)$: a function $d : \mathbb{Z} \to \mathbb{N}$ with $d(0) = 2$, $d(-1) = N$,
$d(n - 1) + d(n + 1) = 2 d(n) + 2$ for every integer $n$, and no integer $n$ with
$d(n) = d(n + 1) = 0$.

The proof needs only the elementary bound $N \le 2 \cdot 2 + 1$. -/
theorem manin_degree_data_of_card_eq_two [Finite F] (hF : Nat.card F = 2)
    (W : WeierstrassCurve F) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtTwo_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

/-- **Manin degree data over the field with four elements.** Let $F$ be a field with exactly
four elements, let $W$ be any Weierstrass curve over $F$, and let $N$ be the number of
nonsingular points of $W$ over $F$, including the point at infinity. Then there is Manin degree
data for $(4, N)$: a function $d : \mathbb{Z} \to \mathbb{N}$ with $d(0) = 4$, $d(-1) = N$,
$d(n - 1) + d(n + 1) = 2 d(n) + 2$ for every integer $n$, and no integer $n$ with
$d(n) = d(n + 1) = 0$.

The proof needs only the elementary bound $N \le 2 \cdot 4 + 1$. -/
theorem manin_degree_data_of_card_eq_four [Finite F] (hF : Nat.card F = 4)
    (W : WeierstrassCurve F) :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  have hle := W.toAffine.natCard_point_le_two_mul_natCard_add_one
  simpa only [hF] using degreeDataAtFour_of_pointCount_bounds
    (Nat.card W.toAffine.Point) Nat.card_pos (by omega)

private def frobeniusTail (h k : F[X]) : ℕ → F[X]
  | 0 => 0
  | e + 1 => frobeniusTail h k e ^ 2 + k ^ (2 ^ (e + 1) - 2) * h

private lemma frobeniusTail_identity [CharP F 2] (h k : F[X]) (e : ℕ) :
    frobeniusTail h k e ^ 2 + k ^ (2 ^ e) * frobeniusTail h k e =
      h ^ (2 ^ e) + k ^ (2 * (2 ^ e - 1)) * h := by
  induction e with
  | zero => simp [frobeniusTail, CharTwo.add_self_eq_zero]
  | succ e ih =>
      let q := 2 ^ e
      have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
      have hqpos : 0 < q := by simp [q]
      have hsq := congrArg (fun p : F[X] ↦ p ^ 2) ih
      rw [CharTwo.add_sq, CharTwo.add_sq, mul_pow, mul_pow] at hsq
      have hB4 : (frobeniusTail h k e ^ 2) ^ 2 = frobeniusTail h k e ^ 4 := by
        ring
      have hk2q : (k ^ (2 ^ e)) ^ 2 = k ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
      have hh2q : (h ^ (2 ^ e)) ^ 2 = h ^ (2 * q) := by
        rw [← pow_mul]
        congr 1
      have hk4q : (k ^ (2 * (2 ^ e - 1))) ^ 2 = k ^ (4 * q - 4) := by
        rw [← pow_mul]
        congr 1
        dsimp [q]
        omega
      rw [hB4, hk2q, hh2q, hk4q] at hsq
      have hsq' :
          frobeniusTail h k e ^ 4 + k ^ (2 * q) * frobeniusTail h k e ^ 2 =
            h ^ (2 * q) + k ^ (4 * q - 4) * h ^ 2 := hsq
      rw [frobeniusTail, hq, CharTwo.add_sq]
      rw [show (k ^ (2 * q - 2) * h) ^ 2 =
        k ^ (4 * q - 4) * h ^ 2 by
          rw [mul_pow, ← pow_mul]
          congr 2
          omega]
      rw [mul_add]
      rw [show k ^ (2 * q) * (k ^ (2 * q - 2) * h) =
        k ^ (4 * q - 2) * h by
          rw [← mul_assoc, ← pow_add]
          congr 2
          omega]
      rw [show h ^ (2 * q) = (h ^ q) ^ 2 by
        rw [← pow_mul]
        congr 1
        omega]
      rw [show k ^ (2 * (2 * q - 1)) = k ^ (4 * q - 2) by
        congr 1
        omega]
      have hcancel :
          k ^ (4 * q - 4) * h ^ 2 + k ^ (4 * q - 4) * h ^ 2 = 0 :=
        CharTwo.add_self_eq_zero _
      linear_combination hsq' + hcancel

private def charTwoExponent [Finite F] : ℕ := Nat.log 2 (Nat.card F)

private lemma card_eq_two_pow [Finite F] [CharP F 2] :
    Nat.card F = 2 ^ charTwoExponent (F := F) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  obtain ⟨e, _, he⟩ := @FiniteField.card F _ fintypeF 2 _
  unfold charTwoExponent
  rw [@Nat.card_eq_fintype_card F fintypeF, he, Nat.log_pow (by norm_num)]

private def charTwoFiber (b c : F) :=
  {y : F // y ^ 2 + b * y = c}

private instance charTwoFiberFinite [Finite F] (b c : F) :
    Finite (charTwoFiber b c) := by
  unfold charTwoFiber
  infer_instance

private lemma charTwoFiber_card_eq_one [Finite F] [CharP F 2] (c : F) :
    Nat.card (charTwoFiber 0 c) = 1 := by
  have hsquareInjective : Function.Injective (fun y : F ↦ y ^ 2) := by
    intro y z hyz
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hyz) with hyz | hyz
    · exact hyz
    · simpa only [CharTwo.neg_eq] using hyz
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hsquareInjective c
  let _ : Nonempty (charTwoFiber 0 c) := ⟨⟨r, by simpa using hr⟩⟩
  let _ : Subsingleton (charTwoFiber 0 c) := ⟨by
    intro y z
    apply Subtype.ext
    apply hsquareInjective
    simpa using y.property.trans z.property.symm⟩
  exact Nat.card_unique

private lemma charTwoFiber_card_eq_two [Finite F] [CharP F 2]
    {b c r : F} (hb : b ≠ 0) (hr : r ^ 2 + b * r = c) :
    Nat.card (charTwoFiber b c) = 2 := by
  classical
  have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
  have hrb : (r + b) ^ 2 + b * (r + b) = c := by
    linear_combination hr + (r * b + b ^ 2) * htwo
  have hbr : r + b ≠ r := by
    intro h
    apply hb
    linear_combination h
  let e : charTwoFiber b c ≃ Bool :=
    { toFun := fun y ↦ if y.1 = r then true else false
      invFun := fun value ↦ match value with
        | true => ⟨r, hr⟩
        | false => ⟨r + b, hrb⟩
      left_inv := by
        intro y
        have hfactor : (y.1 + r) * (y.1 + r + b) = 0 := by
          linear_combination y.property + hr + (y.1 * r + c) * htwo
        have hy : y.1 = r ∨ y.1 = r + b := by
          rcases mul_eq_zero.mp hfactor with h | h
          · left
            simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
          · right
            have hyr : y.1 + r = b := by
              simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
            calc
              y.1 = (y.1 + r) + r := by
                rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
              _ = b + r := by rw [hyr]
              _ = r + b := add_comm _ _
        apply Subtype.ext
        rcases hy with hy | hy
        · simp [hy]
        · simp [hy, hbr]
      right_inv := by
        intro value
        cases value <;> simp [hbr] }
  simpa using Nat.card_congr e

private lemma charTwoFiber_card_eq_zero [Finite F] (b c : F)
    (hempty : ¬∃ y, y ^ 2 + b * y = c) :
    Nat.card (charTwoFiber b c) = 0 := by
  let _ : IsEmpty (charTwoFiber b c) := ⟨fun y ↦ hempty ⟨y.1, y.property⟩⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

private lemma charTwoFiber_card_le_two [Finite F] [CharP F 2]
    (b c : F) : Nat.card (charTwoFiber b c) ≤ 2 := by
  by_cases hb : b = 0
  · subst b
    rw [charTwoFiber_card_eq_one]
    omega
  by_cases hexists : ∃ y, y ^ 2 + b * y = c
  · obtain ⟨r, hr⟩ := hexists
    rw [charTwoFiber_card_eq_two hb hr]
  · rw [charTwoFiber_card_eq_zero b c hexists]
    omega

private def frobeniusValue (c b : F) : ℕ → F
  | 0 => 0
  | e + 1 => frobeniusValue c b e ^ 2 + b ^ (2 ^ (e + 1) - 2) * c

private lemma eval_frobeniusTail (h k : F[X]) (x : F) (e : ℕ) :
    (frobeniusTail h k e).eval x =
      frobeniusValue (h.eval x) (k.eval x) e := by
  induction e with
  | zero => simp [frobeniusTail, frobeniusValue]
  | succ e ih => simp [frobeniusTail, frobeniusValue, ih]

private lemma frobenius_pow_eq_linear_add_value [CharP F 2]
    {b c y : F} (hy : y ^ 2 + b * y = c) (e : ℕ) :
    y ^ (2 ^ e) = b ^ (2 ^ e - 1) * y + frobeniusValue c b e := by
  induction e with
  | zero => simp [frobeniusValue]
  | succ e ih =>
      let q := 2 ^ e
      have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
      have hqpos : 0 < q := by simp [q]
      have hy' : y ^ 2 = b * y + c := by
        calc
          y ^ 2 = c - b * y := eq_sub_of_add_eq hy
          _ = c + b * y := by
            simp only [sub_eq_add_neg, CharTwo.neg_eq]
          _ = b * y + c := add_comm _ _
      have hbpow : (b ^ (q - 1)) ^ 2 = b ^ (2 * q - 2) := by
        rw [← pow_mul]
        congr 1
        omega
      have hbnext : b ^ (2 * q - 2) * (b * y) = b ^ (2 * q - 1) * y := by
        calc
          b ^ (2 * q - 2) * (b * y) =
              (b ^ (2 * q - 2) * b) * y := by ring
          _ = b ^ (2 * q - 2 + 1) * y := by rw [pow_succ]
          _ = b ^ (2 * q - 1) * y := by congr 2; omega
      rw [hq]
      calc
        y ^ (2 * q) = (y ^ q) ^ 2 := by
          rw [← pow_mul]
          congr 1
          omega
        _ = (b ^ (q - 1) * y + frobeniusValue c b e) ^ 2 := by
          rw [show q = 2 ^ e by rfl, ih]
        _ = b ^ (2 * q - 2) * y ^ 2 + frobeniusValue c b e ^ 2 := by
          rw [CharTwo.add_sq, mul_pow, hbpow]
        _ = b ^ (2 * q - 2) * (b * y + c) +
              frobeniusValue c b e ^ 2 := by rw [hy']
        _ = b ^ (2 * q - 1) * y +
              (frobeniusValue c b e ^ 2 + b ^ (2 * q - 2) * c) := by
          rw [mul_add, hbnext]
          ring
        _ = b ^ (2 * q - 1) * y + frobeniusValue c b (e + 1) := by
          rw [frobeniusValue, hq]

private lemma frobeniusValue_eq_zero_of_mem_fiber [Finite F] [CharP F 2]
    {b c y : F} (hb : b ≠ 0) (hy : y ^ 2 + b * y = c) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hyq : y ^ Nat.card F = y := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card y
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have h := frobenius_pow_eq_linear_add_value hy
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hyq, hbq1, one_mul] at h
  have hzero : (0 : F) = frobeniusValue c b (charTwoExponent (F := F)) :=
    add_left_cancel (by simpa only [add_zero] using h)
  exact hzero.symm

private lemma frobeniusValue_eq_zero_or_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0) :
    frobeniusValue c b (charTwoExponent (F := F)) = 0 ∨
      frobeniusValue c b (charTwoExponent (F := F)) = b := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq : b ^ Nat.card F = b := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card b
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hcq : c ^ Nat.card F = c := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card c
  have htail := congrArg (Polynomial.eval (0 : F))
    (frobeniusTail_identity (C c) (C b) (charTwoExponent (F := F)))
  simp only [eval_add, eval_mul, eval_pow, eval_C] at htail
  rw [eval_frobeniusTail, eval_C, eval_C,
    ← card_eq_two_pow (F := F), hbq, hcq] at htail
  rw [show b ^ (2 * (Nat.card F - 1)) = 1 by
    rw [mul_comm, pow_mul, hbq1, one_pow], one_mul] at htail
  rw [CharTwo.add_self_eq_zero] at htail
  have hfactor :
      frobeniusValue c b (charTwoExponent (F := F)) *
        (frobeniusValue c b (charTwoExponent (F := F)) + b) = 0 := by
    calc
      _ = frobeniusValue c b (charTwoExponent (F := F)) ^ 2 +
          b * frobeniusValue c b (charTwoExponent (F := F)) := by ring
      _ = 0 := htail
  rcases mul_eq_zero.mp hfactor with hzero | heq
  · exact Or.inl hzero
  · exact Or.inr (by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left heq)

private def charTwoQuadratic (b c : F) : F[X] :=
  X ^ 2 + C b * X + C c

private def frobeniusQuotient (b c : F) : ℕ → F[X]
  | 0 => 0
  | e + 1 =>
      charTwoQuadratic b c * frobeniusQuotient b c e ^ 2 +
        C (b ^ (2 ^ (e + 1) - 2))

private lemma frobenius_polynomial_mod_quadratic [CharP F 2]
    (b c : F) (e : ℕ) :
    X ^ (2 ^ e) + C (b ^ (2 ^ e - 1)) * X + C (frobeniusValue c b e) =
      charTwoQuadratic b c * frobeniusQuotient b c e := by
  induction e with
  | zero => simp [frobeniusValue, frobeniusQuotient,
      CharTwo.add_self_eq_zero]
  | succ e ih =>
      let q := 2 ^ e
      have hq : 2 ^ (e + 1) = 2 * q := by simp [q, pow_succ, mul_comm]
      have hqpos : 0 < q := by simp [q]
      have hbpow : (b ^ (q - 1)) ^ 2 = b ^ (2 * q - 2) := by
        rw [← pow_mul]
        congr 1
        omega
      have hbnext : b ^ (2 * q - 2) * b = b ^ (2 * q - 1) := by
        calc
          b ^ (2 * q - 2) * b = b ^ (2 * q - 2 + 1) := (pow_succ _ _).symm
          _ = b ^ (2 * q - 1) := by congr 1; omega
      rw [frobeniusValue, frobeniusQuotient, hq]
      rw [show X ^ (2 * q) = (X ^ q) ^ 2 by
        rw [← pow_mul]
        congr 1
        omega]
      rw [show C (b ^ (2 * q - 1)) * X =
        C (b ^ (2 * q - 2)) * (C b * X) by
          calc
            C (b ^ (2 * q - 1)) * X =
                C (b ^ (2 * q - 2) * b) * X := by rw [hbnext]
            _ = (C (b ^ (2 * q - 2)) * C b) * X := by rw [map_mul]
            _ = C (b ^ (2 * q - 2)) * (C b * X) := by ring]
      rw [show C (frobeniusValue c b e ^ 2 + b ^ (2 * q - 2) * c) =
        C (frobeniusValue c b e) ^ 2 +
          C (b ^ (2 * q - 2)) * C c by simp]
      rw [show C (b ^ (2 * q - 2)) = C (b ^ (q - 1)) ^ 2 by
        rw [← map_pow, hbpow]]
      calc
        (X ^ q) ^ 2 + C (b ^ (q - 1)) ^ 2 * (C b * X) +
              (C (frobeniusValue c b e) ^ 2 +
                C (b ^ (q - 1)) ^ 2 * C c) =
            (X ^ q + C (b ^ (q - 1)) * X +
              C (frobeniusValue c b e)) ^ 2 +
                C (b ^ (q - 1)) ^ 2 * charTwoQuadratic b c := by
          rw [CharTwo.add_sq, CharTwo.add_sq]
          unfold charTwoQuadratic
          have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
          linear_combination
            -(X ^ 2 * C (b ^ (q - 1)) ^ 2) * htwo
        _ = (charTwoQuadratic b c * frobeniusQuotient b c e) ^ 2 +
              C (b ^ (q - 1)) ^ 2 * charTwoQuadratic b c := by
          rw [show X ^ q + C (b ^ (q - 1)) * X +
            C (frobeniusValue c b e) =
              charTwoQuadratic b c * frobeniusQuotient b c e by
                simpa only [q] using ih]
        _ = charTwoQuadratic b c *
              (charTwoQuadratic b c * frobeniusQuotient b c e ^ 2 +
                C (b ^ (q - 1)) ^ 2) := by ring

private def charTwoFrobeniusPolynomial [Finite F] : F[X] :=
  X ^ Nat.card F - X

private lemma eval_charTwoFrobeniusPolynomial [Finite F] (x : F) :
    (charTwoFrobeniusPolynomial : F[X]).eval x = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  unfold charTwoFrobeniusPolynomial
  rw [eval_sub, eval_pow, eval_X, @Nat.card_eq_fintype_card F fintypeF,
    FiniteField.pow_card, sub_self]

private lemma charTwoFrobeniusPolynomial_ne_zero [Finite F] :
    (charTwoFrobeniusPolynomial : F[X]) ≠ 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hdegree := FiniteField.X_pow_card_sub_X_natDegree_eq F
    (@Fintype.one_lt_card F fintypeF _)
  intro hzero
  unfold charTwoFrobeniusPolynomial at hzero
  rw [@Nat.card_eq_fintype_card F fintypeF] at hzero
  rw [hzero] at hdegree
  simp only [natDegree_zero] at hdegree
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  omega

private lemma charTwoFrobeniusPolynomial_splits [Finite F] :
    (charTwoFrobeniusPolynomial : F[X]).Splits := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [Polynomial.splits_iff_card_roots]
  unfold charTwoFrobeniusPolynomial
  rw [@Nat.card_eq_fintype_card F fintypeF,
    FiniteField.roots_X_pow_card_sub_X,
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  simp

private lemma exists_mem_charTwoFiber_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    ∃ y, y ^ 2 + b * y = c := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hbq1 : b ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one b hb
  have hmod := frobenius_polynomial_mod_quadratic b c
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F), hbq1, hvalue] at hmod
  simp only [map_one, one_mul, map_zero, add_zero] at hmod
  have hmod' :
      charTwoFrobeniusPolynomial =
        charTwoQuadratic b c *
          frobeniusQuotient b c (charTwoExponent (F := F)) := by
    unfold charTwoFrobeniusPolynomial
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using hmod
  have hdiv : charTwoQuadratic b c ∣
      (charTwoFrobeniusPolynomial : F[X]) :=
    ⟨frobeniusQuotient b c (charTwoExponent (F := F)), hmod'⟩
  have hsplit : (charTwoQuadratic b c).Splits :=
    charTwoFrobeniusPolynomial_splits.of_dvd
      charTwoFrobeniusPolynomial_ne_zero hdiv
  have hnatDegree : (charTwoQuadratic b c).natDegree = 2 := by
    exact (Polynomial.isMonicOfDegree_add_add_two b c).natDegree_eq
  have hdegree : (charTwoQuadratic b c).degree ≠ 0 := by
    apply Polynomial.degree_ne_of_natDegree_ne
    rw [hnatDegree]
    norm_num
  obtain ⟨y, hy⟩ := hsplit.exists_eval_eq_zero hdegree
  refine ⟨y, ?_⟩
  unfold charTwoQuadratic at hy
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy
  have hy' : y ^ 2 + b * y = -c := eq_neg_of_add_eq_zero_left hy
  simpa only [CharTwo.neg_eq] using hy'

private lemma charTwoFiber_card_eq_two_of_value_eq_zero [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = 0) :
    Nat.card (charTwoFiber b c) = 2 := by
  obtain ⟨y, hy⟩ := exists_mem_charTwoFiber_of_value_eq_zero hb hvalue
  exact charTwoFiber_card_eq_two hb hy

private lemma charTwoFiber_card_eq_zero_of_value_eq [Finite F] [CharP F 2]
    {b c : F} (hb : b ≠ 0)
    (hvalue : frobeniusValue c b (charTwoExponent (F := F)) = b) :
    Nat.card (charTwoFiber b c) = 0 := by
  apply charTwoFiber_card_eq_zero
  rintro ⟨y, hy⟩
  have hzero := frobeniusValue_eq_zero_of_mem_fiber hb hy
  exact hb (hvalue ▸ hzero)

private def ordinaryH (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₂ * X ^ 2 + C W.a₆

private def ordinaryU [Finite F] (W : WeierstrassCurve F) : F[X] :=
  X * frobeniusTail (ordinaryH W) X (charTwoExponent (F := F))

private lemma ordinaryH_pow_card [Finite F] (W : WeierstrassCurve F) :
    ordinaryH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₂ * X ^ (2 * Nat.card F) + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.Polynomial.expand_card F _ fintypeF]
  simp only [ordinaryH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma ordinaryU_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryU W ^ 2 + X ^ (Nat.card F + 1) * ordinaryU W =
      X ^ 2 * ordinaryH W ^ Nat.card F + X ^ (2 * Nat.card F) * ordinaryH W := by
  have htail := frobeniusTail_identity (ordinaryH W) X
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  have hterm :
      X ^ 2 * (X ^ (2 * (Nat.card F - 1)) * ordinaryH W) =
        X ^ (2 * Nat.card F) * ordinaryH W := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  unfold ordinaryU
  calc
    (X * frobeniusTail (ordinaryH W) X charTwoExponent) ^ 2 +
        X ^ (Nat.card F + 1) *
          (X * frobeniusTail (ordinaryH W) X charTwoExponent) =
      X ^ 2 * (frobeniusTail (ordinaryH W) X charTwoExponent ^ 2 +
        X ^ Nat.card F * frobeniusTail (ordinaryH W) X charTwoExponent) := by
          ring
    _ = X ^ 2 * (ordinaryH W ^ Nat.card F +
        X ^ (2 * (Nat.card F - 1)) * ordinaryH W) := by rw [htail]
    _ = _ := by rw [mul_add, hterm]

private def ordinaryTwist (W : WeierstrassCurve F) :
    WeierstrassCurve (RatFunc F) :=
  ⟨RatFunc.X, RatFunc.X ^ 3 + RatFunc.C W.a₆, 0, 0,
    RatFunc.C W.a₆ * RatFunc.X ^ 6⟩

private lemma ordinaryTwist_discriminant [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryTwist W).Δ = RatFunc.C W.a₆ * RatFunc.X ^ 12 := by
  simp only [ordinaryTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero, zero_add, sub_zero, CharTwo.neg_eq]
  ring_nf

private instance [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJNeZeroNF] : (ordinaryTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, ordinaryTwist_discriminant,
    isUnit_iff_ne_zero]
  apply mul_ne_zero
  · have hb : W.a₆ ≠ 0 := by
      have h := W.Δ'.ne_zero
      rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
      exact h
    intro hC
    apply hb
    apply RatFunc.C_injective
    simpa using hC
  · exact pow_ne_zero 12 RatFunc.X_ne_zero

private lemma ordinaryQ_equation [CharP F 2] (W : WeierstrassCurve F) :
    (ordinaryTwist W).toAffine.Equation (RatFunc.X ^ 3) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ordinaryTwist]
  ring_nf
  rw [CharTwo.two_eq_zero]
  simp

private def ordinaryQ [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJNeZeroNF] : (ordinaryTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (ordinaryQ_equation W)

private def ordinaryPZeroX [Finite F] : RatFunc F :=
  RatFunc.X ^ (Nat.card F + 2)

private def ordinaryPZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (X ^ 2 * ordinaryU W)

private lemma ordinary_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (X ^ 2 * ordinaryU W) ^ 2 +
        X * X ^ (Nat.card F + 2) * (X ^ 2 * ordinaryU W) =
      (X ^ (Nat.card F + 2)) ^ 3 +
        (X ^ 3 + C W.a₆) * (X ^ (Nat.card F + 2)) ^ 2 +
        C W.a₆ * X ^ 6 := by
  have hu := ordinaryU_identity W
  have hh := ordinaryH_pow_card W
  rw [hh] at hu
  unfold ordinaryH at hu
  have hcancel :
      C W.a₂ * X ^ (2 * Nat.card F + 6) +
        C W.a₂ * X ^ (2 * Nat.card F + 6) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination X ^ 4 * hu + hcancel

private lemma ordinaryPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryTwist W).toAffine.Equation (ordinaryPZeroX (F := F))
      (ordinaryPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (ordinary_pZero_polynomial_equation W)
  simpa only [ordinaryTwist, ordinaryPZeroX, ordinaryPZeroY, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

private def ordinaryPZero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (ordinaryPZero_equation W)

private local instance : DecidableEq F := Classical.decEq F

private def ordinaryPoint [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    (ordinaryTwist W).toAffine.Point := ordinaryPZero W + n • ordinaryQ W

private lemma ordinaryPoint_add_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    ordinaryPoint W (n + 1) = ordinaryPoint W n + ordinaryQ W := by
  rw [ordinaryPoint, ordinaryPoint, add_one_zsmul]
  abel

private def ordinaryPaperX (x : RatFunc F) : RatFunc F := x / RatFunc.X ^ 2

private def ordinaryPaperY (y : RatFunc F) : RatFunc F := y / RatFunc.X ^ 3

private def ordinaryBadAtInfinity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryTwist W).toAffine.Point → Prop
  | 0 => False
  | .some x _ _ => (ordinaryPaperX x).intDegree ≤ 0

private lemma ordinary_paper_coordinates_equation [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y) :
    ordinaryPaperY y ^ 2 + ordinaryPaperX x * ordinaryPaperY y =
      ordinaryPaperX x ^ 3 +
        (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * ordinaryPaperX x ^ 2 +
          RatFunc.C W.a₆ := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [ordinaryTwist] at heq
  unfold ordinaryPaperX ordinaryPaperY
  field_simp [RatFunc.X_ne_zero]
  linear_combination heq

private lemma intDegree_C_div_X_sq_le_zero (b : F) :
    (RatFunc.C b / RatFunc.X ^ 2).intDegree ≤ 0 := by
  by_cases hb : b = 0
  · simp [hb]
  have hCb : RatFunc.C b ≠ 0 := by
    intro hzero
    apply hb
    apply RatFunc.C_injective
    simpa using hzero
  rw [RatFunc.intDegree_div hCb (pow_ne_zero 2 RatFunc.X_ne_zero)]
  rw [intDegree_pow RatFunc.X_ne_zero]
  simp

private lemma ordinary_coefficient_intDegree_le_one (W : WeierstrassCurve F) :
    (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2).intDegree ≤ 1 := by
  exact intDegree_add_le_of_le (m := 1) (by norm_num) (by simp)
    ((intDegree_C_div_X_sq_le_zero W.a₆).trans (by norm_num))

private lemma ordinaryPaperY_intDegree_le_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y)
    (hx : (ordinaryPaperX x).intDegree ≤ 0) :
    (ordinaryPaperY y).intDegree ≤ 0 := by
  let r := ordinaryPaperX x
  let s := ordinaryPaperY y
  by_contra hsnot
  have hspos : 0 < s.intDegree := lt_of_not_ge hsnot
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hspos
    simp at hspos
  have hs2 : (s ^ 2).intDegree = 2 * s.intDegree := by
    rw [intDegree_pow hs0]
    norm_num
  have hrs : (r * s).intDegree ≤ s.intDegree := by
    simpa using intDegree_mul_le_of_le (x := r) (y := s)
      (m := 0) (n := s.intDegree) (by simpa using hspos.le) hx le_rfl
  have hlhs : (s ^ 2 + r * s).intDegree = 2 * s.intDegree := by
    rw [intDegree_add_eq_left_of_lt (pow_ne_zero 2 hs0), hs2]
    omega
  have hr3 : (r ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
  have hr2 : (r ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hx 2
  have hmiddle :
      ((RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2).intDegree ≤ 1 :=
    intDegree_mul_le_of_le (m := 1) (n := 0) (by norm_num)
      (ordinary_coefficient_intDegree_le_one W) hr2
  have hrhs :
      (r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆).intDegree ≤ 1 := by
    have hfirst := intDegree_add_le_of_le (m := 1) (by norm_num)
      (hr3.trans (by norm_num)) hmiddle
    exact intDegree_add_le_of_le (m := 1) (by norm_num) hfirst (by simp)
  have heq := ordinary_paper_coordinates_equation W hxy
  change s ^ 2 + r * s =
    r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
      RatFunc.C W.a₆ at heq
  have hlhsLe : (s ^ 2 + r * s).intDegree ≤ 1 := by rw [heq]; exact hrhs
  rw [hlhs] at hlhsLe
  omega

private lemma ordinaryPaperX_addX_Q_eq [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hx : x ≠ RatFunc.X ^ 3) :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0)) =
      (ordinaryPaperY y /
          (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, ordinaryTwist, sub_zero]
  unfold ordinaryPaperX ordinaryPaperY
  field_simp [RatFunc.X_ne_zero, hx]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  linear_combination RatFunc.X ^ 3 * (x + RatFunc.X ^ 3) ^ 2 * htwo

private lemma ordinaryPaperX_addX_Q_intDegree_le_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {x y : RatFunc F} (hxy : (ordinaryTwist W).toAffine.Nonsingular x y)
    (hxQ : x ≠ RatFunc.X ^ 3)
    (hx : (ordinaryPaperX x).intDegree ≤ 0) :
    (ordinaryPaperX
      ((ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0))).intDegree ≤ 0 := by
  let r := ordinaryPaperX x
  let s := ordinaryPaperY y
  change r.intDegree ≤ 0 at hx
  have hs : s.intDegree ≤ 0 := ordinaryPaperY_intDegree_le_zero W hxy hx
  have hdiff : r - RatFunc.X ≠ 0 := by
    intro hzero
    have hr : r = RatFunc.X := sub_eq_zero.mp hzero
    apply hxQ
    unfold r ordinaryPaperX at hr
    calc
      x = RatFunc.X * RatFunc.X ^ 2 :=
        (div_eq_iff (pow_ne_zero 2 RatFunc.X_ne_zero)).mp hr
      _ = RatFunc.X ^ 3 := by ring
  have hdiffDegree : (r - RatFunc.X).intDegree = 1 := by
    rw [show r - RatFunc.X = -RatFunc.X + r by ring]
    rw [intDegree_add_eq_left_of_lt (neg_ne_zero.mpr RatFunc.X_ne_zero)]
    · simp
    · rw [RatFunc.intDegree_neg]
      norm_num
      omega
  have hslope : (s / (r - RatFunc.X)).intDegree ≤ 0 := by
    by_cases hs0 : s = 0
    · simp [hs0]
    rw [RatFunc.intDegree_div hs0 hdiff, hdiffDegree]
    omega
  have hslope2 : ((s / (r - RatFunc.X)) ^ 2).intDegree ≤ 0 :=
    intDegree_pow_le_zero hslope 2
  rw [ordinaryPaperX_addX_Q_eq W hxQ]
  change ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
    RatFunc.C W.a₆ / RatFunc.X ^ 2 + r).intDegree ≤ 0
  have hfirst := intDegree_add_le_of_le (m := 0) (by norm_num) hslope2 hslope
  have hsecond := intDegree_add_le_of_le (m := 0) (by norm_num) hfirst
    (intDegree_C_div_X_sq_le_zero W.a₆)
  exact intDegree_add_le_of_le (m := 0) (by norm_num) hsecond hx

private lemma ordinaryPaperX_Q_coordinate :
    ordinaryPaperX (RatFunc.X ^ 3 : RatFunc F) = RatFunc.X := by
  unfold ordinaryPaperX
  field_simp [RatFunc.X_ne_zero]

private lemma ordinaryBadAtInfinity_neg [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (P : (ordinaryTwist W).toAffine.Point) :
    ordinaryBadAtInfinity W (-P) ↔ ordinaryBadAtInfinity W P := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      rw [WeierstrassCurve.Affine.Point.neg_some]
      rfl

private lemma ordinaryBadAtInfinity_add_Q [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {P : (ordinaryTwist W).toAffine.Point}
    (hP : ordinaryBadAtInfinity W P) :
    ordinaryBadAtInfinity W (P + ordinaryQ W) := by
  cases P with
  | zero => simp [ordinaryBadAtInfinity] at hP
  | some x y hxy =>
      change (ordinaryPaperX x).intDegree ≤ 0 at hP
      have hx : x ≠ RatFunc.X ^ 3 := by
        intro hx
        have hpaper : ordinaryPaperX x = RatFunc.X := by
          rw [hx, ordinaryPaperX_Q_coordinate]
        rw [hpaper] at hP
        norm_num at hP
      have hvertical :
          ¬(x = RatFunc.X ^ 3 ∧
            y = (ordinaryTwist W).toAffine.negY (RatFunc.X ^ 3) 0) :=
        fun h ↦ hx h.1
      rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 _ from rfl]
      rw [WeierstrassCurve.Affine.Point.add_some hvertical]
      exact ordinaryPaperX_addX_Q_intDegree_le_zero W hxy hx hP

private lemma ordinaryBadAtInfinity_sub_Q [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {P : (ordinaryTwist W).toAffine.Point}
    (hP : ordinaryBadAtInfinity W P) :
    ordinaryBadAtInfinity W (P - ordinaryQ W) := by
  have hnegP : ordinaryBadAtInfinity W (-P) :=
    (ordinaryBadAtInfinity_neg W P).mpr hP
  have hadd := ordinaryBadAtInfinity_add_Q W hnegP
  rw [show P - ordinaryQ W = -(-P + ordinaryQ W) by abel]
  exact (ordinaryBadAtInfinity_neg W (-P + ordinaryQ W)).mpr hadd

private lemma ordinaryBadAtInfinity_add_Q_iff [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (P : (ordinaryTwist W).toAffine.Point) :
    ordinaryBadAtInfinity W (P + ordinaryQ W) ↔ ordinaryBadAtInfinity W P := by
  refine ⟨fun h ↦ ?_, ordinaryBadAtInfinity_add_Q W⟩
  have hsub := ordinaryBadAtInfinity_sub_Q W h
  simpa using hsub

private lemma ordinaryPaperX_pZeroX [Finite F] :
    ordinaryPaperX (ordinaryPZeroX (F := F)) = RatFunc.X ^ Nat.card F := by
  unfold ordinaryPaperX ordinaryPZeroX
  rw [show Nat.card F + 2 = 2 + Nat.card F by omega, pow_add]
  field_simp [RatFunc.X_ne_zero]

private lemma ordinaryPZero_not_badAtInfinity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ¬ordinaryBadAtInfinity W (ordinaryPZero W) := by
  intro hbad
  change (ordinaryPaperX (ordinaryPZeroX (F := F))).intDegree ≤ 0 at hbad
  rw [ordinaryPaperX_pZeroX, intDegree_pow RatFunc.X_ne_zero] at hbad
  simp only [RatFunc.intDegree_X, mul_one] at hbad
  have hcard : (0 : ℤ) < Nat.card F := by exact_mod_cast Nat.card_pos
  omega

private lemma ordinaryPoint_not_badAtInfinity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    ¬ordinaryBadAtInfinity W (ordinaryPoint W n) := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simpa [ordinaryPoint] using ordinaryPZero_not_badAtInfinity W
  · intro k _ hk hbad
    apply hk
    apply (ordinaryBadAtInfinity_add_Q_iff W (ordinaryPoint W k)).mp
    rw [← ordinaryPoint_add_one W k]
    exact hbad
  · intro k _ hk hbad
    apply hk
    have hstep := ordinaryPoint_add_one W (k - 1)
    rw [show k - 1 + 1 = k by ring] at hstep
    rw [hstep]
    exact (ordinaryBadAtInfinity_add_Q_iff W (ordinaryPoint W (k - 1))).mpr hbad

private def ordinaryD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (n : ℤ) : ℕ :=
  match ordinaryPoint W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num (ordinaryPaperX x)).natDegree

private lemma ordinaryQ_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryQ W ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

private lemma ordinaryD_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryD W 0 = Nat.card F := by
  rw [ordinaryD, ordinaryPoint]
  simp only [zero_zsmul, add_zero, ordinaryPZero,
    WeierstrassCurve.Affine.Point.mk]
  have hx : ordinaryPaperX (ordinaryPZeroX (F := F)) =
      RatFunc.X ^ Nat.card F := by
    unfold ordinaryPaperX ordinaryPZeroX
    rw [show Nat.card F + 2 = 2 + Nat.card F by omega, pow_add]
    field_simp [RatFunc.X_ne_zero]
  rw [hx]
  change (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
    Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

private lemma ordinary_num_degree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} {x y : RatFunc F}
    {hxy : (ordinaryTwist W).toAffine.Nonsingular x y}
    (hn : ordinaryPoint W n = .some x y hxy) :
    (RatFunc.denom (ordinaryPaperX x)).natDegree <
      (RatFunc.num (ordinaryPaperX x)).natDegree := by
  have hnotBad := ordinaryPoint_not_badAtInfinity W n
  have hnotLe : ¬(ordinaryPaperX x).intDegree ≤ 0 := by
    intro hdegree
    apply hnotBad
    rw [hn]
    exact hdegree
  have hpos : 0 < (ordinaryPaperX x).intDegree := lt_of_not_ge hnotLe
  unfold RatFunc.intDegree at hpos
  omega

private lemma ordinaryD_eq_zero_iff [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (n : ℤ) :
    ordinaryD W n = 0 ↔ ordinaryPoint W n = 0 := by
  cases hp : ordinaryPoint W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [ordinaryD, hp]
  | some x y hxy =>
      have hdeg := ordinary_num_degree W hp
      constructor
      · intro hd
        simp only [ordinaryD, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

private lemma ordinaryNoAdjacentZeros [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    : ∀ n, ordinaryD W n = 0 → ordinaryD W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (ordinaryD_eq_zero_iff W n).mp hn
  have hp1 := (ordinaryD_eq_zero_iff W (n + 1)).mp hn1
  apply ordinaryQ_ne_zero W
  have hs := ordinaryPoint_add_one W n
  rw [hp, hp1] at hs
  simpa using hs.symm

private def ordinaryMinusOneNumerator [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W

private lemma ordinaryH_derivative [CharP F 2] (W : WeierstrassCurve F) :
    (ordinaryH W).derivative = X ^ 2 := by
  unfold ordinaryH
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : ((3 : ℕ) : F) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, htwo,
      Nat.cast_one, zero_add]
  rw [htwo, hthree, map_zero, map_one]
  norm_num

private lemma derivative_frobeniusTail_ordinary [CharP F 2]
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (ordinaryH W) X e).derivative = X ^ (2 ^ e) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [frobeniusTail]
  have hexponent : 2 ^ (e + 1) - 2 = 2 * (2 ^ e - 1) := by
    rw [pow_succ]
    omega
  rw [hexponent, show X ^ (2 * (2 ^ e - 1)) =
    (X ^ (2 ^ e - 1)) ^ 2 by
      rw [← pow_mul]
      congr 1
      omega]
  rw [derivative_add, derivative_pow, derivative_mul, derivative_pow,
    ordinaryH_derivative]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  rw [htwo, map_zero]
  norm_num
  rw [← pow_mul, ← pow_add]
  congr 1
  rw [pow_succ]
  have hpowpos : 0 < 2 ^ e := pow_pos (by norm_num) e
  omega

private lemma ordinaryU_derivative [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).derivative =
      frobeniusTail (ordinaryH W) X (charTwoExponent (F := F)) +
        X ^ (Nat.card F + 1) := by
  have hexponent : 0 < charTwoExponent (F := F) := by
    have hcard : 1 < Nat.card F := Finite.one_lt_card
    rw [card_eq_two_pow (F := F)] at hcard
    exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard
  unfold ordinaryU
  rw [derivative_mul, derivative_X,
    derivative_frobeniusTail_ordinary W _ hexponent]
  rw [← card_eq_two_pow (F := F)]
  simp only [one_mul]
  rw [mul_comm, ← pow_succ]

private lemma ordinaryH_natDegree (W : WeierstrassCurve F) :
    (ordinaryH W).natDegree = 3 := by
  unfold ordinaryH
  compute_degree <;> norm_num

private lemma frobeniusTail_ordinary_natDegree
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (ordinaryH W) X e).natDegree = 3 * 2 ^ (e - 1) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusTail, ordinaryH_natDegree]
  | more e ih ih1 =>
      rw [frobeniusTail]
      have htail : frobeniusTail (ordinaryH W) X (e + 1) ≠ 0 := by
        intro hzero
        have hdegree := ih1 (by omega)
        rw [hzero] at hdegree
        simp at hdegree
      have hxpow : X ^ (2 ^ (e + 2) - 2) ≠ (0 : F[X]) :=
        pow_ne_zero _ X_ne_zero
      have hH : ordinaryH W ≠ 0 := by
        intro hzero
        have hdegree := ordinaryH_natDegree W
        rw [hzero] at hdegree
        simp at hdegree
      rw [natDegree_add_eq_left_of_natDegree_lt]
      · rw [natDegree_pow, ih1 (by omega)]
        simp [pow_succ]
        ring
      · rw [natDegree_mul hxpow hH, natDegree_pow, natDegree_X,
          ordinaryH_natDegree, natDegree_pow, ih1 (by omega)]
        norm_num
        have hpow : 2 ≤ 2 ^ (e + 1) := by
          rw [pow_succ]
          have hpos : 0 < 2 ^ e := pow_pos (by norm_num) e
          omega
        rw [pow_succ]
        omega

private lemma charTwoExponent_pos [Finite F] [CharP F 2] :
    0 < charTwoExponent (F := F) := by
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  rw [card_eq_two_pow (F := F)] at hcard
  exact Nat.pos_of_ne_zero fun h ↦ by simp [h] at hcard

private lemma ordinaryU_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryU W).natDegree =
      1 + 3 * 2 ^ (charTwoExponent (F := F) - 1) := by
  unfold ordinaryU
  have htailDegree := frobeniusTail_ordinary_natDegree W
    (charTwoExponent (F := F)) (charTwoExponent_pos (F := F))
  have htail : frobeniusTail (ordinaryH W) X
      (charTwoExponent (F := F)) ≠ 0 := by
    intro hzero
    rw [hzero] at htailDegree
    simp at htailDegree
  rw [natDegree_mul X_ne_zero htail, natDegree_X, htailDegree]

private lemma ordinaryMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (ordinaryMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk]
    rw [pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hU : (ordinaryU W).natDegree ≤ 2 * Nat.card F := by
    rw [ordinaryU_natDegree W]
    change 1 + 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    X ^ (Nat.card F + 1) + ordinaryU W
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    dsimp only [remainder]
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have hfirst : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    have hsecond : (X ^ (Nat.card F + 1) : F[X]).natDegree ≤
        2 * Nat.card F := by
      rw [natDegree_X_pow]
      omega
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le hfirst hsecond)) hU)
  have heq : ordinaryMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold ordinaryMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

private lemma eval_ordinaryU [Finite F] (W : WeierstrassCurve F) (x : F) :
    (ordinaryU W).eval x =
      x * frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
  simp only [ordinaryU, eval_mul, eval_X, eval_frobeniusTail]

private lemma eval_ordinaryMinusOneNumerator [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F) :
    (ordinaryMinusOneNumerator W).eval x =
      x ^ 2 + x * frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q1 : x ^ (2 * Nat.card F + 1) = x ^ 3 := by
    calc
      x ^ (2 * Nat.card F + 1) = x ^ (2 * Nat.card F) * x := pow_succ _ _
      _ = (x ^ Nat.card F) ^ 2 * x := by
        rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul]
      _ = x ^ 3 := by rw [hxq]; ring
  have hxq2 : x ^ (Nat.card F + 2) = x ^ 3 := by
    rw [pow_add, hxq]
    ring
  have hxq1 : x ^ (Nat.card F + 1) = x ^ 2 := by
    rw [pow_add, hxq]
    ring
  simp only [ordinaryMinusOneNumerator, eval_add, eval_pow, eval_X,
    eval_ordinaryU, hx2q1, hxq2, hxq1]
  have hcancel : x ^ 3 + x ^ 3 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hcancel

private lemma eval_derivative_ordinaryMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) (x : F) :
    (ordinaryMinusOneNumerator W).derivative.eval x =
      x + frobeniusValue ((ordinaryH W).eval x) x
        (charTwoExponent (F := F)) := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hqcast : ((Nat.card F : ℕ) : F) = 0 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact Nat.cast_card_eq_zero F
  have hcoeff1 : (((2 * Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hcoeff2 : (((Nat.card F + 2 : ℕ) : F)) = 0 := by
    push_cast
    rw [hqcast, zero_add]
    exact CharTwo.two_eq_zero
  have hcoeff3 : (((Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have hxq1 : x ^ (Nat.card F + 1) = x ^ 2 := by
    rw [pow_add, hxq]
    ring
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  have hexponent3 : Nat.card F + 1 - 1 = Nat.card F := by omega
  unfold ordinaryMinusOneNumerator
  simp only [derivative_add, derivative_pow, derivative_X,
    ordinaryU_derivative, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    eval_one, eval_frobeniusTail, hcoeff1, hcoeff2, hcoeff3, one_mul,
    zero_mul, hexponent1, hexponent3, hx2q, hxq, hxq1]
  have hcancel : x ^ 2 + x ^ 2 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hcancel

private lemma frobeniusValue_zero_coefficient (c : F) (e : ℕ) (he : 0 < e) :
    frobeniusValue c 0 e = c ^ (2 ^ (e - 1)) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusValue]
  | more e ih ih1 =>
      rw [frobeniusValue, ih1 (by omega)]
      have hexponent : 0 < 2 ^ (e + 2) - 2 := by
        have hpowpos : 0 < 2 ^ e := pow_pos (by norm_num) e
        rw [show e + 2 = (e + 1) + 1 by omega, pow_succ, pow_succ]
        omega
      rw [zero_pow (Nat.ne_of_gt hexponent), zero_mul, add_zero, ← pow_mul]
      congr 1

private lemma ordinary_a₆_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    W.a₆ ≠ 0 := by
  have h := W.Δ'.ne_zero
  rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact h

private lemma ordinaryTailValue_zero_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    frobeniusValue ((ordinaryH W).eval 0) 0
      (charTwoExponent (F := F)) ≠ 0 := by
  rw [frobeniusValue_zero_coefficient _ _ (charTwoExponent_pos (F := F))]
  simp only [ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C,
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_add]
  exact pow_ne_zero _ (ordinary_a₆_ne_zero W)

private lemma ordinaryEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔ y ^ 2 + x * y = (ordinaryH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₃_of_isCharTwoJNeZeroNF,
    WeierstrassCurve.a₄_of_isCharTwoJNeZeroNF, one_mul, zero_mul,
    add_zero, ordinaryH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

private def affineSolutionsEquivOrdinaryFibers [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, charTwoFiber x ((ordinaryH W).eval x) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (ordinaryEquation_iff_fiber W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (ordinaryEquation_iff_fiber W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma ordinaryPointCount_eq_fiber_sum [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] [W.IsElliptic] :
    Nat.card W.toAffine.Point =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivOrdinaryFibers W), Nat.card_sigma]

private lemma ordinaryMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : ordinaryMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := ordinaryMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

private lemma rootMultiplicity_ordinaryNumerator_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) = 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot 0 := by
    change (ordinaryMinusOneNumerator W).eval 0 = 0
    rw [eval_ordinaryMinusOneNumerator]
    simp
  have hpositive : 0 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
    (Polynomial.rootMultiplicity_pos hN).mpr hroot
  have hnotTwo : ¬1 <
      Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) := by
    intro htwo
    have hderivativeRoot :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mp htwo |>.2
    have hderivative := eval_derivative_ordinaryMinusOneNumerator W 0
    rw [show (ordinaryMinusOneNumerator W).derivative.eval 0 = 0 from
      hderivativeRoot] at hderivative
    simp only [zero_add] at hderivative
    exact ordinaryTailValue_zero_ne_zero W hderivative.symm
  omega

private lemma rootMultiplicity_ordinaryNumerator_eq_zero [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) (x : F) (hx : x ≠ 0)
    (hvalue : frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) = 0) :
    Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heval := eval_ordinaryMinusOneNumerator W x
  rw [hvalue, mul_zero, add_zero] at heval
  exact (pow_ne_zero 2 hx) (heval.symm.trans hroot)

private lemma ordinaryNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F)
    (hvalue : frobeniusValue ((ordinaryH W).eval x) x
      (charTwoExponent (F := F)) = x) :
    (X - C x) ^ 2 ∣ ordinaryMinusOneNumerator W := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hroot : (ordinaryMinusOneNumerator W).IsRoot x := by
    change (ordinaryMinusOneNumerator W).eval x = 0
    rw [eval_ordinaryMinusOneNumerator, hvalue]
    simpa only [pow_two] using CharTwo.add_self_eq_zero (x * x)
  have hderivativeRoot : (ordinaryMinusOneNumerator W).derivative.IsRoot x := by
    change (ordinaryMinusOneNumerator W).derivative.eval x = 0
    rw [eval_derivative_ordinaryMinusOneNumerator, hvalue]
    exact CharTwo.add_self_eq_zero x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

private lemma count_roots_charTwoFrobeniusPolynomial [Finite F] (x : F) :
    Multiset.count x (charTwoFrobeniusPolynomial : F[X]).roots = 1 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  unfold charTwoFrobeniusPolynomial
  rw [@Nat.card_eq_fintype_card F fintypeF,
    FiniteField.roots_X_pow_card_sub_X]
  simp

private lemma count_roots_charTwoFrobeniusPolynomial_sq [Finite F] (x : F) :
    Multiset.count x ((charTwoFrobeniusPolynomial : F[X]) ^ 2).roots = 2 := by
  rw [Polynomial.roots_pow, Multiset.count_nsmul,
    count_roots_charTwoFrobeniusPolynomial]

private def ordinaryMinusOneGCD [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  gcd (ordinaryMinusOneNumerator W) (charTwoFrobeniusPolynomial ^ 2)

private lemma count_roots_ordinaryMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    (x : F) :
    Multiset.count x (ordinaryMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  by_cases hx : x = 0
  · subst x
    have hlinearN : X - C 0 ∣ ordinaryMinusOneNumerator W := by
      apply Polynomial.dvd_iff_isRoot.mpr
      change (ordinaryMinusOneNumerator W).eval 0 = 0
      rw [eval_ordinaryMinusOneNumerator]
      simp
    have hlinearL' : X - C 0 ∣
        (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
      hlinearL.trans ⟨charTwoFrobeniusPolynomial, by ring⟩
    have hcommon : X - C 0 ∣ ordinaryMinusOneGCD W := by
      unfold ordinaryMinusOneGCD
      exact dvd_gcd hlinearN hlinearL'
    have hlower : 1 ≤
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) := by
      rw [Polynomial.le_rootMultiplicity_iff hG]
      simpa using hcommon
    have hupper :
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤ 1 := by
      calc
        Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) ≤
            Polynomial.rootMultiplicity 0 (ordinaryMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN 0
        _ = 1 := rootMultiplicity_ordinaryNumerator_zero W
    have hroot : Polynomial.rootMultiplicity 0 (ordinaryMinusOneGCD W) = 1 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot, charTwoFiber_card_eq_one]
  · rcases frobeniusValue_eq_zero_or_eq
        (c := (ordinaryH W).eval x) hx with hvalue | hvalue
    · have hupper :
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 0 := by
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x (ordinaryMinusOneNumerator W) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
          _ = 0 := rootMultiplicity_ordinaryNumerator_eq_zero W x hx hvalue
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 0 :=
        Nat.eq_zero_of_le_zero hupper
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_two_of_value_eq_zero hx hvalue]
    · have hcommon : (X - C x) ^ 2 ∣ ordinaryMinusOneGCD W := by
        unfold ordinaryMinusOneGCD
        exact dvd_gcd (ordinaryNumerator_sq_dvd_of_value_eq W x hvalue)
          hlinearLsq
      have hlower : 2 ≤
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) :=
        (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
      have hrootL : Polynomial.rootMultiplicity x
          ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
        rw [← Polynomial.count_roots]
        exact count_roots_charTwoFrobeniusPolynomial_sq x
      have hupper : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤ 2 :=
        calc
          Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) ≤
              Polynomial.rootMultiplicity x
                ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
            Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
          _ = 2 := hrootL
      have hroot : Polynomial.rootMultiplicity x (ordinaryMinusOneGCD W) = 2 :=
        le_antisymm hupper hlower
      rw [Polynomial.count_roots, hroot,
        charTwoFiber_card_eq_zero_of_value_eq hx hvalue]

private lemma ordinaryMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : ordinaryMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (ordinaryMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots) =
        (ordinaryMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (ordinaryMinusOneGCD W).roots) (by simp))
  calc
    (ordinaryMinusOneGCD W).natDegree =
        (ordinaryMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (ordinaryMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_ordinaryMinusOneGCD W x

private lemma ordinaryMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x)) =
      2 * Nat.card F := by
  rw [ordinaryMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber x ((ordinaryH W).eval x)) +
        Nat.card (charTwoFiber x ((ordinaryH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two x _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma charTwo_natDegree_num_div (p q : F[X]) (hq : q ≠ 0) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p /
        algebraMap F[X] (RatFunc F) q)).natDegree =
      (p / gcd p q).natDegree := by
  have hg : gcd p q ≠ 0 := by
    intro hzero
    exact hq ((gcd_eq_zero_iff _ _).mp hzero).2
  have hgdivq : gcd p q ∣ q := gcd_dvd_right _ _
  have hmul : gcd p q * (q / gcd p q) = q :=
    EuclideanDomain.mul_div_cancel' hg hgdivq
  have hquotient : q / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hq hmul.symm
  rw [RatFunc.num_div, Polynomial.natDegree_C_mul]
  exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hquotient)

private lemma ordinaryMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  have hN := ordinaryMinusOneNumerator_ne_zero W
  have hG : ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold ordinaryMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : ordinaryMinusOneGCD W ∣ ordinaryMinusOneNumerator W := by
    unfold ordinaryMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : ordinaryMinusOneGCD W *
      (ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W) =
        ordinaryMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : ordinaryMinusOneNumerator W / ordinaryMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, ordinaryMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := ordinaryMinusOneGCD_natDegree_add_fiber_sum W
  omega

private lemma num_natDegree_ordinaryMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber x ((ordinaryH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact ordinaryMinusOneQuotient_natDegree W

private lemma ordinaryPZeroX_ne_QX [Finite F] :
    ordinaryPZeroX (F := F) ≠ RatFunc.X ^ 3 := by
  intro heq
  have hdegree := congrArg RatFunc.intDegree heq
  simp only [ordinaryPZeroX] at hdegree
  rw [intDegree_pow RatFunc.X_ne_zero,
    intDegree_pow RatFunc.X_ne_zero] at hdegree
  simp only [RatFunc.intDegree_X, mul_one] at hdegree
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  omega

private lemma ordinaryPaperY_neg_pZeroY [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryPaperY
        ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
          (ordinaryPZeroY W)) =
      algebraMap F[X] (RatFunc F) (ordinaryU W) / RatFunc.X +
        RatFunc.X ^ Nat.card F := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist,
    ordinaryPZeroX, ordinaryPZeroY, sub_eq_add_neg, CharTwo.neg_eq]
  unfold ordinaryPaperY
  rw [map_mul, map_pow, RatFunc.algebraMap_X]
  field_simp [RatFunc.X_ne_zero]
  ring

private lemma algebraMap_charTwoFrobeniusPolynomial [Finite F] [CharP F 2] :
    algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial =
      RatFunc.X ^ Nat.card F + RatFunc.X := by
  simp only [charTwoFrobeniusPolynomial, sub_eq_add_neg, CharTwo.neg_eq,
    map_add, map_pow, RatFunc.algebraMap_X]

private lemma ordinaryPaperX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) =
      algebraMap F[X] (RatFunc F) (ordinaryMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [ordinaryPaperX_addX_Q_eq W ordinaryPZeroX_ne_QX]
  rw [ordinaryPaperX_pZeroX, ordinaryPaperY_neg_pZeroY W]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [ordinaryMinusOneNumerator, map_add, map_pow,
    RatFunc.algebraMap_X, sub_eq_add_neg, CharTwo.neg_eq]
  let q := Nat.card F
  let t : RatFunc F := RatFunc.X
  let r := t ^ q
  let u := algebraMap F[X] (RatFunc F) (ordinaryU W)
  let a := RatFunc.C W.a₂
  let b := RatFunc.C W.a₆
  let s := u / t + r
  let L := r + t
  let n := t ^ (2 * q + 1) + t ^ (q + 2) + t ^ (q + 1) + u
  change (s / L) ^ 2 + s / L + b / t ^ 2 + r = n / L ^ 2
  have ht : t ≠ 0 := RatFunc.X_ne_zero
  have hL : L ≠ 0 := by
    dsimp only [L, r, t, q]
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hu := congrArg (algebraMap F[X] (RatFunc F)) (ordinaryU_identity W)
  rw [ordinaryH_pow_card W] at hu
  simp only [ordinaryH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hu
  change u ^ 2 + t ^ (q + 1) * u =
    t ^ 2 * (t ^ (3 * q) + a * t ^ (2 * q) + b) +
      t ^ (2 * q) * (t ^ 3 + a * t ^ 2 + b) at hu
  have htq1 : t ^ (q + 1) = t * r := by
    dsimp only [r]
    rw [pow_succ]
    ring
  have ht2q : t ^ (2 * q) = r ^ 2 := by
    dsimp only [r]
    calc
      t ^ (2 * q) = t ^ (q * 2) := by congr 1; omega
      _ = (t ^ q) ^ 2 := pow_mul t q 2
  have ht3q : t ^ (3 * q) = r ^ 3 := by
    dsimp only [r]
    calc
      t ^ (3 * q) = t ^ (q * 3) := by congr 1; omega
      _ = (t ^ q) ^ 3 := pow_mul t q 3
  rw [htq1, ht2q, ht3q] at hu
  have hu' : u ^ 2 + t * r * u =
      t ^ 2 * r ^ 3 + b * t ^ 2 + t ^ 3 * r ^ 2 + b * r ^ 2 := by
    have hcancel : a * t ^ 2 * r ^ 2 + a * t ^ 2 * r ^ 2 = 0 :=
      CharTwo.add_self_eq_zero _
    linear_combination hu + hcancel
  dsimp only [s, n]
  field_simp [ht, hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hu' +
    (u * t * t ^ q + t * t ^ q * b + t ^ 2 * t ^ (q * 2) +
      t ^ 2 * t ^ (q * 3) + t ^ 2 * b + t ^ 3 * t ^ (q * 2) +
        t ^ (q * 2) * b) * htwo

private lemma ordinaryPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ∃ y hxy, ordinaryPoint W (-1) =
      .some
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)) y hxy := by
  have hp : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryPZero_equation W)
  have hneg : (ordinaryTwist W).toAffine.Nonsingular
      (ordinaryPZeroX (F := F))
      ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
        (ordinaryPZeroY W)) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -ordinaryPZero W = .some (ordinaryPZeroX (F := F))
        ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
          (ordinaryPZeroY W)) hneg := by
    rw [show ordinaryPZero W =
      .some (ordinaryPZeroX (F := F)) (ordinaryPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) ordinaryPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (ordinaryQ_equation W))
  rw [← hnegP, ← show ordinaryQ W = .some (RatFunc.X ^ 3) 0 _ from rfl]
    at hadd
  have hpoint : ordinaryPoint W (-1) =
      -(-ordinaryPZero W + ordinaryQ W) := by
    unfold ordinaryPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private lemma ordinaryD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ordinaryD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := ordinaryPoint_neg_one_eq_some W
  unfold ordinaryD
  rw [hpoint]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (ordinaryPZeroX (F := F))
          (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (ordinaryPZeroX (F := F))
            (RatFunc.X ^ 3)
            ((ordinaryTwist W).toAffine.negY (ordinaryPZeroX (F := F))
              (ordinaryPZeroY W)) 0)))).natDegree = _
  rw [ordinaryPaperX_negPZero_add_Q W]
  rw [num_natDegree_ordinaryMinusOneRat W]
  exact (ordinaryPointCount_eq_fiber_sum W).symm

private lemma ordinary_product_formula {R : Type*} [CommRing R] [CharP R 2]
    (t f g b z : R)
    (curve : z ^ 2 + t * f * g * z + t ^ 2 * f ^ 3 * g +
      b * t ^ 2 * g ^ 4 + t ^ 3 * f ^ 2 * g ^ 2 + b * f ^ 2 * g ^ 2 = 0) :
    (t * f * (t * g + f) + t * f * g + z) *
        (t * f * (t * g + f) + z) =
      (t ^ 2 * f ^ 2 + b * g ^ 2) * (t * g + f) ^ 2 := by
  have htwo : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination curve +
    (-t * f * g ^ 3 * b + t * f ^ 2 * z + t ^ 2 * f * g * z -
      t ^ 2 * g ^ 4 * b - f ^ 2 * g ^ 2 * b) * htwo

private def ordinaryNeighborFirst (W : WeierstrassCurve F) (f g : F[X]) : F[X] :=
  (X * f) ^ 2 + C W.a₆ * g ^ 2

private def ordinaryNeighborSecond (f g : F[X]) : F[X] :=
  X * f * g

private def neighborDenominator (f g : F[X]) : F[X] :=
  (X * g + f) ^ 2

private lemma ordinaryNeighborFirst_natDegree
    (W : WeierstrassCurve F) {f g : F[X]} (hf : f ≠ 0)
    (hdegree : g.natDegree < f.natDegree) :
    (ordinaryNeighborFirst W f g).natDegree = 2 * f.natDegree + 2 := by
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  have hremainder : (C W.a₆ * g ^ 2).natDegree < 2 * f.natDegree + 2 := by
    calc
      (C W.a₆ * g ^ 2).natDegree ≤ (g ^ 2).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
      _ < 2 * f.natDegree + 2 := by omega
  unfold ordinaryNeighborFirst
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hmain
  · rwa [hmain]

private lemma ordinaryNeighbor_primitive [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {f g : F[X]} (hfg : IsCoprime f g) (hden : X * g + f ≠ 0) :
    PrimitiveTriple (ordinaryNeighborFirst W f g)
      (ordinaryNeighborSecond f g) (neighborDenominator f g) := by
  have hb : W.a₆ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
    exact h
  apply primitiveTriple_of_no_common_irreducible
    (pow_ne_zero 2 hden)
  intro p hp hpFirst hpSecond hpDen
  have hprime := hp.prime
  have hpD : p ∣ X * g + f := hprime.dvd_of_dvd_pow hpDen
  have forceG (hpMain : p ∣ (X * f) ^ 2) : p ∣ g := by
    have hpRest : p ∣ C W.a₆ * g ^ 2 := by
      have hdifference := hpFirst.sub hpMain
      convert hdifference using 1
      unfold ordinaryNeighborFirst
      ring
    rcases hprime.dvd_mul.mp hpRest with hpC | hpg
    · have hCunit : IsUnit (C W.a₆) :=
        Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb)
      exact (hprime.not_dvd_one
        (hpC.trans (isUnit_iff_dvd_one.mp hCunit))).elim
    · exact hprime.dvd_of_dvd_pow hpg
  have commonDvd (hpf : p ∣ f) (hpg : p ∣ g) : False :=
    hp.not_isUnit (hfg.isUnit_of_dvd' hpf hpg)
  rcases hprime.dvd_mul.mp hpSecond with hpXf | hpg
  · rcases hprime.dvd_mul.mp hpXf with hpX | hpf
    · have hpMain : p ∣ (X * f) ^ 2 := by
        simpa [pow_two] using (hpX.mul_right f).mul_right (X * f)
      have hpg := forceG hpMain
      have hpf : p ∣ f := by
        have hdifference := hpD.sub (hpX.mul_right g)
        convert hdifference using 1
        ring
      exact commonDvd hpf hpg
    · have hpMain : p ∣ (X * f) ^ 2 := by
        simpa [pow_two] using hpXf.mul_right (X * f)
      exact commonDvd hpf (forceG hpMain)
  · have hpf : p ∣ f := by
      have hdifference := hpD.sub (hpg.mul_left X)
      convert hdifference using 1
      ring
    exact commonDvd hpf hpg

private lemma ordinaryNeighborFirst_ratio (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (ordinaryNeighborFirst W r.num r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) /
        (RatFunc.X + r) ^ 2 := by
  simp only [ordinaryNeighborFirst, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d := by
    exact (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    ((RatFunc.X * algebraMap F[X] (RatFunc F) r.num) ^ 2 +
        RatFunc.C W.a₆ * d ^ 2) /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show (RatFunc.X * (r * d)) ^ 2 + RatFunc.C W.a₆ * d ^ 2 =
      d ^ 2 * (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma ordinaryNeighborSecond_ratio (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (ordinaryNeighborSecond r.num r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      RatFunc.X * r / (RatFunc.X + r) ^ 2 := by
  simp only [ordinaryNeighborSecond, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d := by
    exact (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    RatFunc.X * algebraMap F[X] (RatFunc F) r.num * d /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show RatFunc.X * (r * d) * d = d ^ 2 * (RatFunc.X * r) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma ordinary_neighbor_plus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + r * s =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X + r ≠ 0) :
    (s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r =
      (RatFunc.X * r * (RatFunc.X + r) + RatFunc.X * s) /
        (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆ + r * s := by
    calc
      s ^ 2 = (s ^ 2 + r * s) + r * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  rw [div_pow, hs2, hdiffEq]
  field_simp [hdiff, RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma ordinary_neighbor_minus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + r * s =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s + r) / (r - RatFunc.X)) ^ 2 +
        (s + r) / (r - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + r =
      (RatFunc.X * r * (RatFunc.X + r) + RatFunc.X * r + RatFunc.X * s) /
        (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆ + r * s := by
    calc
      s ^ 2 = (s ^ 2 + r * s) + r * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  have hsr2 : (s + r) ^ 2 =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆ + r * s + r ^ 2 := by
    calc
      (s + r) ^ 2 = s ^ 2 + r ^ 2 := by
        rw [add_sq, show (2 : RatFunc F) = 0 from CharTwo.two_eq_zero]
        ring
      _ = _ := by rw [hs2]
  rw [div_pow, hsr2, hdiffEq]
  field_simp [hdiff, RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma ordinary_neighbor_pair_product [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + r * s =
      r ^ 3 + (RatFunc.X + RatFunc.C W.a₆ / RatFunc.X ^ 2) * r ^ 2 +
        RatFunc.C W.a₆)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) *
      (((s + r) / (r - RatFunc.X)) ^ 2 +
        (s + r) / (r - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₆) /
        (RatFunc.X + r) ^ 2 := by
  rw [ordinary_neighbor_plus W heq hdiff,
    ordinary_neighbor_minus W heq hdiff]
  have heq' := heq
  field_simp [RatFunc.X_ne_zero] at heq'
  have heq'' :
      s * r * RatFunc.X ^ 2 + s ^ 2 * RatFunc.X ^ 2 =
        r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
          r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆ := by
    calc
      _ = s * (s + r) * RatFunc.X ^ 2 := by ring
      _ = r ^ 2 *
          (r * RatFunc.X ^ 2 + (RatFunc.X ^ 3 + RatFunc.C W.a₆)) +
            RatFunc.X ^ 2 * RatFunc.C W.a₆ := heq'
      _ = _ := by ring
  have hcurve :
      (RatFunc.X * s) ^ 2 + RatFunc.X * r * (RatFunc.X * s) +
        RatFunc.X ^ 2 * r ^ 3 + RatFunc.C W.a₆ * RatFunc.X ^ 2 +
          RatFunc.X ^ 3 * r ^ 2 + RatFunc.C W.a₆ * r ^ 2 = 0 := by
    calc
      _ = (s * r * RatFunc.X ^ 2 + s ^ 2 * RatFunc.X ^ 2) +
          (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
            r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) := by
            ring
      _ = (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
            r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) +
          (r ^ 2 * RatFunc.X ^ 3 + r ^ 2 * RatFunc.C W.a₆ +
            r ^ 3 * RatFunc.X ^ 2 + RatFunc.X ^ 2 * RatFunc.C W.a₆) := by
              rw [heq'']
      _ = 0 := CharTwo.add_self_eq_zero _
  have hcurve' :
      (RatFunc.X * s) ^ 2 + RatFunc.X * r * 1 * (RatFunc.X * s) +
        RatFunc.X ^ 2 * r ^ 3 * 1 +
          RatFunc.C W.a₆ * RatFunc.X ^ 2 * 1 ^ 4 +
            RatFunc.X ^ 3 * r ^ 2 * 1 ^ 2 +
              RatFunc.C W.a₆ * r ^ 2 * 1 ^ 2 = 0 := by
    simpa using hcurve
  have hformula := ordinary_product_formula RatFunc.X r 1
    (RatFunc.C W.a₆) (RatFunc.X * s) hcurve'
  field_simp [hdiff]
  linear_combination hformula

private lemma ordinary_neighbor_pair_sum [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + s / (r - RatFunc.X) +
        RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) +
      (((s + r) / (r - RatFunc.X)) ^ 2 +
        (s + r) / (r - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + r) =
      RatFunc.X * r / (RatFunc.X + r) ^ 2 := by
  have hdiff' : r - RatFunc.X ≠ 0 := by
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using hdiff
  field_simp [hdiff, hdiff', RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, CharTwo.neg_eq, sub_eq_add_neg, mul_zero, zero_add, add_zero]
  ring

private lemma ordinaryPaperY_negY [CharP F 2]
    (W : WeierstrassCurve F) (x y : RatFunc F) :
    ordinaryPaperY ((ordinaryTwist W).toAffine.negY x y) =
      ordinaryPaperY y + ordinaryPaperX x := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist,
    sub_eq_add_neg, CharTwo.neg_eq]
  unfold ordinaryPaperY ordinaryPaperX
  field_simp [RatFunc.X_ne_zero]
  ring

private lemma neighborPolynomial_ne_zero (r : RatFunc F)
    (hdiff : RatFunc.X + r ≠ 0) : X * r.denom + r.num ≠ 0 := by
  intro hzero
  have hden : algebraMap F[X] (RatFunc F) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num =
      r * algebraMap F[X] (RatFunc F) r.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom r)
  have hmap := congrArg (algebraMap F[X] (RatFunc F)) hzero
  simp only [map_add, map_mul, RatFunc.algebraMap_X, map_zero] at hmap
  rw [hnum] at hmap
  apply hdiff
  exact (mul_eq_zero.mp (show
    (RatFunc.X + r) * algebraMap F[X] (RatFunc F) r.denom = 0 by
      linear_combination hmap)).resolve_right hden

private lemma ordinary_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJNeZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (ordinaryTwist W).toAffine.Nonsingular x y}
    {hMinus : (ordinaryTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (ordinaryTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X ^ 3)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W)
    (hdegree : (ordinaryPaperX x).denom.natDegree <
      (ordinaryPaperX x).num.natDegree)
    (hdegreeMinus : (ordinaryPaperX xMinus).denom.natDegree <
      (ordinaryPaperX xMinus).num.natDegree)
    (hdegreePlus : (ordinaryPaperX xPlus).denom.natDegree <
      (ordinaryPaperX xPlus).num.natDegree) :
    (ordinaryPaperX xMinus).num.natDegree +
        (ordinaryPaperX xPlus).num.natDegree =
      2 * (ordinaryPaperX x).num.natDegree + 2 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3) y 0) :=
    hplusEq.1
  have hneg : (ordinaryTwist W).toAffine.Nonsingular x
      ((ordinaryTwist W).toAffine.negY x y) :=
    ((ordinaryTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (ordinaryTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (ordinaryTwist W).toAffine.Point) - ordinaryQ W =
    -(-(.some x y hxy : (ordinaryTwist W).toAffine.Point) + ordinaryQ W) by
      abel] at hminusEq
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (ordinaryTwist W).toAffine.addX x (RatFunc.X ^ 3)
        ((ordinaryTwist W).toAffine.slope x (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : ordinaryPaperX xPlus =
      (ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        ordinaryPaperY y / (ordinaryPaperX x - RatFunc.X) +
          RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxPlus]
    exact ordinaryPaperX_addX_Q_eq W hxQ
  have hrMinus : ordinaryPaperX xMinus =
      ((ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X)) ^ 2 +
        (ordinaryPaperY y + ordinaryPaperX x) /
          (ordinaryPaperX x - RatFunc.X) +
            RatFunc.C W.a₆ / RatFunc.X ^ 2 + ordinaryPaperX x := by
    rw [hxMinus, ordinaryPaperX_addX_Q_eq W hxQ,
      ordinaryPaperY_negY W]
  have heq := ordinary_paper_coordinates_equation W hxy
  have hdiff : RatFunc.X + ordinaryPaperX x ≠ 0 := by
    intro hzero
    apply hxQ
    have hr : ordinaryPaperX x = RatFunc.X := by
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
    unfold ordinaryPaperX at hr
    calc
      x = RatFunc.X * RatFunc.X ^ 2 :=
        (div_eq_iff (pow_ne_zero 2 RatFunc.X_ne_zero)).mp hr
      _ = RatFunc.X ^ 3 := by ring
  have hpairProd := ordinary_neighbor_pair_product W heq hdiff
  have hpairSum := ordinary_neighbor_pair_sum W
    (s := ordinaryPaperY y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborFirst W (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus * ordinaryPaperX xPlus := by
    rw [ordinaryNeighborFirst_ratio]
    calc
      _ = ordinaryPaperX xPlus * ordinaryPaperX xMinus := hpairProd.symm
      _ = ordinaryPaperX xMinus * ordinaryPaperX xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F)
          (ordinaryNeighborSecond (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) /
        algebraMap F[X] (RatFunc F)
          (neighborDenominator (ordinaryPaperX x).num
            (ordinaryPaperX x).denom) =
        ordinaryPaperX xMinus + ordinaryPaperX xPlus := by
    rw [ordinaryNeighborSecond_ratio]
    calc
      _ = ordinaryPaperX xPlus + ordinaryPaperX xMinus := hpairSum.symm
      _ = ordinaryPaperX xMinus + ordinaryPaperX xPlus := by ring
  have hpoly : X * (ordinaryPaperX x).denom + (ordinaryPaperX x).num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := ordinaryNeighbor_primitive W
    (RatFunc.isCoprime_num_denom (ordinaryPaperX x)) hpoly
  have hout : neighborDenominator (ordinaryPaperX x).num
      (ordinaryPaperX x).denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := ordinaryNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma num_natDegree_div_of_isCoprime (p q : F[X])
    (hp : p ≠ 0) (hq : q ≠ 0) (hcop : IsCoprime p q) :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) p /
        algebraMap F[X] (RatFunc F) q)).natDegree = p.natDegree := by
  rw [charTwo_natDegree_num_div p q hq]
  have hgUnit : IsUnit (gcd p q) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg : gcd p q ≠ 0 := hgUnit.ne_zero
  have hmul : gcd p q * (p / gcd p q) = p :=
    EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hquot : p / gcd p q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact hp hmul.symm
  have hdegree := Polynomial.natDegree_mul hg hquot
  rw [hmul, Polynomial.natDegree_eq_zero_of_isUnit hgUnit, zero_add] at hdegree
  exact hdegree.symm

private lemma ordinaryPoint_sub_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] (n : ℤ) :
    ordinaryPoint W (n - 1) = ordinaryPoint W n - ordinaryQ W := by
  have hstep := ordinaryPoint_add_one W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

private lemma ordinaryD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma ordinaryD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = -ordinaryQ W) : ordinaryD W n = 1 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num (ordinaryPaperX (RatFunc.X ^ 3))).natDegree = 1
  rw [ordinaryPaperX_Q_coordinate]
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma ordinaryQ_y_ne_negY [CharP F 2]
    (W : WeierstrassCurve F) :
    (0 : RatFunc F) ≠
      (ordinaryTwist W).toAffine.negY (RatFunc.X ^ 3) 0 := by
  simp only [WeierstrassCurve.Affine.negY, ordinaryTwist, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  simpa only [add_zero] using
    (mul_ne_zero (RatFunc.X_ne_zero (K := F))
      (pow_ne_zero 3 (RatFunc.X_ne_zero (K := F)))).symm

private def ordinaryDoubleNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 + C W.a₆

private lemma ordinaryPaperX_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) :
    ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)) =
      algebraMap F[X] (RatFunc F) (ordinaryDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (X ^ 2) := by
  rw [(ordinaryTwist W).toAffine.slope_of_Y_ne rfl
    (ordinaryQ_y_ne_negY W)]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    ordinaryTwist, ordinaryPaperX, map_add, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C, ordinaryDoubleNumerator, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  field_simp [RatFunc.X_ne_zero]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma ordinaryDoubleNumerator_natDegree (W : WeierstrassCurve F) :
    (ordinaryDoubleNumerator W).natDegree = 4 := by
  unfold ordinaryDoubleNumerator
  compute_degree
  norm_num

private lemma ordinaryDoubleNumerator_coprime [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    IsCoprime (ordinaryDoubleNumerator W) (X ^ 2) := by
  have hb : W.a₆ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
    exact h
  refine ⟨C W.a₆⁻¹, C W.a₆⁻¹ * X ^ 2, ?_⟩
  unfold ordinaryDoubleNumerator
  have hinv : C W.a₆⁻¹ * C W.a₆ = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hb, C_1]
  have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  linear_combination hinv + X ^ 4 * C W.a₆⁻¹ * htwo

private lemma ordinary_num_natDegree_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (ordinaryDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (X ^ 2))).natDegree = 4 := by
  rw [num_natDegree_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := ordinaryDoubleNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    (pow_ne_zero 2 X_ne_zero) (ordinaryDoubleNumerator_coprime W)]
  exact ordinaryDoubleNumerator_natDegree W

private lemma ordinaryD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = ordinaryQ W + ordinaryQ W) :
    ordinaryD W n = 4 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (ordinaryQ_y_ne_negY W)]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)))).natDegree = 4
  rw [ordinaryPaperX_doubleQ W, ordinary_num_natDegree_doubleQ W]

private lemma ordinaryD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF]
    {n : ℤ} (hn : ordinaryPoint W n = -(ordinaryQ W + ordinaryQ W)) :
    ordinaryD W n = 4 := by
  have hQ : (ordinaryTwist W).toAffine.Nonsingular (RatFunc.X ^ 3) 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (ordinaryQ_equation W)
  unfold ordinaryD
  rw [hn]
  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (ordinaryQ_y_ne_negY W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      (ordinaryPaperX
        ((ordinaryTwist W).toAffine.addX (RatFunc.X ^ 3) (RatFunc.X ^ 3)
          ((ordinaryTwist W).toAffine.slope (RatFunc.X ^ 3)
            (RatFunc.X ^ 3) 0 0)))).natDegree = 4
  rw [ordinaryPaperX_doubleQ W, ordinary_num_natDegree_doubleQ W]

private lemma ordinaryD_recurrence [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    ∀ n, ordinaryD W (n - 1) + ordinaryD W (n + 1) = 2 * ordinaryD W n + 2 := by
  intro n
  cases hn : ordinaryPoint W n with
  | zero =>
      have hplus := ordinaryPoint_add_one W n
      have hminus := ordinaryPoint_sub_one W n
      rw [hn] at hplus hminus
      have hplusQ : ordinaryPoint W (n + 1) = ordinaryQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : ordinaryPoint W (n - 1) = -ordinaryQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := ordinaryD_eq_one_of_point_eq_Q W hplusQ
      have hdMinus := ordinaryD_eq_one_of_point_eq_neg_Q W hminusQ
      have hd : ordinaryD W n = 0 := by simp [ordinaryD, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : ordinaryPoint W (n - 1) with
      | zero =>
          have hsub := ordinaryPoint_sub_one W n
          rw [hn, hminusPoint] at hsub
          have hnQ : ordinaryPoint W n = ordinaryQ W := by
            have hxyQ :
                (.some x y hxy : (ordinaryTwist W).toAffine.Point) =
                  ordinaryQ W := sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := ordinaryPoint_add_one W n
          rw [hnQ] at hplus
          have hd := ordinaryD_eq_one_of_point_eq_Q W hnQ
          have hdPlus := ordinaryD_eq_four_of_point_eq_two_Q W hplus
          have hdMinus : ordinaryD W (n - 1) = 0 := by
            simp [ordinaryD, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : ordinaryPoint W (n + 1) with
          | zero =>
              have hadd := ordinaryPoint_add_one W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : ordinaryPoint W n = -ordinaryQ W := by
                have htranslated := congrArg
                  (fun P : (ordinaryTwist W).toAffine.Point ↦ P - ordinaryQ W)
                  hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (ordinaryTwist W).toAffine.Point) =
                      -ordinaryQ W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := ordinaryPoint_sub_one W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  ordinaryPoint W (n - 1) =
                    -(ordinaryQ W + ordinaryQ W) := by
                calc
                  ordinaryPoint W (n - 1) = -ordinaryQ W - ordinaryQ W :=
                    hminus
                  _ = -(ordinaryQ W + ordinaryQ W) := by abel
              have hd := ordinaryD_eq_one_of_point_eq_neg_Q W hnNegQ
              have hdMinus :=
                ordinaryD_eq_four_of_point_eq_neg_two_Q W hminusNegTwo
              have hdPlus : ordinaryD W (n + 1) = 0 := by
                simp [ordinaryD, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := ordinaryPoint_add_one W n
              have hminus := ordinaryPoint_sub_one W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (ordinaryTwist W).toAffine.Point) ≠
                    ordinaryQ W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (ordinaryTwist W).toAffine.Point) ≠
                    -ordinaryQ W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (ordinaryTwist W).toAffine.Nonsingular
                  (RatFunc.X ^ 3) 0 :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (ordinaryQ_equation W)
              have hxQ : x ≠ RatFunc.X ^ 3 := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show ordinaryQ W = .some (RatFunc.X ^ 3) 0 hQ from rfl]
                  exact heq
              have hdegree := ordinary_num_degree W hn
              have hdegreeMinus := ordinary_num_degree W hminusPoint
              have hdegreePlus := ordinary_num_degree W hplusPoint
              have hgeneric := ordinary_generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [ordinaryD, hn, hminusPoint, hplusPoint] using hgeneric

private lemma ordinary_degree_computation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  exact ⟨{
    d := ordinaryD W
    zero := ordinaryD_zero W
    negOne := ordinaryD_neg_one W
    recurrence := ordinaryD_recurrence W
    noAdjacentZeros := ordinaryNoAdjacentZeros W }⟩

private def superH (W : WeierstrassCurve F) : F[X] :=
  X ^ 3 + C W.a₄ * X + C W.a₆

private def superV [Finite F] (W : WeierstrassCurve F) : F[X] :=
  frobeniusTail (superH W) (C W.a₃) (charTwoExponent (F := F))

private lemma superH_pow_card [Finite F] (W : WeierstrassCurve F) :
    superH W ^ Nat.card F =
      X ^ (3 * Nat.card F) + C W.a₄ * X ^ Nat.card F + C W.a₆ := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  rw [@Nat.card_eq_fintype_card F fintypeF]
  rw [← @FiniteField.Polynomial.expand_card F _ fintypeF]
  simp only [superH, map_add, map_mul, map_pow, Polynomial.expand_X,
    Polynomial.expand_C]
  ring

private lemma superV_identity [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      superH W ^ Nat.card F + superH W := by
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  let fintypeF : Fintype F := Fintype.ofFinite F
  have haq : W.a₃ ^ Nat.card F = W.a₃ := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card F _ fintypeF W.a₃
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact @FiniteField.pow_card_sub_one_eq_one F _ fintypeF W.a₃ ha
  have htail := frobeniusTail_identity (superH W) (C W.a₃)
    (charTwoExponent (F := F))
  rw [← card_eq_two_pow (F := F)] at htail
  have hCq : C W.a₃ ^ Nat.card F = C W.a₃ := by rw [← map_pow, haq]
  have hCq1 : C W.a₃ ^ (2 * (Nat.card F - 1)) = 1 := by
    rw [show 2 * (Nat.card F - 1) = (Nat.card F - 1) * 2 by omega,
      pow_mul, ← map_pow, haq1, map_one, one_pow]
  rw [hCq, hCq1, one_mul] at htail
  exact htail

private def superTwist (W : WeierstrassCurve F) : WeierstrassCurve (RatFunc F) :=
  ⟨0, 0, RatFunc.C W.a₃, RatFunc.C W.a₄,
    RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X⟩

private lemma superTwist_discriminant [CharP F 2]
    (W : WeierstrassCurve F) : (superTwist W).Δ = RatFunc.C W.a₃ ^ 4 := by
  simp only [superTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, add_zero, sub_zero, CharTwo.neg_eq]
  ring_nf
  rw [CharTwo.neg_eq]

private instance [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] : (superTwist W).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, superTwist_discriminant,
    isUnit_iff_ne_zero]
  apply pow_ne_zero
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  intro hC
  apply ha
  apply RatFunc.C_injective
  simpa using hC

private lemma superQ_equation [CharP F 2] (W : WeierstrassCurve F) :
    (superTwist W).toAffine.Equation RatFunc.X 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [superTwist]

private def superQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (superQ_equation W)

private def superPZeroX [Finite F] : RatFunc F := RatFunc.X ^ Nat.card F

private def superPZeroY [Finite F] (W : WeierstrassCurve F) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (superV W)

private lemma super_pZero_polynomial_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superV W ^ 2 + C W.a₃ * superV W =
      (X ^ Nat.card F) ^ 3 + C W.a₄ * X ^ Nat.card F +
        (X ^ 3 + C W.a₄ * X) := by
  rw [superV_identity W, superH_pow_card W]
  unfold superH
  ring_nf
  have htwo : (2 : F[X]) = 0 := CharTwo.two_eq_zero
  linear_combination C W.a₆ * htwo

private lemma superPZero_equation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Equation (superPZeroX (F := F))
      (superPZeroY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := congrArg (algebraMap F[X] (RatFunc F))
    (super_pZero_polynomial_equation W)
  simpa only [superTwist, superPZeroX, superPZeroY, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, add_zero] using h

private def superPZero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (superPZero_equation W)

private def superPoint [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
    (superTwist W).toAffine.Point := superPZero W + n • superQ W

private def superD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (n : ℤ) : ℕ :=
  match superPoint W n with
  | 0 => 0
  | .some x _ _ => (RatFunc.num x).natDegree

private lemma superPoint_add_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
    superPoint W (n + 1) = superPoint W n + superQ W := by
  rw [superPoint, superPoint, add_one_zsmul]
  abel

private lemma superQ_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superQ W ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

private lemma superD_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superD W 0 = Nat.card F := by
  rw [superD, superPoint]
  simp only [zero_zsmul, add_zero, superPZero, WeierstrassCurve.Affine.Point.mk,
    superPZeroX]
  change (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
    Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

private lemma super_num_degree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {x y : RatFunc F} (hxy : (superTwist W).toAffine.Nonsingular x y) :
    (RatFunc.denom x).natDegree < (RatFunc.num x).natDegree := by
  have ha : W.a₃ ≠ 0 := by
    have h := W.Δ'.ne_zero
    rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
    intro ha
    apply h
    simp [ha]
  have hCa : RatFunc.C W.a₃ ≠ 0 := by
    intro hzero
    apply ha
    apply RatFunc.C_injective
    simpa using hzero
  have heq :
      y ^ 2 + RatFunc.C W.a₃ * y =
        x ^ 3 + RatFunc.C W.a₄ * x +
          RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X := by
    have heq' := hxy.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq'
    simp only [superTwist, zero_mul, add_zero] at heq'
    linear_combination heq'
  have hxpos : 0 < x.intDegree := by
    by_contra hxnot
    have hx : x.intDegree ≤ 0 := le_of_not_gt hxnot
    let lower := x ^ 3 + RatFunc.C W.a₄ * x + RatFunc.C W.a₄ * RatFunc.X
    have hx3 : (x ^ 3).intDegree ≤ 0 := intDegree_pow_le_zero hx 3
    have hbx : (RatFunc.C W.a₄ * x).intDegree ≤ 0 := by
      simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₄) (y := x)
        (m := 0) (n := 0) (by norm_num) (by simp) hx
    have hbX : (RatFunc.C W.a₄ * RatFunc.X).intDegree ≤ 1 := by
      simpa using intDegree_mul_le_of_le
        (x := RatFunc.C W.a₄) (y := RatFunc.X)
        (m := 0) (n := 1) (by norm_num) (by simp) (by simp)
    have hlower : lower.intDegree ≤ 1 := by
      dsimp only [lower]
      have hfirst := intDegree_add_le_of_le (m := 1) (by norm_num)
        (hx3.trans (by norm_num)) (hbx.trans (by norm_num))
      exact intDegree_add_le_of_le (m := 1) (by norm_num) hfirst hbX
    have hX3 : (RatFunc.X ^ 3 : RatFunc F).intDegree = 3 := by
      rw [intDegree_pow RatFunc.X_ne_zero]
      norm_num
    have hrhs : (RatFunc.X ^ 3 + lower).intDegree = 3 := by
      rw [intDegree_add_eq_left_of_lt (pow_ne_zero 3 RatFunc.X_ne_zero)]
      · exact hX3
      · rw [hX3]
        omega
    have heq' :
        y ^ 2 + RatFunc.C W.a₃ * y = RatFunc.X ^ 3 + lower := by
      dsimp only [lower]
      linear_combination heq
    by_cases hy0 : y = 0
    · subst y
      have hrhs0 : RatFunc.X ^ 3 + lower = 0 := by
        simpa using heq'.symm
      rw [hrhs0] at hrhs
      norm_num at hrhs
    by_cases hy : y.intDegree ≤ 0
    · have hy2 : (y ^ 2).intDegree ≤ 0 := intDegree_pow_le_zero hy 2
      have hay : (RatFunc.C W.a₃ * y).intDegree ≤ 0 := by
        simpa using intDegree_mul_le_of_le (x := RatFunc.C W.a₃) (y := y)
          (m := 0) (n := 0) (by norm_num) (by simp) hy
      have hlhs : (y ^ 2 + RatFunc.C W.a₃ * y).intDegree ≤ 0 :=
        intDegree_add_le_of_le (m := 0) (by norm_num) hy2 hay
      have hdegrees := congrArg RatFunc.intDegree heq'
      rw [hrhs] at hdegrees
      omega
    · have hypos : 0 < y.intDegree := lt_of_not_ge hy
      have hy2 : (y ^ 2).intDegree = 2 * y.intDegree := by
        rw [intDegree_pow hy0]
        norm_num
      have hay : (RatFunc.C W.a₃ * y).intDegree = y.intDegree := by
        rw [RatFunc.intDegree_mul hCa hy0]
        simp
      have hlhs :
          (y ^ 2 + RatFunc.C W.a₃ * y).intDegree = 2 * y.intDegree := by
        rw [intDegree_add_eq_left_of_lt (pow_ne_zero 2 hy0), hy2]
        rw [hay]
        omega
      have hdegrees := congrArg RatFunc.intDegree heq'
      rw [hlhs, hrhs] at hdegrees
      omega
  unfold RatFunc.intDegree at hxpos
  omega

private lemma superD_eq_zero_iff [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (n : ℤ) :
    superD W n = 0 ↔ superPoint W n = 0 := by
  cases hp : superPoint W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [superD, hp]
  | some x y hxy =>
      have hdeg := super_num_degree W hxy
      constructor
      · intro hd
        simp only [superD, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

private lemma superNoAdjacentZeros [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    : ∀ n, superD W n = 0 → superD W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (superD_eq_zero_iff W n).mp hn
  have hp1 := (superD_eq_zero_iff W (n + 1)).mp hn1
  apply superQ_ne_zero W
  have hs := superPoint_add_one W n
  rw [hp, hp1] at hs
  simpa using hs.symm

private lemma super_a₃_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    W.a₃ ≠ 0 := by
  have h := W.Δ'.ne_zero
  rw [W.coe_Δ', WeierstrassCurve.Δ_of_isCharTwoJEqZeroNF_of_char_two] at h
  intro ha
  apply h
  simp [ha]

private def superMinusOneNumerator [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  X ^ (2 * Nat.card F + 1) + X ^ (Nat.card F + 2) +
    C W.a₄ * (X ^ Nat.card F + X) + C W.a₃ * superV W + C (W.a₃ ^ 2)

private lemma superH_natDegree (W : WeierstrassCurve F) :
    (superH W).natDegree = 3 := by
  unfold superH
  compute_degree <;> norm_num

private lemma frobeniusTail_super_natDegree
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (superH W) (C W.a₃) e).natDegree =
      3 * 2 ^ (e - 1) := by
  induction e using Nat.twoStepInduction with
  | zero => omega
  | one => simp [frobeniusTail, superH_natDegree]
  | more e ih ih1 =>
      rw [frobeniusTail]
      have htail : frobeniusTail (superH W) (C W.a₃) (e + 1) ≠ 0 := by
        intro hzero
        have hdegree := ih1 (by omega)
        rw [hzero] at hdegree
        simp at hdegree
      rw [natDegree_add_eq_left_of_natDegree_lt]
      · rw [natDegree_pow, ih1 (by omega)]
        simp [pow_succ]
        ring
      · calc
          (C W.a₃ ^ (2 ^ (e + 2) - 2) * superH W).natDegree =
              (C (W.a₃ ^ (2 ^ (e + 2) - 2)) * superH W).natDegree := by
                rw [map_pow]
          _ ≤ (superH W).natDegree := Polynomial.natDegree_C_mul_le _ _
          _ = 3 := superH_natDegree W
          _ < (frobeniusTail (superH W) (C W.a₃) (e + 1) ^ 2).natDegree := by
            rw [natDegree_pow, ih1 (by omega)]
            rw [show e + 1 - 1 = e by omega]
            have hpow : 0 < 2 ^ e := pow_pos (by norm_num) e
            nlinarith

private lemma superV_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superV W).natDegree = 3 * 2 ^ (charTwoExponent (F := F) - 1) :=
  frobeniusTail_super_natDegree W _ (charTwoExponent_pos (F := F))

private lemma superMinusOneNumerator_natDegree [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) :
    (superMinusOneNumerator W).natDegree = 2 * Nat.card F + 1 := by
  let e := charTwoExponent (F := F)
  let half := 2 ^ (e - 1)
  have he : 0 < e := charTwoExponent_pos (F := F)
  have hcard : Nat.card F = 2 * half := by
    rw [card_eq_two_pow (F := F)]
    change 2 ^ e = 2 * half
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    dsimp only [half]
    rw [hk, pow_succ, Nat.succ_sub_one]
    omega
  have hhalf : 1 ≤ half := by
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hV : (superV W).natDegree ≤ 2 * Nat.card F := by
    rw [superV_natDegree W]
    change 3 * half ≤ 2 * Nat.card F
    rw [hcard]
    omega
  let remainder := X ^ (Nat.card F + 2) +
    C W.a₄ * (X ^ Nat.card F + X) + C W.a₃ * superV W + C (W.a₃ ^ 2)
  have hremainder : remainder.natDegree ≤ 2 * Nat.card F := by
    have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    have h₁ : (X ^ (Nat.card F + 2) : F[X]).natDegree ≤
        2 * Nat.card F := by rw [natDegree_X_pow]; omega
    have h₂ : (C W.a₄ * (X ^ Nat.card F + X)).natDegree ≤
        2 * Nat.card F := by
      calc
        _ ≤ (X ^ Nat.card F + X : F[X]).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        _ ≤ max (Nat.card F) 1 := by
          exact (natDegree_add_le _ _).trans (max_le
            (by rw [natDegree_X_pow]; exact le_max_left _ _)
            (by rw [natDegree_X]; exact le_max_right _ _))
        _ ≤ 2 * Nat.card F := by omega
    have h₃ : (C W.a₃ * superV W).natDegree ≤ 2 * Nat.card F :=
      (Polynomial.natDegree_C_mul_le _ _).trans hV
    have h₄ : (C (W.a₃ ^ 2) : F[X]).natDegree ≤ 2 * Nat.card F := by
      rw [natDegree_C]
      omega
    dsimp only [remainder]
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le h₁ h₂)) h₃)) h₄)
  have heq : superMinusOneNumerator W =
      X ^ (2 * Nat.card F + 1) + remainder := by
    unfold superMinusOneNumerator remainder
    ring
  rw [heq, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow _
  · rw [natDegree_X_pow]
    omega

private lemma eval_superV [Finite F] (W : WeierstrassCurve F) (x : F) :
    (superV W).eval x =
      frobeniusValue ((superH W).eval x) W.a₃
        (charTwoExponent (F := F)) := by
  simp only [superV, eval_frobeniusTail, eval_C]

private lemma eval_superMinusOneNumerator [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) (x : F) :
    (superMinusOneNumerator W).eval x =
      W.a₃ * frobeniusValue ((superH W).eval x) W.a₃
        (charTwoExponent (F := F)) + W.a₃ ^ 2 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q1 : x ^ (2 * Nat.card F + 1) = x ^ 3 := by
    calc
      x ^ (2 * Nat.card F + 1) = x ^ (2 * Nat.card F) * x := pow_succ _ _
      _ = (x ^ Nat.card F) ^ 2 * x := by
        rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul]
      _ = x ^ 3 := by rw [hxq]; ring
  have hxq2 : x ^ (Nat.card F + 2) = x ^ 3 := by
    rw [pow_add, hxq]
    ring
  simp only [superMinusOneNumerator, eval_add, eval_mul, eval_pow, eval_X,
    eval_C, eval_superV, hx2q1, hxq2, hxq]
  have hcancel₁ : x ^ 3 + x ^ 3 = 0 := CharTwo.add_self_eq_zero _
  have hcancel₂ : W.a₄ * (x + x) = 0 := by rw [CharTwo.add_self_eq_zero, mul_zero]
  linear_combination hcancel₁ + hcancel₂

private lemma superEquation_iff_fiber [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] (x y : F) :
    W.toAffine.Equation x y ↔
      y ^ 2 + W.a₃ * y = (superH W).eval x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.a₁_of_isCharTwoJEqZeroNF,
    WeierstrassCurve.a₂_of_isCharTwoJEqZeroNF, zero_mul, add_zero,
    superH, eval_add, eval_pow, eval_X, eval_mul, eval_C]

private def affineSolutionsEquivSuperFibers [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] :
    {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      Σ x : F, charTwoFiber W.a₃ ((superH W).eval x) where
  toFun xy := ⟨xy.1.1, ⟨xy.1.2, (superEquation_iff_fiber W _ _).mp xy.2⟩⟩
  invFun xy := ⟨(xy.1, xy.2.1), (superEquation_iff_fiber W _ _).mpr xy.2.2⟩
  left_inv xy := by
    apply Subtype.ext
    rfl
  right_inv xy := by
    cases xy
    rfl

private lemma superPointCount_eq_fiber_sum [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] [W.IsElliptic] :
    Nat.card W.toAffine.Point =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  rw [W.toAffine.natCard_point_eq_natCard_affineSolutions_add_one]
  rw [Nat.card_congr (affineSolutionsEquivSuperFibers W), Nat.card_sigma]

private lemma superPZeroX_ne_QX [Finite F] :
    superPZeroX (F := F) ≠ RatFunc.X := by
  intro heq
  have hdegree := congrArg RatFunc.intDegree heq
  simp only [superPZeroX] at hdegree
  rw [intDegree_pow RatFunc.X_ne_zero] at hdegree
  simp only [RatFunc.intDegree_X, mul_one] at hdegree
  have hcard : 1 < Nat.card F := Finite.one_lt_card
  omega

private lemma superX_negPZero_add_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0) =
      algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne superPZeroX_ne_QX]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    superTwist, superPZeroX, superPZeroY, zero_mul, add_zero,
    sub_eq_add_neg, CharTwo.neg_eq]
  rw [algebraMap_charTwoFrobeniusPolynomial]
  simp only [superMinusOneNumerator, map_add, map_mul, map_pow,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hL : (RatFunc.X ^ Nat.card F + RatFunc.X : RatFunc F) ≠ 0 := by
    rw [← algebraMap_charTwoFrobeniusPolynomial (F := F)]
    exact RatFunc.algebraMap_ne_zero
      (charTwoFrobeniusPolynomial_ne_zero (F := F))
  have hv := congrArg (algebraMap F[X] (RatFunc F)) (superV_identity W)
  rw [superH_pow_card W] at hv
  simp only [superH, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
    RatFunc.algebraMap_C] at hv
  field_simp [hL]
  have htwo : (2 : RatFunc F) = 0 := CharTwo.two_eq_zero
  linear_combination hv +
    ((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃ +
      RatFunc.X ^ (Nat.card F * 3) + RatFunc.C W.a₄ *
        RatFunc.X ^ Nat.card F + RatFunc.C W.a₆ + RatFunc.X ^ 3 +
      RatFunc.C W.a₄ * RatFunc.X + RatFunc.C W.a₆) * htwo +
    (-((algebraMap F[X] (RatFunc F)) (superV W) * RatFunc.C W.a₃) +
      RatFunc.X * RatFunc.X ^ (Nat.card F * 2) -
      RatFunc.X * RatFunc.C W.a₄ +
      RatFunc.X ^ 2 * RatFunc.X ^ Nat.card F -
      RatFunc.X ^ Nat.card F * RatFunc.C W.a₄ - RatFunc.C W.a₆) * htwo

private lemma superPoint_neg_one_eq_some [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    ∃ y hxy, superPoint W (-1) =
      .some
        ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
            ((superTwist W).toAffine.negY (superPZeroX (F := F))
              (superPZeroY W)) 0)) y hxy := by
  have hp : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F)) (superPZeroY W) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superPZero_equation W)
  have hneg : (superTwist W).toAffine.Nonsingular
      (superPZeroX (F := F))
      ((superTwist W).toAffine.negY (superPZeroX (F := F))
        (superPZeroY W)) :=
    ((superTwist W).toAffine.nonsingular_neg _ _).mpr hp
  have hnegP :
      -superPZero W = .some (superPZeroX (F := F))
        ((superTwist W).toAffine.negY (superPZeroX (F := F))
          (superPZeroY W)) hneg := by
    rw [show superPZero W =
      .some (superPZeroX (F := F)) (superPZeroY W) hp from rfl]
    rw [WeierstrassCurve.Affine.Point.neg_some]
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) superPZeroX_ne_QX
    (h₁ := hneg)
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (superQ_equation W))
  rw [← hnegP, ← show superQ W = .some RatFunc.X 0 _ from rfl] at hadd
  have hpoint : superPoint W (-1) = -(-superPZero W + superQ W) := by
    unfold superPoint
    simp only [neg_one_zsmul]
    abel
  rw [hpoint, hadd, WeierstrassCurve.Affine.Point.neg_some]
  exact ⟨_, _, rfl⟩

private lemma superH_derivative [CharP F 2] (W : WeierstrassCurve F) :
    (superH W).derivative = X ^ 2 + C W.a₄ := by
  unfold superH
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X,
    derivative_C]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : ((3 : ℕ) : F) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, htwo,
      Nat.cast_one, zero_add]
  rw [hthree, map_one]
  norm_num

private lemma derivative_frobeniusTail_super [CharP F 2]
    (W : WeierstrassCurve F) (e : ℕ) (he : 0 < e) :
    (frobeniusTail (superH W) (C W.a₃) e).derivative =
      C (W.a₃ ^ (2 ^ e - 2)) * (X ^ 2 + C W.a₄) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  rw [frobeniusTail, derivative_add, derivative_pow, derivative_mul,
    derivative_pow, derivative_C, superH_derivative]
  have htwo : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  rw [htwo, map_zero]
  norm_num

private lemma eval_derivative_superMinusOneNumerator [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] (x : F) :
    (superMinusOneNumerator W).derivative.eval x = 0 := by
  let fintypeF : Fintype F := Fintype.ofFinite F
  have hqcast : ((Nat.card F : ℕ) : F) = 0 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact Nat.cast_card_eq_zero F
  have hcoeff1 : (((2 * Nat.card F + 1 : ℕ) : F)) = 1 := by
    push_cast
    rw [hqcast]
    ring
  have hcoeff2 : (((Nat.card F + 2 : ℕ) : F)) = 0 := by
    push_cast
    rw [hqcast, zero_add]
    exact CharTwo.two_eq_zero
  have hxq : x ^ Nat.card F = x := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card x
  have hx2q : x ^ (2 * Nat.card F) = x ^ 2 := by
    rw [show 2 * Nat.card F = Nat.card F * 2 by omega, pow_mul, hxq]
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  have haq1 : W.a₃ ^ (Nat.card F - 1) = 1 := by
    rw [@Nat.card_eq_fintype_card F fintypeF]
    exact FiniteField.pow_card_sub_one_eq_one W.a₃ ha
  have hcard : 2 ≤ Nat.card F := Finite.one_lt_card
  have hamul : W.a₃ * W.a₃ ^ (Nat.card F - 2) = 1 := by
    calc
      W.a₃ * W.a₃ ^ (Nat.card F - 2) =
          W.a₃ ^ (Nat.card F - 2 + 1) := (pow_succ' _ _).symm
      _ = W.a₃ ^ (Nat.card F - 1) := by congr 1; omega
      _ = 1 := haq1
  have hexponent1 : 2 * Nat.card F + 1 - 1 = 2 * Nat.card F := by omega
  unfold superMinusOneNumerator superV
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add]
  rw [derivative_frobeniusTail_super W _ (charTwoExponent_pos (F := F))]
  rw [← card_eq_two_pow (F := F)]
  simp only [derivative_pow, derivative_X, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, eval_one, hcoeff1, hcoeff2, one_mul, zero_mul,
    hexponent1, hx2q, hqcast, add_zero]
  rw [← mul_assoc, hamul, one_mul]
  simp only [mul_one, zero_add]
  exact CharTwo.add_self_eq_zero (x ^ 2 + W.a₄)

private lemma superMinusOneNumerator_ne_zero [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) : superMinusOneNumerator W ≠ 0 := by
  intro hzero
  have hdegree := superMinusOneNumerator_natDegree W
  rw [hzero] at hdegree
  have hcard : 0 < Nat.card F := Nat.card_pos
  simp at hdegree

private lemma rootMultiplicity_superNumerator_eq_zero [Finite F]
    [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
    [W.IsCharTwoJEqZeroNF] (x : F)
    (hvalue : frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) = 0) :
    Polynomial.rootMultiplicity x (superMinusOneNumerator W) = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  intro hroot
  have heval := eval_superMinusOneNumerator W x
  rw [hvalue, mul_zero, zero_add] at heval
  exact (pow_ne_zero 2 (super_a₃_ne_zero W)) (heval.symm.trans hroot)

private lemma superNumerator_sq_dvd_of_value_eq [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F)
    (hvalue : frobeniusValue ((superH W).eval x) W.a₃
      (charTwoExponent (F := F)) = W.a₃) :
    (X - C x) ^ 2 ∣ superMinusOneNumerator W := by
  have hN := superMinusOneNumerator_ne_zero W
  have hroot : (superMinusOneNumerator W).IsRoot x := by
    change (superMinusOneNumerator W).eval x = 0
    rw [eval_superMinusOneNumerator, hvalue]
    simpa only [pow_two] using
      CharTwo.add_self_eq_zero (W.a₃ * W.a₃)
  have hderivativeRoot : (superMinusOneNumerator W).derivative.IsRoot x := by
    exact eval_derivative_superMinusOneNumerator W x
  have hmult : 1 <
      Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hN).mpr
      ⟨hroot, hderivativeRoot⟩
  rw [← Polynomial.le_rootMultiplicity_iff hN]
  omega

private def superMinusOneGCD [Finite F]
    (W : WeierstrassCurve F) : F[X] :=
  gcd (superMinusOneNumerator W) (charTwoFrobeniusPolynomial ^ 2)

private lemma count_roots_superMinusOneGCD [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    (x : F) :
    Multiset.count x (superMinusOneGCD W).roots =
      2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) := by
  have hN := superMinusOneNumerator_ne_zero W
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hlinearL : X - C x ∣ (charTwoFrobeniusPolynomial : F[X]) := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact eval_charTwoFrobeniusPolynomial x
  have hlinearLsq : (X - C x) ^ 2 ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 :=
    pow_dvd_pow_of_dvd hlinearL 2
  have ha : W.a₃ ≠ 0 := super_a₃_ne_zero W
  rcases frobeniusValue_eq_zero_or_eq
      (c := (superH W).eval x) ha with hvalue | hvalue
  · have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 0 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x (superMinusOneNumerator W) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hN hGdivN x
        _ = 0 := rootMultiplicity_superNumerator_eq_zero W x hvalue
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 0 :=
      Nat.eq_zero_of_le_zero hupper
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_two_of_value_eq_zero ha hvalue]
  · have hcommon : (X - C x) ^ 2 ∣ superMinusOneGCD W := by
      unfold superMinusOneGCD
      exact dvd_gcd (superNumerator_sq_dvd_of_value_eq W x hvalue)
        hlinearLsq
    have hlower : 2 ≤ Polynomial.rootMultiplicity x (superMinusOneGCD W) :=
      (Polynomial.le_rootMultiplicity_iff hG).mpr hcommon
    have hrootL : Polynomial.rootMultiplicity x
        ((charTwoFrobeniusPolynomial : F[X]) ^ 2) = 2 := by
      rw [← Polynomial.count_roots]
      exact count_roots_charTwoFrobeniusPolynomial_sq x
    have hupper : Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤ 2 := by
      calc
        Polynomial.rootMultiplicity x (superMinusOneGCD W) ≤
            Polynomial.rootMultiplicity x
              ((charTwoFrobeniusPolynomial : F[X]) ^ 2) :=
          Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hLsq hGdivL x
        _ = 2 := hrootL
    have hroot : Polynomial.rootMultiplicity x (superMinusOneGCD W) = 2 :=
      le_antisymm hupper hlower
    rw [Polynomial.count_roots, hroot,
      charTwoFiber_card_eq_zero_of_value_eq ha hvalue]

private lemma superMinusOneGCD_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree =
      ∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
  have hL : (charTwoFrobeniusPolynomial : F[X]) ≠ 0 :=
    charTwoFrobeniusPolynomial_ne_zero
  have hLsq : (charTwoFrobeniusPolynomial : F[X]) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hL
  have hGdivL : superMinusOneGCD W ∣
      (charTwoFrobeniusPolynomial : F[X]) ^ 2 := by
    unfold superMinusOneGCD
    exact gcd_dvd_right _ _
  have hsplit : (superMinusOneGCD W).Splits :=
    (charTwoFrobeniusPolynomial_splits (F := F)).pow 2 |>.of_dvd
      hLsq hGdivL
  have hsum :
      (∑ x : F, Multiset.count x (superMinusOneGCD W).roots) =
        (superMinusOneGCD W).roots.card := by
    simpa using (Multiset.sum_count_eq_card
      (s := Finset.univ) (m := (superMinusOneGCD W).roots) (by simp))
  calc
    (superMinusOneGCD W).natDegree =
        (superMinusOneGCD W).roots.card := hsplit.natDegree_eq_card_roots
    _ = ∑ x : F, Multiset.count x (superMinusOneGCD W).roots := hsum.symm
    _ = ∑ x : F,
        (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) := by
      apply Finset.sum_congr rfl
      intro x _
      exact count_roots_superMinusOneGCD W x

private lemma superMinusOneGCD_natDegree_add_fiber_sum
    [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneGCD W).natDegree +
        ∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) =
      2 * Nat.card F := by
  rw [superMinusOneGCD_natDegree W, ← Finset.sum_add_distrib]
  calc
    (∑ x : F, (2 - Nat.card (charTwoFiber W.a₃ ((superH W).eval x)) +
        Nat.card (charTwoFiber W.a₃ ((superH W).eval x)))) =
        ∑ _x : F, 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.sub_add_cancel (charTwoFiber_card_le_two W.a₃ _)]
    _ = 2 * Nat.card F := by
      simp [Nat.card_eq_fintype_card, mul_comm]

private lemma superMinusOneQuotient_natDegree [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superMinusOneNumerator W / superMinusOneGCD W).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  have hN := superMinusOneNumerator_ne_zero W
  have hG : superMinusOneGCD W ≠ 0 := by
    intro hzero
    unfold superMinusOneGCD at hzero
    exact hN ((gcd_eq_zero_iff _ _).mp hzero).1
  have hGdivN : superMinusOneGCD W ∣ superMinusOneNumerator W := by
    unfold superMinusOneGCD
    exact gcd_dvd_left _ _
  have hmulN : superMinusOneGCD W *
      (superMinusOneNumerator W / superMinusOneGCD W) =
        superMinusOneNumerator W :=
    EuclideanDomain.mul_div_cancel' hG hGdivN
  have hquotN : superMinusOneNumerator W / superMinusOneGCD W ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmulN
    exact hN hmulN.symm
  have hdegreeProduct := Polynomial.natDegree_mul hG hquotN
  rw [hmulN, superMinusOneNumerator_natDegree W] at hdegreeProduct
  have hdegreeG := superMinusOneGCD_natDegree_add_fiber_sum W
  omega

private lemma num_natDegree_superMinusOneRat [Fintype F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (superMinusOneNumerator W) /
        algebraMap F[X] (RatFunc F) charTwoFrobeniusPolynomial ^ 2)).natDegree =
      (∑ x : F, Nat.card (charTwoFiber W.a₃ ((superH W).eval x))) + 1 := by
  rw [← map_pow (algebraMap F[X] (RatFunc F))
    (charTwoFrobeniusPolynomial : F[X]) 2]
  rw [charTwo_natDegree_num_div _ _
    (pow_ne_zero 2 charTwoFrobeniusPolynomial_ne_zero)]
  exact superMinusOneQuotient_natDegree W

private lemma superD_neg_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superD W (-1) = Nat.card W.toAffine.Point := by
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨y, hxy, hpoint⟩ := superPoint_neg_one_eq_some W
  unfold superD
  rw [hpoint]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX (superPZeroX (F := F)) RatFunc.X
        ((superTwist W).toAffine.slope (superPZeroX (F := F)) RatFunc.X
          ((superTwist W).toAffine.negY (superPZeroX (F := F))
            (superPZeroY W)) 0))).natDegree = _
  rw [superX_negPZero_add_Q W]
  rw [num_natDegree_superMinusOneRat W]
  exact (superPointCount_eq_fiber_sum W).symm

private lemma super_product_formula {R : Type*} [CommRing R] [CharP R 2]
    (t f g a b z : R)
    (curve : z ^ 2 + a * g ^ 2 * z + f ^ 3 * g + b * f * g ^ 3 +
      t ^ 3 * g ^ 4 + b * t * g ^ 4 = 0) :
    ((t * f + b * g) * (t * g + f) + a * z + a ^ 2 * g ^ 2) *
        ((t * f + b * g) * (t * g + f) + a * z) =
      (t ^ 2 * f ^ 2 + b ^ 2 * g ^ 2 + a ^ 2 * g * (t * g + f)) *
        (t * g + f) ^ 2 := by
  have htwo : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination a ^ 2 * curve +
    (-t * f ^ 2 * g ^ 2 * a ^ 2 + t * f ^ 2 * a * z +
      t * f ^ 3 * b * g + t * b * g ^ 2 * a * z + t ^ 2 * f * g * a * z -
      t ^ 2 * f * g ^ 3 * a ^ 2 + 2 * t ^ 2 * f ^ 2 * b * g ^ 2 +
      t ^ 3 * f * b * g ^ 3 - t ^ 3 * g ^ 4 * a ^ 2 +
      f * b * g * a * z - f ^ 3 * g * a ^ 2) * htwo

private def superNeighborFirst (W : WeierstrassCurve F) (f g : F[X]) : F[X] :=
  (X * f) ^ 2 + (C (W.a₄ ^ 2) * g ^ 2 +
    C (W.a₃ ^ 2) * g * (X * g + f))

private def superNeighborSecond (W : WeierstrassCurve F) (g : F[X]) : F[X] :=
  C (W.a₃ ^ 2) * g ^ 2

private lemma superNeighborFirst_natDegree
    (W : WeierstrassCurve F) {f g : F[X]} (hf : f ≠ 0)
    (hdegree : g.natDegree < f.natDegree) :
    (superNeighborFirst W f g).natDegree = 2 * f.natDegree + 2 := by
  have hXf : (X * f).natDegree = f.natDegree + 1 := by
    rw [Polynomial.natDegree_mul X_ne_zero hf, Polynomial.natDegree_X]
    omega
  have hmain : ((X * f) ^ 2).natDegree = 2 * f.natDegree + 2 := by
    rw [Polynomial.natDegree_pow, hXf]
    omega
  have hfirst : (C (W.a₄ ^ 2) * g ^ 2).natDegree ≤ 2 * g.natDegree := by
    calc
      (C (W.a₄ ^ 2) * g ^ 2).natDegree ≤ (g ^ 2).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ = 2 * g.natDegree := Polynomial.natDegree_pow _ _
  have hXg : (X * g).natDegree ≤ f.natDegree := by
    calc
      (X * g).natDegree ≤ X.natDegree + g.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ f.natDegree := by rw [Polynomial.natDegree_X]; omega
  have hD : (X * g + f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le hXg le_rfl)
  have hsecond :
      (C (W.a₃ ^ 2) * g * (X * g + f)).natDegree ≤
        g.natDegree + f.natDegree := by
    calc
      (C (W.a₃ ^ 2) * g * (X * g + f)).natDegree ≤
          (C (W.a₃ ^ 2) * g).natDegree + (X * g + f).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ g.natDegree + f.natDegree :=
        Nat.add_le_add (Polynomial.natDegree_C_mul_le _ _) hD
  have hremainder :
      (C (W.a₄ ^ 2) * g ^ 2 +
        C (W.a₃ ^ 2) * g * (X * g + f)).natDegree <
          2 * f.natDegree + 2 := by
    apply (Polynomial.natDegree_add_le _ _).trans_lt
    rw [max_lt_iff]
    constructor <;> omega
  unfold superNeighborFirst
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact hmain
  · rwa [hmain]

private lemma superNeighbor_primitive [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {f g : F[X]} (hfg : IsCoprime f g) (hden : X * g + f ≠ 0) :
    PrimitiveTriple (superNeighborFirst W f g) (superNeighborSecond W g)
      (neighborDenominator f g) := by
  have ha := super_a₃_ne_zero W
  apply primitiveTriple_of_no_common_irreducible (pow_ne_zero 2 hden)
  intro p hp _hpFirst hpSecond hpDen
  have hprime := hp.prime
  have hpD : p ∣ X * g + f := hprime.dvd_of_dvd_pow hpDen
  have hpG : p ∣ g := by
    have hpProduct : p ∣ C (W.a₃ ^ 2) * g ^ 2 := hpSecond
    rcases hprime.dvd_mul.mp hpProduct with hpC | hpg
    · have hCunit : IsUnit (C (W.a₃ ^ 2)) :=
        Polynomial.isUnit_C.mpr
          (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 ha))
      exact (hprime.not_dvd_one
        (hpC.trans (isUnit_iff_dvd_one.mp hCunit))).elim
    · exact hprime.dvd_of_dvd_pow hpg
  have hpF : p ∣ f := by
    have hdifference := hpD.sub (hpG.mul_left X)
    convert hdifference using 1
    ring
  exact hp.not_isUnit (hfg.isUnit_of_dvd' hpF hpG)

private lemma superNeighborFirst_ratio (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (superNeighborFirst W r.num r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C (W.a₄ ^ 2) +
        RatFunc.C (W.a₃ ^ 2) * (RatFunc.X + r)) /
          (RatFunc.X + r) ^ 2 := by
  simp only [superNeighborFirst, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d :=
    (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    ((RatFunc.X * algebraMap F[X] (RatFunc F) r.num) ^ 2 +
        (RatFunc.C W.a₄ ^ 2 * d ^ 2 +
          RatFunc.C W.a₃ ^ 2 * d *
            (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num))) /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show
    (RatFunc.X * (r * d)) ^ 2 + (RatFunc.C W.a₄ ^ 2 * d ^ 2 +
        RatFunc.C W.a₃ ^ 2 * d * (RatFunc.X * d + r * d)) =
      d ^ 2 * (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C W.a₄ ^ 2 +
        RatFunc.C W.a₃ ^ 2 * (RatFunc.X + r)) by ring]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma superNeighborSecond_ratio (W : WeierstrassCurve F)
    (r : RatFunc F) :
    algebraMap F[X] (RatFunc F) (superNeighborSecond W r.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator r.num r.denom) =
      RatFunc.C (W.a₃ ^ 2) / (RatFunc.X + r) ^ 2 := by
  simp only [superNeighborSecond, neighborDenominator, map_add, map_mul,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  let d := algebraMap F[X] (RatFunc F) r.denom
  have hd : d ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hnum : algebraMap F[X] (RatFunc F) r.num = r * d :=
    (div_eq_iff hd).mp (RatFunc.num_div_denom r)
  change
    RatFunc.C W.a₃ ^ 2 * d ^ 2 /
      (RatFunc.X * d + algebraMap F[X] (RatFunc F) r.num) ^ 2 = _
  rw [hnum]
  rw [show (RatFunc.X * d + r * d) ^ 2 =
      d ^ 2 * (RatFunc.X + r) ^ 2 by ring]
  rw [show RatFunc.C W.a₃ ^ 2 * d ^ 2 =
      d ^ 2 * RatFunc.C W.a₃ ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hd)

private lemma super_neighbor_plus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + RatFunc.C W.a₃ * s =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
    (hdiff : RatFunc.X + r ≠ 0) :
    (s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X =
      ((RatFunc.X * r + RatFunc.C W.a₄) * (RatFunc.X + r) +
        RatFunc.C W.a₃ * s) / (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
          RatFunc.C W.a₃ * s := by
    calc
      s ^ 2 = (s ^ 2 + RatFunc.C W.a₃ * s) +
          RatFunc.C W.a₃ * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  rw [div_pow, hs2, hdiffEq]
  field_simp [hdiff]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero]
  ring

private lemma super_neighbor_minus [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + RatFunc.C W.a₃ * s =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X =
      ((RatFunc.X * r + RatFunc.C W.a₄) * (RatFunc.X + r) +
        RatFunc.C W.a₃ * s + RatFunc.C (W.a₃ ^ 2)) /
          (RatFunc.X + r) ^ 2 := by
  have hdiffEq : r - RatFunc.X = RatFunc.X + r := by
    simp only [sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  have hs2 : s ^ 2 =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
          RatFunc.C W.a₃ * s := by
    calc
      s ^ 2 = (s ^ 2 + RatFunc.C W.a₃ * s) +
          RatFunc.C W.a₃ * s := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = _ := by rw [heq]
  have hsum2 : (s + RatFunc.C W.a₃) ^ 2 =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X +
          RatFunc.C W.a₃ * s + RatFunc.C (W.a₃ ^ 2) := by
    calc
      (s + RatFunc.C W.a₃) ^ 2 = s ^ 2 + RatFunc.C (W.a₃ ^ 2) := by
        rw [add_sq, show (2 : RatFunc F) = 0 from CharTwo.two_eq_zero]
        simp only [zero_mul, add_zero, ← map_pow]
      _ = _ := by rw [hs2]
  rw [div_pow, hsum2, hdiffEq]
  field_simp [hdiff]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, add_zero]
  ring

private lemma super_neighbor_pair_product [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (heq : s ^ 2 + RatFunc.C W.a₃ * s =
      r ^ 3 + RatFunc.C W.a₄ * r +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X)
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) *
      (((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) =
      (RatFunc.X ^ 2 * r ^ 2 + RatFunc.C (W.a₄ ^ 2) +
        RatFunc.C (W.a₃ ^ 2) * (RatFunc.X + r)) /
          (RatFunc.X + r) ^ 2 := by
  rw [super_neighbor_plus W heq hdiff, super_neighbor_minus W heq hdiff]
  have hcurve :
      s ^ 2 + RatFunc.C W.a₃ * s + r ^ 3 +
        RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
          RatFunc.C W.a₄ * RatFunc.X = 0 := by
    calc
      _ = (s ^ 2 + RatFunc.C W.a₃ * s) +
          (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
            RatFunc.C W.a₄ * RatFunc.X) := by ring
      _ = (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
            RatFunc.C W.a₄ * RatFunc.X) +
          (r ^ 3 + RatFunc.C W.a₄ * r + RatFunc.X ^ 3 +
            RatFunc.C W.a₄ * RatFunc.X) := by rw [heq]
      _ = 0 := CharTwo.add_self_eq_zero _
  have hformula := super_product_formula RatFunc.X r 1
    (RatFunc.C W.a₃) (RatFunc.C W.a₄) s (by simpa using hcurve)
  simp only [map_pow] at ⊢
  simp only [mul_one, one_pow] at hformula
  field_simp [hdiff]
  linear_combination hformula

private lemma super_neighbor_pair_sum [CharP F 2]
    (W : WeierstrassCurve F) {r s : RatFunc F}
    (hdiff : RatFunc.X + r ≠ 0) :
    ((s / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) +
      (((s + RatFunc.C W.a₃) / (r - RatFunc.X)) ^ 2 + r + RatFunc.X) =
      RatFunc.C (W.a₃ ^ 2) / (RatFunc.X + r) ^ 2 := by
  have hdiff' : r - RatFunc.X ≠ 0 := by
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using hdiff
  field_simp [hdiff, hdiff']
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    CharTwo.neg_eq, sub_eq_add_neg, mul_zero, zero_add, add_zero,
    ← map_pow]

private lemma super_coordinates_equation [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF]
    {x y : RatFunc F} (hxy : (superTwist W).toAffine.Nonsingular x y) :
    y ^ 2 + RatFunc.C W.a₃ * y =
      x ^ 3 + RatFunc.C W.a₄ * x +
        RatFunc.X ^ 3 + RatFunc.C W.a₄ * RatFunc.X := by
  have heq := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [superTwist, zero_mul, add_zero] at heq
  linear_combination heq

private lemma super_generic_neighbor_degree_identity [CharP F 2]
    (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF] [W.IsElliptic]
    {x y xMinus yMinus xPlus yPlus : RatFunc F}
    {hxy : (superTwist W).toAffine.Nonsingular x y}
    {hMinus : (superTwist W).toAffine.Nonsingular xMinus yMinus}
    {hPlus : (superTwist W).toAffine.Nonsingular xPlus yPlus}
    (hxQ : x ≠ RatFunc.X)
    (hplus : .some xPlus yPlus hPlus =
      (.some x y hxy : (superTwist W).toAffine.Point) + superQ W)
    (hminus : .some xMinus yMinus hMinus =
      (.some x y hxy : (superTwist W).toAffine.Point) - superQ W)
    (hdegree : x.denom.natDegree < x.num.natDegree)
    (hdegreeMinus : xMinus.denom.natDegree < xMinus.num.natDegree)
    (hdegreePlus : xPlus.denom.natDegree < xPlus.num.natDegree) :
    xMinus.num.natDegree + xPlus.num.natDegree =
      2 * x.num.natDegree + 2 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hxy) (h₂ := hQ)
  have hplusEq := hplus.trans hadd
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hplusEq
  have hxPlus : xPlus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X y 0) := hplusEq.1
  have hneg : (superTwist W).toAffine.Nonsingular x
      ((superTwist W).toAffine.negY x y) :=
    ((superTwist W).toAffine.nonsingular_neg x y).mpr hxy
  have haddNeg := WeierstrassCurve.Affine.Point.add_of_X_ne
    (W := (superTwist W).toAffine) hxQ (h₁ := hneg) (h₂ := hQ)
  have hminusEq := hminus
  rw [show (.some x y hxy : (superTwist W).toAffine.Point) - superQ W =
    -(-(.some x y hxy : (superTwist W).toAffine.Point) + superQ W) by
      abel] at hminusEq
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl] at hminusEq
  rw [WeierstrassCurve.Affine.Point.neg_some, haddNeg,
    WeierstrassCurve.Affine.Point.neg_some] at hminusEq
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at hminusEq
  have hxMinus : xMinus =
      (superTwist W).toAffine.addX x RatFunc.X
        ((superTwist W).toAffine.slope x RatFunc.X
          ((superTwist W).toAffine.negY x y) 0) := hminusEq.1
  have hrPlus : xPlus = (y / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxPlus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, superTwist, zero_mul,
      add_zero, sub_eq_add_neg, CharTwo.neg_eq]
  have hrMinus : xMinus =
      ((y + RatFunc.C W.a₃) / (x - RatFunc.X)) ^ 2 + x + RatFunc.X := by
    rw [hxMinus, (superTwist W).toAffine.slope_of_X_ne hxQ]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      superTwist, zero_mul, add_zero, sub_eq_add_neg,
      CharTwo.neg_eq]
  have heq := super_coordinates_equation W hxy
  have hdiff : RatFunc.X + x ≠ 0 := by
    intro hzero
    apply hxQ
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hzero
  have hpairProd := super_neighbor_pair_product W heq hdiff
  have hpairSum := super_neighbor_pair_sum W (s := y) hdiff
  rw [← hrPlus, ← hrMinus] at hpairProd hpairSum
  have hprod :
      algebraMap F[X] (RatFunc F)
          (superNeighborFirst W x.num x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus * xPlus := by
    rw [superNeighborFirst_ratio]
    calc
      _ = xPlus * xMinus := hpairProd.symm
      _ = xMinus * xPlus := by ring
  have hsum :
      algebraMap F[X] (RatFunc F) (superNeighborSecond W x.denom) /
        algebraMap F[X] (RatFunc F) (neighborDenominator x.num x.denom) =
          xMinus + xPlus := by
    rw [superNeighborSecond_ratio]
    calc
      _ = xPlus + xMinus := hpairSum.symm
      _ = xMinus + xPlus := by ring
  have hpoly : X * x.denom + x.num ≠ 0 :=
    neighborPolynomial_ne_zero _ hdiff
  have hprimitive := superNeighbor_primitive W
    (RatFunc.isCoprime_num_denom x) hpoly
  have hout : neighborDenominator x.num x.denom ≠ 0 := pow_ne_zero 2 hpoly
  have hprojective := projective_first_natDegree hprimitive hout
    (ratFunc_ne_zero_of_num_degree_gt hdegreeMinus)
    (ratFunc_ne_zero_of_num_degree_gt hdegreePlus) hprod hsum
  have hcenter := superNeighborFirst_natDegree W
    (RatFunc.num_ne_zero (ratFunc_ne_zero_of_num_degree_gt hdegree)) hdegree
  omega

private lemma superPoint_sub_one [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] (n : ℤ) :
    superPoint W (n - 1) = superPoint W n - superQ W := by
  have hstep := superPoint_add_one W (n - 1)
  rw [show n - 1 + 1 = n by ring] at hstep
  rw [hstep]
  abel

private lemma superD_eq_one_of_point_eq_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma superD_eq_one_of_point_eq_neg_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = -superQ W) : superD W n = 1 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change (RatFunc.num RatFunc.X).natDegree = 1
  change (RatFunc.num (algebraMap F[X] (RatFunc F) X)).natDegree = 1
  rw [RatFunc.num_algebraMap, Polynomial.natDegree_X]

private lemma superQ_y_ne_negY [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (0 : RatFunc F) ≠ (superTwist W).toAffine.negY RatFunc.X 0 := by
  simp only [WeierstrassCurve.Affine.negY, superTwist, zero_mul, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  intro hzero
  apply super_a₃_ne_zero W
  apply RatFunc.C_injective
  simpa using hzero.symm

private def superDoubleNumerator (W : WeierstrassCurve F) : F[X] :=
  X ^ 4 + C (W.a₄ ^ 2)

private def superDoubleDenominator (W : WeierstrassCurve F) : F[X] :=
  C (W.a₃ ^ 2)

private lemma superX_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0) =
      algebraMap F[X] (RatFunc F) (superDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (superDoubleDenominator W) := by
  rw [(superTwist W).toAffine.slope_of_Y_ne rfl (superQ_y_ne_negY W)]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    superTwist, superDoubleNumerator, superDoubleDenominator, map_add,
    map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, zero_mul, zero_add,
    sub_eq_add_neg, CharTwo.neg_eq]
  have haC : RatFunc.C W.a₃ ≠ 0 := by
    intro hzero
    apply super_a₃_ne_zero W
    apply RatFunc.C_injective
    simpa using hzero
  field_simp [haC]
  ring_nf
  simp only [CharTwo.ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero,
    Nat.cast_one, mul_zero, zero_add, add_zero]
  ring

private lemma superDoubleNumerator_natDegree (W : WeierstrassCurve F) :
    (superDoubleNumerator W).natDegree = 4 := by
  unfold superDoubleNumerator
  compute_degree
  norm_num

private lemma superDoubleDenominator_ne_zero [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    superDoubleDenominator W ≠ 0 := by
  exact Polynomial.C_ne_zero.mpr (pow_ne_zero 2 (super_a₃_ne_zero W))

private lemma superDouble_coprime [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    IsCoprime (superDoubleNumerator W) (superDoubleDenominator W) := by
  have ha2 : W.a₃ ^ 2 ≠ 0 := pow_ne_zero 2 (super_a₃_ne_zero W)
  refine ⟨0, C (W.a₃ ^ 2)⁻¹, ?_⟩
  simp only [zero_mul, zero_add, superDoubleDenominator]
  rw [← C_mul, inv_mul_cancel₀ ha2, C_1]

private lemma super_num_natDegree_doubleQ [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (RatFunc.num
      (algebraMap F[X] (RatFunc F) (superDoubleNumerator W) /
        algebraMap F[X] (RatFunc F) (superDoubleDenominator W))).natDegree = 4 := by
  rw [num_natDegree_div_of_isCoprime _ _
    (by
      intro hzero
      have hdegree := superDoubleNumerator_natDegree W
      rw [hzero] at hdegree
      norm_num at hdegree)
    (superDoubleDenominator_ne_zero W) (superDouble_coprime W)]
  exact superDoubleNumerator_natDegree W

private lemma superD_eq_four_of_point_eq_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = superQ W + superQ W) :
    superD W n = 4 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (superQ_y_ne_negY W)]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0))).natDegree = 4
  rw [superX_doubleQ W, super_num_natDegree_doubleQ W]

private lemma superD_eq_four_of_point_eq_neg_two_Q [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]
    {n : ℤ} (hn : superPoint W n = -(superQ W + superQ W)) :
    superD W n = 4 := by
  have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (superQ_equation W)
  unfold superD
  rw [hn]
  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (superQ_y_ne_negY W)]
  rw [WeierstrassCurve.Affine.Point.neg_some]
  change
    (RatFunc.num
      ((superTwist W).toAffine.addX RatFunc.X RatFunc.X
        ((superTwist W).toAffine.slope RatFunc.X RatFunc.X 0 0))).natDegree = 4
  rw [superX_doubleQ W, super_num_natDegree_doubleQ W]

private lemma superD_recurrence [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    ∀ n, superD W (n - 1) + superD W (n + 1) = 2 * superD W n + 2 := by
  intro n
  cases hn : superPoint W n with
  | zero =>
      have hplus := superPoint_add_one W n
      have hminus := superPoint_sub_one W n
      rw [hn] at hplus hminus
      have hplusQ : superPoint W (n + 1) = superQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_add] using hplus
      have hminusQ : superPoint W (n - 1) = -superQ W := by
        simpa only [← WeierstrassCurve.Affine.Point.zero_def, zero_sub] using hminus
      have hdPlus := superD_eq_one_of_point_eq_Q W hplusQ
      have hdMinus := superD_eq_one_of_point_eq_neg_Q W hminusQ
      have hd : superD W n = 0 := by simp [superD, hn]
      omega
  | some x y hxy =>
      cases hminusPoint : superPoint W (n - 1) with
      | zero =>
          have hsub := superPoint_sub_one W n
          rw [hn, hminusPoint] at hsub
          have hnQ : superPoint W n = superQ W := by
            have hxyQ :
                (.some x y hxy : (superTwist W).toAffine.Point) = superQ W :=
              sub_eq_zero.mp hsub.symm
            exact hn.trans hxyQ
          have hplus := superPoint_add_one W n
          rw [hnQ] at hplus
          have hd := superD_eq_one_of_point_eq_Q W hnQ
          have hdPlus := superD_eq_four_of_point_eq_two_Q W hplus
          have hdMinus : superD W (n - 1) = 0 := by
            simp [superD, hminusPoint]
          omega
      | some xMinus yMinus hMinus =>
          cases hplusPoint : superPoint W (n + 1) with
          | zero =>
              have hadd := superPoint_add_one W n
              rw [hn, hplusPoint] at hadd
              have hnNegQ : superPoint W n = -superQ W := by
                have htranslated := congrArg
                  (fun P : (superTwist W).toAffine.Point ↦ P - superQ W)
                  hadd.symm
                have hxyNegQ :
                    (.some x y hxy : (superTwist W).toAffine.Point) =
                      -superQ W := by
                  simpa only [← WeierstrassCurve.Affine.Point.zero_def,
                    zero_sub, add_sub_cancel_right] using htranslated
                exact hn.trans hxyNegQ
              have hminus := superPoint_sub_one W n
              rw [hnNegQ] at hminus
              have hminusNegTwo :
                  superPoint W (n - 1) = -(superQ W + superQ W) := by
                calc
                  superPoint W (n - 1) = -superQ W - superQ W := hminus
                  _ = -(superQ W + superQ W) := by abel
              have hd := superD_eq_one_of_point_eq_neg_Q W hnNegQ
              have hdMinus :=
                superD_eq_four_of_point_eq_neg_two_Q W hminusNegTwo
              have hdPlus : superD W (n + 1) = 0 := by
                simp [superD, hplusPoint]
              omega
          | some xPlus yPlus hPlus =>
              have hplus := superPoint_add_one W n
              have hminus := superPoint_sub_one W n
              rw [hn, hplusPoint] at hplus
              rw [hn, hminusPoint] at hminus
              have hPNeQ :
                  (.some x y hxy : (superTwist W).toAffine.Point) ≠ superQ W := by
                intro heq
                rw [heq] at hminus
                simp at hminus
              have hPNeNegQ :
                  (.some x y hxy : (superTwist W).toAffine.Point) ≠
                    -superQ W := by
                intro heq
                rw [heq] at hplus
                simp at hplus
              have hQ : (superTwist W).toAffine.Nonsingular RatFunc.X 0 :=
                WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                  (superQ_equation W)
              have hxQ : x ≠ RatFunc.X := by
                intro hx
                rcases (WeierstrassCurve.Affine.Point.X_eq_iff.mp hx) with
                  heq | heq
                · apply hPNeQ
                  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
                  exact heq
                · apply hPNeNegQ
                  rw [show superQ W = .some RatFunc.X 0 hQ from rfl]
                  exact heq
              have hdegree := super_num_degree W hxy
              have hdegreeMinus := super_num_degree W hMinus
              have hdegreePlus := super_num_degree W hPlus
              have hgeneric := super_generic_neighbor_degree_identity W hxQ
                hplus hminus hdegree hdegreeMinus hdegreePlus
              simpa [superD, hn, hminusPoint, hplusPoint] using hgeneric

private lemma supersingular_degree_computation [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  exact ⟨{
    d := superD W
    zero := superD_zero W
    negOne := superD_neg_one W
    recurrence := superD_recurrence W
    noAdjacentZeros := superNoAdjacentZeros W }⟩

/-- **Manin degree data for the characteristic-two normal forms.** Let $F$ be a finite field of
characteristic $2$ with $q$ elements, let $W$ be a Weierstrass curve over $F$ with nonzero
discriminant that is in one of the two characteristic-two normal forms
$y^2 + xy = x^3 + a_2 x^2 + a_6$ (that is, $a_1 = 1$ and $a_3 = a_4 = 0$) or
$y^2 + a_3 y = x^3 + a_4 x + a_6$ (that is, $a_1 = a_2 = 0$), and let $N$ be the number of
points of $W$ over $F$, including the point at infinity. Then there is Manin degree data for
$(q, N)$: a function $d : \mathbb{Z} \to \mathbb{N}$ with $d(0) = q$, $d(-1) = N$,
$d(n - 1) + d(n + 1) = 2 d(n) + 2$ for every integer $n$, and no integer $n$ with
$d(n) = d(n + 1) = 0$. -/
theorem manin_degree_data_of_isCharTwoNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoNF] :
    Nonempty (MathlibExt.AlgebraicGeometry.EllipticCurve.ManinDegreeData
      (Nat.card F) (Nat.card W.toAffine.Point)) := by
  by_cases hF : Nat.card F = 2
  · exact manin_degree_data_of_card_eq_two hF W
  · by_cases hF' : Nat.card F = 4
    · exact manin_degree_data_of_card_eq_four hF' W
    · cases ‹W.IsCharTwoNF› with
      | of_j_ne_zero => exact ordinary_degree_computation W
      | of_j_eq_zero => exact supersingular_degree_computation W

/-- **Hasse bound for the characteristic-two normal forms.** Let $F$ be a finite field of
characteristic $2$ with $q$ elements and let $W$ be a Weierstrass curve over $F$ with nonzero
discriminant that is in one of the two characteristic-two normal forms
$y^2 + xy = x^3 + a_2 x^2 + a_6$ (that is, $a_1 = 1$ and $a_3 = a_4 = 0$) or
$y^2 + a_3 y = x^3 + a_4 x + a_6$ (that is, $a_1 = a_2 = 0$). If $N$ is the number of points of
$W$ over $F$, including the point at infinity, then $(q + 1 - N)^2 \le 4q$. -/
theorem hasse_bound_of_isCharTwoNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) :=
  (Classical.choice (manin_degree_data_of_isCharTwoNF W)).hasse_bound

/-- **Hasse bound for the ordinary characteristic-two normal form.** Let $F$ be a finite field of
characteristic $2$ with $q$ elements and let $W$ be a Weierstrass curve
$y^2 + xy = x^3 + a_2 x^2 + a_6$ over $F$ (that is, $a_1 = 1$ and $a_3 = a_4 = 0$) with nonzero
discriminant. If $N$ is the number of points of $W$ over $F$, including the point at infinity,
then $(q + 1 - N)^2 \le 4q$. -/
theorem hasse_bound_of_isCharTwoJNeZeroNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) := by
  let _ : W.IsCharTwoNF := .of_j_ne_zero
  exact hasse_bound_of_isCharTwoNF W

/-- **Hasse bound for the supersingular characteristic-two normal form.** Let $F$ be a finite
field of characteristic $2$ with $q$ elements and let $W$ be a Weierstrass curve
$y^2 + a_3 y = x^3 + a_4 x + a_6$ over $F$ (that is, $a_1 = a_2 = 0$) with nonzero discriminant.
If $N$ is the number of points of $W$ over $F$, including the point at infinity, then
$(q + 1 - N)^2 \le 4q$. -/
theorem hasse_bound_of_isCharTwoJEqZeroNF [Finite F] [CharP F 2]
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF] :
    (((Nat.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card F : ℤ)) := by
  let _ : W.IsCharTwoNF := .of_j_eq_zero
  exact hasse_bound_of_isCharTwoNF W

end

end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
