/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_EDSEngine.lean`,
`Definitions/Def_Compat_Mathlib430.lean`,
`P2M/Sol/S_WeierstrassCurve_Affine_evalEval_psi_sq.lean`
and
`P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Embedding.Set
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Multiplication by an integer through division polynomials

For a Weierstrass curve `W` over a field and a nonsingular point `(x, y)` of `W`,
`zsmul_eq_smulEval` computes `n • (x, y)` in Jacobian coordinates as
`(φₙ(x, y), ωₙ(x, y), ψₙ(x, y))`. The proof goes through the universal Weierstrass curve and
the theory of elliptic divisibility sequences; that machinery is private to this module.

## Main results

* `WeierstrassCurve.zsmul_eq_smulEval`: for a nonsingular point `(x, y)` over a field, `n • (x, y)`
  is the class of the triple `smulEval W x y n`.
* `WeierstrassCurve.smul_eq_zero_iff_evalEval_ψ`: `n • (x, y) = 0` exactly when `ψₙ(x, y) = 0`.
* `WeierstrassCurve.evalEval_ψ_sq_of_commRing` and `WeierstrassCurve.evalEval_φ_of_commRing`: over
  a commutative ring, at any pair `(x, y)` that satisfies the curve equation, `ψₙ ^ 2` and `φₙ`
  agree with the univariate polynomials `ΨSqₙ` and `Φₙ`. `WeierstrassCurve.evalEval_ψ_sq` and
  `WeierstrassCurve.evalEval_φ` are the same statements over a field.
* `WeierstrassCurve.isCoprime_Φ_ΨSq`: over an algebraically closed field, `Φₙ` and `ΨSqₙ` are
  coprime for an elliptic curve and `n > 0`.
-/

section IsEllDivSequence430

universe u

variable {R : Type u} [CommRing R]

variable (W : ℤ → R)

def IsEllSequence' : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

def IsDivSequence' : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

def IsEllDivSequence' : Prop :=
  IsEllSequence' W ∧ IsDivSequence' W

lemma isEllSequence'_id : IsEllSequence' id :=
  fun _ _ _ => by simp_rw [id_eq]; ring1

lemma isDivSequence'_id : IsDivSequence' id :=
  fun _ _ => Int.ofNat_dvd.mpr

theorem isEllDivSequence'_id : IsEllDivSequence' id :=
  ⟨isEllSequence'_id, isDivSequence'_id⟩

variable {W}

lemma IsEllSequence'.smul (h : IsEllSequence' W) (x : R) : IsEllSequence' (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp_rw [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

lemma IsDivSequence'.smul (h : IsDivSequence' W) (x : R) : IsDivSequence' (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r

lemma IsEllDivSequence'.smul (h : IsEllDivSequence' W) (x : R) : IsEllDivSequence' (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

end IsEllDivSequence430

namespace WeierstrassCurve.Affine

scoped notation3:max W' "⟮" S "⟯" =>
  WeierstrassCurve.Affine.Point (WeierstrassCurve.Affine.baseChange W' S)

end WeierstrassCurve.Affine

namespace WeierstrassCurve

/-- **Base change of an elliptic curve is elliptic.** `WeierstrassCurve.baseChange` is not
reducible, so instance search does not see through it to `WeierstrassCurve.map`. -/
public instance instIsEllipticBaseChange {R : Type*} {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs <| (W.map (algebraMap R A)).IsElliptic

end WeierstrassCurve


section PortEllSequenceCore

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)

open scoped nonZeroDivisors

namespace EllSequence

def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)

def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c

def net (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r
    - W (p + r + s) * W (p - r) * W (q + s) * W q
    + W (q + r + s) * W (q - r) * W (p + s) * W p

variable {W} in
lemma net_eq_rel₄ {p q r s : ℤ} :
    net W p q r s = rel₄ W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [net, rel₄, addMulSub, add_add_add_comm _ s, add_sub_add_comm, sub_self, add_zero,
    add_assoc, ← two_mul, add_sub_cancel_right, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]
  ring

def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

lemma _root_.isEllSequence_iff_rel₃ : IsEllSequence' W ↔ ∀ m n r : ℤ, Rel₃ W m n r :=
  Iff.rfl

def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [net]; ring_nf))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

lemma net_add_sub_iff (m n : ℤ) :
    net W (m + n) m (m - n) n = 0 ↔
      W (2 * (m + n)) * W (m - n) * W m * W n =
        (W (2 * m + n) * W (2 * n) * W m - W (m + 2 * n) * W (2 * m) * W n) * W (m + n) := by
  rw [net]; conv_rhs => rw [← sub_eq_zero]
  ring_nf

lemma addMulSub_two_zero : addMulSub W 2 0 = W 1 ^ 2 := (sq _).symm
lemma addMulSub_three_one : addMulSub W 3 1 = W 2 * W 1 := rfl

lemma addMulSub_even (m n : ℤ) : addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]

lemma addMulSub_odd (m n : ℤ) :
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := by
  have h k := Int.mul_tdiv_cancel_left k two_ne_zero
  rw [addMulSub, ← h (m + n + 1), ← h (m - n)]; congr <;> ring

lemma addMulSub_same (zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0 := by
  rw [addMulSub, sub_self, Int.zero_tdiv, zero, mul_zero]

lemma addMulSub_neg₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W (-m) n = addMulSub W m n := by
  simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring

lemma addMulSub_neg₁ (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
  rw [addMulSub, addMulSub, mul_comm]; abel_nf

lemma addMulSub_abs₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W |m| n = addMulSub W m n := by
  obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]

lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring_nf

section transf

variable (a b c d : ℤ)

def StrictAnti₄ : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

def avg₄ : ℤ := (a + b + c + d) / 2

namespace HaveSameParity₄
open Int Equiv

variable {W a b c d} (same : HaveSameParity₄ a b c d)

include same in
lemma rel₄_eq_net : rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  have h := @Int.two_mul_ediv_two_of_even
  rw [net_eq_rel₄, h, h, h]; · simp_rw [sub_add_cancel]
  all_goals simp only [← negOnePow_eq_iff, same.1, same.2.1, same.2.2]

include same in
lemma even_sum : Even (a + b + c + d) := by
  simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
    same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]

include same in
lemma avg₄_add_avg₄ : avg₄ a b c d + avg₄ a b c d = a + b + c + d := by
  rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd

include same in
lemma same₀₃ : a.negOnePow = d.negOnePow := by rw [same.1, same.2.1, same.2.2]

include same in
protected lemma abs : HaveSameParity₄ |a| |b| |c| |d| := by
  simpa only [HaveSameParity₄, negOnePow_abs] using same

lemma perm (σ : Perm (Fin 4)) :
    ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)) := by
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction ?_ (fun _ ↦ id) (fun σ τ _ _ hσ hτ t same ↦ ?_) this
  on_goal 2 => simp_rw [Perm.mul_apply]; exact hτ (t ∘ σ) (hσ _ same)
  rintro _ ⟨i, rfl⟩ t ⟨h₀₁, h₁₂, h₂₃⟩; fin_cases i
  exacts [⟨h₀₁.symm, h₀₁ ▸ h₁₂, h₂₃⟩, ⟨h₀₁ ▸ h₁₂, h₁₂.symm, h₁₂ ▸ h₂₃⟩, ⟨h₀₁, h₁₂ ▸ h₂₃, h₂₃.symm⟩]
include same in
lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
  simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  rw [← add_two_le_iff_lt_of_even_sub] at hdc hcb hba
  · linarith
  exacts [same.1, same.2.1, same.2.2]

variable (W) in
def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)

lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub]; ring

include same in
lemma addMulSub_transf :
    addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - c) = addMulSub₄ W a b c d ∧
      addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - b) = addMulSub₄ W a c b d ∧
      addMulSub W (avg₄ a b c d - d) |avg₄ a b c d - a| = addMulSub₄ W b c a d ∧
      addMulSub W (avg₄ a b c d - c) (avg₄ a b c d - b) = addMulSub₄ W a d b c ∧
      addMulSub W (avg₄ a b c d - c) |avg₄ a b c d - a| = addMulSub₄ W b d a c ∧
      addMulSub W (avg₄ a b c d - b) |avg₄ a b c d - a| = addMulSub₄ W c d a b := by
  simp_rw [addMulSub_abs₁, addMulSub, addMulSub₄, sub_add_sub_comm, same.avg₄_add_avg₄]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf

include same in
theorem rel₄_transf :
    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf (W := W)
  simp_rw [rel₄, h₁, h₂, h₃, h₄, h₅, h₆, addMulSub₄_mul_addMulSub₄, mul_comm]

include same in
theorem transf : HaveSameParity₄
    (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]

include same in
theorem strictAnti₄_transf (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]
  · rw [sub_neg_eq_add, sub_add_sub_comm, same.avg₄_add_avg₄]; linarith only [hd, hdc]
  all_goals linarith only [hdc, hcb, hba]

end HaveSameParity₄

end transf

def rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  rw [rel₄, ← mul_zero 2, Rel₃]
  simp_rw [addMulSub_even, add_zero, sub_zero]
  convert sub_eq_zero.symm using 2; ring

lemma rel₆_eq₃ (c d m n r : ℤ) :
    rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d := by
  simp_rw [rel₆, rel₄]; ring

lemma rel₆_eq₃' (c d m n r : ℤ) :
    rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d := by
  simp_rw [rel₆, rel₄]; ring

theorem rel₆_eq₁₀ (c d m n r s : ℤ) :
    rel₆ W c d m n r s =
      rel₆ W n d m r s c - rel₆ W r d m n s c + rel₆ W s d m n r c
      + rel₆ W n c m r s d - rel₆ W r c m n s d + rel₆ W s c m n r d
      + rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d
      - 2 * rel₆ W m d n r s c := by
  simp_rw [rel₆, rel₄]; ring

theorem addMulSub_sq_mul_rel₄_eq₉ (c d m n r s : ℤ) :
    (addMulSub W c d) ^ 2 * rel₄ W m n r s =
      addMulSub W m c * (rel₆ W n d r s c d - rel₆ W r d n s c d + rel₆ W s d n r c d)
      - addMulSub W m d * (rel₆ W n c r s c d - rel₆ W r c n s c d + rel₆ W s c n r c d)
      + addMulSub W c d * (rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d) := by
  simp_rw [rel₆, rel₄]; ring

def OddRec (m : ℤ) : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

def EvenRec (m : ℤ) : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
  rw [Rel₃, OddRec]; ring_nf

lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m := by
  rw [Rel₃, EvenRec]; ring_nf

lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  rw [iff_comm, EvenRec, ← sub_eq_zero, show 2 * m - 1 = 2 * (m - 1) + 1 by ring]
  change _ ↔ rel₄ W (2 * m + 1) (2 * (m - 1) + 1) (2 * 1 + 1) (2 * 0 + 1) = 0
  simp_rw [rel₄, addMulSub_odd]; ring_nf

def dMin (a : ℤ) : ℤ := if Even a then 0 else 1

def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_nonneg (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two

lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h
  · simp [Int.negOnePow_even a h]
  · simp [Int.negOnePow_odd a (Int.not_even_iff_odd.mp h)]
lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]

variable {W}
lemma addMulSub_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]

lemma dMin_le {a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]

open Int

section Rel₄OfValid

variable (W) in
def Rel₄OfValid (a b c d : ℤ) : Prop :=
  HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0

variable {a c₀ d₀ : ℤ} (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀) (lt : d₀ < c₀)
  (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀) (mem : addMulSub W c₀ d₀ ∈ R⁰)

include par le lt rel mem in
lemma rel₄_fix₁_of_fix₂ (b c : ℤ) :
    Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀) := by
  refine ⟨fun same anti ↦ (mem_nonZeroDivisors_iff.mp mem).2 _ ?_,
    fun _hc same anti ↦ (mem_nonZeroDivisors_iff.mp mem).2 _ ?_⟩ <;> rw [mul_comm, ← rel₆]
  on_goal 1 => rw [rel₆_eq₃]; have _hc := trivial
  on_goal 2 => rw [rel₆_eq₃']
  all_goals simp_rw [rel₆]; rw [rel le_rfl, rel le_rfl, rel anti.2.2.2.le]
  iterate 2
    simp_rw [mul_zero, add_zero, sub_zero]
    iterate 3
      simp only [HaveSameParity₄, par, same.1, same.2.1, same.2.2, true_and]
      refine ⟨le, lt, ?_, ?_⟩ <;> linarith only [_hc, anti.2.1, anti.2.2.1, anti.2.2.2]
include par le lt rel mem in
lemma rel₄_of_fix₂ (b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) :
    Rel₄OfValid W a b c d := fun same ⟨_, hdc, hcb, hba⟩ ↦
      (mem_nonZeroDivisors_iff.mp mem).2 _ <| by
  rw [mul_comm, ← rel₆, rel₆_eq₁₀]; simp_rw [rel₆]
  have fix₁ b c := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).1
  have fix₂ {b c} := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).2
  rw [fix₁, fix₁, fix₁, fix₂ hc, fix₂ hc, fix₂ (hc.trans hdc), rel le_rfl, rel le_rfl,
    rel le_rfl, (rel₄_fix₁_of_fix₂ par le lt (fun h ↦ rel <| h.trans hba.le) mem _ _).1]
  · simp_rw [mul_zero, add_zero, sub_zero]
  iterate 10
    simp only [HaveSameParity₄, par, par', same.1, same.2.1, same.2.2, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hc, le, lt, hdc, hcb, hba]

theorem rel₄_of_min₂ (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) :
    Rel₄OfValid W a b c d := fun same anti ↦ by
  obtain hc|hc := lt_or_ge (cMin a) d
  · refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
      (addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ same anti
    rw [negOnePow_dMin, same.1, same.2.1, same.2.2]
  have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
    (addMulSub_mem_nonZeroDivisors one two a) b c
  obtain rfl|hc := (show d ≤ cMin a from hc).eq_or_lt
  · exact fix.1 same anti
  obtain rfl : dMin a = d := (dMin_le same.same₀₃ anti.1).antisymm <| by
    rwa [← add_two_le_iff_lt_of_even_sub, cMin, add_le_add_iff_right] at hc
    rw [← negOnePow_eq_iff, negOnePow_cMin, same.same₀₃]
  obtain rfl|hc : cMin a = c ∨ _ := ((add_two_le_iff_lt_of_even_sub <| by
    rw [← negOnePow_eq_iff, negOnePow_dMin, same.1, same.2.1]).mpr anti.2.1).eq_or_lt
  exacts [rel le_rfl same anti, fix.2 hc same anti]
theorem rel₄_of_anti_oddRec_evenRec (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :
    ∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d :=
  Int.strongRec (m := 6)
    (fun a ha b c d same anti ↦
      absurd (ha.trans_le (same.six_le_of_strictAnti₄ anti)) (lt_irrefl a))
    fun a h6 ih ↦ rel₄_of_min₂ one two fun {a' b} haa same anti ↦ by
  obtain ha'|ha' := haa.lt_or_eq
  · exact ih _ ha' same anti
  obtain hba|rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (add_two_le_iff_lt_of_even_sub <| (negOnePow_eq_iff _ _).1 same.1).mpr anti.2.2.2
  · rw [← same.rel₄_transf]
    refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)
    rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
    linarith only [hba]
  obtain ⟨m, rfl|rfl⟩ := b.even_or_odd'
  · have ea : Even a := by rw [← ha']; exact (even_two_mul _).add even_two
    simp_rw [cMin, dMin, ite_eq_left ea]
    have hm : m ≥ 2 := by linarith only [h6, ha']
    convert (rel₃_iff₄ W (m + 1) m 1).mp ((rel₃_iff_oddRec W m).mpr <| oddRec _ hm) using 2
    all_goals ring
  · have nea : ¬ Even a := by
      rw [← ha', Int.not_even_iff_odd]; convert odd_two_mul_add_one (m + 1) using 1; ring
    simp_rw [cMin, dMin, ite_eq_right nea]
    have hm : m + 1 ≥ 3 := by linarith only [h6, ha']
    convert (rel₄_iff_evenRec W (m + 1)).mpr (evenRec _ hm) using 2
    all_goals ring
end Rel₄OfValid

section Perm

variable (neg : ∀ k, W (-k) = -W k)

include neg in
lemma rel₄_abs {m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]

include neg in
lemma rel₄_swap₀₁ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W n m r s := by
  simp_rw [rel₄, addMulSub_swap W neg n m]; ring

include neg in
lemma rel₄_swap₁₂ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m r n s := by
  simp_rw [rel₄, addMulSub_swap W neg r n]; ring

include neg in
lemma rel₄_swap₂₃ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m n s r := by
  simp_rw [rel₄, addMulSub_swap W neg s r]; ring

open Equiv

variable (W) in
def relFin4 (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)

include neg in
theorem relFin4_perm (σ : Perm (Fin 4)) : ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t := by
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction ?_ (by simp) (fun σ τ _ _ hσ hτ t ↦ ?_) this
  · rintro _ ⟨i, rfl⟩ t; fin_cases i <;>
      rw [Perm.sign_swap (Fin.castSucc_lt_succ).ne, Units.neg_smul, one_smul]
    exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]
  rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ, map_mul, mul_comm, mul_smul]
include neg in
lemma relFin4_perm' (σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]
variable (zero : W 0 = 0)

include zero in
lemma rel₄_same₀₁ (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

include zero in
lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

include zero in
lemma rel₄_same₂₃ (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m)

include neg zero one two oddRec evenRec in
theorem rel₄_of_oddRec_evenRec {a b c d : ℤ} (same : HaveSameParity₄ a b c d) :
    rel₄ W a b c d = 0 := by
  let t := ![|a|, |b|, |c|, |d|]
  have nonneg i : 0 ≤ t i := by fin_cases i <;> exact abs_nonneg _
  let σ := Fin.revPerm.trans (Tuple.sort t)
  have anti : Antitone (t ∘ σ) := by
    simp_rw [σ, coe_trans, ← Function.comp_assoc]
    exact (Tuple.monotone_sort t).comp_antitone fun _ _ ↦ Fin.rev_le_rev.mpr
  clear_value σ
  rw [← rel₄_abs neg]; change relFin4 W t = 0
  rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]
  by_cases h₃₂ : t (σ 3) = t (σ 2); · rw [h₃₂, rel₄_same₂₃ zero, smul_zero]
  by_cases h₂₁ : t (σ 2) = t (σ 1); · rw [h₂₁, rel₄_same₁₂ zero, smul_zero]
  by_cases h₁₀ : t (σ 1) = t (σ 0); · rw [h₁₀, rel₄_same₀₁ zero, smul_zero]
  rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec (same.abs.perm _ _), smul_zero]
  exact ⟨nonneg _, (anti <| by decide).lt_of_ne h₃₂,
    (anti <| by decide).lt_of_ne h₂₁, (anti <| by decide).lt_of_ne h₁₀⟩
include neg zero one two oddRec evenRec in
theorem _root_.IsEllSequence'.of_oddRec_evenRec : IsEllSequence' W := by
  rw [isEllSequence_iff_rel₃]
  intro m n r
  rw [rel₃_iff₄, rel₄_of_oddRec_evenRec neg zero one two oddRec evenRec]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [negOnePow_two_mul, negOnePow_zero]
end Perm

end EllSequence

open EllSequence

variable {W}

lemma IsEllSequence'.map (h : IsEllSequence' W) : IsEllSequence' (f ∘ W) :=
  fun m n r => by simpa using congr_arg f (h m n r)

lemma IsDivSequence'.map (h : IsDivSequence' W) : IsDivSequence' (f ∘ W) :=
  (map_dvd f <| h · · ·)

lemma IsEllDivSequence'.map (h : IsEllDivSequence' W) : IsEllDivSequence' (f ∘ W) :=
  ⟨h.1.map f, h.2.map f⟩

namespace IsEllSequence'

open EllSequence

variable (ell : IsEllSequence' W)

include ell in
lemma oddRec (m : ℤ) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)
include ell in
lemma evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)

include ell in
lemma zero' [IsReduced R] : W 0 = 0 := by
  have := ell 0 0 0
  simp_rw [add_zero, sub_self, mul_assoc, ← pow_succ'] at this
  exact IsReduced.eq_zero _ ⟨_, this⟩
include ell in
lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have := ell m m (2 * m)
  rw [add_comm, sub_self, sub_self, ← two_mul, mul_comm (W _)] at this
  exact (mem_nonZeroDivisors_iff.mp mem).2 _
    ((mem_nonZeroDivisors_iff.mp (pow_mem mem 2)).2 _ this)
include ell in
lemma sub_add_neg_sub_mul_eq_zero (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have := congr($(ell m n r) + $(ell n m r))
  rw [add_comm n, ← right_distrib, ← left_distrib, mul_comm (W _)] at this
  convert this using 4 <;> ring_nf

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)

include ell one two in
lemma neg (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  on_goal 1 => apply (mem_nonZeroDivisors_iff.mp two).2
  on_goal 2 => apply (mem_nonZeroDivisors_iff.mp one).2
  all_goals apply (mem_nonZeroDivisors_iff.mp (pow_mem one 2)).2
  · convert sub_add_neg_sub_mul_eq_zero ell (1 - m) (m + 1) 1 using 2; ring_nf
  · convert sub_add_neg_sub_mul_eq_zero ell (-m) (m + 1) 1 using 2; ring_nf
include ell one two in
protected lemma rel₄ {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0 :=
  rel₄_of_oddRec_evenRec (ell.neg one two) (ell.zero 1 two) one two
    (fun _ _ ↦ ell.oddRec _) (fun _ _ ↦ ell.evenRec _) same
include ell one two in
protected lemma net (p q r s : ℤ) : net W p q r s = 0 := by
  rw [net_eq_rel₄]
  refine ell.rel₄ one two ?_
  simp_rw [HaveSameParity₄, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, true_and]
include ell in
include one two in
lemma invar (s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invar_of_net _ (ell.net one two) _ _ _
end IsEllSequence'

variable (b c d : R)

lemma invarNum_normEDS (n : ℤ) : letI W := normEDS b c d
    invarNum W 1 n = W (n + 2) * W (n - 1) ^ 2 + W (n + 1) ^ 2 * W (n - 2) + W n ^ 3 * b ^ 2 := by
  simp [invarNum]
lemma invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [invarNum, right_distrib, ← pow_succ, ← pow_add]
lemma invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b := by simp [invarDenom]

section Complement

variable (b c d : R) (m : ℤ)

def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] lemma compl₂EDSAux_zero : compl₂EDSAux b c d 0 = -1 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_one : compl₂EDSAux b c d 1 = -b := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_one : compl₂EDSAux b c d (-1) = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_two : compl₂EDSAux b c d 2 = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_two : compl₂EDSAux b c d (-2) = -d := by simp [compl₂EDSAux]

lemma compl₂EDSAux_mul_b :
    compl₂EDSAux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [compl₂EDSAux, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]; split_ifs <;> ring

lemma compl₂EDSAux_neg : compl₂EDSAux b c d (-m) = -complEDS₂ b c d m - compl₂EDSAux b c d m := by
  simp_rw [compl₂EDSAux, complEDS₂, neg_sub_left, neg_add_eq_sub, ← neg_sub m,
    preNormEDS_neg, even_neg]; ring_nf

lemma normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_complEDS₂, complEDS₂, ite_eq_right (by decide)]
  simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]
  rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, ite_eq_right (by decide)]
  ring

end Complement

section Map

variable {b c d}

private lemma map_normEDS_fl (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
  map_normEDS f b c d n

lemma map_addMulSub (m n : ℤ) : f (addMulSub W m n) = addMulSub (f ∘ W) m n := by
  simp_rw [addMulSub, map_mul, Function.comp]

lemma map_rel₄ (p q r s : ℤ) : f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s := by
  simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]

lemma map_net (p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s := by
  simp_rw [net_eq_rel₄, map_rel₄]

lemma map_invarNum (s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp]

lemma map_invarDenom (s m : ℤ) : f (invarDenom W s m) = invarDenom (f ∘ W) s m := by
  simp only [invarDenom, map_mul, Function.comp_apply]

inductive Param : Type | B : Param | C : Param | D : Param

open Param MvPolynomial

noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)

lemma normEDS_eq_aeval : normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) := by
  simp_rw [universalNormEDS, map_normEDS_fl, aeval_X]

lemma complEDS₂_eq_aeval :
    complEDS₂ b c d =
      (aeval (Param.rec b c d) <| complEDS₂ (X (R := ℤ) B) (X C) (X D) ·) := by
  simp_rw [map_complEDS₂, aeval_X]

end Map

section

variable {b c d} {U : ℤ → R} (ellW : IsEllSequence' W) (ellU : IsEllSequence' U)
open MvPolynomial

private lemma normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) : IsEllSequence' (normEDS b c d) :=
  IsEllSequence'.of_oddRec_evenRec (normEDS_neg b c d) (normEDS_zero b c d)
    (by rw [normEDS_one]; exact one_mem _) (by rwa [normEDS_two])
    (fun m _ => by simp only [OddRec, normEDS_one, one_pow, mul_one]; exact normEDS_odd b c d m)
    (fun m _ => by
      simp only [EvenRec, normEDS_one, normEDS_two, one_pow, mul_one]
      rw [normEDS_even]; ring)

protected lemma IsEllSequence'.normEDS : IsEllSequence' (normEDS b c d) := by
  rw [normEDS_eq_aeval]
  exact IsEllSequence'.map _
    (normEDS_of_mem_nonZeroDivisors <| mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _)

include ellW ellU in
protected lemma IsEllSequence'.ext (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U := by
  funext n
  induction n using Int.negInduction with
  | nat n =>
    refine normEDSRec ?_ h1 h2 h3 h4 (fun m h₁ h₂ h₃ h₄ h₅ ↦ ?_) (fun m h₁ h₂ h₃ h₄ ↦ ?_) n
    · rw [Nat.cast_zero, ellW.zero 1 two, ellU.zero 1 (h2 ▸ two)]
    · erw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two <| pow_mem one 2), ← mul_assoc,
        ← mul_assoc, Nat.cast_mul, Nat.cast_add, ellW.evenRec, h1, h2, ellU.evenRec]
      convert congr($h₃ * ($h₂ ^ 2 * $h₅ - $h₁ * $h₄ ^ 2)) <;> omega
    · rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
      erw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, ellW.oddRec, h1, ellU.oddRec]
      convert congr($h₄ * $h₂ ^ 3 - $h₁ * $h₃ ^ 3) <;> omega
  | neg ih n => rw [ellW.neg one two, ellU.neg (h1 ▸ one) (h2 ▸ two), ih]

section Divisibility

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (dvd₁₂ : W 1 ∣ W 2) (dvd₁₃ : W 1 ∣ W 3) (dvd₂₄ : W 2 ∣ W 4)

include ellW one two dvd₁₂ dvd₁₃ dvd₂₄ in
theorem IsEllSequence'.eq_normEDS_of_dvd :
    ∃ b c d, W = (fun n => W 1 * _root_.normEDS b c d n) := by
  obtain ⟨b, h₁₂⟩ := dvd₁₂
  obtain ⟨c, h₁₃⟩ := dvd₁₃
  obtain ⟨d, h₂₄⟩ := dvd₂₄
  have hU : IsEllSequence' (fun n => W 1 * _root_.normEDS b c d n) :=
    (IsEllSequence'.smul IsEllSequence'.normEDS (W 1))
  exact ⟨b, c, d, ellW.ext (ellU := hU) one two (by simp) (by simp [h₁₂])
    (by simp [h₁₃]) (by rw [h₂₄, h₁₂, normEDS_four]; ring)⟩

include one two in
theorem IsEllDivSequence'.eq_normEDS (h : IsEllDivSequence' W) :
    ∃ b c d, W = (fun n => W 1 * _root_.normEDS b c d n) :=
  (IsEllSequence'.eq_normEDS_of_dvd (ellW := h.1) one two (h.2 _ _ ⟨2, rfl⟩)
    (h.2 _ _ ⟨3, rfl⟩) (h.2 _ _ ⟨2, rfl⟩))

section Complement

variable (m n : ℤ)

lemma normEDS_mul_complEDS_div (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :
    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n := by
  obtain ⟨n, rfl⟩ := dvd
  rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]

namespace EllSequence

variable (b c d)

def redInvarNum : R :=
  complEDS₂ b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m

lemma complEDS₂_eq_redInvarNum_sub :
    complEDS₂ b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * compl₂EDSAux b c d m := by
  rw [redInvarNum]; ring

lemma invarNum_eq_redInvarNum_mul : invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b,
    compl₂EDSAux_mul_b, invarNum_normEDS]; ring

def redInvarDenom : R :=
  letI C := complEDS b c d
  letI W := normEDS b c d
  letI r₆ := normEDS b c d 5 - d ^ 2
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0

lemma invarDenom_eq_redInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c := by
  have h6 : (6 : ℤ) ≠ 0 := by decide
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hd (k m : ℤ) (dvd : k ∣ 6) (eq : m % 6 % k = 0) : k ∣ m :=
    Int.dvd_iff_emod_eq_zero.mpr ((Int.emod_emod_of_dvd m dvd).symm.trans eq)
  have hd2 {m} := hd 2 m ⟨3, rfl⟩
  have hd3 {m} := hd 3 m ⟨2, rfl⟩
  have dvd_sub {a b c : ℤ} (h : a % b = c) : b ∣ a - c := by
    rw [← h, Int.emod_def, sub_sub_cancel]
    apply dvd_mul_right
  have mul_eq := @normEDS_mul_complEDS_div _ _ b c d
  rw [invarDenom, redInvarDenom]; split_ifs with h h h h h h
  · rw [← mul_eq _ h6 _ (Int.dvd_of_emod_eq_zero h), normEDS_six_eq_mul]; ring
  · rw [← mul_eq _ h6 _ (dvd_sub h), normEDS_six_eq_mul]; ring
  · rw [show m + 1 = m + 6 - 5 by abel,
      ← mul_eq _ h6 _ (dvd_sub (show (m + 6) % 6 = 5 by omega)), normEDS_six_eq_mul]; ring
  on_goal 1 => rw [← mul_eq _ h3 _ (hd3 <| by simp [h, Int.add_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 2 => rw [← mul_eq _ h3 (m - 1) (hd3 <| by simp [h, Int.sub_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 3 => rw [← mul_eq _ h3 m (hd3 <| by simp [h]),
    ← mul_eq _ two_ne_zero (m - 1) (hd2 <| by simp [h, Int.sub_emod])]
  on_goal 4 =>
    have h0 := Int.emod_nonneg m h6
    have lt := Int.emod_lt_of_pos m (show 0 < 6 by decide)
    interval_cases m % 6 <;> contradiction
  all_goals rw [normEDS_three, normEDS_two]; ring

@[simp] lemma redInvarDenom_zero : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom]

@[simp] lemma redInvarDenom_one : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom]

@[simp] lemma redInvarDenom_two : redInvarDenom b c d 2 = 1 := by
  simp [redInvarDenom]

lemma map_compl₂EDSAux : f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m := by
  have mp : ∀ n : ℤ, f (preNormEDS (b ^ 4) c d n) = preNormEDS (f b ^ 4) (f c) (f d) n :=
    fun n ↦ by
      rw [show f b ^ 4 = f (b ^ 4) from (map_pow f b 4).symm]
      exact map_preNormEDS f (b ^ 4) c d n
  simp [compl₂EDSAux, apply_ite f, mp]

lemma map_redInvarNum : f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n ↦ map_normEDS f b c d n
  simp [redInvarNum, map_complEDS₂, mn, map_compl₂EDSAux, map_ofNat]

lemma map_redInvarDenom : f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n ↦ map_normEDS f b c d n
  simp [redInvarDenom, apply_ite f, mn, map_complEDS]

end EllSequence

end Complement

protected theorem IsDivSequence'.normEDS : IsDivSequence' (normEDS b c d) := by
  rintro m _ ⟨n, rfl⟩
  rw [Nat.cast_mul, mul_comm (m : ℤ), ← normEDS_mul_complEDS]
  exact dvd_mul_right _ _

protected theorem IsEllDivSequence'.normEDS : IsEllDivSequence' (normEDS b c d) :=
  ⟨IsEllSequence'.normEDS, IsDivSequence'.normEDS⟩

include ellW one two dvd₁₂ dvd₁₃ dvd₂₄ in
lemma IsEllSequence'.isDivSequence_of_dvd : IsDivSequence' W := by
  obtain ⟨b, c, d, h⟩ := (IsEllSequence'.eq_normEDS_of_dvd (ellW := ellW) one two dvd₁₂ dvd₁₃ dvd₂₄)
  rw [h]; exact IsDivSequence'.normEDS.smul _

include ellW one two dvd₁₂ dvd₁₃ dvd₂₄ in
lemma IsEllSequence'.isEllDivSequence_of_dvd : IsEllDivSequence' W :=
  ⟨ellW, ellW.isDivSequence_of_dvd one two dvd₁₂ dvd₁₃ dvd₂₄⟩

end Divisibility

section

lemma net_normEDS (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 := by
  rw [normEDS_eq_aeval, ← Function.comp_def, ← map_net,
    universalNormEDS, IsEllSequence'.normEDS.net, map_zero] <;>
    apply mem_nonZeroDivisors_of_ne_zero <;>
    simp only [normEDS_one, normEDS_two] <;>
    first
      | exact one_ne_zero
      | exact MvPolynomial.X_ne_zero _

lemma rel₄_normEDS (p q r s : ℤ) (same : HaveSameParity₄ p q r s) :
    rel₄ (normEDS b c d) p q r s = 0 := by
  rw [same.rel₄_eq_net, net_normEDS]

lemma invar_normEDS (s m n : ℤ) :
    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =
      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=
  invar_of_net _ net_normEDS _ _ _

private lemma invar₂_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, mul_assoc, mul_assoc, mul_comm (invarDenom _ _ _)]
  convert invar_normEDS 1 m 2 <;> simp only [invarNum_normEDS_two, invarDenom_normEDS_two]

open MvPolynomial Param in
lemma invar₂_normEDS {m : ℤ} :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(invar₂_normEDS_of_mem_nonZeroDivisors
    (c := X Param.C) (d := X D) (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero (R := ℤ) B) m))
  rw [← universalNormEDS] at this
  simpa only [map_mul, map_invarNum, map_invarDenom,
    Function.comp_def, ← normEDS_eq_aeval, map_add, map_pow, aeval_X] using this

private lemma redInvar_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (hc : c ∈ R⁰) (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]
  ring

open MvPolynomial Param in
lemma redInvar_normEDS (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(redInvar_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) B) (c := X Param.C) (d := X D) ?_ ?_ m))
  · simpa only [map_redInvarNum, map_mul, map_add, map_pow, map_redInvarDenom, aeval_X] using this
  all_goals exact mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)
end

end

end PortEllSequenceCore

section PortEllSequenceUniversal

noncomputable section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Affine.CoordinateRing

lemma algebraMap_injective' {R : Type*} [CommRing R] (W : Affine R) :
    Function.Injective (algebraMap R W.CoordinateRing) := by
  have h : Function.Injective (algebraMap (Polynomial R) W.CoordinateRing) :=
    (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
      smul_basis_eq_zero (W' := W) (q := 0) <| by
        rw [smul, smul, mul_one, Polynomial.C_0, map_zero, zero_mul, add_zero]
        exact hp
  exact h.comp Polynomial.C_injective

end Affine.CoordinateRing

namespace Univ

open scoped Polynomial Polynomial.Bivariate
open Coeff

open MvPolynomial (X) in
def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

protected abbrev Ring : Type := curve.CoordinateRing

protected abbrev Field : Type := FractionRing Univ.Ring

lemma Poly.two_ne_zero : (2 : Poly) ≠ 0 :=
  Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℤ) <|
    MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h

def polyToField : Poly →+* Univ.Field := (algebraMap Univ.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Univ.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Univ.Field = polyToField.comp (algebraMap _ _) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Univ.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Univ.Field) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' _)

abbrev pointedCurve : WeierstrassCurve Univ.Field :=
  baseChange curve Univ.Field

instance : pointedCurve.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by
    simpa only [pointedCurve, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
      using Δ_curve_ne_zero

open Polynomial (CC)

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  have h := polyToField_polynomial
  simp only [Affine.polynomial, map_add, map_sub, map_mul, map_pow] at h
  rw [Affine.equation_iff', pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₃, pointedCurve_a₄,
    pointedCurve_a₆]
  linear_combination h

open Polynomial Affine in
def Affine.point : curve⟮Univ.Field⟯ :=
  .some (polyToField (C X)) (polyToField Y)
    ((pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      (by simpa only [pointedCurve, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
        using Δ_curve_ne_zero)).mp equation_point)

def Jacobian.point : Jacobian.Point (WeierstrassCurve.baseChange curve Univ.Field) :=
  Jacobian.Point.fromAffine Affine.point

abbrev curvePoly : WeierstrassCurve Poly := WeierstrassCurve.baseChange curve Poly

abbrev curveRing : WeierstrassCurve Univ.Ring :=
  WeierstrassCurve.baseChange curve Univ.Ring

abbrev curveField : WeierstrassCurve Univ.Field :=
  WeierstrassCurve.baseChange curve Univ.Field

lemma curveField_eq : curveField = pointedCurve := rfl

end Univ

def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

open Univ
variable {R} [CommRing R] (W : WeierstrassCurve R)

def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

lemma map_specialize : WeierstrassCurve.map Univ.curve W.specialize = W := by
  simp [specialize, curve, map]

namespace Univ

variable (x y : R)

open Polynomial (eval₂RingHom) in
def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in
def ringEval : Univ.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]
    rw [← Affine.map_polynomial]
    simpa only [Affine.map, map_specialize, Affine.Equation, evalEval, coe_evalRingHom] using eqn

lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval, -AddMonoidAlgebra.coe_algebraMap]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

protected lemma Field.two_ne_zero : (2 : Univ.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Univ.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; cases h

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, WeierstrassCurve.baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

end Univ

end WeierstrassCurve

end

end PortEllSequenceUniversal

section PortEllSequenceDivisionPolys

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

noncomputable section

def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

open Affine (polynomial polynomialX polynomialY negPolynomial)
open EllSequence

lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, preΨ₄_add_Ψ₂Sq_sq]; C_simp; ring

lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [WeierstrassCurve.φ, invarDenom]; ring

/-- **The division polynomial `ωₙ`.** A bivariate polynomial over the commutative ring `R`,
defined for every Weierstrass curve `W` and every `n`, which can be evaluated at any pair
`(x, y)`. It is the second entry of the triple `smulEval W x y n`: when `R` is a field and `(x, y)`
is a nonsingular point of `W`, that triple represents `n • (x, y)` in Jacobian coordinates
(`zsmul_eq_smulEval`). -/
public protected def ωe (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

lemma ωe_spec (n : ℤ) :
    2 * W.ωe n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  have hψ : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
  rw [ψc, complEDS₂_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four,
    mul_assoc (C _), φ_mul_ψ, hψ, invarDenom_eq_redInvarDenom_mul, WeierstrassCurve.ωe, ← hψ,
    invar, b₂, b₄, ψ₂, Affine.polynomialY, Affine.polynomialX, Affine.negPolynomial]
  C_simp; ring

lemma two_mul_ωe (n : ℤ) :
    2 * W.ωe n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ωe_spec]; abel

lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_complEDS₂ _ _ _ _

@[simp] lemma ωe_zero : W.ωe 0 = 1 := by simp [WeierstrassCurve.ωe]

@[simp] lemma ωe_one : W.ωe 1 = Y := by simp [WeierstrassCurve.ωe, ψ₂, ← Affine.Y_sub_polynomialY]

@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]

end

section Map

variable (f : R →+* S)

lemma map_ψc (n : ℤ) : (W.map f).ψc n = (W.ψc n).map (mapRingHom f) := by
  simp only [ψc, ← coe_mapRingHom, map_complEDS₂, map_ψ₂, map_Ψ₃, map_preΨ₄]
  simp only [coe_mapRingHom, map_C]

lemma map_invar : (W.map f).invar = W.invar.map f := by
  simp only [invar, map_b₂, map_b₄]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    map_C, map_X]

open Affine EllSequence in
lemma map_ωe (n : ℤ) : (W.map f).ωe n = (W.ωe n).map (mapRingHom f) := by
  simp_rw [WeierstrassCurve.ωe, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom,
    map_compl₂EDSAux, map_polynomial, map_polynomialX, map_polynomialY, map_negPolynomial,
    map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]; simp

end Map

end WeierstrassCurve

end PortEllSequenceDivisionPolys

section PortEllSequenceZSMul

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

namespace Univ

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

lemma evalEval_ωe : (W.ωe n).evalEval x y =  polyEval W x y (curve.ωe n) := by
  simp_rw [polyEval_apply, ← map_ωe, map_specialize]

open WeierstrassCurve (ψ φ ωe)

lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by
  simp [cusp, ψ₂, Affine.polynomialY, map_ofNat]

lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]

lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring

lemma polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2 := by
  rw [ψc, map_complEDS₂, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, complEDS₂_two_three_two]

lemma polyEval_cusp_ωe : polyEval cusp 1 1 (curve.ωe n) = 1 := by
  have := congr(polyEval cusp 1 1 $(curve.two_mul_ωe n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this

abbrev ψᵤ (n : ℤ) : Univ.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : IsEllSequence' ψᵤ := by rw [ψᵤ_eq_normEDS]; exact IsEllSequence'.normEDS
lemma net_ψᵤ (p q r s) : EllSequence.net ψᵤ p q r s = 0 := by rw [ψᵤ_eq_normEDS]; apply net_normEDS

lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]

namespace Affine

variable (n)

def smulX : Univ.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

def smulY : Univ.Field := polyToField (curve.ωe n) / (ψᵤ n) ^ 3
variable {n}

@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, smulX_one, φ, map_sub, sub_div, map_mul, map_pow, mul_div_cancel_right₀, map_mul]
  exact pow_ne_zero _ (ψᵤ_ne_zero hn)

lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left, div_sub_div]
  · rw [mul_pow]; congr; convert (isEllSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]; ring_nf

lemma smulX_neg : smulX (-n) = smulX n := by simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, map_neg, neg_sq]

lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h; exact smulX_ne_smulX h.1 h.2
  · rintro (rfl|rfl); exacts [rfl, smulX_neg]

private lemma smulY_sub_negY_aux {G} [_root_.Field G] {a₁ a₃ x y z : G} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, ← ψc_spec, ← ωe_spec,
    map_mul, map_add, map_mul, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

def slopeOne : Univ.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY, Affine.polynomialX]
  congr
  simp [algebraMap_field_eq_comp, Polynomial.algebraMap_apply, map_ofNat,
    -AddMonoidAlgebra.coe_algebraMap]

private lemma addX_smul_one_smul_one_aux {G} [_root_.Field G] {a₁ a₂ x dx dy : G} (h0 : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by
  field_simp; ring

lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := .symm <| by
  rw [smulX_two, Affine.addX, sub_eq_neg_add, ← eq_sub_iff_add_eq, ← neg_div _ (polyToField _),
    slopeOne_eq_neg_div, addX_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_ψ₂Sq, ψᵤ,
    ψ_two, ψ_three, C_Ψ₃_eq, polyToField_polynomial, pointedCurve_a₁, pointedCurve_a₂, smulX_one]
  ring

private lemma addY_smul_one_smul_one_aux {G} [_root_.Field G]
    {a₁ a₃ dx dy x y ψ₃ t : G} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

open EllSequence in
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ωe, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, Affine.addY,
    Affine.negAddY, addX_smul_one_smul_one, smulX_two, Affine.negY, Affine.negPolynomial,
    slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero]
  exact addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)

private lemma smulY_neg_aux {G} [_root_.Field G] {a₁ a₃ x y z : G} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

open Polynomial (CC) in
lemma ωe_neg' : curve.ωe (-n) =
    curve.ωe n + CC curve.a₁ * curve.φ n * curve.ψ n + CC curve.a₃ * curve.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ωe, ψc_neg, ψ_neg, φ_neg]; ring

lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψ_neg, ωe_neg',
    map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)

private lemma smulX_add_aux {G} [_root_.Field G] {m n m₂ n₂ a s : G}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp

lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', smulX_sub_sub_smulX_add add_ne sub_ne]
  simp_rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
  apply smulX_add_aux <;> apply ψᵤ_ne_zero <;> assumption

private lemma smulY_add_sub_negY_aux {G} [_root_.Field G] {m n m₂ n₂ a s am an : G}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by
  field_simp

lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    ψ₂ (smulX (n + m)) (smulY (n + m)) =
      (ψ₂ (smulX m) (smulY m) * (smulX n - smulX (n + m))
        - ψ₂ (smulX n) (smulY n) * (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hn add_ne,
    smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, add_sub_cancel_left, add_sub_cancel_right]
  rw [smulY_add_sub_negY_aux]
  · congr; rw [eq_div_iff]
    · linear_combination (norm := ring_nf) (EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)
    apply_rules [mul_ne_zero, ψᵤ_ne_zero]
  all_goals apply ψᵤ_ne_zero; assumption

open Affine.Point

open WeierstrassCurve.Affine in
instance : AddGroup (curve⟮Univ.Field⟯) := inferInstance

theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : Affine.Nonsingular curveField (smulX n) (smulY n),
      n • Affine.point = .some (smulX n) (smulY n) h := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _|_|_|n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨(pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        (by simpa only [pointedCurve, baseChange, map_Δ,
          map_ne_zero_iff _ algebraMap_field_injective]
          using Δ_curve_ne_zero)).mp equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2,
        dite_eq_right fun h ↦ smulY_one_ne_negY h.2⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, add_of_X_ne ne, Affine.Point.some.injEq] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]; rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Field.two_ne_zero),
        ← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [Affine.negY, Nat.cast_add]; simp only [_U]; ring_nf
      convert _U.addY_sub_negY_addY (smulY n2) (smulY 1) ne using 1
      · rw [Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns fun h ↦ (ne h.1).elim, add_of_X_ne ne⟩
  | neg hn n =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := hn n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨(Affine.nonsingular_neg ..).mpr ns, trivial⟩

lemma nonsingular_smulX_smulY (hn : n ≠ 0) : Affine.Nonsingular curveField (smulX n) (smulY n) := by
  exact (zsmul_point_eq_smulX_smulY hn).1

lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Affine.point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]; exact Affine.Point.some_ne_zero ns

end Affine

namespace Jacobian

open WeierstrassCurve.Jacobian

open Point in
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0 := by
  rw [Jacobian.point, ← toAffineAddEquiv_symm_apply, ← map_zsmul (toAffineAddEquiv _).symm,
    Ne, map_eq_zero_iff _ (toAffineAddEquiv _).symm.injective]
  exact Affine.zsmul_point_ne_zero h0

lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)

lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ωe n, curve.ψ n]

abbrev smulRing (n : ℤ) : Fin 3 → Univ.Ring := AdjoinRoot.mk _ ∘ smulPoly n

abbrev smulField (n : ℤ) : Fin 3 → Univ.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ωe_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := Affine.zsmul_point_eq_smulX_smulY hn
  change (n • (Point.toAffineAddEquiv _).symm Affine.point).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, Jacobian.smul_fin3]
  ext i; fin_cases i <;>
    simp only [Units.val_mk0, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    field_simp [Affine.smulX, Affine.smulY, this] <;> rfl

lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  simp_rw [dblZ, smulPoly, negY, fin3_def_ext, curvePoly, baseChange, map, coe_algebraMap_eq_CC]
  rw [← ψc_spec _ n]; congr; convert curve.ωe_spec n using 1; ring

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  simpa only [zsmul_point_eq_smulField, Jacobian.nonsingularLift_iff]
    using (n • Jacobian.point).nonsingular

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero]
    have h0 : smulField (0 : ℤ) = ![1, 1, 0] := by
      ext i
      fin_cases i <;> simp [smulField, smulPoly, φ_zero, ωe_zero, ψ_zero]
    rw [h0, dblXYZ_of_Z_eq_zero equation_zero rfl]
    simp
  have h2 : ((2 : ℤ) • (n • Jacobian.point)).point =
      ⟦dblXYZ curveField (smulField n)⟧ := by
    rw [two_zsmul, Point.add_point, zsmul_point_eq_smulField, addMap_eq, add_self]
  refine (equiv_iff_eq_of_Z_eq ?_ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn)).mp
    (Quotient.exact ?_)
  · simp only [smulField, smulPoly, fin3_def_ext, Function.comp, ← dblZ_smulPoly]
    exact map_dblZ (W' := curvePoly) polyToField _
  rw [← h2, ← mul_zsmul]
  exact zsmul_point_eq_smulField

lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ Univ.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField

lemma addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  have hES : IsEllSequence' (WeierstrassCurve.ψ curve) := IsEllSequence'.normEDS
  simp_rw [addZ, smulPoly, φ]; convert (hES n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

lemma ωe_neg_eq_neg_negY : curve.ωe (-n) = -negY curvePoly (smulPoly n) := by
  simp_rw [Affine.ωe_neg' (n := n), negY, smulPoly, fin3_def_ext, curvePoly, baseChange, map,
    coe_algebraMap_eq_CC]
  ring

lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp only [smulPoly, φ_neg, ωe_neg_eq_neg_negY, ψ_neg, neg, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val, smul_fin3, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
    Matrix.vecCons_inj, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> ring

lemma smulRing_neg : smulRing (-n) = (-1 : Univ.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulField_neg : smulField (-n) = (-1 : Univ.Field) • neg curveField (smulField n) := by
  rw [smulField, smulPoly_neg]
  refine (Jacobian.comp_smul (R := Poly) (S := Univ.Field) polyToField _ _).trans ?_
  rw [map_neg, map_one]
  exact congrArg _
    (Jacobian.map_neg (R := Poly) (S := Univ.Field) (W' := curvePoly) polyToField _).symm

lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
lemma smulField_zero : smulField 0 = ![1, 1, 0] := by simp [smulField, smulPoly_zero, comp_fin3]

lemma addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul (M := Univ.Field) (smulField m), smulField_neg, neg_add_cancel,
      addXYZ_smul, one_mul, neg_one_sq (R := Univ.Field), addXYZ_neg nonsingular_smulField.1,
      one_smul, ← neg_add', ← two_mul, ψ_neg, map_neg, ← dblZ_smulPoly, smulField_zero]
    congr 2
    exact map_dblZ (W' := curvePoly) polyToField _
  have hne : ¬ smulField m ≈ smulField n := fun heq ↦ zsmul_point_ne h <| by
    rw [Point.ext_iff, zsmul_point_eq_smulField, zsmul_point_eq_smulField]
    exact Quotient.sound heq
  have key : (m • Jacobian.point + n • Jacobian.point).point =
      ⟦addXYZ curveField (smulField m) (smulField n)⟧ := by
    rw [Point.add_point, zsmul_point_eq_smulField, zsmul_point_eq_smulField, addMap_eq,
      add_of_not_equiv hne]
  erw [← equiv_iff_eq_of_Z_eq]
  · exact Quotient.exact (by
      rw [smul_eq _ (ψᵤ_ne_zero <| sub_ne_zero_of_ne h.symm).isUnit,
        ← zsmul_point_eq_smulField, add_comm, add_zsmul, key])
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
    simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly]
    exact map_addZ polyToField (smulPoly m) (smulPoly n)
  · rw [(smul_fin3_ext _ _).2.2]
    apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega

lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp_left <| by
    simp_rw [← map_addXYZ, Jacobian.comp_smul]; exact addXYZ_smulField

lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

end Jacobian

end Univ

variable (x y) in
/-- **The division-polynomial triple at `(x, y)`.** The triple `(φₙ(x, y), ωₙ(x, y), ψₙ(x, y))`
of values of the division polynomials at any pair `(x, y)` over the commutative ring `R`. When `R`
is a field and `(x, y)` is a nonsingular point of `W`, its class is the Jacobian point
`n • (x, y)` (`zsmul_eq_smulEval`); at other pairs it has no such meaning. -/
public abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ωe n, W.ψ n]

variable {W} (eqn : W.toAffine.Equation x y)

open Univ Jacobian

lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ωe, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

include eqn in
lemma dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]
  simp_rw [curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Univ

/-- **Multiplication by `n` through division polynomials.** For a nonsingular point `(x, y)`
of a Weierstrass curve `W` over a field, the Jacobian point `n • (x, y)` is the class of the
triple `(φₙ(x, y), ωₙ(x, y), ψₙ(x, y))`. -/
public theorem zsmul_eq_smulEval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some x y h)).point = ⟦smulEval W x y n⟧ := by
  have add_point_eq : ∀ (P Q : Jacobian.Point W) (P' Q' : Fin 3 → F),
      P.point = ⟦P'⟧ → Q.point = ⟦Q'⟧ → (P + Q).point = ⟦Jacobian.add W P' Q'⟧ := by
    intro P Q P' Q' hP hQ
    rw [Point.add_point, hP, hQ, addMap_eq]
  have two_zsmul_point : ∀ (P : Jacobian.Point W) (P' : Fin 3 → F), P.point = ⟦P'⟧ →
      (2 • P).point = ⟦dblXYZ W P'⟧ := by
    intro P P' hP
    rw [two_smul, add_point_eq P P P' P' hP hP, Jacobian.add_self]
  have add_point_of_ne : ∀ (P Q : Jacobian.Point W) (P' Q' : Fin 3 → F), P.point = ⟦P'⟧ →
      Q.point = ⟦Q'⟧ → P ≠ Q → (P + Q).point = ⟦addXYZ W P' Q'⟧ := by
    intro P Q P' Q' hP hQ ne
    rw [add_point_eq P Q P' Q' hP hQ, Jacobian.add_of_not_equiv fun h' ↦
      ne (Point.ext <| hP.trans <| (Quotient.sound h').trans hQ.symm)]
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [add_assoc, ← two_mul, ← left_distrib, Nat.cast_mul, mul_smul, natCast_zsmul,
        two_zsmul_point _ _ (ih _ <| by omega), dblXYZ_smulEval h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul,
        add_point_of_ne _ _ _ _ (ih _ <| by omega) (ih _ <| by omega), Nat.cast_add (n + 1),
        Nat.cast_one, addXYZ_smulEval₁ h.1, ← add_assoc, two_mul]
      simp_rw [Nat.cast_add]
      rw [ne_comm, ← sub_ne_zero, ← sub_smul, add_sub_cancel_left, Nat.cast_one, one_smul]
      apply Point.fromAffine_some_ne_zero
  | neg hn n =>
    simp_rw [_root_.neg_smul, Point.neg_point, hn, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.comp_smul, ← Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end WeierstrassCurve

end PortEllSequenceZSMul

section PortEllSequenceAffineBridge

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

section Ring

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **`ψₙ` squared on the curve.** For a Weierstrass curve `W` over a commutative ring and any pair
`(x, y)` that satisfies the equation of `W`, singular or not, `ψₙ(x, y) ^ 2 = ΨSqₙ(x)`. -/
public theorem evalEval_ψ_sq_of_commRing {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : Affine.CoordinateRing.mk W (W.ψ n ^ 2) = Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at h1
  exact h1

/-- **`φₙ` on the curve.** For a Weierstrass curve `W` over a commutative ring and any pair
`(x, y)` that satisfies the equation of `W`, singular or not, `φₙ(x, y) = Φₙ(x)`. -/
public theorem evalEval_φ_of_commRing {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

end Ring

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
/-- **`ψₙ` squared on the curve, over a field.** For a Weierstrass curve `W` over a field and a
pair `(x, y)` that satisfies the equation of `W`, `ψₙ(x, y) ^ 2 = ΨSqₙ(x)`. This is the case of
`evalEval_ψ_sq_of_commRing` for fields. -/
public theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x :=
  evalEval_ψ_sq_of_commRing W h n

omit [DecidableEq F] in
/-- **`φₙ` on the curve, over a field.** For a Weierstrass curve `W` over a field and a pair
`(x, y)` that satisfies the equation of `W`, `φₙ(x, y) = Φₙ(x)`. This is the case of
`evalEval_φ_of_commRing` for fields. -/
public theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x :=
  evalEval_φ_of_commRing W h n

/-- **`n`-torsion through `ψₙ`.** A nonsingular point `(x, y)` of a Weierstrass curve `W` over a
field satisfies `n • (x, y) = 0` exactly when `ψₙ(x, y) = 0`. -/
public theorem smul_eq_zero_iff_evalEval_ψ {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := by
  have key := zsmul_eq_smulEval (W := W) h n
  have hQns := (n • Jacobian.Point.fromAffine (Affine.Point.some x y h)).nonsingular
  rw [key] at hQns
  calc n • (Affine.Point.some x y h) = 0
      ↔ (Jacobian.Point.toAffineAddEquiv W).symm (n • Affine.Point.some x y h) =
        (Jacobian.Point.toAffineAddEquiv W).symm 0 := (AddEquiv.injective _).eq_iff.symm
    _ ↔ n • Jacobian.Point.fromAffine (Affine.Point.some x y h) = 0 := by
        rw [map_zsmul, map_zero, Jacobian.Point.toAffineAddEquiv_symm_apply]
    _ ↔ (⟦smulEval W x y n⟧ : Jacobian.PointClass F) = ⟦![1, 1, 0]⟧ := by
        rw [Jacobian.Point.ext_iff, key, Jacobian.Point.zero_point]
    _ ↔ (W.ψ n).evalEval x y = 0 := by
        constructor
        · intro heq
          have hz := (Jacobian.Z_eq_zero_of_equiv (Quotient.eq.mp heq)).mpr rfl
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz
        · intro hz
          refine Quotient.eq.mpr (Jacobian.equiv_zero_of_Z_eq_zero
            ((Jacobian.nonsingularLift_iff _).mp hQns) ?_)
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz

end WeierstrassCurve

end PortEllSequenceAffineBridge

section DivisionPolynomialCoprime

namespace WeierstrassCurve

open Polynomial

section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

private theorem ΨSq_eval_eq_zero_of_preΨ {m : ℕ} {x₀ : K}
    (h : ((W.baseChange K).preΨ (m : ℤ)).eval x₀ = 0) :
    ((W.baseChange K).ΨSq m).eval x₀ = 0 := by
  rw [preΨ_ofNat] at h
  rw [ΨSq_ofNat, eval_mul, eval_pow, h, zero_pow two_ne_zero, zero_mul]

private lemma eval_ne_of_isCoprime {f g : Polynomial K} (h : IsCoprime f g) {x₀ : K}
    (hf : f.eval x₀ = 0) (hg : g.eval x₀ = 0) : False := by
  obtain ⟨a, b, hab⟩ := h
  have h1 := congrArg (Polynomial.eval x₀) hab
  simp only [eval_add, eval_mul, hf, hg, mul_zero, add_zero, eval_one] at h1
  exact zero_ne_one h1

variable [IsAlgClosed K]

private theorem isCoprime_ΨSq_succ [DecidableEq K] [W.IsElliptic] (n : ℕ) :
    IsCoprime ((W.baseChange K).ΨSq n) ((W.baseChange K).ΨSq (n + 1)) := by
  classical
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hn0, hn1⟩ := hcon
  rw [coe_aeval_eq_eval] at hn0 hn1
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
    (C (1 : K) * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X +
      C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
        (W.baseChange K).a₆)))
    (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  have heq : (W.baseChange K).toAffine.Equation x₀ y₀ := by
    rw [Affine.equation_iff]
    simp only [IsRoot.def, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hy₀
    linear_combination hy₀
  have hns : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    (Affine.equation_iff_nonsingular).mp heq
  have hψ0 : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq (n : ℤ)
    rw [hn0] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hψ1 : ((W.baseChange K).ψ ((n : ℤ) + 1)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq ((n : ℤ) + 1)
    rw [hn1] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have h0 : (n : ℤ) • (Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns (n : ℤ)).mpr hψ0
  have h1 : ((n : ℤ) + 1) • (Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns ((n : ℤ) + 1)).mpr hψ1
  have hP : (Affine.Point.some x₀ y₀ hns : (W.baseChange K).toAffine.Point) = 0 := by
    have hsub := sub_smul ((n : ℤ) + 1) (n : ℤ) (Affine.Point.some x₀ y₀ hns)
    rw [h1, h0, sub_zero, add_sub_cancel_left, one_smul] at hsub
    exact hsub
  exact Affine.Point.some_ne_zero hns hP

end

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

/-- **`Φₙ` and `ΨSqₙ` are coprime.** For an elliptic curve `W` over `F`, an algebraically closed
field `K` over `F` and `n > 0`, the polynomials `Φₙ` and `ΨSqₙ` of `W` over `K` are coprime. -/
public theorem isCoprime_Φ_ΨSq [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : 0 < n) :
    IsCoprime ((W.baseChange K).Φ n) ((W.baseChange K).ΨSq n) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hΦ0, hΨ0⟩ := hcon
  rw [coe_aeval_eq_eval] at hΦ0 hΨ0
  have hΦdef : (W.baseChange K).Φ (n : ℤ) =
      X * (W.baseChange K).ΨSq (n : ℤ) -
        (W.baseChange K).preΨ ((n : ℤ) + 1) * (W.baseChange K).preΨ ((n : ℤ) - 1) *
          (if Even (n : ℤ) then 1 else (W.baseChange K).Ψ₂Sq) := rfl
  have h0 : ((W.baseChange K).preΨ ((n : ℤ) + 1)).eval x₀ *
      ((W.baseChange K).preΨ ((n : ℤ) - 1)).eval x₀ *
      (if Even (n : ℤ) then (1 : K) else ((W.baseChange K).Ψ₂Sq).eval x₀) = 0 := by
    have h1 := congrArg (Polynomial.eval x₀) hΦdef
    rw [hΦ0] at h1
    simp only [eval_sub, eval_mul, eval_X, apply_ite (Polynomial.eval x₀), eval_one, hΨ0,
      mul_zero, zero_sub] at h1
    linear_combination h1
  rcases mul_eq_zero.mp h0 with h12 | hG
  · rcases mul_eq_zero.mp h12 with hE | hF
    · have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 := ΨSq_eval_eq_zero_of_preΨ W (m := n + 1) (K := K)
          (by rwa [Nat.cast_add, Nat.cast_one])
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb
    · have hb : ((W.baseChange K).ΨSq ((n - 1 : ℕ) : ℤ)).eval x₀ = 0 :=
        ΨSq_eval_eq_zero_of_preΨ W (m := n - 1) (K := K)
          (by rwa [Nat.cast_sub hn, Nat.cast_one])
      have hA := isCoprime_ΨSq_succ W (K := K) (n - 1)
      have hc : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
      rw [hc] at hA
      exact eval_ne_of_isCoprime hA hb hΨ0
  · by_cases hev : Even (n : ℤ)
    · rw [ite_eq_left hev] at hG
      exact one_ne_zero hG
    · rw [ite_eq_right hev] at hG
      have hnodd : ¬Even n := fun h => hev (by exact_mod_cast h)
      have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 : ((W.baseChange K).ΨSq ((n + 1 : ℕ) : ℤ)).eval x₀ = 0 := by
          rw [ΨSq_ofNat, ite_eq_left (Nat.even_add_one.mpr hnodd), eval_mul, hG, mul_zero]
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb

end WeierstrassCurve

end DivisionPolynomialCoprime
