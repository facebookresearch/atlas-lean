/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Polynomial lifts modulo a prime square

A simple root modulo `p` has at most one lift to a root modulo `p²`. For a bivariate
polynomial, a nonsingular point has exactly `p * (p - 1)` lifts of valuation one, and all lifts
of a singular point have the same value modulo `p²`.
See the [authors' preprint](https://arxiv.org/abs/2411.05366).
-/

namespace MetaMathlibExt

/-- **At most one lift has valuation above one.** Let $p$ be a prime, $g \in \mathbb{Z}[x]$ and
$r$ an integer with $0 \le r < p$ such that $g(r)$ and $g'(r)$ are not both divisible by $p$.
Then at most one $k \in \{0, \dots, p - 1\}$ satisfies $p^2 \mid g(r + kp)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 1
(`integers-2026-A82-prop-1`). -/
public theorem card_lift_padicVal_gt_one_le_one {p : ℕ} (hp : p.Prime) (g : Polynomial ℤ)
    {r : ℕ} (hr : r < p)
    (hroot : ¬ ((p : ℤ) ∣ g.eval (r : ℤ) ∧ (p : ℤ) ∣ (Polynomial.derivative g).eval (r : ℤ))) :
    ((Finset.range p).filter fun k : ℕ => (p : ℤ) ^ 2 ∣ g.eval ((r : ℤ) + k * p)).card ≤ 1 := by
  have linear (k : ℕ) (hk : (p : ℤ) ^ 2 ∣ g.eval ((r : ℤ) + k * p)) :
      (p : ℤ) ^ 2 ∣ g.derivative.eval (r : ℤ) * k * p + g.eval (r : ℤ) := by
    obtain ⟨c, hc⟩ := g.exists_mul_sq_add_linear_part_eq_eval_add (r : ℤ) ((k : ℤ) * p)
    rw [← hc, add_assoc, mul_pow, ← mul_assoc c, Int.dvd_add_right (dvd_mul_left _ _)] at hk
    simpa only [mul_assoc] using hk
  apply Finset.card_le_one.mpr
  intro k hk l hl
  simp only [Finset.mem_filter, Finset.mem_range] at hk hl
  have h₁ := linear k hk.2
  have h₂ := linear l hl.2
  have hval : (p : ℤ) ∣ g.eval (r : ℤ) :=
    (Int.dvd_add_right (dvd_mul_left _ _)).mp ((dvd_pow_self _ (by decide : 2 ≠ 0)).trans h₁)
  have hdiff := dvd_sub h₂ h₁
  rw [add_sub_add_right_eq_sub, ← sub_mul, ← mul_sub, sq] at hdiff
  have hp₀ : (p : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.zero_lt_of_lt hr)
  have hprod := (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd (Int.dvd_of_mul_dvd_mul_right hp₀ hdiff)
  have hkl := Nat.modEq_iff_dvd.mpr (hprod.resolve_left fun hd => hroot ⟨hval, hd⟩)
  exact hkl.eq_of_lt_of_lt hk.1 hl.1

open MvPolynomial

/-- The linear terms of a lift account for its change in value up to a multiple of `p²`. -/
private lemma exists_eval_lift_remainder (f : MvPolynomial (Fin 2) ℤ) (r s k l p : ℤ) :
    ∃ q : ℤ, eval ![r + k * p, s + l * p] f = eval ![r, s] f +
      p * (k * eval ![r, s] (pderiv 0 f) + l * eval ![r, s] (pderiv 1 f)) + p ^ 2 * q := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, by simp only [map_add, ha, hb]; ring⟩
  | mul_X f i ih =>
    obtain ⟨q, hq⟩ := ih
    let d := k * eval ![r, s] (pderiv 0 f) + l * eval ![r, s] (pderiv 1 f)
    refine ⟨q * ![r + k * p, s + l * p] i + d * ![k, l] i, ?_⟩
    fin_cases i <;> simp [d, hq] <;> ring

/-- An affine function with nonzero slope has one zero among the residue representatives. -/
private lemma sum_affine_ne_zero {p : ℕ} [Fact p.Prime] (a b : ZMod p) (ha : a ≠ 0) :
    (∑ k ∈ Finset.range p, if (k : ZMod p) * a + b ≠ 0 then 1 else 0) = p - 1 := by
  let root := -b / a
  have eq_root (k : ℕ) (hk : k < p) : (k : ZMod p) * a + b = 0 ↔ k = root.val := by
    rw [add_eq_zero_iff_eq_neg, ← eq_div_iff ha]
    exact ⟨fun h => (ZMod.val_natCast_of_lt hk).symm.trans (congrArg ZMod.val h),
      fun h => h ▸ ZMod.natCast_zmod_val root⟩
  rw [← Finset.card_filter]
  calc
    _ = ((Finset.range p).filter fun k => k ≠ root.val).card := by
      apply congrArg Finset.card
      exact Finset.filter_congr fun k hk => (eq_root k (Finset.mem_range.mp hk)).not
    _ = p - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_range.mpr root.val_lt)]
      simp

set_option linter.unusedVariables false in
/-- **Lifts of a nonsingular point with valuation one.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $r, s$ be integers in
$\{0, \dots, p - 1\}$ with $p \mid f(r, s)$ such that $f_x(r, s)$ and $f_y(r, s)$ are not both
divisible by $p$. Then exactly $p(p - 1)$ of the pairs $(k, l)$ with $0 \le k, l < p$ satisfy
$p \mid f(r + kp, s + lp)$ and $p^2 \nmid f(r + kp, s + lp)$, that is,
$\nu_p(f(r + kp, s + lp)) = 1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 2
(`integers-2026-A82-prop-2`). -/
public theorem card_lift_padicVal_eq_one {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r s : ℕ} (hr : r < p) (hs : s < p)
    (hcurve : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f)
    (hgrad : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
      (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f))) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card =
      p * (p - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  let a := eval ![(r : ℤ), s] (pderiv 0 f)
  let b := eval ![(r : ℤ), s] (pderiv 1 f)
  obtain ⟨c, hc⟩ := hcurve
  -- Dividing the first-order expansion by p leaves an affine function modulo p.
  have lift (k l : ℕ) :
      (p : ℤ) * (k * a + l * b + c) ≡
        eval ![(r : ℤ) + k * p, (s : ℤ) + l * p] f [ZMOD (p : ℤ) ^ 2] := by
    obtain ⟨q, hq⟩ := exists_eval_lift_remainder f r s k l p
    rw [Int.modEq_iff_dvd, hq, hc]
    exact ⟨q, by dsimp [a, b]; ring⟩
  calc
    _ = ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (kl.1 : ZMod p) * a + kl.2 * b + c ≠ 0).card := by
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro ⟨k, l⟩ _
      have h := lift k l
      have hd := (h.of_dvd (dvd_pow_self _ (by decide))).dvd_iff.mp (dvd_mul_right _ _)
      rw [and_iff_right hd, ← h.dvd_iff, sq,
        mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hp.ne_zero),
        ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp
    _ = p * (p - 1) := by
      rw [Finset.card_filter]
      by_cases ha : (a : ZMod p) = 0
      · have hb : (b : ZMod p) ≠ 0 := fun h =>
          hgrad ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h⟩
        rw [Finset.sum_product]
        simp only [ha, mul_zero, zero_add, sum_affine_ne_zero _ _ hb, Finset.sum_const,
          Finset.card_range, smul_eq_mul]
      · rw [Finset.sum_product_right]
        simp only [add_assoc, sum_affine_ne_zero _ _ ha, Finset.sum_const,
          Finset.card_range, smul_eq_mul]

set_option linter.unusedVariables false in
/-- **Lifts of a singular point with valuation one.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $r, s$ be integers in
$\{0, \dots, p - 1\}$ such that $p$ divides $f(r, s)$, $f_x(r, s)$ and $f_y(r, s)$. Then the
number of pairs $(k, l)$ with $0 \le k, l < p$, $p \mid f(r + kp, s + lp)$ and
$p^2 \nmid f(r + kp, s + lp)$ is $0$ if $p^2 \mid f(r, s)$, and $p^2$ otherwise.

The cited statement prints the two cases swapped. By the paper's eq. (7) every lift
$f(r + kp, s + lp)$ is congruent to $f(r, s)$ modulo $p^2$. The printed version fails for
$f = x^2 + y^2 + 3$, $p = 3$, $(r, s) = (0, 0)$: $f(0, 0) = 3$ is not divisible by $9$, and all
$9$ lifts have valuation $1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Corollary 3 (`integers-2026-A82-cor-3`). -/
public theorem card_lift_padicVal_eq_one_of_singular {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r s : ℕ} (hr : r < p) (hs : s < p)
    (hcurve : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f)
    (hx : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f))
    (hy : (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card =
      if (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ), s] f then 0 else p ^ 2 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have lift (k l : ℕ) : eval ![(r : ℤ), s] f ≡
      eval ![(r : ℤ) + k * p, (s : ℤ) + l * p] f [ZMOD (p : ℤ) ^ 2] := by
    obtain ⟨q, hq⟩ := exists_eval_lift_remainder f r s k l p
    rw [Int.modEq_iff_dvd, hq, ha, hb]
    exact ⟨k * a + l * b + q, by ring⟩
  by_cases h : (p : ℤ) ^ 2 ∣ eval ![(r : ℤ), s] f
  · rw [ite_eq_left h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun ⟨k, l⟩ _ hkl => hkl.2 ((lift k l).dvd_iff.mp h)
  · rw [ite_eq_right h, Finset.filter_true_of_mem]
    · simp [sq]
    · intro ⟨k, l⟩ _
      have hl := lift k l
      exact ⟨(hl.of_dvd (dvd_pow_self _ (by decide))).dvd_iff.mp hcurve,
        fun hkl => h (hl.dvd_iff.mpr hkl)⟩

/-- Divisibility by `p` of a polynomial value is unchanged by a lift. -/
private lemma padicVal_dvd_eval_lift_iff (f : MvPolynomial (Fin 2) ℤ) (r s k l p : ℤ) :
    (p : ℤ) ∣ eval ![r, s] f ↔ (p : ℤ) ∣ eval ![r + k * p, s + l * p] f := by
  obtain ⟨q, hq⟩ := exists_eval_lift_remainder f r s k l p
  have hmod : eval ![r + k * p, s + l * p] f ≡ eval ![r, s] f [ZMOD p] := by
    rw [Int.modEq_iff_dvd, hq]
    exact ⟨-(k * eval ![r, s] (pderiv 0 f) + l * eval ![r, s] (pderiv 1 f) + p * q), by ring⟩
  exact hmod.dvd_iff.symm

/-- A lift of a residue below `p` stays below `p ^ 2`. -/
private lemma padicVal_add_mul_lt_pow_two {p r k : ℕ} (hr : r < p) (hk : k < p) :
    r + k * p < p ^ 2 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · exact absurd hr (by simp)
  · have hle : k * p ≤ (p - 1) * p :=
      Nat.mul_le_mul_right p (Nat.le_pred_of_lt hk)
    have hle2 : p ≤ p * p := by
      nth_rewrite 1 [← mul_one p]
      exact Nat.mul_le_mul_left p hp0
    have heq : (p - 1) * p + p = p * p := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel hle2]
    rw [sq]
    omega

/-- **Number of points of valuation one modulo $p^2$.** Let $p$ be a prime and let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$. Suppose that for all integers
$r, s \in \{0, \dots, p - 1\}$ with $p \mid f(r, s)$, the integers $f_x(r, s)$ and $f_y(r, s)$
are not both divisible by $p$. Let $m$ be the number of pairs $(r, s)$ with $0 \le r, s < p$ and
$p \mid f(r, s)$. Then the number of pairs $(x, y)$ with $0 \le x, y < p^2$, $p \mid f(x, y)$
and $p^2 \nmid f(x, y)$ is $m p (p - 1)$.

Without the hypothesis on $f_x$ and $f_y$ the count fails: for $f = x^2 - y^2$ and $p = 3$ one
has $m = 5$, but only $24$ pairs, not $30$, have valuation $1$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82,
Corollary 2 (`integers-2026-A82-cor-2`). -/
public theorem card_padicVal_eq_one_mod_sq_eq {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ)
    (hns : ∀ r < p, ∀ s < p, (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] f →
      ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f))) :
    ((Finset.range (p ^ 2) ×ˢ Finset.range (p ^ 2)).filter fun xy : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f).card =
      ((Finset.range p ×ˢ Finset.range p).filter fun rs : ℕ × ℕ =>
          (p : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f).card * (p * (p - 1)) := by
  classical
  have hp0 : 0 < p := hp.pos
  -- The residue map sends the left-hand set into the right-hand set.
  have hmaps : ((((Finset.range (p ^ 2) ×ˢ Finset.range (p ^ 2)).filter fun xy : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f) : Finset (ℕ × ℕ)) :
      Set (ℕ × ℕ)).MapsTo (fun xy => (xy.1 % p, xy.2 % p))
      ((Finset.range p ×ˢ Finset.range p).filter fun rs : ℕ × ℕ =>
          (p : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f) := by
    rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hxy ⊢
    obtain ⟨⟨hx, hy⟩, hdiv, -⟩ := hxy
    have hxeq : (x : ℤ) = ((x % p : ℕ) : ℤ) + ((x / p : ℕ) : ℤ) * (p : ℤ) := by
      rw [← Nat.cast_mul, ← Nat.cast_add]
      congr 1
      rw [mul_comm]
      exact (Nat.mod_add_div x p).symm
    have hyeq : (y : ℤ) = ((y % p : ℕ) : ℤ) + ((y / p : ℕ) : ℤ) * (p : ℤ) := by
      rw [← Nat.cast_mul, ← Nat.cast_add]
      congr 1
      rw [mul_comm]
      exact (Nat.mod_add_div y p).symm
    refine ⟨⟨Nat.mod_lt _ hp0, Nat.mod_lt _ hp0⟩, ?_⟩
    rw [hxeq, hyeq] at hdiv
    exact (padicVal_dvd_eval_lift_iff f _ _ _ _ _).mpr hdiv
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber : ∀ rs ∈ (Finset.range p ×ˢ Finset.range p).filter (fun rs : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(rs.1 : ℤ), rs.2] f),
      ((((Finset.range (p ^ 2) ×ˢ Finset.range (p ^ 2)).filter fun xy : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f).filter
        fun xy => (xy.1 % p, xy.2 % p) = rs).card = p * (p - 1)) := by
    rintro ⟨r, s⟩ hrs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hrs
    obtain ⟨⟨hr, hs⟩, hdiv⟩ := hrs
    have hgrad : ¬ ((p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 0 f) ∧
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ), s] (MvPolynomial.pderiv 1 f)) :=
      hns r hr s hs hdiv
    have hlift := card_lift_padicVal_eq_one hp f hr hs hdiv hgrad
    -- Bijection between the fibre and the lift set.
    have hbij : ((((Finset.range (p ^ 2) ×ˢ Finset.range (p ^ 2)).filter fun xy : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(xy.1 : ℤ), xy.2] f).filter
        fun xy => (xy.1 % p, xy.2 % p) = (r, s)).card =
        ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r : ℤ) + kl.1 * p, (s : ℤ) + kl.2 * p] f).card) := by
      apply Finset.card_bij' (fun xy _ => (xy.1 / p, xy.2 / p))
        (fun kl _ => (r + kl.1 * p, s + kl.2 * p))
      · intro ⟨x, y⟩ hxy
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hxy ⊢
        obtain ⟨⟨hx, hy⟩, hdiv, hnot⟩ := hxy.1
        have hmod : (x % p, y % p) = (r, s) := hxy.2
        have hxr : x % p = r := congrArg Prod.fst hmod
        have hys : y % p = s := congrArg Prod.snd hmod
        have hxeq : (x : ℤ) = (r : ℤ) + ((x / p : ℕ) : ℤ) * (p : ℤ) := by
          have h := Nat.div_add_mod x p
          rw [hxr] at h
          have h2 : (x : ℤ) = ((p * (x / p) + r : ℕ) : ℤ) := by exact_mod_cast h.symm
          rw [h2]; push_cast; ring
        have hyeq : (y : ℤ) = (s : ℤ) + ((y / p : ℕ) : ℤ) * (p : ℤ) := by
          have h := Nat.div_add_mod y p
          rw [hys] at h
          have h2 : (y : ℤ) = ((p * (y / p) + s : ℕ) : ℤ) := by exact_mod_cast h.symm
          rw [h2]; push_cast; ring
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · have hxp : x < p * p := by rwa [sq] at hx
          exact Nat.div_lt_of_lt_mul hxp
        · have hyp : y < p * p := by rwa [sq] at hy
          exact Nat.div_lt_of_lt_mul hyp
        · rw [hxeq, hyeq] at hdiv
          exact hdiv
        · rw [hxeq, hyeq] at hnot
          exact hnot
      · intro ⟨k, l⟩ hkl
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hkl ⊢
        obtain ⟨⟨hk, hl⟩, hdiv, hnot⟩ := hkl
        have e1 : (r + k * p) % p = r := by
          rw [mul_comm k p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
        have e2 : (s + l * p) % p = s := by
          rw [mul_comm l p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
        refine ⟨⟨⟨padicVal_add_mul_lt_pow_two hr hk,
          padicVal_add_mul_lt_pow_two hs hl⟩, ?_, ?_⟩, ?_⟩
        · have h1 : ((r + k * p : ℕ) : ℤ) = (r : ℤ) + (k : ℤ) * (p : ℤ) := by push_cast; ring
          have h2 : ((s + l * p : ℕ) : ℤ) = (s : ℤ) + (l : ℤ) * (p : ℤ) := by push_cast; ring
          rw [h1, h2]
          exact hdiv
        · have h1 : ((r + k * p : ℕ) : ℤ) = (r : ℤ) + (k : ℤ) * (p : ℤ) := by push_cast; ring
          have h2 : ((s + l * p : ℕ) : ℤ) = (s : ℤ) + (l : ℤ) * (p : ℤ) := by push_cast; ring
          rw [h1, h2]
          exact hnot
        · exact Prod.ext e1 e2
      · intro ⟨x, y⟩ hxy
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hxy
        obtain ⟨⟨hx, hy⟩, -, -⟩ := hxy.1
        have hmod : (x % p, y % p) = (r, s) := hxy.2
        have hxr : x % p = r := congrArg Prod.fst hmod
        have hys : y % p = s := congrArg Prod.snd hmod
        have hx1 : r + x / p * p = x := by
          have h := Nat.div_add_mod x p
          rw [hxr] at h
          rw [mul_comm (x / p) p, add_comm r (p * (x / p))]
          exact h
        have hy1 : s + y / p * p = y := by
          have h := Nat.div_add_mod y p
          rw [hys] at h
          rw [mul_comm (y / p) p, add_comm s (p * (y / p))]
          exact h
        exact Prod.ext hx1 hy1
      · intro ⟨k, l⟩ hkl
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hkl
        obtain ⟨⟨hk, hl⟩, -, -⟩ := hkl
        have e1 : (r + k * p) / p = k := by
          rw [mul_comm k p, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hr, zero_add]
        have e2 : (s + l * p) / p = l := by
          rw [mul_comm l p, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hs, zero_add]
        exact Prod.ext e1 e2
    rw [hbij, hlift]
  rw [Finset.sum_congr rfl hfiber]
  simp [Finset.sum_const, Nat.mul_comm]

end MetaMathlibExt
