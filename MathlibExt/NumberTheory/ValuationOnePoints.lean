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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Polynomial lifts modulo a prime square

A simple root modulo `p` has at most one lift to a root modulo `p²`. For a bivariate
polynomial, a nonsingular point has exactly `p * (p - 1)` lifts of valuation one, and all lifts
of a singular point have the same value modulo `p²`. For two points whose gradients are
independent modulo `p`, exactly `(p - 1)^2` common lifts have valuation one at both points,
exactly `p - 1` have valuation above one at the first point and valuation one at the second,
and exactly one has valuation above one at both.
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

/-- Every lift is divisible by `p`, and divisible by `p²` iff its linear part vanishes. -/
private lemma lift_char {p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin 2) ℤ) (r s k l : ℕ)
    (a b c : ℤ)
    (ha : a = MvPolynomial.eval ![((r : ℤ)), ((s : ℤ))] (MvPolynomial.pderiv 0 f))
    (hb : b = MvPolynomial.eval ![((r : ℤ)), ((s : ℤ))] (MvPolynomial.pderiv 1 f))
    (hc : MvPolynomial.eval ![((r : ℤ)), ((s : ℤ))] f = (p : ℤ) * c) :
    (p : ℤ) ∣ MvPolynomial.eval ![((r : ℤ)) + k * p, ((s : ℤ)) + l * p] f ∧
      (((p : ℤ) ^ 2 ∣ MvPolynomial.eval ![((r : ℤ)) + k * p, ((s : ℤ)) + l * p] f) ↔
        (k : ZMod p) * a + (l : ZMod p) * b + (c : ZMod p) = 0) := by
  rw [ha, hb]
  obtain ⟨q, hq⟩ := exists_eval_lift_remainder f r s k l p
  have hpp : p.Prime := Fact.out
  have hp₀ : (p : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.Prime.pos hpp)
  have hmod : (p : ℤ) * ((k : ℤ) *
      MvPolynomial.eval ![((r : ℤ)), ((s : ℤ))] (MvPolynomial.pderiv 0 f) + (l : ℤ) *
      MvPolynomial.eval ![((r : ℤ)), ((s : ℤ))] (MvPolynomial.pderiv 1 f) + c) ≡
      MvPolynomial.eval ![((r : ℤ)) + k * p, ((s : ℤ)) + l * p] f [ZMOD (p : ℤ) ^ 2] := by
    rw [Int.modEq_iff_dvd, hq, hc]
    exact ⟨q, by ring⟩
  refine ⟨(hmod.of_dvd (dvd_pow_self _ (by decide))).dvd_iff.mp (dvd_mul_right _ _), ?_⟩
  rw [← hmod.dvd_iff, pow_two, mul_dvd_mul_iff_left hp₀, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp

/-- An affine map of the plane whose determinant is nonzero is bijective. -/
private lemma affine_bij {p : ℕ} [Fact p.Prime] (A₁ B₁ C₁ A₂ B₂ C₂ d : ZMod p)
    (hd : d = A₁ * B₂ - A₂ * B₁) (hd0 : d ≠ 0) :
    Function.Bijective fun z : ZMod p × ZMod p =>
      (z.1 * A₁ + z.2 * B₁ + C₁, z.1 * A₂ + z.2 * B₂ + C₂) := by
  refine ⟨?_, ?_⟩
  · intro z₁ z₂ h
    obtain ⟨x₁, y₁⟩ := z₁
    obtain ⟨x₂, y₂⟩ := z₂
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hx : d * x₁ = d * x₂ := by
      rw [hd]
      linear_combination B₂ * h1 - B₁ * h2
    have hy : d * y₁ = d * y₂ := by
      rw [hd]
      linear_combination A₁ * h2 - A₂ * h1
    have hx' : x₁ = x₂ := mul_left_cancel₀ hd0 hx
    have hy' : y₁ = y₂ := mul_left_cancel₀ hd0 hy
    exact Prod.ext hx' hy'
  · rintro ⟨u, v⟩
    refine ⟨(d⁻¹ * (B₂ * (u - C₁) - B₁ * (v - C₂)),
      d⁻¹ * (A₁ * (v - C₂) - A₂ * (u - C₁))), ?_⟩
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · have e : A₁ * (B₂ * (u - C₁) - B₁ * (v - C₂)) +
          B₁ * (A₁ * (v - C₂) - A₂ * (u - C₁)) = d * (u - C₁) := by
        rw [hd]
        ring
      have step : d⁻¹ * (A₁ * (B₂ * (u - C₁) - B₁ * (v - C₂)) +
          B₁ * (A₁ * (v - C₂) - A₂ * (u - C₁))) = u - C₁ := by
        rw [e]
        exact inv_mul_cancel_left₀ hd0 _
      linear_combination step
    · have e : A₂ * (B₂ * (u - C₁) - B₁ * (v - C₂)) +
          B₂ * (A₁ * (v - C₂) - A₂ * (u - C₁)) = d * (v - C₂) := by
        rw [hd]
        ring
      have step : d⁻¹ * (A₂ * (B₂ * (u - C₁) - B₁ * (v - C₂)) +
          B₂ * (A₁ * (v - C₂) - A₂ * (u - C₁))) = v - C₂ := by
        rw [e]
        exact inv_mul_cancel_left₀ hd0 _
      linear_combination step

/-- There are `p - 1` nonzero residues mod `p`. -/
private lemma card_nonzero {p : ℕ} [NeZero p] :
    (Finset.univ.filter fun y : ZMod p => y ≠ 0).card = p - 1 := by
  rw [Finset.filter_ne' _ 0, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
    ZMod.card]

/-- Lifts counted by an affine condition are as many as the values they hit. -/
private lemma card_filter_preimage {p : ℕ} [Fact p.Prime] [NeZero p]
    (E : ZMod p × ZMod p → ZMod p × ZMod p) (hE : Function.Bijective E)
    (S : Finset (ZMod p × ZMod p)) :
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
      E ((kl.1 : ZMod p), (kl.2 : ZMod p)) ∈ S).card = S.card := by
  have hcast : ∀ m n : ℕ, m < p → n < p → (m : ZMod p) = (n : ZMod p) → m = n := by
    intro m n hm hn h
    have hval := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at hval
  refine Finset.card_bij (fun kl _ => E ((kl.1 : ZMod p), (kl.2 : ZMod p))) ?_ ?_ ?_
  · intro kl hkl
    simp only [Finset.mem_filter] at hkl
    exact hkl.2
  · intro a₁ ha₁ a₂ ha₂ h
    obtain ⟨k₁, l₁⟩ := a₁
    obtain ⟨k₂, l₂⟩ := a₂
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha₁ ha₂
    dsimp only at h
    have heq := hE.injective h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨heq1, heq2⟩ := heq
    have hk : k₁ = k₂ := hcast k₁ k₂ ha₁.1.1 ha₂.1.1 heq1
    have hl : l₁ = l₂ := hcast l₁ l₂ ha₁.1.2 ha₂.1.2 heq2
    exact Prod.ext hk hl
  · intro b hb
    obtain ⟨z, hz⟩ := hE.surjective b
    obtain ⟨x, y⟩ := z
    refine ⟨(x.val, y.val), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr x.val_lt, Finset.mem_range.mpr y.val_lt⟩, ?_⟩
      simp only [ZMod.natCast_zmod_val]
      rw [hz]
      exact hb
    · simp only [ZMod.natCast_zmod_val]
      exact hz

set_option linter.unusedVariables false in
/-- **Common lifts of two points with independent gradients.** Let $p$ be a prime, let
$f \in \mathbb{Z}[x, y]$ have partial derivatives $f_x$ and $f_y$, and let $(r_1, s_1)$ and
$(r_2, s_2)$ be pairs of integers in $\{0, \dots, p - 1\}$ with $p \mid f(r_i, s_i)$ for
$i = 1, 2$ and
$$
p \nmid f_x(r_1, s_1) f_y(r_2, s_2) - f_y(r_1, s_1) f_x(r_2, s_2).
$$
Write $F_i(k, l) = f(r_i + kp, s_i + lp)$. Among the pairs $(k, l)$ with $0 \le k, l < p$,
exactly $(p - 1)^2$ have $p \mid F_i(k, l)$ and $p^2 \nmid F_i(k, l)$ for both $i$, exactly
$p - 1$ have $p^2 \mid F_1(k, l)$, $p \mid F_2(k, l)$ and $p^2 \nmid F_2(k, l)$, and exactly
one has $p^2 \mid F_1(k, l)$ and $p^2 \mid F_2(k, l)$.

Source: Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a
Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Proposition 3
(`integers-2026-A82-prop-3`). -/
public theorem card_common_lift_padicVal_of_gradients_independent {p : ℕ} (hp : p.Prime)
    (f : MvPolynomial (Fin 2) ℤ) {r₁ s₁ r₂ s₂ : ℕ} (hr₁ : r₁ < p) (hs₁ : s₁ < p) (hr₂ : r₂ < p)
    (hs₂ : s₂ < p) (h₁ : (p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ), s₁] f)
    (h₂ : (p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ), s₂] f)
    (hind : ¬ (p : ℤ) ∣
      MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 0 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 1 f) -
        MvPolynomial.eval ![(r₁ : ℤ), s₁] (MvPolynomial.pderiv 1 f) *
          MvPolynomial.eval ![(r₂ : ℤ), s₂] (MvPolynomial.pderiv 0 f)) :
    let F₁ : ℕ × ℕ → ℤ := fun kl => MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f
    let F₂ : ℕ × ℕ → ℤ := fun kl => MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f
    let one : ℤ → Prop := fun v => (p : ℤ) ∣ v ∧ ¬ (p : ℤ) ^ 2 ∣ v
    ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ => one (F₁ kl) ∧ one (F₂ kl)).card =
        (p - 1) ^ 2 ∧
      ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ F₁ kl ∧ one (F₂ kl)).card = p - 1 ∧
      ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ F₁ kl ∧ (p : ℤ) ^ 2 ∣ F₂ kl).card = 1
    := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  set a₁ : ℤ := MvPolynomial.eval ![((r₁ : ℤ)), ((s₁ : ℤ))] (MvPolynomial.pderiv 0 f) with ha₁
  set b₁ : ℤ := MvPolynomial.eval ![((r₁ : ℤ)), ((s₁ : ℤ))] (MvPolynomial.pderiv 1 f) with hb₁
  set a₂ : ℤ := MvPolynomial.eval ![((r₂ : ℤ)), ((s₂ : ℤ))] (MvPolynomial.pderiv 0 f) with ha₂
  set b₂ : ℤ := MvPolynomial.eval ![((r₂ : ℤ)), ((s₂ : ℤ))] (MvPolynomial.pderiv 1 f) with hb₂
  set E : ZMod p × ZMod p → ZMod p × ZMod p := fun z =>
    (z.1 * (a₁ : ZMod p) + z.2 * (b₁ : ZMod p) + (c₁ : ZMod p),
      z.1 * (a₂ : ZMod p) + z.2 * (b₂ : ZMod p) + (c₂ : ZMod p)) with hEdef
  have hind' : ¬ (p : ℤ) ∣ (a₁ * b₂ - b₁ * a₂) := hind
  have hd0 : ((a₁ * b₂ - b₁ * a₂ : ℤ) : ZMod p) ≠ 0 :=
    fun h => hind' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hdd : ((a₁ * b₂ - b₁ * a₂ : ℤ) : ZMod p) =
      (a₁ : ZMod p) * (b₂ : ZMod p) - (a₂ : ZMod p) * (b₁ : ZMod p) := by
    rw [Int.cast_sub, Int.cast_mul, Int.cast_mul]
    ring
  have hE : Function.Bijective E :=
    affine_bij (a₁ : ZMod p) (b₁ : ZMod p) (c₁ : ZMod p) (a₂ : ZMod p) (b₂ : ZMod p)
      (c₂ : ZMod p) ((a₁ * b₂ - b₁ * a₂ : ℤ) : ZMod p) hdd hd0
  refine ⟨?_, ?_, ?_⟩
  · change ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        ((p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f) ∧
        ((p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f ∧
          ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f)).card =
        (p - 1) ^ 2
    have hS : (Finset.range p ×ˢ Finset.range p).filter (fun kl : ℕ × ℕ =>
          ((p : ℤ) ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f ∧
            ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f) ∧
          ((p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f ∧
            ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f)) =
        (Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          E ((kl.1 : ZMod p), (kl.2 : ZMod p)) ∈
            (Finset.univ.filter (fun y : ZMod p => y ≠ 0) ×ˢ
              Finset.univ.filter (fun y : ZMod p => y ≠ 0)) := by
      apply Finset.filter_congr
      intro kl _
      have c1 := lift_char f r₁ s₁ kl.1 kl.2 a₁ b₁ c₁ ha₁ hb₁ hc₁
      have c2 := lift_char f r₂ s₂ kl.1 kl.2 a₂ b₂ c₂ ha₂ hb₂ hc₂
      simp only [c1.1, c2.1, true_and, c1.2, c2.2, hEdef, Finset.mem_product,
        Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    rw [hS]
    refine (card_filter_preimage E hE _).trans ?_
    rw [Finset.card_product, card_nonzero]
    exact (pow_two _).symm
  · change ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f ∧
          ((p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f ∧
            ¬ (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f)).card =
        p - 1
    have hS : (Finset.range p ×ˢ Finset.range p).filter (fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f ∧
            ((p : ℤ) ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f ∧
              ¬ (p : ℤ) ^ 2 ∣
                MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f)) =
        (Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          E ((kl.1 : ZMod p), (kl.2 : ZMod p)) ∈
            (({0} : Finset (ZMod p)) ×ˢ Finset.univ.filter (fun y : ZMod p => y ≠ 0)) := by
      apply Finset.filter_congr
      intro kl _
      have c1 := lift_char f r₁ s₁ kl.1 kl.2 a₁ b₁ c₁ ha₁ hb₁ hc₁
      have c2 := lift_char f r₂ s₂ kl.1 kl.2 a₂ b₂ c₂ ha₂ hb₂ hc₂
      simp only [c2.1, true_and, c1.2, c2.2, hEdef, Finset.mem_product,
        Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    rw [hS]
    refine (card_filter_preimage E hE _).trans ?_
    rw [Finset.card_product, Finset.card_singleton, card_nonzero, one_mul]
  · change ((Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
        (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f ∧
          (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f).card = 1
    have hS : (Finset.range p ×ˢ Finset.range p).filter (fun kl : ℕ × ℕ =>
          (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₁ : ℤ) + kl.1 * p, (s₁ : ℤ) + kl.2 * p] f ∧
            (p : ℤ) ^ 2 ∣ MvPolynomial.eval ![(r₂ : ℤ) + kl.1 * p, (s₂ : ℤ) + kl.2 * p] f) =
        (Finset.range p ×ˢ Finset.range p).filter fun kl : ℕ × ℕ =>
          E ((kl.1 : ZMod p), (kl.2 : ZMod p)) ∈
            ({((0 : ZMod p), 0)} : Finset (ZMod p × ZMod p)) := by
      apply Finset.filter_congr
      intro kl _
      have c1 := lift_char f r₁ s₁ kl.1 kl.2 a₁ b₁ c₁ ha₁ hb₁ hc₁
      have c2 := lift_char f r₂ s₂ kl.1 kl.2 a₂ b₂ c₂ ha₂ hb₂ hc₂
      simp only [c1.2, c2.2, hEdef, Finset.mem_singleton, Prod.mk.injEq]
    rw [hS]
    refine (card_filter_preimage E hE _).trans ?_
    exact Finset.card_singleton _

end MetaMathlibExt
