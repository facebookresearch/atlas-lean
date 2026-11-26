/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer values of the generalized Fibonacci generating function

The rational inputs giving integer values are the ratios of consecutive generalized Fibonacci
numbers and their images under the involution `q ↦ -1 / (b * q)` for nonzero `q`.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔽[" a ", " b "]" =>
  generalizedFibonacciPolynomial 0 1 (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

namespace fibonacciGenFun_eval_isInt_iff

private noncomputable abbrev F (a b n : ℕ) := (𝔽[a, b] n).eval 1

private lemma fib_step (a b n : ℕ) :
    F a b (n + 2) = a * F a b (n + 1) + b * F a b n := by simp [F]

private lemma fib_pos {a b : ℕ} (ha : 0 < a) (n : ℕ) : 0 < F a b (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [F]
  | one => simpa [F] using ha
  | more n ih₀ ih₁ =>
    rw [show n + 2 + 1 = (n + 1) + 2 by rfl, fib_step]
    positivity

private def form (a b : ℕ) (p r : ℤ) := r ^ 2 - a * p * r - b * p ^ 2

-- Two Fibonacci steps, with their common factor b removed, preserve the form.
private lemma form_advance {a b : ℕ} {c : ℤ} (hc : (a : ℤ) = b * c) (p r : ℤ) :
    form a b (p + c * r) (r + a * (p + c * r)) = form a b p r := by
  unfold form
  rw [hc]
  ring

private def Matches (a b : ℕ) (p r : ℤ) (n : ℕ) :=
  p * F a b (n + 1) = r * F a b n

private lemma matches_advance {a b n : ℕ} {c p r : ℤ} (hc : (a : ℤ) = b * c)
    (h : Matches a b p r n) :
    Matches a b (p + c * r) (r + a * (p + c * r)) (n + 2) := by
  unfold Matches at h ⊢
  rw [show n + 2 + 1 = (n + 1) + 2 by rfl, fib_step a b (n + 1), fib_step a b n, hc]
  linear_combination (b : ℤ) * h

-- For a reduced positive fraction, the form cannot vanish. Otherwise r divides b,
-- but r * (r - a*p) = b*p² forces r > a*p ≥ b.
private lemma form_ne_zero {a b : ℕ} {p r : ℤ} (hb : 0 < b) (hba : b ≤ a)
    (hp : 0 < p) (hr : 0 < r) (hcop : IsCoprime p r) : form a b p r ≠ 0 := by
  intro h
  have he : r * (r - a * p) = b * p ^ 2 := by unfold form at h; linarith only [h]
  have hd : r ∣ (b : ℤ) := (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right
    (he ▸ dvd_mul_right r (r - a * p))
  have hpos : 0 < r - a * p := pos_of_mul_pos_right (he ▸ (by positivity)) hr.le
  have hle : (a : ℤ) ≤ a * p := le_mul_of_one_le_right (by positivity) (by omega)
  have := Int.le_of_dvd (by exact_mod_cast hb) hd
  omega

private lemma form_divisors {a b : ℕ} {p r : ℤ} (hcop : IsCoprime p r)
    (hd : form a b p r ∣ p * r) : form a b p r ∣ r ∧ form a b p r ∣ (b : ℤ) := by
  have hc : IsCoprime (form a b p r) p := by
    rw [show form a b p r = r ^ 2 - p * (a * r + b * p) by unfold form; ring,
      IsCoprime.sub_mul_left_left_iff]
    exact hcop.symm.pow_left
  have hr := hc.dvd_of_dvd_mul_left hd
  refine ⟨hr, (hc.pow_right (n := 2)).dvd_of_dvd_mul_right ?_⟩
  rw [show (b : ℤ) * p ^ 2 = r * (r - a * p) - form a b p r by unfold form; ring]
  exact dvd_sub (hr.mul_right _) dvd_rfl

-- Reverse two steps by setting s = r - a*p and t = p - c*s. The form divides
-- both r and s, forcing s and t to be nonnegative. For p > 0, s is smaller than r.
private lemma descent {a b : ℕ} {c : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hc : (a : ℤ) = b * c) (p r : ℤ) (hp : 0 ≤ p) (hr : 0 < r)
    (hd : form a b p r ∣ r) (hda : form a b p r ∣ (a : ℤ)) :
    ∃ n, Matches a b p r n := by
  by_cases hp₀ : p = 0
  · exact ⟨0, by simp [Matches, F, hp₀]⟩
  have hp' : 0 < p := by omega
  let s := r - a * p
  have hs : 0 ≤ s := by
    by_contra! h
    have hle := Int.le_of_dvd hr (neg_dvd.mpr hd)
    have := mul_le_mul_of_nonneg_left (show s ≤ -1 by omega) hr.le
    dsimp [form] at hle
    dsimp [s] at this
    nlinarith only [hle, this, mul_pos (Int.natCast_pos.mpr hb) (sq_pos_of_pos hp')]
  by_cases hs₀ : s = 0
  · exact ⟨1, by simpa [Matches, F, s, mul_comm] using (sub_eq_zero.mp hs₀).symm⟩
  have hs' : 0 < s := by omega
  let t := p - c * s
  have hds : form a b p r ∣ s := dvd_sub hd (hda.mul_right p)
  have ht : 0 ≤ t := by
    by_contra! h
    have he : form a b p r = s ^ 2 - b * p * t := by
      dsimp [form, t, s]
      rw [hc]
      ring
    have hle := Int.le_of_dvd hs' hds
    rw [he] at hle
    nlinarith only [hle, mul_nonpos_of_nonneg_of_nonpos hs'.le (show 1 - s ≤ 0 by omega),
      mul_neg_of_pos_of_neg (mul_pos (Int.natCast_pos.mpr hb) hp') h]
  have htp : t + c * s = p := sub_add_cancel ..
  have hsr : s + a * p = r := sub_add_cancel ..
  have he := form_advance hc t s
  rw [htp, hsr] at he
  obtain ⟨n, hn⟩ := descent ha hb hc t s ht hs' (he ▸ hds) (he ▸ hda)
  exact ⟨n + 2, by simpa only [htp, hsr] using matches_advance hc hn⟩
termination_by r.toNat
decreasing_by
  have := mul_pos (Int.natCast_pos.mpr ha) hp'
  omega

-- Conversely, construct integer representatives of every ratio with the same divisibility.
private lemma representatives {a b : ℕ} {c : ℤ} (ha : 0 < a) (hc₀ : 0 ≤ c)
    (hc : (a : ℤ) = b * c) (n : ℕ) :
    ∃ p r : ℤ, 0 ≤ p ∧ 0 < r ∧ form a b p r ∣ r ∧ form a b p r ∣ (a : ℤ) ∧
      Matches a b p r n := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨0, 1, by simp [form, Matches, F]⟩
  | one =>
    refine ⟨1, a, by decide, by exact_mod_cast ha, ?_, ?_, by simp [Matches, F]⟩ <;>
      simpa [form, sq] using (show (b : ℤ) ∣ a from ⟨c, hc⟩)
  | more n ih _ =>
    obtain ⟨p, r, hp, hr, hd, hda, hm⟩ := ih
    refine ⟨p + c * r, r + a * (p + c * r), by positivity, by positivity, ?_, ?_,
      matches_advance hc hm⟩
    · rw [form_advance hc]
      exact dvd_add hd (hda.mul_right _)
    · rwa [form_advance hc]

private def value (a b : ℕ) (q : ℚ) := q / (1 - a * q - b * q ^ 2)

private lemma value_div (a b : ℕ) (x y : ℚ) (hy : y ≠ 0) :
    value a b (x / y) = x * y / (y ^ 2 - a * x * y - b * x ^ 2) := by
  have h : 1 - a * (x / y) - b * (x / y) ^ 2 = (y ^ 2 - a * x * y - b * x ^ 2) / y ^ 2 := by
    field_simp
  rw [value, h, div_div_eq_mul_div]
  congr 1
  field_simp

private lemma value_fraction (a b : ℕ) (p r : ℤ) (hr : 0 < r) :
    value a b ((p : ℚ) / r) = ((p * r : ℤ) : ℚ) / (form a b p r : ℚ) := by
  simpa [form] using value_div a b p r (by exact_mod_cast hr.ne')

private noncomputable def ratio (a b i : ℕ) : ℚ := F a b i / (F a b (i + 1) : ℚ)

private lemma matches_iff {a b i : ℕ} (ha : 0 < a) {p r : ℤ} (hr : 0 < r) :
    Matches a b p r i ↔ (p : ℚ) / r = ratio a b i := by
  rw [ratio, div_eq_div_iff (by exact_mod_cast hr.ne') (by exact_mod_cast (fib_pos ha i).ne')]
  unfold Matches
  rw [mul_comm r]
  norm_cast

private lemma ratio_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ∣ a)
    {q : ℚ} (hq : 0 < q) (hint : ∃ n : ℤ, value a b q = n) : ∃ i, q = ratio a b i := by
  let p := q.num
  let r : ℤ := q.den
  have hr : 0 < r := Int.natCast_pos.mpr q.den_pos
  have hqr : (p : ℚ) / r = q := by simpa [p, r] using q.num_div_den
  have hp : 0 < p := by
    have := (div_pos_iff_of_pos_right (show 0 < (r : ℚ) by exact_mod_cast hr)).mp (hqr ▸ hq)
    exact_mod_cast this
  have hcop : IsCoprime p r := q.isCoprime_num_den
  have hne := form_ne_zero hb (Nat.le_of_dvd ha hba) hp hr hcop
  obtain ⟨n, hn⟩ := hint
  rw [← hqr, value_fraction a b p r hr, div_eq_iff (by exact_mod_cast hne)] at hn
  have hd : form a b p r ∣ p * r := ⟨n, by simpa [mul_comm] using (mod_cast hn :
    p * r = n * form a b p r)⟩
  obtain ⟨hdr, hdb⟩ := form_divisors hcop hd
  obtain ⟨c, hc⟩ := hba
  have hc' : (a : ℤ) = b * (c : ℤ) := by exact_mod_cast hc
  obtain ⟨i, hi⟩ := descent ha hb hc' p r hp.le hr hdr (hdb.trans ⟨c, hc'⟩)
  exact ⟨i, hqr ▸ (matches_iff ha hr).mp hi⟩

private lemma integral_ratio {a b : ℕ} (ha : 0 < a) (hba : b ∣ a) (i : ℕ) :
    ∃ n : ℤ, value a b (ratio a b i) = n := by
  obtain ⟨c, hc⟩ := hba
  obtain ⟨p, r, _, hr, hd, _, hm⟩ :=
    representatives ha (Int.natCast_nonneg c) (by exact_mod_cast hc) i
  have hne : form a b p r ≠ 0 := ne_zero_of_dvd_ne_zero hr.ne' hd
  obtain ⟨k, hk⟩ := hd
  refine ⟨p * k, ?_⟩
  rw [← (matches_iff ha hr).mp hm, value_fraction a b p r hr, div_eq_iff (by exact_mod_cast hne)]
  exact_mod_cast (show p * r = p * k * form a b p r by linear_combination p * hk)

private def reflect (b : ℕ) (q : ℚ) := -1 / (b * q)

private lemma value_reflect {a b : ℕ} (hb : 0 < b) {q : ℚ} (hq : q ≠ 0) :
    value a b (reflect b q) = value a b q := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [reflect, value_div _ _ _ _ (mul_ne_zero hb' hq), value]
  rw [show ((b : ℚ) * q) ^ 2 - a * -1 * (b * q) - b * (-1) ^ 2 =
    -(b : ℚ) * (1 - a * q - b * q ^ 2) by ring]
  simpa using mul_div_mul_left q (1 - a * q - b * q ^ 2) (neg_ne_zero.mpr hb')

private lemma reflect_ratio {a b : ℕ} (i : ℕ) :
    reflect b (ratio a b i) = -(F a b (i + 1) : ℚ) / (b * (F a b i : ℚ)) := by
  simp [reflect, ratio, mul_div_assoc', div_div_eq_mul_div]

end fibonacciGenFun_eval_isInt_iff

open fibonacciGenFun_eval_isInt_iff

/-- **Integer values of the generalized Fibonacci generating function at rationals.** Let $a$ and
$b$ be positive integers with $b \mid a$, and let $F_i(x) \in \mathbb{Z}[x]$ be the polynomials
with $F_0 = 0$, $F_1 = 1$ and $F_{i+2} = ax\,F_{i+1} + b\,F_i$ for all $i \ge 0$. For a rational
number $q$, the number $q / (1 - aq - bq^2)$ is an integer if and only if
$q = F_i(1) / F_{i+1}(1)$ for some $i \in \mathbb{N}$ or $q = -F_{i+1}(1) / (b F_i(1))$ for some
$i \ge 1$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024, Theorem 1.4
(`fq-2024-tsuno05142024-thm-1.4`). -/
public theorem fibonacciGenFun_eval_isInt_iff {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ∣ a) (q : ℚ) :
    (∃ n : ℤ, q / (1 - a * q - b * q ^ 2) = n) ↔
      (∃ i : ℕ, q = (((𝔽[a, b] i).eval 1 : ℤ) : ℚ) / (((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ)) ∨
        ∃ i : ℕ, 0 < i ∧
          q = -(((𝔽[a, b] (i + 1)).eval 1 : ℤ) : ℚ) / (b * (((𝔽[a, b] i).eval 1 : ℤ) : ℚ)) := by
  change (∃ n : ℤ, value a b q = n) ↔ (∃ i, q = ratio a b i) ∨
    ∃ i : ℕ, 0 < i ∧ q = -(F a b (i + 1) : ℚ) / (b * (F a b i : ℚ))
  constructor
  · intro hint
    rcases lt_trichotomy q 0 with hq | rfl | hq
    · have hb' : 0 < (b : ℚ) := by exact_mod_cast hb
      have hpos : 0 < reflect b q :=
        div_pos_of_neg_of_neg (by norm_num) (mul_neg_of_pos_of_neg hb' hq)
      obtain ⟨i, hi⟩ := ratio_of_pos ha hb hba hpos (by rwa [value_reflect hb hq.ne])
      have hi₀ : i ≠ 0 := by
        rintro rfl
        simp [hi, ratio, F] at hpos
      refine Or.inr ⟨i, Nat.pos_of_ne_zero hi₀, ?_⟩
      rw [← reflect_ratio, ← hi]
      simp [reflect, mul_div_assoc', div_div_eq_mul_div, hb'.ne']
    · exact Or.inl ⟨0, by simp [ratio, F]⟩
    · exact Or.inl (ratio_of_pos ha hb hba hq hint)
  · rintro (⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact integral_ratio ha hba i
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
      have hne : ratio a b (i + 1) ≠ 0 :=
        div_ne_zero (by exact_mod_cast (fib_pos ha i).ne')
          (by exact_mod_cast (fib_pos ha (i + 1)).ne')
      rw [← reflect_ratio, value_reflect hb hne]
      exact integral_ratio ha hba _

end MetaMathlibExt
