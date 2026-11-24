/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Divisors in short intervals

Letendre's saving exponent is the largest cutoff for which a quadratic in the interval
parameter stays nonnegative. Reflecting the interval interchanges its two endpoints, so
it suffices to locate the sharp cutoff for `θ ≤ 1 / 2`. Shrinking the cutoff gives a
uniform lower bound for the quadratic in `exists_alpha_with_margin`.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped Classical in
/-- **Number of divisors in a short interval.** For a natural number $n$ and real numbers $X$
and $Y$, Letendre's $D_n(X, Y)$ is the number of positive divisors $d$ of $n$ with
$X \le d \le X + Y$. Here $0$ is taken to have no divisors, so $D_0(X, Y) = 0$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Section 1 (definition of `D_n(X, Y)`). -/
public noncomputable def shortIntervalDivisorCount (n : ℕ) (X Y : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => X ≤ (d : ℝ) ∧ (d : ℝ) ≤ X + Y).card

/-- **Trivial bound for the short-interval divisor count.** For every natural number $n$ and
all real numbers $X$ and $Y$, the number $D_n(X, Y)$ of positive divisors of $n$ in
$[X, X + Y]$ is at most the number $\tau(n)$ of positive divisors of $n$. Here $0$ is taken to
have no divisors, so $D_0(X, Y) = \tau(0) = 0$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Section 1 (definition of `D_n(X, Y)`). -/
public theorem shortIntervalDivisorCount_le_card_divisors (n : ℕ) (X Y : ℝ) :
    shortIntervalDivisorCount n X Y ≤ n.divisors.card :=
  Finset.card_filter_le _ _

-- Preserve the hypotheses of Proposition 4; the construction only needs ε ≤ θ.
set_option linter.unusedVariables false in
/-- **Arbitrarily large integers with a divisor in a short window.** Let $\theta$ and $\varepsilon$
be real numbers with $0 < \theta < 1$ and $0 < \varepsilon < \theta$. Then for every natural
number $N$ there is a natural number $n \ge N$ with at least one divisor $d$ satisfying
$n^\theta \le d \le n^\theta + n^{\theta - \varepsilon}$.

This is the nontrivial form of the statement that a constant bounding the number of such divisors
for all $n \ge 1$ is at least $1$; that weaker statement already follows from $n = 1$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 4 (`integers-2026-A115-prop-4`). -/
public theorem exists_large_shortIntervalDivisorCount_pos {θ ε : ℝ} (hθ₀ : 0 < θ)
    (hθ₁ : θ < 1) (hε₀ : 0 < ε) (hε : ε < θ) :
    ∀ N : ℕ, ∃ n ≥ N, 1 ≤ shortIntervalDivisorCount n ((n : ℝ) ^ θ) ((n : ℝ) ^ (θ - ε)) := by
  intro N
  let m := max 1 N
  have hm : 1 ≤ m := le_max_left ..
  have hm₁ : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm₀ : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsub : 0 < 1 - θ := sub_pos.mpr hθ₁
  -- Round up the real solution of x = (x * m)^θ.
  let x := (m : ℝ) ^ (θ / (1 - θ))
  let d := ⌈x⌉₊
  let n := d * m
  have hx : 1 ≤ x := Real.one_le_rpow hm₁ (div_nonneg hθ₀.le hsub.le)
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hxd : x ≤ (d : ℝ) := Nat.le_ceil x
  have hd₁ : 1 ≤ (d : ℝ) := hx.trans hxd
  have hd : 1 ≤ d := by exact_mod_cast hd₁
  have hn : m ≤ n := by simpa only [one_mul] using Nat.mul_le_mul_right m hd
  have hn₁ : 1 ≤ n := hm.trans hn
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn₁).ne'
  have hxpow : x ^ (1 - θ) = (m : ℝ) ^ θ := by
    dsimp only [x]
    rw [← Real.rpow_mul hm₀, div_mul_cancel₀ _ hsub.ne']
  have hsum : θ + (1 - θ) = 1 := by ring
  have hpow : (n : ℝ) ^ θ = (d : ℝ) ^ θ * (m : ℝ) ^ θ := by
    dsimp only [n]
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) hm₀]
  have hlo : x ≤ (n : ℝ) ^ θ := by
    calc
      x = x ^ θ * (m : ℝ) ^ θ := by
        rw [← hxpow, ← Real.rpow_add hx₀, hsum, Real.rpow_one]
      _ ≤ (d : ℝ) ^ θ * (m : ℝ) ^ θ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx₀.le hxd hθ₀.le)
          (Real.rpow_nonneg hm₀ _)
      _ = _ := hpow.symm
  have hhi : (n : ℝ) ^ θ ≤ (d : ℝ) := by
    rw [hpow]
    calc
      (d : ℝ) ^ θ * (m : ℝ) ^ θ ≤ (d : ℝ) ^ θ * (d : ℝ) ^ (1 - θ) := by
        rw [← hxpow]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx₀.le hxd hsub.le)
          (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      _ = (d : ℝ) := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hd₁), hsum, Real.rpow_one]
  have hw : 1 ≤ (n : ℝ) ^ (θ - ε) :=
    Real.one_le_rpow (by exact_mod_cast hn₁) (sub_nonneg.mpr hε.le)
  refine ⟨n, (le_max_right 1 N).trans hn, ?_⟩
  unfold shortIntervalDivisorCount
  exact Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right d m, hn₀⟩, hhi,
      (Nat.ceil_lt_add_one hx₀.le).le.trans (add_le_add hlo hw)⟩⟩

/-- **Letendre's saving exponent.** For real numbers $\theta$ and $\eta$, Letendre's saving
exponent $\xi(\theta, \eta)$ is defined as follows. If $\eta \le \theta^2$, then
$\xi(\theta, \eta) = 1$. Otherwise, if $\theta \le 1/2$, then $\xi(\theta, \eta) = \theta^2/\eta$
when $2\eta \le \theta$ and $\xi(\theta, \eta) = 4(\theta - \eta)$ when $2\eta > \theta$; and if
$\theta > 1/2$, then $\xi(\theta, \eta) = (1 - \theta)^2/((1 - \theta)^2 + \eta - \theta^2)$ when
$2\eta \le 3\theta - 1$ and $\xi(\theta, \eta) = 4(\theta - \eta)$ when $2\eta > 3\theta - 1$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public noncomputable def letendreXi (θ η : ℝ) : ℝ :=
  if η ≤ θ ^ 2 then 1
  else if θ ≤ 1 / 2 then (if 2 * η ≤ θ then θ ^ 2 / η else 4 * (θ - η))
  else if 2 * η ≤ 3 * θ - 1 then (1 - θ) ^ 2 / ((1 - θ) ^ 2 + η - θ ^ 2)
  else 4 * (θ - η)

/-- **Letendre's exponent equals $1$ when $\eta \le \theta^2$.** For all real numbers $\theta$ and
$\eta$ with $\eta \le \theta^2$, Letendre's saving exponent satisfies $\xi(\theta, \eta) = 1$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public theorem letendreXi_of_le_sq {θ η : ℝ} (h : η ≤ θ ^ 2) : letendreXi θ η = 1 := by
  simp [letendreXi, h]

/-- **Letendre's exponent for $\theta^2 < \eta$, $\theta \le 1/2$ and $\theta < 2\eta$.** For all
real numbers $\theta$ and $\eta$ with $\theta^2 < \eta$, $\theta \le 1/2$ and $\theta < 2\eta$,
Letendre's saving exponent satisfies $\xi(\theta, \eta) = 4(\theta - \eta)$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Theorem 1, display (2). -/
public theorem letendreXi_of_small_theta_large_eta {θ η : ℝ} (h : θ ^ 2 < η) (hθ : θ ≤ 1 / 2)
    (hη : θ < 2 * η) : letendreXi θ η = 4 * (θ - η) := by
  unfold letendreXi
  split_ifs <;> first | rfl | linarith

end

namespace isGreatest_letendreXi

/-- Admissible cutoffs after clearing the positive denominator `α ^ 2`. -/
private def admissible (θ η : ℝ) : Set ℝ :=
  {A | 0 < A ∧ A ≤ 1 ∧ ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t →
    t ≤ 1 - α → α * (η - t) ≤ (θ - t) ^ 2}

private theorem quotient_nonneg_iff {θ η α t : ℝ} (hα : 0 < α) :
    0 ≤ ((θ - t) / α) ^ 2 - (η - t) / α ↔ α * (η - t) ≤ (θ - t) ^ 2 := by
  rw [sub_nonneg, div_pow]
  field_simp

/-- When `2 * η ≤ θ`, the sharp constraint comes from `t = 0`. -/
private theorem isGreatest_ratio {θ η : ℝ} (hsq : θ ^ 2 ≤ η) (hlt : η < θ)
    (h : 2 * η ≤ θ) : IsGreatest (admissible θ η) (θ ^ 2 / η) := by
  have hθ : 0 < θ := lt_of_le_of_lt ((sq_nonneg θ).trans hsq) hlt
  have hη : 0 < η := (sq_pos_of_pos hθ).trans_le hsq
  have hslope : 2 * θ ≤ θ ^ 2 / η := by
    apply (le_div_iff₀ hη).2
    nlinarith only [mul_nonneg hθ.le (sub_nonneg.mpr h)]
  constructor
  · refine ⟨div_pos (sq_pos_of_pos hθ) hη, (div_le_one hη).2 hsq, ?_⟩
    intro α hα hαR t ht _
    by_cases htη : t ≤ η
    · calc
        α * (η - t) ≤ (θ ^ 2 / η) * (η - t) :=
          mul_le_mul_of_nonneg_right hαR (sub_nonneg.mpr htη)
        _ ≤ (θ - t) ^ 2 := by
          nlinarith only [div_mul_cancel₀ (θ ^ 2) hη.ne', sq_nonneg t,
            mul_nonneg (sub_nonneg.mpr hslope) ht]
    · exact (mul_nonpos_of_nonneg_of_nonpos hα.le (by linarith)).trans (sq_nonneg _)
  · rintro A ⟨hA, hA₁, htest⟩
    apply (le_div_iff₀ hη).2
    simpa using htest A hA le_rfl 0 le_rfl (sub_nonneg.mpr hA₁)

/-- In the interior case the quadratic has a double root at the sharp cutoff.
Keeping this root fixed rules out every larger cutoff. -/
private theorem isGreatest_linear {θ η : ℝ} (hlt : η < θ) (hθ : θ ≤ 1 / 2)
    (h : θ < 2 * η) : IsGreatest (admissible θ η) (4 * (θ - η)) := by
  constructor
  · refine ⟨by linarith, by linarith, ?_⟩
    intro α hα hαΔ t _ _
    nlinarith only [sq_nonneg (2 * (θ - t) - α), mul_nonneg hα.le (sub_nonneg.mpr hαΔ)]
  · rintro A ⟨_, _, htest⟩
    by_contra! hA
    let t := 2 * η - θ
    let α := min A (1 - t)
    have hα : 4 * (θ - η) < α := lt_min hA (by dsimp [t]; linarith)
    have htest' := htest α (by linarith) (min_le_left ..) t (by dsimp [t]; linarith)
      (by linarith only [show α ≤ 1 - t from min_le_right ..])
    dsimp only [t] at htest'
    nlinarith only [htest', mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hα)]

private theorem isGreatest_small {θ η : ℝ} (hsq : θ ^ 2 ≤ η) (hlt : η < θ)
    (hθ : θ ≤ 1 / 2) : IsGreatest (admissible θ η) (letendreXi θ η) := by
  have hpos : 0 < θ := lt_of_le_of_lt ((sq_nonneg θ).trans hsq) hlt
  by_cases h : 2 * η ≤ θ
  · have hvalue : letendreXi θ η = θ ^ 2 / η := by
      by_cases heq : η ≤ θ ^ 2
      · rw [letendreXi_of_le_sq heq, le_antisymm hsq heq, div_self]
        exact ((sq_pos_of_pos hpos).trans_le hsq).ne'
      · simp only [letendreXi, ite_eq_right heq, ite_eq_left hθ, ite_eq_left h]
    rw [hvalue]
    exact isGreatest_ratio hsq hlt h
  · have hstrict : θ ^ 2 < η := by
      nlinarith only [h, mul_nonneg hpos.le (sub_nonneg.mpr hθ)]
    rw [letendreXi_of_small_theta_large_eta hstrict hθ (lt_of_not_ge h)]
    exact isGreatest_linear hlt hθ (lt_of_not_ge h)

/-- The substitution `t ↦ 1 - α - t` reflects the interval of admissible `t`. -/
private theorem admissible_reflect (θ η : ℝ) :
    admissible (1 - θ) (1 - 2 * θ + η) = admissible θ η := by
  ext A
  constructor <;> rintro ⟨hA, hA₁, htest⟩ <;> refine ⟨hA, hA₁, ?_⟩ <;>
    intro α hα hαA t ht ht₁ <;>
    have href := htest α hα hαA (1 - α - t) (by linarith) (by linarith) <;>
    nlinarith only [href]

private theorem letendreXi_reflect {θ η : ℝ} (hθ : ¬ θ ≤ 1 / 2) :
    letendreXi (1 - θ) (1 - 2 * θ + η) = letendreXi θ η := by
  have hsq : 1 - 2 * θ + η ≤ (1 - θ) ^ 2 ↔ η ≤ θ ^ 2 := by
    constructor <;> intro h <;> nlinarith only [h]
  have hcut : 2 * (1 - 2 * θ + η) ≤ 1 - θ ↔ 2 * η ≤ 3 * θ - 1 := by
    constructor <;> intro h <;> linarith only [h]
  simp only [letendreXi, hsq, hcut, ite_eq_right hθ,
    ite_eq_left (show 1 - θ ≤ 1 / 2 by linarith)]
  ring_nf

end isGreatest_letendreXi

open isGreatest_letendreXi in
/-- **Letendre's exponent as the largest admissible exponent.** Let $\theta$ and $\eta$ be real
numbers with $\theta^2 \le \eta < \theta$. Then Letendre's saving exponent $\xi(\theta, \eta)$ is
the largest real number $A$ with $0 < A \le 1$ such that
$$\left(\frac{\theta - t}{\alpha}\right)^2 - \frac{\eta - t}{\alpha} \ge 0$$
for all real numbers $\alpha$ and $t$ with $0 < \alpha \le A$ and $0 \le t \le 1 - \alpha$.

On this range $\xi(\theta, \eta)$ equals the paper's $\alpha(\theta, \eta)$ of display (4). The cap
$A \le 1$ reflects $\alpha$ being an exponent ($a = n^\alpha \le n$); without it the set of such
$A$ is unbounded when $\eta = \theta^2$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 2 (`integers-2026-A115-prop-2`). -/
public theorem isGreatest_letendreXi {θ η : ℝ} (h₁ : θ ^ 2 ≤ η) (h₂ : η < θ) :
    IsGreatest {A : ℝ | 0 < A ∧ A ≤ 1 ∧ ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t →
      t ≤ 1 - α → 0 ≤ ((θ - t) / α) ^ 2 - (η - t) / α} (letendreXi θ η) := by
  suffices h : IsGreatest (admissible θ η) (letendreXi θ η) by
    simpa +contextual only [admissible, quotient_nonneg_iff] using h
  by_cases hθ : θ ≤ 1 / 2
  · exact isGreatest_small h₁ h₂ hθ
  · have href := isGreatest_small (θ := 1 - θ) (η := 1 - 2 * θ + η)
      (by nlinarith) (by linarith) (by linarith)
    rwa [admissible_reflect, letendreXi_reflect hθ] at href

namespace exists_alpha_with_margin

/-- With the relative position `p` fixed, the improvement from shrinking the interval
has a uniform lower bound coming from the two endpoint values `θ ^ 2` and `(1 - θ) ^ 2`. -/
private theorem margin_le_weight {θ p α β : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hp : 0 ≤ p) (hp₁ : p ≤ 1) (hαβ : 0 < α * β) (hαβ₁ : α * β ≤ 1) :
    (θ * (1 - θ)) ^ 2 ≤ (θ - p) ^ 2 / (α * β) + p * (1 - p) := by
  have hprod := mul_nonneg hθ (sub_nonneg.mpr hθ₁)
  have hleft := pow_le_pow_left₀ hprod
    (mul_le_of_le_one_right hθ (show 1 - θ ≤ 1 by linarith)) 2
  have hright := pow_le_pow_left₀ hprod
    (mul_le_of_le_one_left (sub_nonneg.mpr hθ₁) hθ₁) 2
  -- (θ - p)² + p(1 - p) is the weighted average of θ² and (1 - θ)².
  nlinarith only [mul_nonneg (sub_nonneg.mpr hp₁) (sub_nonneg.mpr hleft),
    mul_nonneg hp (sub_nonneg.mpr hright), le_div_self (sq_nonneg (θ - p)) hαβ hαβ₁]

/-- Compare the quadratic at the same relative position in intervals of lengths `1 - α`
and `1 - β`. -/
private theorem rescale {θ η δ α β : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hδ : 0 ≤ δ) (hα : 0 < α) (hβ : 0 < β) (hβ₁ : β ≤ 1) (hratio : 1 + δ ≤ β / α)
    (hbase : ∀ t : ℝ, 0 ≤ t → t ≤ 1 - β →
      0 ≤ ((θ - t) / β) ^ 2 - (η - t) / β)
    {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1 - α) :
    (θ * (1 - θ)) ^ 2 * δ ≤ ((θ - t) / α) ^ 2 - (η - t) / α := by
  obtain ⟨p, hp, hp₁, rfl⟩ : ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ t = (1 - α) * p := by
    rcases ht.eq_or_lt with rfl | htpos
    · exact ⟨0, le_rfl, zero_le_one, by simp⟩
    · have h := htpos.trans_le ht₁
      exact ⟨t / (1 - α), div_nonneg ht h.le, (div_le_one h).2 ht₁,
        (mul_div_cancel₀ t h.ne').symm⟩
  let s := (1 - β) * p
  have hs := hbase s (mul_nonneg (sub_nonneg.mpr hβ₁) hp)
    (mul_le_of_le_one_right (sub_nonneg.mpr hβ₁) hp₁)
  have hw := margin_le_weight hθ hθ₁ hp hp₁ (mul_pos hα hβ)
    ((mul_le_of_le_one_left hβ.le (by linarith)).trans hβ₁)
  calc
    (θ * (1 - θ)) ^ 2 * δ ≤
        ((θ - p) ^ 2 / (α * β) + p * (1 - p)) * (β / α - 1) :=
      mul_le_mul hw (by linarith) hδ ((sq_nonneg _).trans hw)
    _ ≤ _ + (β / α) * (((θ - s) / β) ^ 2 - (η - s) / β) :=
      le_add_of_nonneg_right (mul_nonneg (div_nonneg hβ.le hα.le) hs)
    _ = _ := by dsimp [s]; field_simp; ring

end exists_alpha_with_margin

open exists_alpha_with_margin in
/-- **Exponents with a margin in Letendre's inequality.** Let $\xi(\theta, \eta)$ denote Letendre's
saving exponent, and let $\theta$, $\eta$ and $\delta$ be real numbers with $0 \le \delta \le 1$,
$\eta < \theta < 1$ and $0 < \theta^2 - (\theta(1 - \theta))^2 \delta \le \eta$. Then there is a
real number $A > 0$ with $\xi(\theta, \eta) - \delta \le A \le \xi(\theta, \eta)$ such that
$((\theta - t)/\alpha)^2 - (\eta - t)/\alpha \ge (\theta(1 - \theta))^2 \delta$ for all real
numbers $\alpha$ and $t$ with $0 < \alpha \le A$ and $0 \le t \le 1 - \alpha$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Proposition 3 (`integers-2026-A115-prop-3`). -/
public theorem exists_alpha_with_margin {θ η δ : ℝ}
    (h₀ : 0 < θ ^ 2 - (θ * (1 - θ)) ^ 2 * δ) (h₁ : θ ^ 2 - (θ * (1 - θ)) ^ 2 * δ ≤ η)
    (h₂ : η < θ) (h₃ : θ < 1) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ letendreXi θ η - δ ≤ A ∧ A ≤ letendreXi θ η ∧
      ∀ α : ℝ, 0 < α → α ≤ A → ∀ t : ℝ, 0 ≤ t → t ≤ 1 - α →
        (θ * (1 - θ)) ^ 2 * δ ≤ ((θ - t) / α) ^ 2 - (η - t) / α := by
  have hθ : 0 < θ := (h₀.trans_le h₁).trans h₂
  have hsq : θ ^ 2 < θ := by nlinarith only [mul_pos hθ (sub_pos.mpr h₃)]
  -- Raising η to θ² below the threshold preserves the cutoff and decreases the quadratic.
  have hξ : letendreXi θ (max η (θ ^ 2)) = letendreXi θ η := by
    rcases le_total η (θ ^ 2) with h | h
    · rw [max_eq_right h, letendreXi_of_le_sq le_rfl, letendreXi_of_le_sq h]
    · rw [max_eq_left h]
  have hcut := (isGreatest_letendreXi (le_max_right η (θ ^ 2)) (max_lt h₂ hsq)).1
  rw [hξ] at hcut
  obtain ⟨hβ, hβ₁, hquad⟩ := hcut
  let β := letendreXi θ η
  have hd : 0 < 1 + δ := by linarith
  have hhalf : β / 2 ≤ β / (1 + δ) :=
    div_le_div_of_nonneg_left hβ.le hd (by linarith only [hδ₁])
  refine ⟨β / (1 + δ), (half_pos hβ).trans_le hhalf, (le_div_iff₀ hd).2 ?_,
    div_le_self hβ.le (by linarith), ?_⟩
  · dsimp only [β]
    nlinarith only [mul_nonneg hδ₀ (sub_nonneg.mpr hβ₁), sq_nonneg δ]
  · intro α hα hαA t ht ht₁
    apply rescale hθ.le h₃.le hδ₀ hα hβ hβ₁ _ _ ht ht₁
    · exact (le_div_iff₀ hα).2 (by simpa only [mul_comm] using (le_div_iff₀ hd).1 hαA)
    · intro s hs hs₁
      have h := hquad β hβ le_rfl s hs hs₁
      exact h.trans (sub_le_sub_left
        (div_le_div_of_nonneg_right (sub_le_sub_right (le_max_left ..) _) hβ.le) _)

end MetaMathlibExt
