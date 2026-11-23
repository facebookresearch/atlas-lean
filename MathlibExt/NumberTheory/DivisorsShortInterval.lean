/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Divisors in short intervals

Letendre's saving exponent is the largest cutoff for which a quadratic in the interval
parameter stays nonnegative. Reflecting the interval interchanges its two endpoints, so
it suffices to locate the sharp cutoff for `θ ≤ 1 / 2`.
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

end MetaMathlibExt
