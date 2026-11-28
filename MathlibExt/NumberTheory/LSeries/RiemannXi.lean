/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/CompletedXi.lean` (PrimeNumberTheoremAnd):
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Matteo Cipollina
-/

module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

/-!
# The Riemann xi function

This module defines the Riemann xi function in the normalization

  `ξ(s) = s * (s - 1) / 2 * Λ₀(s) + 1 / 2`,

where `Λ₀ = completedRiemannZeta₀` is Mathlib's entire completed Riemann zeta
function (the completed zeta function with its polar parts removed). The
additive constant `1 / 2` is forced algebraically by `completedRiemannZeta_eq`
together with the requirement that `ξ` agree with `s * (s - 1) / 2 * Λ(s)`
away from the poles of `Λ` at `s = 0` and `s = 1`.

## Main results

* `Complex.riemannXi`: the Riemann xi function (as in PrimeNumberTheoremAnd).
* `RiemannXi.differentiable_riemannXi`: `ξ` is entire.
* `RiemannXi.riemannXi_one_sub`: the functional equation `ξ(1 - s) = ξ(s)`.
* `RiemannXi.riemannXi_eq_mul_completedRiemannZeta`: away from `s = 0, 1`,
  `ξ(s) = s * (s - 1) / 2 * Λ(s)`.
* `RiemannXi.riemannXi_ne_zero_of_one_le_re`: `ξ` does not vanish on
  `1 ≤ s.re` (proved from the agreement theorem plus
  `riemannZeta_ne_zero_of_one_le_re`; the point `s = 1` is handled separately).
* `RiemannXi.re_pos_of_riemannXi_eq_zero` and
  `RiemannXi.re_lt_one_of_riemannXi_eq_zero`: every zero of `ξ` lies in the
  open critical strip `0 < s.re < 1` (the left half follows by reflecting
  through the functional equation into the nonvanishing half-plane).
* `RiemannXi.riemannXi_entire_functional_equation_and_critical_strip`: packaged
  corollary conjoining the entireness, functional equation, and critical-strip
  claims.
* `riemannZetaNontrivialZeros`: the zeros of `ζ` in the open critical strip
  `0 < Re s < 1`, with `mem_riemannZetaNontrivialZeros_iff_le` for the closed strip.
* `RiemannXi.riemannXi_eq_zero_iff`: the zeros of `ξ` are exactly the nontrivial
  zeros of `ζ`.
-/

namespace RiemannXi

/-- **Riemann xi function.** Let $\Lambda$ be the completed Riemann zeta function, the
meromorphic continuation of $\pi^{-s/2}\Gamma(s/2)\zeta(s)$, which has simple poles at
$s = 0$ and $s = 1$, and let $\Lambda_0$ be the entire function with
$\Lambda_0(s) = \Lambda(s) + \frac{1}{s} + \frac{1}{1 - s}$ for $s \ne 0, 1$. The Riemann
xi function is $\xi(s) = \frac{s(s - 1)}{2}\Lambda_0(s) + \frac{1}{2}$ for $s \in \mathbb{C}$. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

/-- **The Riemann xi function is entire.** The Riemann xi function $\xi$ is complex
differentiable at every point of $\mathbb{C}$. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  have h1 : Differentiable ℂ (fun s : ℂ => s * (s - 1) / 2) := by fun_prop
  have h2 := h1.mul differentiable_completedZeta₀
  have h3 := h2.add_const (1 / 2 : ℂ)
  unfold riemannXi
  exact h3

/-- **Functional equation of the Riemann xi function.** Let $\xi$ be the Riemann xi function.
For every complex number $s$, $\xi(1 - s) = \xi(s)$. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  have hfactor : (1 - s) * ((1 - s) - 1) / 2 = s * (s - 1) / 2 := by ring
  rw [hfactor, completedRiemannZeta₀_one_sub]

/-- **The xi function in terms of the completed zeta function.** Let $\xi$ be the Riemann xi
function and let $\Lambda$ be the completed Riemann zeta function, the meromorphic continuation
of $\pi^{-s/2}\Gamma(s/2)\zeta(s)$, which has simple poles at $s = 0$ and $s = 1$. For every
complex number $s$ with $s \ne 0$ and $s \ne 1$, $\xi(s) = \frac{s(s - 1)}{2}\Lambda(s)$. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold riemannXi
  rw [completedRiemannZeta_eq]
  field_simp
  ring

/-- **The xi function has no zeros with real part at least one.** Let $\xi$ be the Riemann xi
function. For every complex number $s$ with $\operatorname{Re}(s) \ge 1$, $\xi(s) \ne 0$. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  rcases eq_or_ne s 1 with rfl | hs1
  · have hval : riemannXi 1 = 1 / 2 := by simp [riemannXi]
    rw [hval]
    norm_num
  · have hzeta := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_completedRiemannZeta₀ hs0] at hzeta
    have hN : completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) ≠ 0 :=
      fun hN => hzeta (by rw [hN, zero_div])
    have hfac : s * (s - 1) / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero
    have hag := riemannXi_eq_mul_completedRiemannZeta hs0 hs1
    rw [completedRiemannZeta_eq] at hag
    rw [hag]
    exact mul_ne_zero hfac hN

/-- **Zeros of the xi function have positive real part.** Let $\xi$ be the Riemann xi
function. If $s$ is a complex number with $\xi(s) = 0$, then $\operatorname{Re}(s) > 0$. -/
theorem re_pos_of_riemannXi_eq_zero {s : ℂ} (h : riemannXi s = 0) :
    0 < s.re := by
  by_contra hle
  push Not at hle
  have h1 : 1 ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hne := riemannXi_ne_zero_of_one_le_re h1
  rw [riemannXi_one_sub] at hne
  exact hne h

/-- **Zeros of the xi function have real part less than one.** Let $\xi$ be the Riemann xi
function. If $s$ is a complex number with $\xi(s) = 0$, then $\operatorname{Re}(s) < 1$. -/
theorem re_lt_one_of_riemannXi_eq_zero {s : ℂ} (h : riemannXi s = 0) :
    s.re < 1 := by
  by_contra hle
  push Not at hle
  exact riemannXi_ne_zero_of_one_le_re hle h

/-- **Zeros of the xi function lie in the critical strip.** Let $\xi$ be the Riemann xi
function. If $s$ is a complex number with $\xi(s) = 0$, then $0 < \operatorname{Re}(s) < 1$. -/
theorem riemannXi_mem_strip {s : ℂ} (h : riemannXi s = 0) :
    0 < s.re ∧ s.re < 1 :=
  ⟨re_pos_of_riemannXi_eq_zero h, re_lt_one_of_riemannXi_eq_zero h⟩

/-- **Basic properties of the Riemann xi function.** The Riemann xi function $\xi$ is
entire, satisfies $\xi(1 - s) = \xi(s)$ for every complex number $s$, and every complex
number $s$ with $\xi(s) = 0$ satisfies $0 < \operatorname{Re}(s) < 1$. -/
theorem riemannXi_entire_functional_equation_and_critical_strip :
    Differentiable ℂ riemannXi ∧
      (∀ s : ℂ, riemannXi (1 - s) = riemannXi s) ∧
      ∀ s : ℂ, riemannXi s = 0 → 0 < s.re ∧ s.re < 1 :=
  ⟨differentiable_riemannXi, riemannXi_one_sub,
    fun _s h => riemannXi_mem_strip h⟩

end RiemannXi

namespace Complex

export RiemannXi (riemannXi)

end Complex

/-- The **nontrivial zeros** of the Riemann zeta function: the zeros of `riemannZeta` in the
open critical strip `0 < Re s < 1`, as `NontrivialZeros` in PrimeNumberTheoremAnd. Unlike
`riemannZetaZeros`, this excludes the trivial zeros at the negative even integers; since `ζ` has no
zeros on `Re s = 0` or `Re s = 1`, it is also the set of zeros in the closed strip
(`mem_riemannZetaNontrivialZeros_iff_le`). Zeros are counted without multiplicity. -/
def riemannZetaNontrivialZeros : Set ℂ :=
  {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

/-- Membership in the nontrivial zeros of `ζ`, unfolded. -/
theorem mem_riemannZetaNontrivialZeros {s : ℂ} :
    s ∈ riemannZetaNontrivialZeros ↔ riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 :=
  Iff.rfl

namespace RiemannXi

open Complex (riemannXi)

/-- The zeros of `ξ` are the zeros of `ζ` in the closed critical strip. -/
private theorem riemannXi_eq_zero_iff_le (s : ℂ) :
    riemannXi s = 0 ↔ riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 := by
  -- `Γℝ` vanishes only at `-2n`, so not for `Re s ≥ 0`, `s ≠ 0`
  have hG : ∀ z : ℂ, z ≠ 0 → 0 ≤ z.re → z.Gammaℝ ≠ 0 := by
    intro z hz hre h
    obtain ⟨n, rfl⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at hz
    · have : (-(2 * (n : ℂ))).re = -(2 * (n : ℝ)) := by simp
      rw [this] at hre
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  have hΛ : ∀ z : ℂ, z ≠ 0 → 0 ≤ z.re →
      (completedRiemannZeta z = 0 ↔ riemannZeta z = 0) := by
    intro z hz hre
    rw [riemannZeta_def_of_ne_zero hz, div_eq_zero_iff]
    have := hG z hz hre
    tauto
  have hR : ∀ z : ℂ, 1 ≤ z.re → completedRiemannZeta z ≠ 0 := by
    intro z hre
    have hz : z ≠ 0 := by
      rintro rfl; simp at hre; linarith
    rw [Ne, hΛ z hz (by linarith)]
    exact riemannZeta_ne_zero_of_one_le_re hre
  by_cases h0 : s = 0
  · subst h0
    simp [riemannXi, riemannZeta_zero]
  by_cases h1 : s = 1
  · subst h1
    have := riemannZeta_ne_zero_of_one_le_re (s := 1) (by simp)
    simp [riemannXi, this]
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1, mul_eq_zero,
    or_iff_right (div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) two_ne_zero)]
  rcases lt_or_ge s.re 0 with hneg | hnn
  · constructor
    · intro h
      exfalso
      refine hR (1 - s) ?_ ?_
      · simp; linarith
      · rw [completedRiemannZeta_one_sub]; exact h
    · rintro ⟨-, h, -⟩; linarith
  rcases le_or_gt s.re 1 with hle | hgt
  · rw [hΛ s h0 hnn]
    tauto
  · constructor
    · intro h; exact absurd h (hR s hgt.le)
    · rintro ⟨-, -, h⟩; linarith

/-- **The zeros of `ξ` are the nontrivial zeros of `ζ`.** The factor `s (s - 1) / 2` cancels the
pole of `ζ` at `1`, the poles of `Γ(s/2)` cancel the trivial zeros at `-2n`, and `ζ` does not
vanish on `Re s ≥ 1`.

Source: B. Riemann, *Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse* (1859), in
*Gesammelte mathematische Werke*, Cambridge University Press, 2013, 136–144,
DOI 10.1017/CBO9781139568050.008.
-/
theorem riemannXi_eq_zero_iff (s : ℂ) : riemannXi s = 0 ↔ s ∈ riemannZetaNontrivialZeros := by
  refine ⟨fun h => ⟨((riemannXi_eq_zero_iff_le s).1 h).1, re_pos_of_riemannXi_eq_zero h,
    re_lt_one_of_riemannXi_eq_zero h⟩, fun h => (riemannXi_eq_zero_iff_le s).2
      ⟨h.1, h.2.1.le, h.2.2.le⟩⟩

end RiemannXi

/-- The nontrivial zeros of `ζ` are its zeros in the closed critical strip `0 ≤ Re s ≤ 1`: `ζ`
does not vanish on the boundary lines. -/
theorem mem_riemannZetaNontrivialZeros_iff_le {s : ℂ} :
    s ∈ riemannZetaNontrivialZeros ↔ riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 := by
  rw [← RiemannXi.riemannXi_eq_zero_iff, RiemannXi.riemannXi_eq_zero_iff_le]
