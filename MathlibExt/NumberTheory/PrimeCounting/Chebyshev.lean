/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Prime number theorem via Chebyshev's theta function

This file packages the equivalence between the prime number theorem, in the form
`π(x) ~ x / log x`, and Chebyshev's estimate `θ(x) ~ x`, both as `x → +∞`.

The key input is `Chebyshev.primeCounting_sub_theta_div_log_isBigO`, which bounds
the difference between `π(x)` and `θ(x) / log x`. Since that error is little-o of
`x / log x`, the two asymptotics imply each other by `Asymptotics` algebra.
-/

@[expose] public section

open scoped Asymptotics

namespace Chebyshev

/-- **Prime counting versus theta over log.** Let $\pi(x)$ be the number of primes $p \le x$ and
let $\theta(x) = \sum_{p \le x} \log p$, the sum running over primes. As the real number $x$ tends
to $+\infty$,
$$\pi(x) - \frac{\theta(x)}{\log x} = o\left(\frac{x}{\log x}\right).$$

The proof upgrades the bound $\pi(x) - \theta(x)/\log x = O(x/(\log x)^2)$, using that
$x/(\log x)^2 = o(x/\log x)$. -/
theorem primeCounting_sub_theta_div_log_isLittleO :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x)
      =o[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
  have haux : (fun x : ℝ => x / Real.log x ^ 2)
      =o[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
    refine Asymptotics.isLittleO_iff_tendsto' (by simp) |>.mpr ?_
    refine Filter.Tendsto.congr' (f₁ := fun x : ℝ => (Real.log x)⁻¹) ?_
      Real.tendsto_log_atTop.inv_tendsto_atTop
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hxlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
    field
  exact Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO haux

/-- **Theta asymptotic implies the prime number theorem.** Let $\pi(x)$ be the number of primes
$p \le x$ and let $\theta(x) = \sum_{p \le x} \log p$, the sum running over primes. If
$\theta(x) \sim x$ as the real number $x$ tends to $+\infty$, then $\pi(x) \sim x / \log x$ as
$x \to +\infty$. -/
theorem primeCounting_isEquivalent_of_theta_isEquivalent
    (h : Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
      ~[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
  have hlog : (fun x : ℝ => Real.log x) ~[Filter.atTop] (fun x : ℝ => Real.log x) :=
    Asymptotics.IsEquivalent.refl
  have hdiv : (fun x : ℝ => Chebyshev.theta x / Real.log x)
      ~[Filter.atTop] (fun x : ℝ => x / Real.log x) :=
    h.div hlog
  have hadd := Asymptotics.IsLittleO.add_isEquivalent
    primeCounting_sub_theta_div_log_isLittleO hdiv
  refine hadd.congr_left ?_
  exact Filter.Eventually.of_forall fun x => sub_add_cancel _ _

/-- **Prime number theorem implies the theta asymptotic.** Let $\pi(x)$ be the number of primes
$p \le x$ and let $\theta(x) = \sum_{p \le x} \log p$, the sum running over primes. If
$\pi(x) \sim x / \log x$ as the real number $x$ tends to $+\infty$, then $\theta(x) \sim x$ as
$x \to +\infty$. -/
theorem theta_isEquivalent_of_primeCounting_isEquivalent
    (h : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
      ~[Filter.atTop] (fun x : ℝ => x / Real.log x)) :
    Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x := by
  have hlog : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≠ 0 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact ne_of_gt (Real.log_pos hx)
  have hlogequiv : (fun x : ℝ => Real.log x) ~[Filter.atTop]
      (fun x : ℝ => Real.log x) :=
    Asymptotics.IsEquivalent.refl
  have hcancel : (fun x : ℝ => x / Real.log x) * Real.log
      =ᶠ[Filter.atTop] (fun x : ℝ => x) := by
    filter_upwards [hlog] with x hx
    simp only [Pi.mul_apply]
    exact div_mul_cancel₀ _ hx
  have hpi : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x)
      ~[Filter.atTop] (fun x : ℝ => x) :=
    (h.mul hlogequiv).trans_eventuallyEq hcancel
  have herr : (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ)
      - Chebyshev.theta x / Real.log x) * Real.log x)
      =o[Filter.atTop] (fun x : ℝ => x) :=
    (primeCounting_sub_theta_div_log_isLittleO.mul_isBigO
      (Asymptotics.isBigO_refl _ _)).trans_eventuallyEq hcancel
  have hsub := hpi.sub_isLittleO herr
  refine Filter.EventuallyEq.trans_isEquivalent ?_ hsub
  filter_upwards [hlog] with x hx
  simp only [Pi.sub_apply]
  rw [sub_mul, div_mul_cancel₀ _ hx]
  abel

/-- **Prime number theorem is equivalent to the theta asymptotic.** Let $\pi(x)$ be the number of
primes $p \le x$ and let $\theta(x) = \sum_{p \le x} \log p$ be Chebyshev's theta function, the
sum running over primes. Then, as the real number $x$ tends to $+\infty$, $\pi(x) \sim x / \log x$
holds if and only if $\theta(x) \sim x$. -/
theorem primeCounting_isEquivalent_iff_theta_isEquivalent :
    ((fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
      ~[Filter.atTop] (fun x : ℝ => x / Real.log x))
      ↔ (Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) :=
  ⟨theta_isEquivalent_of_primeCounting_isEquivalent,
    primeCounting_isEquivalent_of_theta_isEquivalent⟩

end Chebyshev
