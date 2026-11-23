/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting

/-!
# Brun's constant

Brun's constant is the sum of the reciprocals of the primes in every twin-prime pair.
-/

/-- **Twin-prime reciprocal term.** For a natural number $p$, the twin-prime reciprocal term
$t(p)$ is the real number $\frac{1}{p} + \frac{1}{p + 2}$ when $p$ and $p + 2$ are both prime,
and $0$ otherwise.

Source: teorth/optimizationproblems, “Brun's Constant,” `constants/81a.md`; the convention counts a
prime once for every twin-prime pair containing it.
-/
noncomputable def brunTwinPrimeReciprocalTerm (p : ℕ) : ℝ :=
  if p.Prime ∧ (p + 2).Prime then
    (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
  else 0

@[simp]
theorem brunTwinPrimeReciprocalTerm_eq_zero (p : ℕ)
    (h : ¬(p.Prime ∧ (p + 2).Prime)) :
    brunTwinPrimeReciprocalTerm p = 0 := by
  simp [brunTwinPrimeReciprocalTerm, h]

theorem brunTwinPrimeReciprocalTerm_eq (p : ℕ)
    (h : p.Prime ∧ (p + 2).Prime) :
    brunTwinPrimeReciprocalTerm p =
      (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ) := by
  simp [brunTwinPrimeReciprocalTerm, h]

/-- **Summability of the twin-prime reciprocal terms.** For a natural number $p$, let $t(p)$ be
$\frac{1}{p} + \frac{1}{p + 2}$ when $p$ and $p + 2$ are both prime and $0$ otherwise. Then the
series $\sum_{p \ge 0} t(p)$ converges unconditionally in $\mathbb{R}$. -/
theorem summable_brunTwinPrimeReciprocalTerm :
    Summable brunTwinPrimeReciprocalTerm := by
  exact BrunTwinPrimeReciprocalsWanted.brun_twin_prime_reciprocal_series_summable

/-- **Brun's constant.** Brun's constant is the real number
$B = \sum_{p} \left(\frac{1}{p} + \frac{1}{p + 2}\right)$, the sum over all primes $p$ such that
$p + 2$ is also prime. A prime lying in two twin-prime pairs, such as $5$ in $(3, 5)$ and
$(5, 7)$, is counted once for each pair. -/
noncomputable def brunConstant : ℝ :=
  ∑' p : ℕ, brunTwinPrimeReciprocalTerm p

/-- **Brun's constant is the sum of the twin-prime reciprocal series.** For a natural number $p$,
let $t(p)$ be $\frac{1}{p} + \frac{1}{p + 2}$ when $p$ and $p + 2$ are both prime and $0$
otherwise. Then the series $\sum_{p \ge 0} t(p)$ over the natural numbers converges
unconditionally in $\mathbb{R}$, and its sum is Brun's constant. -/
theorem hasSum_brunConstant :
    HasSum brunTwinPrimeReciprocalTerm brunConstant :=
  summable_brunTwinPrimeReciprocalTerm.hasSum

end MathlibExt.NumberTheory.PrimeCounting
