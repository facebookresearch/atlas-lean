/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NicomachusGeneralization

/-!
# The Kim–Stolarsky convergents

This file defines the convergents `αₖ` by their rational recurrence and expresses them in terms of
`uₖ`, the coefficients of the Kim–Stolarsky generating function.

The proof checks the two recurrences against the invariant `(11 - (2αₖ + 1)^2) * (3 + 2uₖ) = 10`.
See Proposition 7 of the authors' preprint (<https://arxiv.org/html/2511.15133v1>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.NicomachusGeneralizationWanted

/-- **The Kim–Stolarsky convergents $\alpha_k$.** The rational numbers $\alpha_k$, for natural
numbers $k$, are defined by $\alpha_0 = 0$, $\alpha_1 = 1$ and
$\alpha_{k+1} = \frac{15 + 7\alpha_k}{13 + 6\alpha_k}$ for $k \ge 1$.

For $k \ge 1$, $\alpha_k$ is the continued-fraction convergent $[1; 6, 3, \ldots, 6, 3]$ with
$2k - 2$ partial quotients after the semicolon (Equation (12) of Kim and Stolarsky); the value
$\alpha_0 = 0$ is a placeholder. -/
def nicomachusAlpha : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (k + 2) => (15 + 7 * nicomachusAlpha (k + 1)) /
      (13 + 6 * nicomachusAlpha (k + 1))

/-- **The convergents $\alpha_k$ in terms of the integers $u_k$.** Let $\alpha_k$ be the
Kim–Stolarsky convergents, with $\alpha_1 = 1$ and
$\alpha_{k+1} = (15 + 7\alpha_k)/(13 + 6\alpha_k)$ for $k \ge 1$, and let $u_k$ be the
coefficient of $x^{k-1}$ in the power series expansion of
$(1 + 502x + x^2)/((1 - x)(1 - 398x + x^2))$. For every integer $k \ge 1$,
$$\alpha_k = \frac{-1 + \sqrt{11 - \frac{10}{3 + 2u_k}}}{2}.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Proposition 2. -/
theorem nicomachusAlpha_eq (k : ℕ) (hk : 1 ≤ k) :
    (nicomachusAlpha k : ℝ) =
      (-1 + Real.sqrt (11 - 10 / (3 + 2 * (nicomachusU k : ℝ)))) / 2 := by
  let a (j : ℕ) : ℝ := 2 * (nicomachusAlpha j : ℝ) + 1
  let d (j : ℕ) : ℝ := 3 + 2 * (nicomachusU j : ℝ)
  have invariant (j : ℕ) (hj : 1 ≤ j) :
      0 < a j ∧ 0 < d j ∧ (11 - a j ^ 2) * d j = 10 := by
    induction j, hj using Nat.le_induction with
    | base =>
      have hu : nicomachusU 1 = 1 := by
        simp [nicomachusU, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      norm_num [a, d, nicomachusAlpha, hu]
    | succ j hj ih =>
      obtain ⟨ha, hd, heq⟩ := ih
      have hden : 0 < 10 + 3 * a j := by positivity
      have ha' : a (j + 1) = (10 * a j + 33) / (10 + 3 * a j) := by
        have hden' : 13 + 6 * (nicomachusAlpha j : ℝ) ≠ 0 := by
          dsimp only [a] at hden
          linarith
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
        dsimp only [a]
        rw [nicomachusAlpha.eq_3]
        push_cast
        generalize (nicomachusAlpha (n + 1) : ℝ) = x at hden' ⊢
        rw [show 10 + 3 * (2 * x + 1) = 13 + 6 * x by ring]
        apply (eq_div_iff hden').2
        rw [add_mul, mul_assoc, div_mul_cancel₀ _ hden', one_mul]
        ring
      have hd_eq : d j = 3 + 2 * (nicomachusU j : ℝ) := rfl
      have hrad : 23 + 22 * (nicomachusU j : ℝ) = a j ^ 2 * d j := by
        linear_combination heq - 11 * hd_eq
      have hs : Real.sqrt (d j * (23 + 22 * (nicomachusU j : ℝ))) = a j * d j := by
        rw [hrad, show d j * (a j ^ 2 * d j) = (a j * d j) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      have hd' : d (j + 1) = d j * (10 + 3 * a j) ^ 2 := by
        change 3 + 2 * (nicomachusU (j + 1) : ℝ) = _
        rw [nicomachusU_succ_eq j hj, ← hd_eq, hs]
        linear_combination 9 * heq - 199 * hd_eq
      rw [ha', hd']
      refine ⟨by positivity, by positivity, ?_⟩
      calc
        (11 - ((10 * a j + 33) / (10 + 3 * a j)) ^ 2) * (d j * (10 + 3 * a j) ^ 2) =
            (11 - a j ^ 2) * d j := by
          field_simp
          ring
        _ = 10 := heq
  obtain ⟨ha, hd, heq⟩ := invariant k hk
  have hrad : 11 - 10 / d k = a k ^ 2 := by
    rw [← (eq_div_iff (ne_of_gt hd)).2 heq, sub_sub_cancel]
  change (nicomachusAlpha k : ℝ) = (-1 + Real.sqrt (11 - 10 / d k)) / 2
  rw [hrad, Real.sqrt_sq ha.le]
  dsimp only [a]
  ring

end MathlibExt.NumberTheory.NicomachusGeneralizationWanted
