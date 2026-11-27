/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NicomachusCubeSums
public import MathlibExt.NumberTheory.NicomachusGeneralization

/-!
# The Kim–Stolarsky convergents

This file defines the convergents `αₖ` by their rational recurrence, expresses them in terms of
`uₖ`, the coefficients of the Kim–Stolarsky generating function, and evaluates the associated
balanced quadratic sum.

The proof checks the two recurrences against the invariant `(11 - (2αₖ + 1)^2) * (3 + 2uₖ) = 10`.
For the sum, this gives `αₖ(1 + αₖ) = (5/2)(1 - 1/(3 + 2uₖ))`; the closed form then follows by
checking its finite difference instead of using power-sum formulas.

## References

* Seon-Hong Kim and Kenneth B. Stolarsky, *A Balanced Three or More-term Generalization of
  Nicomachus' Identity*, INTEGERS 26 (2026), Article A98, pp. 1–12, Proposition 2 and Theorem 2
  (<https://math.colgate.edu/~integers/aa98/aa98.pdf>).
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

/-- The positive quantity `2αₖ + 1` squares to the radicand in the formula for `αₖ`. -/
private lemma nicomachusAlpha_radical (k : ℕ) (hk : 1 ≤ k) :
    0 < 2 * (nicomachusAlpha k : ℝ) + 1 ∧
      (2 * (nicomachusAlpha k : ℝ) + 1) ^ 2 = 11 - 10 / (3 + 2 * (nicomachusU k : ℝ)) := by
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
  exact ⟨ha, hrad.symm⟩

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
  obtain ⟨ha, hsq⟩ := nicomachusAlpha_radical k hk
  rw [← hsq, Real.sqrt_sq ha.le]
  ring

/-- **Kim–Stolarsky balanced quadratic sum.** Let $k \ge 1$, let $\alpha_k$ be the numbers of
Equation (12) (so $\alpha_1 = 1$ and $\alpha_{k+1} = (15 + 7\alpha_k)/(13 + 6\alpha_k)$), let $u_k$
be the integers of Proposition 1, and let $T_n = n(n+1)/2$. With
$(a, b, c) = (1, \alpha_k, -(1 + \alpha_k))$ and $(d, e, f) = (-a, -c, -b)$ as in (17), for every
natural number $m$,
$$\sum_{j=1}^{m} (a + bj + cj^2)(d + ej + fj^2) =
T_{m-1}\left(\frac{(1 + m)(2 - 3m^2)}{3(3 + 2u_k)} + (3 + 2m)\,T_{m-1}\right).$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 2. -/
theorem sum_quadratic_mul_quadratic_eq (k : ℕ) (hk : 1 ≤ k)
    (m : ℕ) :
    (∑ j ∈ Finset.Icc 1 m,
      (1 + (nicomachusAlpha k : ℝ) * (j : ℝ) -
          (1 + (nicomachusAlpha k : ℝ)) * (j : ℝ) ^ 2) *
        (-1 + (1 + (nicomachusAlpha k : ℝ)) * (j : ℝ) -
          (nicomachusAlpha k : ℝ) * (j : ℝ) ^ 2)) =
      nicomachusTriangular (m - 1) *
        (((1 + (m : ℝ)) * (2 - 3 * (m : ℝ) ^ 2) /
          (3 * (3 + 2 * (nicomachusU k : ℝ)))) +
            (3 + 2 * (m : ℝ)) * nicomachusTriangular (m - 1)) := by
  let a : ℝ := nicomachusAlpha k
  let q : ℝ := (3 + 2 * (nicomachusU k : ℝ))⁻¹
  have hprod : a * (1 + a) = 5 / 2 * (1 - q) := by
    have hsq := (nicomachusAlpha_radical k hk).2
    rw [div_eq_mul_inv] at hsq
    change (2 * a + 1) ^ 2 = 11 - 10 * q at hsq
    linear_combination (1 / 4 : ℝ) * hsq
  let summand (x : ℝ) : ℝ :=
    (1 + a * x - (1 + a) * x ^ 2) * (-1 + (1 + a) * x - a * x ^ 2)
  let tri (x : ℝ) : ℝ := (x - 1) * x / 2
  let F (x : ℝ) : ℝ := tri x * ((1 + x) * (2 - 3 * x ^ 2) / 3 * q + (3 + 2 * x) * tri x)
  -- The finite difference of `F` is the summand, using only the product `a * (1 + a)`.
  have hstep (x : ℝ) : F (x - 1) + summand x = F x := by
    dsimp only [F, tri, summand]
    linear_combination (x - 1) ^ 2 * x ^ 2 * hprod
  have hsum (n : ℕ) : (∑ j ∈ Finset.Icc 1 n, summand j) = F n := by
    induction n with
    | zero => norm_num [F, tri]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), ih, Nat.cast_succ]
      simpa using hstep ((n : ℝ) + 1)
  have htri : nicomachusTriangular (m - 1) = tri m := by
    cases m with
    | zero => norm_num [nicomachusTriangular, tri]
    | succ n => simp [nicomachusTriangular, tri]
  change (∑ j ∈ Finset.Icc 1 m, summand j) = _
  rw [hsum, htri]
  dsimp only [F, q]
  rw [← div_eq_mul_inv, div_div]

end MathlibExt.NumberTheory.NicomachusGeneralizationWanted
