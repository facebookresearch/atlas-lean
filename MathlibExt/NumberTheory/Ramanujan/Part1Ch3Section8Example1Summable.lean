/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Section 8, Example 1

Summability of an alternating rising-factorial series past radius R.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example1Summable

def sector (lam : Option ℝ) (eps : ℝ) (z : ℂ) : Prop :=
  match lam with
  | some l => |Complex.arg (z - (l : ℂ))| ≤ Real.pi / 2 - eps
  | none => |Complex.arg z| ≤ Real.pi - eps

/-- **Convergence of a factorial series in a sector, general form.** Let $a_0, a_1, \ldots$ be
complex numbers, let $\lambda$ be either a real number or $-\infty$, and let $\varepsilon > 0$.
Suppose that the series
$$\sum_{j=0}^{\infty} \frac{(-1)^j a_j}{(z + 1)(z + 2) \cdots (z + j + 1)}$$
converges absolutely for every complex $z$ that is not a negative integer and satisfies
$\operatorname{Re} z > \lambda$. Then there is a real number $R$ such that the series converges
absolutely for every complex $z$ with $|z| > R$ that lies in the sector
$|\arg(z - \lambda)| \le \pi/2 - \varepsilon$ when $\lambda$ is real, or
$|\arg z| \le \pi - \varepsilon$ when $\lambda = -\infty$. -/
theorem ramanujan_part1_ch3_section8_example1_summable_general
    (a : ℕ → ℂ) (lam : Option ℝ) (eps : ℝ) (heps_pos : 0 < eps)
    (hSumm : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) →
      (∀ l : ℝ, lam = some l → l < z.re) →
      Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
        ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ)))) :
    ∃ R : ℝ, ∀ z : ℂ, sector lam eps z → R < ‖z‖ →
        Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
            ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ))) := by
  cases lam with
  | none =>
    refine ⟨0, fun z hz hR => ?_⟩
    apply hSumm z ?_ ?_
    · intro n hn
      have hz2 : |Complex.arg z| ≤ Real.pi - eps := hz
      have harg : Complex.arg z = Real.pi := by
        apply Complex.arg_eq_pi_iff.mpr
        rw [hn]
        constructor
        · simp only [Complex.neg_re, Complex.natCast_re]
          have hnn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
          push_cast
          linarith
        · simp
      rw [harg, abs_of_nonneg Real.pi_pos.le] at hz2
      linarith
    · intro l hl
      simp at hl
  | some l =>
    refine ⟨|l|, fun z hz hR => ?_⟩
    have hz2 : |Complex.arg (z - (l : ℂ))| ≤ Real.pi / 2 - eps := hz
    have hnorm_l : ‖((l : ℝ) : ℂ)‖ = |l| := by simp
    have hw_ne : z - ((l : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have hzeq : z = ((l : ℝ) : ℂ) := sub_eq_zero.mp h0
      rw [hzeq, hnorm_l] at hR
      exact lt_irrefl _ hR
    have hRe : l < z.re := by
      have hcos : 0 < Real.cos (z - ((l : ℝ) : ℂ)).arg := by
        apply Real.cos_pos_of_mem_Ioo
        have habs := abs_le.mp hz2
        have hpi := Real.pi_pos
        constructor <;> linarith
      have hnorm_pos : 0 < ‖z - ((l : ℝ) : ℂ)‖ := norm_pos_iff.mpr hw_ne
      have hre := Complex.norm_mul_cos_arg (z - ((l : ℝ) : ℂ))
      have hRe_w : 0 < (z - ((l : ℝ) : ℂ)).re := by
        rw [← hre]
        exact mul_pos hnorm_pos hcos
      have hsub : (z - ((l : ℝ) : ℂ)).re = z.re - l := by simp
      rw [hsub] at hRe_w
      linarith
    apply hSumm z ?_ ?_
    · intro n hn
      have hR2 : |l| < ‖z‖ := hR
      rw [hn, norm_neg, Complex.norm_natCast] at hR2
      have harg : Complex.arg (z - ((l : ℝ) : ℂ)) = Real.pi := by
        apply Complex.arg_eq_pi_iff.mpr
        rw [hn]
        constructor
        · simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re,
            Complex.ofReal_re]
          have h3 : -(l) ≤ |l| := neg_le_abs l
          have hcast : (((n + 1 : ℕ)) : ℝ) = ((n : ℕ) : ℝ) + 1 := by
            push_cast; ring
          have h4 : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg n
          linarith
        · simp
      rw [harg, abs_of_nonneg Real.pi_pos.le] at hz2
      have hpi := Real.pi_pos
      linarith
    · intro l' hl'
      obtain rfl := Option.some_inj.mp hl'
      exact hRe

set_option linter.unusedVariables false in
/-- **Convergence of a factorial series in a sector.** Let $a_0, a_1, \ldots$ be complex numbers,
let $\lambda$ be either a real number or $-\infty$, and let $\varepsilon > 0$, with
$\varepsilon < \pi/2$ when $\lambda$ is real and $\varepsilon < \pi$ when $\lambda = -\infty$.
Suppose that the series
$$\sum_{j=0}^{\infty} \frac{(-1)^j a_j}{(z + 1)(z + 2) \cdots (z + j + 1)}$$
converges absolutely for every complex $z$ that is not a negative integer and satisfies
$\operatorname{Re} z > \lambda$. Then there is a real number $R$ such that the series converges
absolutely for every complex $z$ with $|z| > R$ that lies in the sector
$|\arg(z - \lambda)| \le \pi/2 - \varepsilon$ when $\lambda$ is real, or
$|\arg z| \le \pi - \varepsilon$ when $\lambda = -\infty$.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 1, formula
    (8.1), printed p. 50 / PDF p. 60.
Proves `Wanted` entry `ramanujan_part1_ch3_section8_example1_summable`. It follows from
`ramanujan_part1_ch3_section8_example1_summable_general`; the upper bound `heps_lt` is unused and
keeps the source's shape.
-/
theorem ramanujan_part1_ch3_section8_example1_summable
    (a : ℕ → ℂ) (lam : Option ℝ) (eps : ℝ) (heps_pos : 0 < eps)
    (heps_lt : match lam with | some _ => eps < Real.pi / 2 | none => eps < Real.pi)
    (hSumm : ∀ z : ℂ, (∀ n : ℕ, z ≠ -((n + 1 : ℕ) : ℂ)) →
      (∀ l : ℝ, lam = some l → l < z.re) →
      Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
        ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ)))) :
    ∃ R : ℝ, ∀ z : ℂ, sector lam eps z → R < ‖z‖ →
        Summable (fun j : ℕ => ((-1 : ℂ) ^ j * a j) /
            ((Finset.range (j + 1)).prod fun k : ℕ => z + ((k + 1 : ℕ) : ℂ))) :=
  ramanujan_part1_ch3_section8_example1_summable_general a lam eps heps_pos hSumm

end Section8Example1Summable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
