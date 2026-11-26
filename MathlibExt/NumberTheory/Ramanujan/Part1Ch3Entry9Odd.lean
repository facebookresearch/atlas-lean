/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Defs.Filter
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry9Odd

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating
  ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining)

/-- **Ramanujan's product series.** For complex numbers $a$, $b$, $x$, $z$, Ramanujan's product
series of Entry 9(i) is
$$P(a, b, x; z) = \sum_{j=0}^{\infty} \frac{(-b)^j x^{j+1}}{\prod_{r=0}^{j} (z + a + b(r + 1))}.$$

The definition is totalized: a quotient with vanishing denominator is taken to be $0$, and the sum
of a non-summable series is taken to be $0$. Hence at a pole of the source expression, for example
$a = 0$, $b = 1$, $x = 1$, $z = -1$, where every product contains the vanishing factor
$z + a + b = 0$, every term and so $P$ itself equals $0$, whereas the source expression has a
singularity there. Off the poles, when $b \neq 0$ and $w = (z + a)/b$ is nonzero and satisfies
$|\arg w| \le \pi - \varepsilon$ for some $0 < \varepsilon < \pi$, the closed form of Ramanujan's
product series identifies $P$ with the source's closed form. -/
noncomputable def entry9_P (a b x : ℂ) (z : ℂ) : ℂ :=
  ∑' (j : ℕ), ((-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (z + a + b * ((r : ℂ) + 1)))

private lemma sector_add_real_ge (w : ℂ) (ε : ℝ) (hεpos : 0 < ε) (hεlt : ε < Real.pi)
    (h1 : -Real.pi + ε ≤ Complex.arg w) (h2 : Complex.arg w ≤ Real.pi - ε)
    (t : ℝ) (ht : 0 ≤ t) : Real.sin ε * ‖w‖ ≤ ‖w + (t : ℂ)‖ := by
  have hs_nonneg : 0 ≤ Real.sin ε :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hεpos) (le_of_lt hεlt)
  by_cases hRe : 0 ≤ w.re
  · have hle : ‖w‖ ≤ ‖w + (t : ℂ)‖ := by
      have hsq : ‖w‖ ^ 2 ≤ ‖w + (t : ℂ)‖ ^ 2 := by
        have e1 : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        have e2 : ‖w + (t : ℂ)‖ ^ 2 = (w.re + t) * (w.re + t) + w.im * w.im := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp [Complex.add_re, Complex.add_im]
        rw [e1, e2]
        nlinarith [hRe, ht]
      exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq
    calc Real.sin ε * ‖w‖ ≤ 1 * ‖w‖ :=
          mul_le_mul_of_nonneg_right (Real.sin_le_one ε) (norm_nonneg _)
      _ = ‖w‖ := one_mul _
      _ ≤ ‖w + (t : ℂ)‖ := hle
  · have hRe' : w.re < 0 := lt_of_not_ge hRe
    have habs : Real.pi / 2 < |Complex.arg w| := by
      by_contra hcon
      have hcon' : |Complex.arg w| ≤ Real.pi / 2 := le_of_not_gt hcon
      exact (not_le.mpr hRe') (Complex.abs_arg_le_pi_div_two_iff.mp hcon')
    by_cases hε2 : ε ≤ Real.pi / 2
    · have hθ_le : |Complex.arg w| ≤ Real.pi - ε := by
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      have hθ_pi : Complex.arg w ≤ Real.pi := by
        linarith [hθ_le, le_abs_self (Complex.arg w), hεpos]
      have e2 : Real.sin |Complex.arg w| = |Real.sin (Complex.arg w)| := by
        by_cases hθ0 : 0 ≤ Complex.arg w
        · rw [abs_of_nonneg hθ0, abs_of_nonneg
            (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ_pi)]
        · have hθ0' : Complex.arg w < 0 := lt_of_not_ge hθ0
          rw [abs_of_neg hθ0', Real.sin_neg, abs_of_nonpos
            (Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_lt hθ0') (by linarith))]
      have hφ_lo : ε ≤ Real.pi - |Complex.arg w| := by linarith
      have hφ_hi : Real.pi - |Complex.arg w| ≤ Real.pi / 2 := by linarith
      have hφ0 : -(Real.pi / 2) ≤ ε := by linarith
      have hsin : Real.sin ε ≤ Real.sin (Real.pi - |Complex.arg w|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two hφ0 hφ_hi hφ_lo
      have habs_sin : |Real.sin (Complex.arg w)| = Real.sin (Real.pi - |Complex.arg w|) := by
        rw [Real.sin_pi_sub]
        exact e2.symm
      have him : ‖w‖ * Real.sin ε ≤ |w.im| := by
        have hmul : ‖w‖ * Real.sin ε ≤ ‖w‖ * |Real.sin (Complex.arg w)| :=
          mul_le_mul_of_nonneg_left (habs_sin ▸ hsin) (norm_nonneg _)
        have hnorm : ‖w‖ * |Real.sin (Complex.arg w)| = |w.im| := by
          have h := Complex.norm_mul_sin_arg w
          rw [← h, abs_mul, abs_of_nonneg (norm_nonneg _)]
        rw [hnorm] at hmul
        exact hmul
      have him2 : (w + (t : ℂ)).im = w.im := by simp
      calc Real.sin ε * ‖w‖ = ‖w‖ * Real.sin ε := mul_comm _ _
        _ ≤ |w.im| := him
        _ = |(w + (t : ℂ)).im| := by rw [him2]
        _ ≤ ‖w + (t : ℂ)‖ := Complex.abs_im_le_norm _
    · have hε2' : Real.pi / 2 < ε := lt_of_not_ge hε2
      have hle : |Complex.arg w| ≤ Real.pi / 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith

private lemma partial_fraction : ∀ (N : ℕ) (w : ℂ), (∀ r : ℕ, w + ((r : ℂ) + 1) ≠ 0) →
    ∑ m ∈ Finset.range (N + 1), ((-1 : ℂ) ^ m * (Nat.choose N m : ℂ) / (w + ((m : ℂ) + 1)))
      = (Nat.factorial N : ℂ) / ∏ r ∈ Finset.range (N + 1), (w + ((r : ℂ) + 1)) := by
  intro N
  induction N with
  | zero =>
    intro w hw
    simp
  | succ N ih =>
    intro w hw
    have hw1 : ∀ r : ℕ, (w + 1) + ((r : ℂ) + 1) ≠ 0 := by
      intro r
      have h := hw (r + 1)
      have he : (w + 1) + ((r : ℂ) + 1) = w + ((((r + 1 : ℕ)) : ℂ) + 1) := by
        push_cast
        ring
      rw [he]
      exact h
    have hsplit : ∑ m ∈ Finset.range (N + 1 + 1),
          ((-1 : ℂ) ^ m * (Nat.choose (N + 1) m : ℂ) / (w + ((m : ℂ) + 1)))
        = (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ m * (Nat.choose N m : ℂ) / (w + ((m : ℂ) + 1))))
        - (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ m * (Nat.choose N m : ℂ) / ((w + 1) + ((m : ℂ) + 1)))) := by
      have hPasc : ∀ m ∈ Finset.range (N + 1),
          ((-1 : ℂ) ^ (m + 1) * (Nat.choose (N + 1) (m + 1) : ℂ) / (w + ((((m + 1 : ℕ)) : ℂ) + 1)))
          = ((-1 : ℂ) ^ (m + 1) * (Nat.choose N m : ℂ) / (w + ((m : ℂ) + 2)))
          + ((-1 : ℂ) ^ (m + 1) * (Nat.choose N (m + 1) : ℂ) / (w + ((m : ℂ) + 2))) := by
        intro m _
        have hcastm : (((m + 1 : ℕ)) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
        have hP : ((N + 1).choose (m + 1)) = (N.choose m + N.choose (m + 1)) :=
          Nat.choose_succ_succ' N m
        have hDm : w + (((m : ℂ) + 1) + 1) = w + ((m : ℂ) + 2) := by ring
        rw [hcastm, hP]
        push_cast
        rw [hDm, mul_add, add_div]
      have hC1 : (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ (m + 1) * (Nat.choose N m : ℂ) / (w + ((m : ℂ) + 2))))
          = -(∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ m * (Nat.choose N m : ℂ) / ((w + 1) + ((m : ℂ) + 1)))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro m _
        have hdm : (w + 1) + ((m : ℂ) + 1) = w + ((m : ℂ) + 2) := by ring
        rw [hdm, pow_succ]
        ring
      have hC0 : ((-1 : ℂ) ^ 0 * (Nat.choose (N + 1) 0 : ℂ) / (w + ((((0 : ℕ)) : ℂ) + 1)))
          = ((-1 : ℂ) ^ 0 * (Nat.choose N 0 : ℂ) / (w + ((((0 : ℕ)) : ℂ) + 1))) := by
        simp
      have hB : (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ (m + 1) * (Nat.choose N (m + 1) : ℂ) / (w + ((m : ℂ) + 2))))
          = ∑ j ∈ Finset.range N,
            ((-1 : ℂ) ^ (j + 1) * (Nat.choose N (j + 1) : ℂ) /
                (w + ((((j + 1 : ℕ)) : ℂ) + 1))) := by
        rw [Finset.sum_range_succ]
        have hGN : ((-1 : ℂ) ^ (N + 1) * (Nat.choose N (N + 1) : ℂ) / (w + ((N : ℂ) + 2))) = 0 := by
          rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N)]
          simp
        rw [hGN, add_zero]
        apply Finset.sum_congr rfl
        intro j _
        have hcastj : (((j + 1 : ℕ)) : ℂ) = (j : ℂ) + 1 := by push_cast; ring
        have hDj : w + (((j : ℂ) + 1) + 1) = w + ((j : ℂ) + 2) := by ring
        rw [hcastj, hDj]
      have hS : (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ m * (Nat.choose N m : ℂ) / (w + ((m : ℂ) + 1))))
          = (∑ j ∈ Finset.range N,
            ((-1 : ℂ) ^ (j + 1) * (Nat.choose N (j + 1) : ℂ) / (w + ((((j + 1 : ℕ)) : ℂ) + 1))))
          + ((-1 : ℂ) ^ 0 * (Nat.choose N 0 : ℂ) / (w + ((((0 : ℕ)) : ℂ) + 1))) :=
        Finset.sum_range_succ' _ _
      have hC2 : ((-1 : ℂ) ^ 0 * (Nat.choose (N + 1) 0 : ℂ) / (w + ((((0 : ℕ)) : ℂ) + 1)))
          + (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ (m + 1) * (Nat.choose N (m + 1) : ℂ) / (w + ((m : ℂ) + 2))))
          = (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ m * (Nat.choose N m : ℂ) / (w + ((m : ℂ) + 1)))) := by
        rw [hB, hS, hC0, add_comm]
      have hpeel : (∑ m ∈ Finset.range (N + 1 + 1),
            ((-1 : ℂ) ^ m * (Nat.choose (N + 1) m : ℂ) / (w + ((m : ℂ) + 1))))
          = (∑ m ∈ Finset.range (N + 1),
            ((-1 : ℂ) ^ (m + 1) * (Nat.choose (N + 1) (m + 1) : ℂ) /
                (w + ((((m + 1 : ℕ)) : ℂ) + 1))))
          + ((-1 : ℂ) ^ 0 * (Nat.choose (N + 1) 0 : ℂ) / (w + ((((0 : ℕ)) : ℂ) + 1))) :=
        Finset.sum_range_succ' _ _
      rw [hpeel, Finset.sum_congr rfl hPasc, Finset.sum_add_distrib]
      linear_combination hC2 + hC1
    have hPne : ∏ r ∈ Finset.range (N + 1), (w + ((r : ℂ) + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun r _ => hw r)
    have hQne : ∏ r ∈ Finset.range (N + 1), ((w + 1) + ((r : ℂ) + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun r _ => hw1 r)
    have hRne : ∏ r ∈ Finset.range (N + 1 + 1), (w + ((r : ℂ) + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun r _ => hw r)
    have hprod := Finset.prod_range_succ (fun r => w + ((r : ℂ) + 1)) (N + 1)
    have hprod2 := Finset.prod_range_succ' (fun r => w + ((r : ℂ) + 1)) (N + 1)
    have hPw : (∏ r ∈ Finset.range (N + 1), (w + ((r : ℂ) + 1))) * (w + ((N : ℂ) + 1) + 1)
        = ∏ r ∈ Finset.range (N + 1 + 1), (w + ((r : ℂ) + 1)) := by
      rw [hprod]
      congr 1
      push_cast
      ring
    have hQw : (∏ r ∈ Finset.range (N + 1), ((w + 1) + ((r : ℂ) + 1))) * (w + 1)
        = ∏ r ∈ Finset.range (N + 1 + 1), (w + ((r : ℂ) + 1)) := by
      rw [hprod2]
      congr 1
      · apply Finset.prod_congr rfl
        intro r _
        have hcr : (((r + 1 : ℕ)) : ℂ) = (r : ℂ) + 1 := by push_cast; ring
        rw [hcr]
        ring
      · simp
    have eP : (∏ r ∈ Finset.range (N + 1 + 1), (w + ((r : ℂ) + 1)))
          / (∏ r ∈ Finset.range (N + 1), (w + ((r : ℂ) + 1)))
        = w + ((N : ℂ) + 1) + 1 := by
      rw [← hPw]
      exact mul_div_cancel_left₀ _ hPne
    have eQ : (∏ r ∈ Finset.range (N + 1 + 1), (w + ((r : ℂ) + 1)))
          / (∏ r ∈ Finset.range (N + 1), ((w + 1) + ((r : ℂ) + 1)))
        = w + 1 := by
      rw [← hQw]
      exact mul_div_cancel_left₀ _ hQne
    have key : (Nat.factorial N : ℂ) / (∏ r ∈ Finset.range (N + 1), (w + ((r : ℂ) + 1)))
          - (Nat.factorial N : ℂ) / (∏ r ∈ Finset.range (N + 1), ((w + 1) + ((r : ℂ) + 1)))
          = (Nat.factorial (N + 1) : ℂ) /
              (∏ r ∈ Finset.range (N + 1 + 1), (w + ((r : ℂ) + 1))) := by
      rw [eq_div_iff hRne, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
        mul_div_assoc, mul_div_assoc, eP, eQ, Nat.factorial_succ]
      push_cast
      ring
    rw [hsplit, ih w hw, ih (w + 1) hw1]
    exact key

/-- **Closed form of Ramanujan's product series off the poles.** Let $a, b, x, z \in \mathbb{C}$
with $b \neq 0$, let $0 < \varepsilon < \pi$, and put $w = (z + a)/b$. Suppose that $w \neq 0$,
that $-\pi + \varepsilon \le \arg w \le \pi - \varepsilon$, and that $w + r + 1 \neq 0$ for every
natural number $r$. Then Ramanujan's product series $P$ satisfies
$$P(a, b, x; z) = e^{-x} \sum_{m=0}^{\infty} \frac{x^{m+1}}{m!\,(z + a + b(m + 1))}.$$ -/
theorem entry9_P_closed (a b x z w : ℂ) (ε : ℝ)
    (hεpos : 0 < ε) (hεlt : ε < Real.pi)
    (hb : b ≠ 0)
    (h1 : -Real.pi + ε ≤ Complex.arg w) (h2 : Complex.arg w ≤ Real.pi - ε)
    (hwpos : 0 < ‖w‖) (hz : (z + a) / b = w)
    (hw : ∀ r : ℕ, w + ((r : ℂ) + 1) ≠ 0) :
    entry9_P a b x z = Complex.exp (-x) * ∑' (m : ℕ),
      (x ^ (m + 1) / ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))) := by
  have hs : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hεpos hεlt
  have hbw : b * w = z + a := by
    have h := div_mul_cancel₀ (z + a) hb
    rw [hz] at h
    rw [mul_comm b w]
    exact h
  set f : ℕ → ℂ := fun i => (-x) ^ i / (Nat.factorial i : ℂ) with hf
  set g : ℕ → ℂ := fun m => x ^ m / ((Nat.factorial m : ℂ) * (w + ((m : ℂ) + 1))) with hg
  have hfsum : Summable fun i => ‖f i‖ := by
    have h := Real.summable_pow_div_factorial ‖x‖
    refine (summable_congr (fun i => ?_)).mp h
    simp only [hf]
    rw [norm_div, norm_pow, norm_natCast, norm_neg]
  have hbound : Summable fun m : ℕ =>
      (‖x‖ ^ m / (Nat.factorial m : ℝ) * (1 / (Real.sin ε * ‖w‖))) :=
    (Real.summable_pow_div_factorial ‖x‖).mul_right _
  have hgsum : Summable fun m => ‖g m‖ := by
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ hbound
    intro m
    have hden : Real.sin ε * ‖w‖ ≤ ‖w + ((m : ℂ) + 1)‖ := by
      have hcast : ((m : ℂ) + 1) = ((((m : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
      rw [hcast]
      exact sector_add_real_ge w ε hεpos hεlt h1 h2 _ (by positivity)
    have hpos : (0 : ℝ) < Real.sin ε * ‖w‖ := mul_pos hs hwpos
    simp only [hg]
    rw [norm_div, norm_mul, norm_pow, norm_natCast]
    have hle : 1 / ‖w + ((m : ℂ) + 1)‖ ≤ 1 / (Real.sin ε * ‖w‖) :=
      one_div_le_one_div_of_le hpos hden
    calc ‖x‖ ^ m / (↑(Nat.factorial m) * ‖w + (↑m + 1)‖)
        = (‖x‖ ^ m / ↑(Nat.factorial m)) * (1 / ‖w + (↑m + 1)‖) := by
          rw [div_mul_div_comm, mul_one]
      _ ≤ (‖x‖ ^ m / ↑(Nat.factorial m)) * (1 / (Real.sin ε * ‖w‖)) := by
          apply mul_le_mul_of_nonneg_left hle (by positivity)
  have hCauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfsum hgsum
  have hF : (∑' (i : ℕ), f i) = Complex.exp (-x) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (-x : ℂ)
    rw [← Complex.exp_eq_exp_ℂ] at h
    exact h.tsum_eq
  have hN : ∀ N : ℕ, ((-b) ^ N * x ^ (N + 1) / ∏ r ∈ Finset.range (N + 1),
      (z + a + b * ((r : ℂ) + 1)))
      = (x / b) * (∑ k ∈ Finset.range (N + 1), f k * g (N - k)) := by
    intro N
    have hrefl : (∑ k ∈ Finset.range (N + 1), f k * g (N - k))
        = ∑ m ∈ Finset.range (N + 1), f (N - m) * g m := by
      have h := Finset.sum_range_reflect (fun k => f k * g (N - k)) (N + 1)
      have hN11 : ∀ j, N + 1 - 1 - j = N - j := fun j => by omega
      simp only [hN11] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have e2 : N - (N - m) = m := Nat.sub_sub_self hmN
      rw [e2]
    have hterm : ∀ m ∈ Finset.range (N + 1), f (N - m) * g m
        = x ^ N * ((-1 : ℂ) ^ (N - m) /
            ((Nat.factorial (N - m) : ℂ) * ((Nat.factorial m : ℂ) * (w + ((m : ℂ) + 1))))) := by
      intro m hm
      have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have hpow : (-x) ^ (N - m) * x ^ m = x ^ N * (-1 : ℂ) ^ (N - m) := by
        rw [neg_eq_neg_one_mul, mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hmN]
        ring
      simp only [hf, hg]
      rw [div_mul_div_comm, hpow, mul_div_assoc]
    have hTS : ∀ m ∈ Finset.range (N + 1),
        ((-1 : ℂ) ^ (N - m) / ((Nat.factorial (N - m) : ℂ) *
            ((Nat.factorial m : ℂ) * (w + ((m : ℂ) + 1)))))
        = (((-1 : ℂ) ^ N / (Nat.factorial N : ℂ)) *
            (((-1 : ℂ) ^ m * (Nat.choose N m : ℂ)) / (w + ((m : ℂ) + 1)))) := by
      intro m hm
      have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have hsq : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by
        rcases neg_one_pow_eq_or (R := ℂ) m with h | h <;> rw [h] <;> norm_num
      have hsgn : (-1 : ℂ) ^ (N - m) = (-1) ^ N * (-1) ^ m := by
        have he : N = (N - m) + m := (Nat.sub_add_cancel hmN).symm
        have h1 : (-1 : ℂ) ^ N = (-1) ^ (N - m) * (-1) ^ m := by
          conv_lhs => rw [he]
          rw [pow_add]
        calc (-1 : ℂ) ^ (N - m) = (-1) ^ (N - m) * 1 := (mul_one _).symm
          _ = (-1) ^ (N - m) * ((-1) ^ m * (-1) ^ m) := by rw [hsq]
          _ = ((-1) ^ (N - m) * (-1) ^ m) * (-1) ^ m := by ring
          _ = (-1) ^ N * (-1) ^ m := by rw [← h1]
      have hA : ((Nat.factorial (N - m) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hB : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfN : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hD1 : ((Nat.factorial (N - m) : ℕ) : ℂ) *
          (((Nat.factorial m : ℕ) : ℂ) * (w + ((m : ℂ) + 1))) ≠ 0 :=
        mul_ne_zero hA (mul_ne_zero hB (hw m))
      have hD2 : ((Nat.factorial N : ℕ) : ℂ) * (w + ((m : ℂ) + 1)) ≠ 0 :=
        mul_ne_zero hfN (hw m)
      have hch2 : (Nat.choose N m : ℂ) * ((Nat.factorial m : ℕ) : ℂ) *
          ((Nat.factorial (N - m) : ℕ) : ℂ)
          = ((Nat.factorial N : ℕ) : ℂ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmN
      rw [hsgn, div_mul_div_comm, div_eq_div_iff hD1 hD2]
      linear_combination (-((-1 : ℂ) ^ N * (-1 : ℂ) ^ m * (w + ((m : ℂ) + 1)))) * hch2
    have hsumS : (∑ m ∈ Finset.range (N + 1),
        ((-1 : ℂ) ^ (N - m) / ((Nat.factorial (N - m) : ℂ) *
            ((Nat.factorial m : ℂ) * (w + ((m : ℂ) + 1))))))
        = (((-1 : ℂ) ^ N / (Nat.factorial N : ℂ))) *
            (∑ m ∈ Finset.range (N + 1), (((-1 : ℂ) ^ m * (Nat.choose N m : ℂ)) /
                (w + ((m : ℂ) + 1)))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m hm => hTS m hm)
    have hsumT : (∑ m ∈ Finset.range (N + 1), f (N - m) * g m)
        = x ^ N * (((-1 : ℂ) ^ N / (Nat.factorial N : ℂ)) *
            (∑ m ∈ Finset.range (N + 1), (((-1 : ℂ) ^ m * (Nat.choose N m : ℂ)) /
                (w + ((m : ℂ) + 1))))) := by
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsumS]
    have hPz : ∏ r ∈ Finset.range (N + 1), (z + a + b * ((r : ℂ) + 1))
        = b ^ (N + 1) * ∏ r ∈ Finset.range (N + 1), (w + ((r : ℂ) + 1)) := by
      have hfac : ∀ r ∈ Finset.range (N + 1), z + a + b * ((r : ℂ) + 1) = b *
          (w + ((r : ℂ) + 1)) := by
        intro r _
        rw [← hbw]
        ring
      rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hProdNe : ∏ r ∈ Finset.range (N + 1), (w + ((r : ℂ) + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun r _ => hw r)
    have hbB : b ^ (N + 1) ≠ 0 := pow_ne_zero _ hb
    have hfN : ((Nat.factorial N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hnb : (-b : ℂ) ^ N = (-1) ^ N * b ^ N := by
      rw [show (-b : ℂ) = -1 * b from by ring, mul_pow]
    rw [hrefl, hsumT, partial_fraction N w hw, hPz, hnb]
    field_simp
    ring
  have hPeq : entry9_P a b x z = ∑' (N : ℕ),
      ((x / b) * (∑ k ∈ Finset.range (N + 1), f k * g (N - k))) :=
    tsum_congr hN
  have hG : (x / b) * (∑' (m : ℕ), g m) = ∑' (m : ℕ),
      (x ^ (m + 1) / ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))) := by
    have hBm : ∀ m : ℕ, ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := fun m => by
      exact_mod_cast Nat.factorial_ne_zero _
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    have hbw2 : z + (a + b * ((m : ℂ) + 1)) = b * (w + ((m : ℂ) + 1)) := by
      linear_combination -hbw
    have hwm : (w + ((m : ℂ) + 1)) ≠ 0 := hw m
    have hBm' : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := hBm m
    simp only [hg]
    rw [hbw2, pow_succ']
    field_simp
  rw [hPeq, tsum_mul_left, ← hCauchy, hF, mul_left_comm, hG]

private lemma K_summable (a b x : ℂ) (n : ℕ) :
    Summable fun m : ℕ => (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) /
        (Nat.factorial m : ℝ)) := by
  have hYsum : Summable (fun m : ℕ => (2 ^ (n + 1) * ‖x‖) ^ m / (Nat.factorial m : ℝ)) :=
    Real.summable_pow_div_factorial (2 ^ (n + 1) * ‖x‖)
  have hCsum : Summable (fun m : ℕ => (‖a‖ + ‖b‖) ^ (n + 1) * 2 ^ (n + 1) * ‖x‖ *
      ((2 ^ (n + 1) * ‖x‖) ^ m / (Nat.factorial m : ℝ))) :=
    hYsum.mul_left _
  apply Summable.of_nonneg_of_le (fun m => by positivity) _ hCsum
  intro m
  have hfact_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hnorm1 : ‖((m : ℂ) + 1)‖ = (((m + 1 : ℕ)) : ℝ) := by
    have h : ((m : ℂ) + 1) = (((m + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [h, norm_natCast]
  have hP : ‖a + b * ((m : ℂ) + 1)‖ ≤ (‖a‖ + ‖b‖) * ((((m + 1 : ℕ))) : ℝ) := by
    have h := norm_add_le a (b * ((m : ℂ) + 1))
    rw [norm_mul, hnorm1] at h
    have hk1 : (1 : ℝ) ≤ ((((m + 1 : ℕ))) : ℝ) := by
      have h1n : (1 : ℕ) ≤ m + 1 := Nat.le_add_left 1 m
      exact_mod_cast h1n
    have hAle : ‖a‖ ≤ ‖a‖ * ((((m + 1 : ℕ))) : ℝ) :=
      le_mul_of_one_le_right (norm_nonneg _) hk1
    calc ‖a + b * ((m : ℂ) + 1)‖ ≤ ‖a‖ + ‖b‖ * ((((m + 1 : ℕ))) : ℝ) := h
      _ ≤ ‖a‖ * ((((m + 1 : ℕ))) : ℝ) + ‖b‖ * ((((m + 1 : ℕ))) : ℝ) := by linarith
      _ = (‖a‖ + ‖b‖) * ((((m + 1 : ℕ))) : ℝ) := by ring
  have hNatLe : m + 1 ≤ 2 ^ (m + 1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hRealLe : ((((m + 1 : ℕ))) : ℝ) ≤ (((2 ^ (m + 1) : ℕ)) : ℝ) := by exact_mod_cast hNatLe
  have h2cast : (((2 ^ (m + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (m + 1) := by push_cast; ring
  have hpoly : ((((m + 1 : ℕ))) : ℝ) ^ (n + 1) ≤ ((2 : ℝ) ^ (m + 1)) ^ (n + 1) := by
    rw [← h2cast]
    exact pow_le_pow_left₀ (by positivity) hRealLe (n + 1)
  have h2eq : ((2 : ℝ) ^ (m + 1)) ^ (n + 1) = (2 ^ (n + 1)) ^ (m + 1) := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hPn : ‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) ≤ (‖a‖ + ‖b‖) ^ (n + 1) * (2 ^ (n + 1)) ^
      (m + 1) := by
    calc ‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) ≤ ((‖a‖ + ‖b‖) * ((((m + 1 : ℕ))) : ℝ)) ^ (n + 1) :=
          pow_le_pow_left₀ (norm_nonneg _) hP (n + 1)
      _ = (‖a‖ + ‖b‖) ^ (n + 1) * ((((m + 1 : ℕ))) : ℝ) ^ (n + 1) := by rw [mul_pow]
      _ ≤ (‖a‖ + ‖b‖) ^ (n + 1) * (((2 : ℝ) ^ (m + 1)) ^ (n + 1)) := by
          apply mul_le_mul_of_nonneg_left hpoly (pow_nonneg (by positivity) (n + 1))
      _ = (‖a‖ + ‖b‖) ^ (n + 1) * (2 ^ (n + 1)) ^ (m + 1) := by rw [h2eq]
  have h2succ : (2 ^ (n + 1) : ℝ) ^ (m + 1) = 2 ^ (n + 1) * (2 ^ (n + 1)) ^ m := pow_succ' _ _
  have hXsucc : ‖x‖ ^ (m + 1) = ‖x‖ * ‖x‖ ^ m := pow_succ' _ _
  calc ‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ)
      ≤ ((‖a‖ + ‖b‖) ^ (n + 1) * (2 ^ (n + 1)) ^ (m + 1)) * ‖x‖ ^ (m + 1) /
          (Nat.factorial m : ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hfact_pos)
        exact mul_le_mul_of_nonneg_right hPn (pow_nonneg (norm_nonneg _) _)
    _ = (‖a‖ + ‖b‖) ^ (n + 1) * 2 ^ (n + 1) * ‖x‖ *
        ((2 ^ (n + 1) * ‖x‖) ^ m / (Nat.factorial m : ℝ)) := by
        rw [h2succ, hXsucc, mul_pow]
        ring

private lemma geom_remainder (c z : ℂ) (n : ℕ) (hzne : z ≠ 0) (hzc : z + c ≠ 0) :
    (∑ k ∈ Finset.range (n + 1), (-c) ^ k / z ^ (k + 1)) - 1 / (z + c)
      = -(((-c) ^ (n + 1)) / (z ^ (n + 1) * (z + c))) := by
  have hu : (-c) / z ≠ 1 := by
    intro hcon
    have h3 := div_mul_cancel₀ (-c) hzne
    rw [hcon] at h3
    have h0 : z + c = 0 := by linear_combination h3
    exact hzc h0
  have hu1 : (-c) / z - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hgeom := geom_sum_mul ((-c) / z) (n + 1)
  have hS : (∑ i ∈ Finset.range (n + 1), ((-c) / z) ^ i) = (((-c) / z) ^ (n + 1) - 1) /
      (((-c) / z) - 1) := by
    rw [eq_div_iff hu1]
    exact hgeom
  have hterm : ∀ k ∈ Finset.range (n + 1), (-c) ^ k / z ^ (k + 1) = (1 / z) * (((-c) / z) ^ k) := by
    intro k _
    rw [div_pow, div_mul_div_comm, one_mul, pow_succ']
  have hcomb : (∑ k ∈ Finset.range (n + 1), (-c) ^ k / z ^ (k + 1))
      = (1 / z) * ((((-c) / z) ^ (n + 1) - 1) / (((-c) / z) - 1)) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hS]
  have hu1z : (((-c) / z) - 1) = -(z + c) / z := by
    field_simp
    ring
  have hzN : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hzne
  rw [hcomb, hu1z, div_pow]
  field_simp
  ring

private lemma diff_identity (a b x z w : ℂ) (ε : ℝ) (n : ℕ)
    (hεpos : 0 < ε) (hεlt : ε < Real.pi) (hb : b ≠ 0)
    (h1 : -Real.pi + ε ≤ Complex.arg w) (h2 : Complex.arg w ≤ Real.pi - ε)
    (hwpos : 0 < ‖w‖) (hz : (z + a) / b = w)
    (hw : ∀ r : ℕ, w + ((r : ℂ) + 1) ≠ 0) (hzne : z ≠ 0) :
    (Finset.sum (Finset.range (n + 1))
        (fun k => ((-1 : ℂ) ^ k * generalizedBellGenerating a b x k) / z ^ (k + 1)) - entry9_P a b x
            z)
      = -Complex.exp (-x) * (∑' (m : ℕ),
          (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
              ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))))) / z ^ (n + 1) := by
  have hs : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hεpos hεlt
  have hbw : b * w = z + a := by
    have h := div_mul_cancel₀ (z + a) hb
    rw [hz] at h
    rw [mul_comm b w]
    exact h
  have hzc : ∀ m : ℕ, z + (a + b * ((m : ℂ) + 1)) ≠ 0 := by
    intro m
    have h : z + (a + b * ((m : ℂ) + 1)) = b * (w + ((m : ℂ) + 1)) := by
      linear_combination -hbw
    rw [h]
    exact mul_ne_zero hb (hw m)
  set bell : ℕ → ℕ → ℂ := fun k m =>
      ((a + b * (↑(m + 1) : ℂ)) ^ k * x ^ (m + 1) / (↑(Nat.factorial m) : ℂ)) with hbell
  have hFk : ∀ k, generalizedBellGenerating a b x k = Complex.exp (-x) * (∑' (m : ℕ), bell k m) :=
      fun k => rfl
  have hlanded : ∀ k, HasSum (bell k ·) (Complex.exp x * generalizedBellGenerating a b x k) :=
    fun k => ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining a b x k
  have hSbell : ∀ k, Summable (bell k ·) := fun k => (hlanded k).summable
  have hk : ∀ k ∈ Finset.range (n + 1),
      (((-1 : ℂ) ^ k * generalizedBellGenerating a b x k / z ^ (k + 1)))
      = Complex.exp (-x) * (∑' (m : ℕ), (((-1 : ℂ) ^ k / z ^ (k + 1)) * bell k m)) := by
    intro k _
    rw [hFk k, tsum_mul_left]
    ring
  have hswap : (Finset.sum (Finset.range (n + 1))
      (fun k => (((-1 : ℂ) ^ k * generalizedBellGenerating a b x k / z ^ (k + 1)))))
      = Complex.exp (-x) * (∑' (m : ℕ),
          (∑ k ∈ Finset.range (n + 1), (((-1 : ℂ) ^ k / z ^ (k + 1)) * bell k m))) := by
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum]
    congr 1
    exact (Summable.tsum_finsetSum (fun k _ => ((hSbell k).mul_left _))).symm
  set g : ℕ → ℂ := fun m => x ^ m / ((Nat.factorial m : ℂ) * (w + ((m : ℂ) + 1))) with hg
  have hbound : Summable fun m : ℕ =>
      (‖x‖ ^ m / (Nat.factorial m : ℝ) * (1 / (Real.sin ε * ‖w‖))) :=
    (Real.summable_pow_div_factorial ‖x‖).mul_right _
  have hSg : Summable g := by
    have hgnorm : Summable fun m => ‖g m‖ := by
      apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ hbound
      intro m
      have hden : Real.sin ε * ‖w‖ ≤ ‖w + ((m : ℂ) + 1)‖ := by
        have hcast : ((m : ℂ) + 1) = ((((m : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
        rw [hcast]
        exact sector_add_real_ge w ε hεpos hεlt h1 h2 _ (by positivity)
      have hpos : (0 : ℝ) < Real.sin ε * ‖w‖ := mul_pos hs hwpos
      simp only [hg]
      rw [norm_div, norm_mul, norm_pow, norm_natCast]
      have hle : 1 / ‖w + ((m : ℂ) + 1)‖ ≤ 1 / (Real.sin ε * ‖w‖) :=
        one_div_le_one_div_of_le hpos hden
      calc ‖x‖ ^ m / (↑(Nat.factorial m) * ‖w + (↑m + 1)‖)
          = (‖x‖ ^ m / ↑(Nat.factorial m)) * (1 / ‖w + (↑m + 1)‖) := by
            rw [div_mul_div_comm, mul_one]
        _ ≤ (‖x‖ ^ m / ↑(Nat.factorial m)) * (1 / (Real.sin ε * ‖w‖)) := by
            apply mul_le_mul_of_nonneg_left hle (by positivity)
    exact Summable.of_norm_bounded hgnorm (fun m => le_refl _)
  have hSclosed : Summable (fun (m : ℕ) =>
      (x ^ (m + 1) / ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))))) := by
    have h := hSg.mul_left (x / b)
    refine (summable_congr (fun m => ?_)).mpr h
    have hbw2 : z + (a + b * ((m : ℂ) + 1)) = b * (w + ((m : ℂ) + 1)) := by
      linear_combination -hbw
    have hwm : (w + ((m : ℂ) + 1)) ≠ 0 := hw m
    have hBm' : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    simp only [hg]
    rw [hbw2, pow_succ']
    field_simp
  have hSinner : Summable (fun m =>
      (∑ k ∈ Finset.range (n + 1), (((-1 : ℂ) ^ k / z ^ (k + 1)) * bell k m))) :=
    summable_sum (fun k _ => ((hSbell k).mul_left _))
  have hper : ∀ m : ℕ, (∑ k ∈ Finset.range (n + 1), (((-1 : ℂ) ^ k / z ^ (k + 1)) * bell k m))
      - (x ^ (m + 1) / ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))))
      = -((x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
          ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))))) / z ^ (n + 1) := by
    intro m
    have hcastm : (((m + 1 : ℕ)) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    have hcm : a + b * (((m + 1 : ℕ)) : ℂ) = a + b * ((m : ℂ) + 1) := by rw [hcastm]
    have hfac : (∑ k ∈ Finset.range (n + 1), (((-1 : ℂ) ^ k / z ^ (k + 1)) * bell k m))
        = (x ^ (m + 1) / (Nat.factorial m : ℂ)) *
            (∑ k ∈ Finset.range (n + 1), (-(a + b * (((m + 1 : ℕ)) : ℂ))) ^ k / z ^ (k + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [hbell]
      rw [show (-(a + b * (((m + 1 : ℕ)) : ℂ)) : ℂ) = -1 * (a + b * (((m + 1 : ℕ)) : ℂ))
          from by ring, mul_pow]
      ring
    have hfactm : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hzN : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hzne
    have hzc_m : z + (a + b * ((m : ℂ) + 1)) ≠ 0 := hzc m
    rw [hfac, hcm]
    have hrm := geom_remainder (a + b * ((m : ℂ) + 1)) z n hzne (hzc m)
    have hstep : (x ^ (m + 1) / (Nat.factorial m : ℂ)) *
        (∑ k ∈ Finset.range (n + 1), (-(a + b * ((m : ℂ) + 1))) ^ k / z ^ (k + 1))
        - x ^ (m + 1) / ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))
        = (x ^ (m + 1) / (Nat.factorial m : ℂ)) *
            ((∑ k ∈ Finset.range (n + 1), (-(a + b * ((m : ℂ) + 1))) ^ k / z ^ (k + 1)) - 1 /
                (z + (a + b * ((m : ℂ) + 1)))) := by
      rw [mul_sub, div_mul_div_comm, mul_one]
    rw [hstep, hrm]
    field_simp
  have hdiff : (∑' (m : ℕ), (∑ k ∈ Finset.range (n + 1), (((-1 : ℂ) ^ k / z ^ (k + 1)) * bell k m)))
      - (∑' (m : ℕ), (x ^ (m + 1) / ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))))
      = -((∑' (m : ℕ), (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
          ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))))) / z ^ (n + 1) := by
    rw [← Summable.tsum_sub hSinner hSclosed, tsum_congr (fun m => hper m)]
    have hTform : ∀ m : ℕ, (-((x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
        ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))))) / z ^ (n + 1))
        = (-1 / z ^ (n + 1)) * ((x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
            ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))))) := fun m => by
      ring
    rw [tsum_congr hTform, tsum_mul_left]
    ring
  have hPform := entry9_P_closed a b x z w ε hεpos hεlt hb h1 h2 hwpos hz hw
  rw [hswap, hPform, ← mul_sub, hdiff]
  ring

private lemma final_bound (a b x z w : ℂ) (ε : ℝ) (n : ℕ)
    (hεpos : 0 < ε) (hεlt : ε < Real.pi) (hb : b ≠ 0)
    (h1 : -Real.pi + ε ≤ Complex.arg w) (h2 : Complex.arg w ≤ Real.pi - ε)
    (hWa : ‖a‖ / ‖b‖ + 1 ≤ ‖w‖) (hW1 : 1 ≤ ‖w‖) (hz : (z + a) / b = w) :
    ‖(Finset.sum (Finset.range (n + 1))
        (fun k => ((-1 : ℂ) ^ k * generalizedBellGenerating a b x k) / z ^ (k + 1)) - entry9_P a b x
            z)‖
      ≤ (2 * ‖Complex.exp (-x)‖ * (∑' (m : ℕ),
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ))) / Real.sin ε)
              * ‖(1 : ℂ) / z ^ (n + 2)‖ := by
  have hs : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hεpos hεlt
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le one_pos hW1
  have hw : ∀ r : ℕ, w + ((r : ℂ) + 1) ≠ 0 := by
    intro r
    have hle : Real.sin ε * ‖w‖ ≤ ‖w + ((r : ℂ) + 1)‖ := by
      have hcast : ((r : ℂ) + 1) = ((((r : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
      rw [hcast]
      exact sector_add_real_ge w ε hεpos hεlt h1 h2 _ (by positivity)
    have hpos : 0 < ‖w + ((r : ℂ) + 1)‖ := lt_of_lt_of_le (mul_pos hs hwpos) hle
    exact norm_pos_iff.mp hpos
  have hbw : b * w = z + a := by
    have h := div_mul_cancel₀ (z + a) hb
    rw [hz] at h
    rw [mul_comm b w]
    exact h
  have hzaw : z + a = w * b := (div_eq_iff hb).mp hz
  have hzeq : z = w * b - a := by linear_combination hzaw
  have h1z : ‖w * b‖ ≤ ‖z‖ + ‖a‖ := by
    have h := norm_add_le z a
    rw [hzaw] at h
    exact h
  have h2z : ‖a‖ + ‖b‖ ≤ ‖w * b‖ := by
    have h3 : (‖a‖ / ‖b‖ + 1) * ‖b‖ ≤ ‖w‖ * ‖b‖ :=
      mul_le_mul_of_nonneg_right hWa (le_of_lt hbn)
    have h4 : (‖a‖ / ‖b‖ + 1) * ‖b‖ = ‖a‖ + ‖b‖ := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hbn), one_mul]
    rw [norm_mul]
    linarith [h3, h4]
  have hzpos : 0 < ‖z‖ := by
    have h4z : ‖b‖ ≤ ‖z‖ := by linarith [h2z, h1z]
    exact lt_of_lt_of_le hbn h4z
  have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
  have hzub : ‖z‖ ≤ 2 * ‖b‖ * ‖w‖ := by
    have h1u : ‖z‖ ≤ ‖w * b‖ + ‖a‖ := by
      rw [hzeq]
      exact norm_sub_le _ _
    have h2u : ‖a‖ ≤ ‖b‖ * ‖w‖ := by
      have h3 : ‖a‖ / ‖b‖ ≤ ‖w‖ := by linarith [hWa]
      calc ‖a‖ ≤ ‖w‖ * ‖b‖ := (div_le_iff₀ hbn).mp h3
        _ = ‖b‖ * ‖w‖ := mul_comm _ _
    calc ‖z‖ ≤ ‖w * b‖ + ‖a‖ := h1u
      _ ≤ ‖w‖ * ‖b‖ + ‖b‖ * ‖w‖ := by
        rw [norm_mul]
        linear_combination h2u
      _ = 2 * ‖b‖ * ‖w‖ := by ring
  have hW : (1 : ℝ) / ‖w‖ ≤ 2 * ‖b‖ / ‖z‖ := by
    rw [div_le_iff₀ hwpos, show (2 * ‖b‖ / ‖z‖) * ‖w‖ = (2 * ‖b‖ * ‖w‖) / ‖z‖
        from by ring, le_div_iff₀ hzpos]
    linarith [hzub]
  have hdiff := diff_identity a b x z w ε n hεpos hεlt hb h1 h2 hwpos hz hw hzne
  have hK := K_summable a b x n
  have bound_m : ∀ m : ℕ, ‖(x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
      ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))))‖
      ≤ (1 / (‖b‖ * Real.sin ε * ‖w‖)) *
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ)) := by
    intro m
    have hform : z + (a + b * ((m : ℂ) + 1)) = b * (w + ((m : ℂ) + 1)) := by
      linear_combination -hbw
    have hcast : ((m : ℂ) + 1) = ((((m : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
    have hsec := sector_add_real_ge w ε hεpos hεlt h1 h2 ((m : ℝ) + 1) (by positivity)
    rw [← hcast] at hsec
    have hden : ‖b‖ * Real.sin ε * ‖w‖ ≤ ‖z + (a + b * ((m : ℂ) + 1))‖ := by
      rw [hform, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left hsec (norm_nonneg _)
    have hpos : (0 : ℝ) < ‖b‖ * Real.sin ε * ‖w‖ := mul_pos (mul_pos hbn hs) hwpos
    have hSnn : (0 : ℝ) ≤ ‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) /
        (Nat.factorial m : ℝ) := by
      positivity
    have eTm : ‖x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
        ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))‖
        = (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ)) *
            (1 / ‖z + (a + b * ((m : ℂ) + 1))‖) := by
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_natCast]
      ring
    calc ‖x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
        ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1))))‖
        = (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ)) *
            (1 / ‖z + (a + b * ((m : ℂ) + 1))‖) := eTm
      _ ≤ (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ)) *
          (1 / (‖b‖ * Real.sin ε * ‖w‖)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hden) hSnn
      _ = (1 / (‖b‖ * Real.sin ε * ‖w‖)) *
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ)) := by
          ring
  have hSTnorm : Summable (fun (m : ℕ) =>
      ‖(x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
          ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => bound_m m) (hK.mul_left _)
  have hR : ‖∑' (m : ℕ), (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
      ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖
      ≤ (1 / (‖b‖ * Real.sin ε * ‖w‖)) *
          (∑' (m : ℕ), (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) /
              (Nat.factorial m : ℝ))) := by
    calc ‖∑' (m : ℕ), (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
        ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖
        ≤ ∑' (m : ℕ), ‖(x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
            ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖ :=
          norm_tsum_le_tsum_norm hSTnorm
      _ ≤ ∑' (m : ℕ), ((1 / (‖b‖ * Real.sin ε * ‖w‖)) *
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ))) :=
          Summable.tsum_le_tsum (fun m => bound_m m) hSTnorm (hK.mul_left _)
      _ = (1 / (‖b‖ * Real.sin ε * ‖w‖)) *
          (∑' (m : ℕ), (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) /
              (Nat.factorial m : ℝ))) :=
          tsum_mul_left
  have hfrac : 1 / (‖b‖ * Real.sin ε * ‖w‖) ≤ 2 / (Real.sin ε * ‖z‖) := by
    calc 1 / (‖b‖ * Real.sin ε * ‖w‖) = (1 / (‖b‖ * Real.sin ε)) * (1 / ‖w‖) := by ring
      _ ≤ (1 / (‖b‖ * Real.sin ε)) * (2 * ‖b‖ / ‖z‖) := by
          apply mul_le_mul_of_nonneg_left hW (le_of_lt (one_div_pos.mpr (mul_pos hbn hs)))
      _ = 2 / (Real.sin ε * ‖z‖) := by
          have hbe : (‖b‖ : ℝ) ≠ 0 := ne_of_gt hbn
          have hse : Real.sin ε ≠ 0 := ne_of_gt hs
          have hze : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hzpos
          field_simp
  have hR2 : ‖∑' (m : ℕ), (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
      ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖
      ≤ (2 / (Real.sin ε * ‖z‖)) * (∑' (m : ℕ),
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ))) := by
    calc ‖∑' (m : ℕ), (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
        ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖
        ≤ (1 / (‖b‖ * Real.sin ε * ‖w‖)) *
            (∑' (m : ℕ), (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) /
                (Nat.factorial m : ℝ))) := hR
      _ ≤ (2 / (Real.sin ε * ‖z‖)) * (∑' (m : ℕ),
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ))) :=
          mul_le_mul_of_nonneg_right hfrac (tsum_nonneg (fun m => by positivity))
  have hdiff_eq : ‖(Finset.sum (Finset.range (n + 1))
      (fun k => ((-1 : ℂ) ^ k * generalizedBellGenerating a b x k) / z ^ (k + 1)) - entry9_P a b x
          z)‖
      = ‖Complex.exp (-x)‖ * ‖∑' (m : ℕ),
          (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
              ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖ / ‖z‖ ^ (n + 1) := by
    rw [hdiff, norm_div, norm_mul, norm_neg, norm_pow]
  have hgnorm : ‖(1 : ℂ) / z ^ (n + 2)‖ = 1 / ‖z‖ ^ (n + 2) := by
    rw [norm_div, norm_one, norm_pow]
  have hfin : ‖Complex.exp (-x)‖ * ‖∑' (m : ℕ),
      (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
          ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖ / ‖z‖ ^ (n + 1)
      ≤ (2 * ‖Complex.exp (-x)‖ * (∑' (m : ℕ),
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ))) / Real.sin ε)
              * (1 / ‖z‖ ^ (n + 2)) := by
    calc ‖Complex.exp (-x)‖ * ‖∑' (m : ℕ),
        (x ^ (m + 1) * (-(a + b * ((m : ℂ) + 1))) ^ (n + 1) /
            ((Nat.factorial m : ℂ) * (z + (a + b * ((m : ℂ) + 1)))) )‖ / ‖z‖ ^ (n + 1)
        ≤ ‖Complex.exp (-x)‖ * ((2 / (Real.sin ε * ‖z‖)) *
            (∑' (m : ℕ), (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) /
                (Nat.factorial m : ℝ)))) / ‖z‖ ^ (n + 1) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt (pow_pos hzpos _))
          exact mul_le_mul_of_nonneg_left hR2 (norm_nonneg _)
      _ = (2 * ‖Complex.exp (-x)‖ * (∑' (m : ℕ),
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ))) / Real.sin ε)
              * (1 / ‖z‖ ^ (n + 2)) := by
          have hn2 : n + 2 = (n + 1) + 1 := by omega
          have hse : Real.sin ε ≠ 0 := ne_of_gt hs
          have hze : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hzpos
          have hzN : (‖z‖ : ℝ) ^ (n + 1) ≠ 0 := ne_of_gt (pow_pos hzpos _)
          rw [hn2, pow_succ' _ (n + 1)]
          field_simp
  rw [hdiff_eq, hgnorm]
  exact hfin

/-- **Asymptotic expansion of Ramanujan's product series.** Let $a, b, x \in \mathbb{C}$ with
$b \neq 0$, let $0 < \varepsilon < \pi$, and let $n$ be a natural number. Write $F(a, b, x; k)$
for Ramanujan's generalized Bell function and $P(a, b, x; z)$ for Ramanujan's product series.
Then
$$P(a, b, x; z) = \sum_{k=0}^{n} \frac{(-1)^k F(a, b, x; k)}{z^{k+1}} + O(|z|^{-n-2})$$
as $|(z + a)/b| \to \infty$ with $-\pi + \varepsilon \le \arg((z + a)/b) \le \pi - \varepsilon$:
there are real numbers $C$ and $R$ such that the difference of the two sides has absolute value
at most $C / |z|^{n+2}$ for every complex $z$ with $|(z + a)/b| \ge R$ and
$-\pi + \varepsilon \le \arg((z + a)/b) \le \pi - \varepsilon$.

Proves `Wanted` entry `ramanujan_part1_ch3_entry9_odd`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 9(i), definitions printed
    p. 53 / PDF p. 63 and result printed p. 54 / PDF p. 64.
-/
theorem ramanujan_part1_ch3_entry9_odd (a b x : ℂ)
    (hb : b ≠ 0) (ε : ℝ) (hεpos : 0 < ε) (hεlt : ε < Real.pi) (n : ℕ) :
    Asymptotics.IsBigO
      (Filter.comap (fun z : ℂ => (z + a) / b)
        (Filter.cocompact ℂ ⊓ Filter.principal {w : ℂ | -Real.pi + ε ≤ Complex.arg w ∧
            Complex.arg w ≤ Real.pi - ε}))
      (fun z : ℂ =>
          (Finset.sum (Finset.range (n + 1))
              (fun k => ((-1 : ℂ) ^ k * generalizedBellGenerating a b x k) / z ^ (k + 1)) -
            entry9_P a b x z))
      (fun z : ℂ => (1 : ℂ) / z ^ (n + 2)) := by
  have hcoc : ∀ᶠ w : ℂ in Filter.cocompact ℂ, max (‖a‖ / ‖b‖ + 1) 1 ≤ ‖w‖ :=
    tendsto_norm_cocompact_atTop.eventually
      (Filter.eventually_ge_atTop (max (‖a‖ / ‖b‖ + 1) 1))
  refine Asymptotics.IsBigO.of_bound
      (2 * ‖Complex.exp (-x)‖ * (∑' (m : ℕ),
          (‖a + b * ((m : ℂ) + 1)‖ ^ (n + 1) * ‖x‖ ^ (m + 1) / (Nat.factorial m : ℝ))) / Real.sin ε)
              ?_
  rw [Filter.eventually_comap, Filter.eventually_inf_principal]
  filter_upwards [hcoc] with w hwR hsec z hz
  have hWa : ‖a‖ / ‖b‖ + 1 ≤ ‖w‖ := le_trans (le_max_left _ _) hwR
  have hW1 : 1 ≤ ‖w‖ := le_trans (le_max_right _ _) hwR
  obtain ⟨h1, h2⟩ := hsec
  exact final_bound a b x z w ε n hεpos hεlt hb h1 h2 hWa hW1 hz

end Entry9Odd
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
