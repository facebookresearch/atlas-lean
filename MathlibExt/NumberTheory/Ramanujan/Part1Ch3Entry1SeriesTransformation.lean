/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 1

Series transformation relates Q-weighted Taylor coefficients at 0, 1.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry1SeriesTransformation

private lemma iterDeriv_comp_fun (j k : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv k (iteratedDeriv j f) = iteratedDeriv (j + k) f := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      have hAdd : j + k + 1 = j + (k + 1) := by omega
      rw [iteratedDeriv_succ, ih, ← iteratedDeriv_succ, hAdd]

private lemma analytic_diffIter (R₁ : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁)) (j : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv j f) (Metric.ball (0 : ℂ) R₁) := by
  have hU : UniqueDiffOn ℂ (Metric.ball (0 : ℂ) R₁) := Metric.isOpen_ball.uniqueDiffOn
  have hC : ContDiffOn ℂ (⊤ : WithTop ℕ∞) f (Metric.ball (0 : ℂ) R₁) := hf.contDiffOn hU
  have hDw : DifferentiableOn ℂ (iteratedDerivWithin j f (Metric.ball (0 : ℂ) R₁))
      (Metric.ball (0 : ℂ) R₁) :=
    hC.differentiableOn_iteratedDerivWithin (by simp) hU
  refine hDw.congr (fun x hx => ?_)
  exact (iteratedDerivWithin_eq_iteratedDeriv hU
    ((hC.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le le_top) hx).symm

private lemma rowHasSum (R₁ : ℝ) (hR₁ : 1 < R₁) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁)) (Q : ℕ → ℂ) (j : ℕ) :
    HasSum (fun k : ℕ => Q j * iteratedDeriv (j + k) f 0 / (Nat.factorial k : ℂ))
      (Q j * iteratedDeriv j f 1) := by
  have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R₁ := by
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    exact hR₁
  have hT := Complex.hasSum_taylorSeries_on_ball (analytic_diffIter R₁ f hf j) h1mem
  have hEq : ∀ k : ℕ, Q j * (((Nat.factorial k : ℂ))⁻¹ • ((1 : ℂ) - 0) ^ k •
      iteratedDeriv k (iteratedDeriv j f) 0)
      = Q j * iteratedDeriv (j + k) f 0 / (Nat.factorial k : ℂ) := by
    intro k
    have hdk : iteratedDeriv k (iteratedDeriv j f) 0 = iteratedDeriv (j + k) f 0 :=
      congrFun (iterDeriv_comp_fun j k f) 0
    rw [hdk]
    simp only [sub_zero, one_pow, smul_eq_mul, one_mul]
    ring
  exact (hT.mul_left (Q j)).congr_fun (fun k => (hEq k).symm)

private def fibEquiv (n : ℕ) : Fin (n + 1) ≃ {p : ℕ × ℕ // p.1 + p.2 = n} where
  toFun j := ⟨(j.val, n - j.val), by have hj := j.2; show j.val + (n - j.val) = n; omega⟩
  invFun q := ⟨q.val.1, by have hq := q.property; omega⟩
  left_inv j := by
    obtain ⟨jv, hj⟩ := j
    rfl
  right_inv q := by
    obtain ⟨⟨j, k⟩, hk⟩ := q
    have hk' : j + k = n := hk
    apply Subtype.ext
    show (j, n - j) = (j, k)
    rw [Prod.mk.injEq]
    exact ⟨rfl, by omega⟩

private lemma fibSum_eq (Q : ℕ → ℂ) (f : ℂ → ℂ) (n : ℕ) :
    (∑' q : {p : ℕ × ℕ // p.1 + p.2 = n},
      Q q.val.1 * iteratedDeriv (q.val.1 + q.val.2) f 0 / (Nat.factorial q.val.2 : ℂ))
    = (∑ j ∈ Finset.range (n + 1), Q j / (Nat.factorial (n - j) : ℂ)) *
      iteratedDeriv n f 0 := by
  have hStep1 : (∑' q : {p : ℕ × ℕ // p.1 + p.2 = n},
      Q q.val.1 * iteratedDeriv (q.val.1 + q.val.2) f 0 / (Nat.factorial q.val.2 : ℂ))
      = ∑ x : Fin (n + 1), Q x.val * iteratedDeriv (x.val + (n - x.val)) f 0 /
        (Nat.factorial (n - x.val) : ℂ) := by
    have hTs := (fibEquiv n).tsum_eq (fun q : {p : ℕ × ℕ // p.1 + p.2 = n} =>
      Q q.val.1 * iteratedDeriv (q.val.1 + q.val.2) f 0 / (Nat.factorial q.val.2 : ℂ))
    rw [tsum_fintype] at hTs
    rw [← hTs]
    apply Finset.sum_congr rfl
    intro x _
    rfl
  rw [hStep1, Fin.sum_univ_eq_sum_range (fun j => Q j * iteratedDeriv (j + (n - j)) f 0 /
    (Nat.factorial (n - j) : ℂ)) (n + 1), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := by
    have hmem := Finset.mem_range.mp hj
    omega
  have hjn : j + (n - j) = n := Nat.add_sub_cancel' hjle
  rw [hjn]
  ring

/-- **Ramanujan's series transformation without the radius hypothesis.** Let $R_1 > 1$, let
$f : \mathbb{C} \to \mathbb{C}$ be analytic on the open disc $|z| < R_1$, and let
$Q_0, Q_1, Q_2, \ldots$ be complex numbers such that the double series
$$\sum_{j, m \ge 0} \frac{Q_j\, f^{(j+m)}(0)}{m!}$$
is absolutely summable. Then the series
$$\sum_{n=0}^{\infty} \Bigl(\sum_{j=0}^{n} \frac{Q_j}{(n-j)!}\Bigr) f^{(n)}(0)$$
and
$$\sum_{n=0}^{\infty} Q_n\, f^{(n)}(1)$$
converge unconditionally to the same sum. -/
theorem ramanujan_part1_ch3_entry1_series_transformation_general
    (R₁ : ℝ) (hR₁ : 1 < R₁)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁))
    (Q : ℕ → ℂ)
    (hSumm : Summable (fun p : ℕ × ℕ => Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) /
        ((Nat.factorial p.2 : ℂ)))) :
    ∃ v : ℂ,
        HasSum (fun n : ℕ => (∑ j ∈ Finset.range (n + 1), Q j / ((Nat.factorial (n - j) : ℂ))) *
            iteratedDeriv n f (0 : ℂ)) v ∧
            HasSum (fun n : ℕ => Q n * iteratedDeriv n f (1 : ℂ)) v := by
  refine ⟨∑' p : ℕ × ℕ, Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) /
      ((Nat.factorial p.2 : ℂ)), ?_, ?_⟩
  · have hFib := hSumm.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 + p.2)
    exact hFib.congr_fun (fun n => (fibSum_eq Q f n).symm)
  · exact HasSum.prod_fiberwise hSumm.hasSum (fun j => rowHasSum R₁ hR₁ f hf Q j)

set_option linter.unusedVariables false in
/-- **Ramanujan's series transformation (Chapter 3, Entry 1).** Let $R_1 > 1$, let
$f : \mathbb{C} \to \mathbb{C}$ be analytic on the open disc $|z| < R_1$, and let
$Q_0, Q_1, Q_2, \ldots$ be complex numbers such that, for some $R_2 > 0$, the power series
$\sum_n Q_n z^n$ converges absolutely for every complex $z$ with $|z| < R_2$. Suppose that the
double series
$$\sum_{j, m \ge 0} \frac{Q_j\, f^{(j+m)}(0)}{m!}$$
is absolutely summable. Then the series
$$\sum_{n=0}^{\infty} \Bigl(\sum_{j=0}^{n} \frac{Q_j}{(n-j)!}\Bigr) f^{(n)}(0)$$
and
$$\sum_{n=0}^{\infty} Q_n\, f^{(n)}(1)$$
converge unconditionally to the same sum.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 1, printed p. 45 / PDF p.
    55.
Proves `Wanted` entry `ramanujan_part1_ch3_entry1_series_transformation`.
-/
theorem ramanujan_part1_ch3_entry1_series_transformation
    (R₁ : ℝ) (hR₁ : 1 < R₁)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁))
    (Q : ℕ → ℂ)
    (hQ : ∃ R₂ : ℝ, 0 < R₂ ∧ ∀ z : ℂ, ‖z‖ < R₂ → Summable (fun n : ℕ => Q n * z ^ n))
    (hSumm : Summable (fun p : ℕ × ℕ => Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) /
        ((Nat.factorial p.2 : ℂ)))) :
    ∃ v : ℂ,
        HasSum (fun n : ℕ => (∑ j ∈ Finset.range (n + 1), Q j / ((Nat.factorial (n - j) : ℂ))) *
            iteratedDeriv n f (0 : ℂ)) v ∧
            HasSum (fun n : ℕ => Q n * iteratedDeriv n f (1 : ℂ)) v :=
  by apply ramanujan_part1_ch3_entry1_series_transformation_general <;> assumption

end Entry1SeriesTransformation

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
