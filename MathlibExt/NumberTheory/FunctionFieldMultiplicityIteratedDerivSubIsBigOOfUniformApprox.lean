/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville

/-!
# Derivatives at `z = 1` of uniform approximations

This module proves `MetaMathlibExt.iteratedDeriv_sub_isBigO_of_uniform_approx`: the `k`-th
derivatives at `1` of uniformly approximated analytic functions differ by `O(n ^ (ε - 1))`.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 1 (`integers-2025-A9-lem-1`).
-/

open Filter

namespace MetaMathlibExt

/-- **Derivatives at $z = 1$ of uniform approximations.** Let $r > 0$, let $D$ be the open disk of
radius $r$ centred at $1$ in $\mathbb{C}$, and let $f$ and $G_n$ ($n \in \mathbb{N}$) be complex
functions analytic on $D$. Suppose there is a real constant $C$ such that
$|G_n(z) - f(z)\, n^{z-1}| \le C\, n^{\operatorname{Re} z - 2}$ for all $n \ge 1$ and all
$z \in D$. Then for every $k \in \mathbb{N}$ and every $\varepsilon > 0$, as $n \to \infty$,

$$G_n^{(k)}(1) - \frac{d^k}{dz^k}\big(f(z)\, n^{z-1}\big)\Big|_{z=1} = O(n^{\varepsilon - 1}).$$

This is the paper's Lemma 1, a corrected version of Lalín and Zhang's Lemma 3.2; Equation (11) is
the case $k = 1$. The paper's "analytic at $z = 1$" with an error term "in a neighborhood of
$z = 1$" is read as analyticity on a fixed disk on which the bound holds with one constant for all
$n \ge 1$.

Source: Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in
h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9,
Lemma 1 (`integers-2025-A9-lem-1`). -/
public theorem iteratedDeriv_sub_isBigO_of_uniform_approx
    (G : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) (Metric.ball 1 r))
    (hf : AnalyticOnNhd ℂ f (Metric.ball 1 r))
    (hbound : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ z ∈ Metric.ball (1 : ℂ) r,
      ‖G n z - f z * (n : ℂ) ^ (z - 1)‖ ≤ C * (n : ℝ) ^ (z.re - 2))
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => iteratedDeriv k (G n) 1 -
        iteratedDeriv k (fun z => f z * (n : ℂ) ^ (z - 1)) 1)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (ε - 1)) := by
  obtain ⟨C, hC⟩ := hbound
  set ρ : ℝ := min (r / 2) ε with hρdef
  have hr2 : (0 : ℝ) < r / 2 := by linarith
  have hρ0 : 0 < ρ := by rw [hρdef]; exact lt_min_iff.mpr ⟨hr2, hε⟩
  have hρr : ρ < r := by
    rw [hρdef]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρε : ρ ≤ ε := by rw [hρdef]; exact min_le_right _ _
  have h1mem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) r := Metric.mem_ball_self hr
  have key : ∀ n : ℕ, 1 ≤ n → ‖iteratedDeriv k (G n) 1 -
      iteratedDeriv k (fun z => f z * (n : ℂ) ^ (z - 1)) 1‖
      ≤ (k.factorial : ℝ) * (ρ ^ k)⁻¹ * |C| * (n : ℝ) ^ (ε - 1) := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hnn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hbase : AnalyticOnNhd ℂ (fun _ : ℂ => (n : ℂ)) (Metric.ball 1 r) :=
      analyticOnNhd_const
    have hexp : AnalyticOnNhd ℂ (fun z : ℂ => z - 1) (Metric.ball 1 r) :=
      analyticOnNhd_id.sub analyticOnNhd_const
    have hcpow : AnalyticOnNhd ℂ (fun z : ℂ => (n : ℂ) ^ (z - 1)) (Metric.ball 1 r) :=
      hbase.cpow hexp (fun z _ => Complex.natCast_mem_slitPlane.2 hn0)
    have hfn : AnalyticOnNhd ℂ (fun z : ℂ => f z * (n : ℂ) ^ (z - 1))
        (Metric.ball 1 r) := hf.mul hcpow
    have hsub : AnalyticOnNhd ℂ (fun z : ℂ => G n z - f z * (n : ℂ) ^ (z - 1))
        (Metric.ball 1 r) := (hG n).sub hfn
    have hGcd : ContDiffAt ℂ ((k : ℕ) : WithTop ℕ∞) (G n) 1 :=
      ((hG n) 1 h1mem).contDiffAt
    have hfcd : ContDiffAt ℂ ((k : ℕ) : WithTop ℕ∞)
        (fun z => f z * (n : ℂ) ^ (z - 1)) 1 := (hfn 1 h1mem).contDiffAt
    have hsplit : iteratedDeriv k (G n) 1 -
        iteratedDeriv k (fun z => f z * (n : ℂ) ^ (z - 1)) 1
        = iteratedDeriv k (fun z => G n z - f z * (n : ℂ) ^ (z - 1)) 1 :=
      (iteratedDeriv_fun_sub hGcd hfcd).symm
    rw [hsplit]
    have hb : ∀ z ∈ Metric.sphere (1 : ℂ) ρ,
        ‖G n z - f z * (n : ℂ) ^ (z - 1)‖ ≤ |C| * (n : ℝ) ^ (ρ - 1) := by
      intro z hz
      have hdist : dist z 1 = ρ := Metric.mem_sphere.mp hz
      have hnorm : ‖z - 1‖ = ρ := by rw [← dist_eq_norm]; exact hdist
      have hzball : z ∈ Metric.ball (1 : ℂ) r :=
        Metric.mem_ball.mpr (by rw [hdist]; exact hρr)
      have hle := hC n hn z hzball
      have hre : z.re ≤ 1 + ρ := by
        have h1 := Complex.re_le_norm (z - 1)
        rw [Complex.sub_re, Complex.one_re] at h1
        rw [hnorm] at h1
        linarith
      have hexp : (n : ℝ) ^ (z.re - 2) ≤ (n : ℝ) ^ (ρ - 1) :=
        Real.rpow_le_rpow_of_exponent_le hnn (by linarith)
      calc ‖G n z - f z * (n : ℂ) ^ (z - 1)‖ ≤ C * (n : ℝ) ^ (z.re - 2) := hle
          _ ≤ |C| * (n : ℝ) ^ (z.re - 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C)
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ ≤ |C| * (n : ℝ) ^ (ρ - 1) :=
            mul_le_mul_of_nonneg_left hexp (abs_nonneg C)
    have hd := hsub.differentiableOn.diffContOnCl_ball (Metric.closedBall_subset_ball hρr)
    have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ0 hd hb
    have hexp2 : (n : ℝ) ^ (ρ - 1) ≤ (n : ℝ) ^ (ε - 1) :=
      Real.rpow_le_rpow_of_exponent_le hnn (by linarith)
    have hnonneg2 : (0 : ℝ) ≤ (k.factorial : ℝ) * (ρ ^ k)⁻¹ * |C| :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
        (inv_nonneg.mpr (pow_nonneg hρ0.le _))) (abs_nonneg _)
    calc ‖iteratedDeriv k (fun z : ℂ => G n z - f z * (n : ℂ) ^ (z - 1)) 1‖
        ≤ (k.factorial : ℝ) * (|C| * (n : ℝ) ^ (ρ - 1)) / ρ ^ k := hderiv
      _ = (k.factorial : ℝ) * (ρ ^ k)⁻¹ * |C| * (n : ℝ) ^ (ρ - 1) := by ring
      _ ≤ (k.factorial : ℝ) * (ρ ^ k)⁻¹ * |C| * (n : ℝ) ^ (ε - 1) :=
        mul_le_mul_of_nonneg_left hexp2 hnonneg2
  refine Asymptotics.IsBigO.of_bound ((k.factorial : ℝ) * (ρ ^ k)⁻¹ * |C|)
    (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hgn : ‖(n : ℝ) ^ (ε - 1)‖ = (n : ℝ) ^ (ε - 1) :=
    Real.norm_eq_abs _ |>.trans (abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  rw [hgn]
  exact key n hn

end MetaMathlibExt
