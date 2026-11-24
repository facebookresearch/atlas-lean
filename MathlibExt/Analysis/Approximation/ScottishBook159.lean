/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Uniform approximation by partial sums of one power series -/

@[expose] public section

open Set Filter
open scoped Topology

namespace MathlibExt.Analysis.ScottishBook159Wanted

/-- **The claim of Scottish Book Problem 159.** There is a sequence of real numbers
$a_0, a_1, a_2, \dots$ such that for every $\varepsilon > 0$ there is a natural number $N$ with the
following property: for every function $f : \mathbb{R} \to \mathbb{R}$ that is continuous on
$[0, 1]$ and satisfies $f(0) = 0$ and $0 \le f(x) \le 1$ for all $x \in [0, 1]$, there is a natural
number $n \le N$ with $|f(x) - P_n(x)| < \varepsilon$ for all $x \in [0, 1]$, where
$P_n(x) = \sum_{k=0}^{n} a_k x^k$ is the $n$-th partial sum of the power series $\sum a_k x^k$. -/
def ScottishBookProblem159Claim : Prop :=
  ∃ a : ℕ → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ f : ℝ → ℝ,
    ContinuousOn f (Set.Icc 0 1) → f 0 = 0 →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc 0 1) →
      ∃ n : ℕ, n ≤ N ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
        dist (f x) (∑ k ∈ Finset.range (n + 1), a k * x ^ k) < ε

/--
**Scottish Book Problem 159 has a negative answer.** There is no sequence of real numbers
$a_0, a_1, a_2, \dots$ with the following property: for every $\varepsilon > 0$ there is a natural
number $N$ such that for every function $f : \mathbb{R} \to \mathbb{R}$ that is continuous on
$[0, 1]$ and satisfies $f(0) = 0$ and $0 \le f(x) \le 1$ for all $x \in [0, 1]$, there is a natural
number $n \le N$ with $\left|f(x) - \sum_{k=0}^{n} a_k x^k\right| < \varepsilon$ for all
$x \in [0, 1]$.

Sternbach's argument in the addendum Ad 159 uses the functions $\sin^2(2^n \pi x)$. Mazur showed
that for an arbitrary family $\Phi$ of functions of this kind, a power series with this property
exists exactly when the functions of $\Phi$ are equicontinuous.

Source: S. Ruziewicz, Problem 159 of the Scottish Book; Ad 159 in the
typescript (Sternbach's negative argument; Mazur's equicontinuity criterion).
-/
theorem problem159Refuted : ¬ ScottishBookProblem159Claim := by
  rintro ⟨a, ha⟩
  obtain ⟨N, hN⟩ := ha (1 / 4) (by norm_num)
  let P (n : ℕ) (x : ℝ) := ∑ k ∈ Finset.range (n + 1), a k * x ^ k
  have hP (n : ℕ) : Continuous (P n) := by
    unfold P
    fun_prop
  have hclose (n : ℕ) : ∀ᶠ x : ℝ in 𝓝 0, dist (P n x) (P n 0) < 1 / 4 :=
    (Metric.tendsto_nhds.1 ((hP n).continuousAt (x := 0))) _ (by norm_num)
  -- These finitely many partial sums have a common modulus at zero for this tolerance.
  have hnear (m : ℕ) : ∀ᶠ x : ℝ in 𝓝 0, ∀ n ≤ m, dist (P n x) (P n 0) < 1 / 4 := by
    induction m with
    | zero =>
      filter_upwards [hclose 0] with x hx n hn
      simpa only [Nat.eq_zero_of_le_zero hn] using hx
    | succ m ih =>
      filter_upwards [ih, hclose (m + 1)] with x hx hxm n hn
      rcases lt_or_eq_of_le hn with hl | rfl
      · exact hx n (Nat.le_of_lt_succ hl)
      · exact hxm
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.1 (hnear N)
  let t : ℝ := min (δ / 2) 1
  have htpos : 0 < t := lt_min (by linarith) zero_lt_one
  have htle : t ≤ 1 := min_le_right _ _
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨htpos.le, htle⟩
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact (min_le_left _ _).trans_lt (by linarith)
  -- A clipped ramp reaches one inside that same neighborhood.
  let f (x : ℝ) := min 1 (x / t)
  have hf : Continuous f := continuous_const.min (continuous_id.div_const t)
  have hf0 : f 0 = 0 := by simp [f]
  have hft : f t = 1 := by simp [f, htpos.ne']
  have hfrange : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨le_min zero_le_one (div_nonneg hx.1 htpos.le), min_le_left _ _⟩
  obtain ⟨n, hn, happrox⟩ := hN f hf.continuousOn hf0 hfrange
  have h0 := happrox 0 (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  have h1 := happrox t ht
  change dist (f 0) (P n 0) < 1 / 4 at h0
  change dist (f t) (P n t) < 1 / 4 at h1
  have hPn := hδ htball n hn
  have htriangle : (1 : ℝ) ≤
      dist (f t) (P n t) + (dist (P n t) (P n 0) + dist (P n 0) (f 0)) := by
    calc
      1 = dist (f t) (f 0) := by rw [hft, hf0, Real.dist_eq]; norm_num
      _ ≤ dist (f t) (P n t) + dist (P n t) (f 0) := dist_triangle _ _ _
      _ ≤ _ := by linarith only [dist_triangle (P n t) (P n 0) (f 0)]
  rw [dist_comm (P n 0) (f 0)] at htriangle
  linarith

end MathlibExt.Analysis.ScottishBook159Wanted
