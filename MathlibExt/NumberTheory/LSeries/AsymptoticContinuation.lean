/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.AbelContinuation
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

open Filter Asymptotics Topology

noncomputable section

/-- **Linear asymptotic Dirichlet continuation.** For $a : \mathbb{N} \to \mathbb{C}$ and
$\rho \in \mathbb{C}$, the linear asymptotic Dirichlet continuation of $a$ with constant $\rho$ is
the function $L_{a,\rho} : \mathbb{C} \to \mathbb{C}$ given by
$L_{a,\rho}(s) = \rho\,\zeta(s) + F_{a-\rho}(s)$, where $\zeta$ is the Riemann zeta function and
$F_{a-\rho}$ is the Abel continuation of the sequence $n \mapsto a(n) - \rho$.

For $\rho \neq 0$ the term $\rho\,\zeta(s)$ carries the pole at $s = 1$, and $F_{a-\rho}$
continues the remainder. At $s = 1$ the formula uses the finite value that Mathlib assigns to
$\zeta(1)$. -/
def linearAsymptoticDirichletContinuation (a : ℕ → ℂ) (ρ s : ℂ) : ℂ :=
  ρ * riemannZeta s + abelContinuation (fun n => a n - ρ) s

/-- **Partial sums after subtracting a constant.** For $a : \mathbb{N} \to \mathbb{C}$,
$\rho \in \mathbb{C}$ and $n \in \mathbb{N}$, the one-based partial sum
$\sum_{k=1}^{n} (a(k) - \rho)$ equals $\sum_{k=1}^{n} a(k) - n\rho$. -/
theorem abelPartialSum_sub_const (a : ℕ → ℂ) (ρ : ℂ) (n : ℕ) :
    abelPartialSum (fun k => a k - ρ) n = abelPartialSum a n - n • ρ := by
  simp only [abelPartialSum, Finset.sum_sub_distrib, Finset.sum_const,
    Nat.card_Icc, Nat.add_sub_cancel]

/-- **Growth bound for the partial sums of a shifted sequence.** Let
$a : \mathbb{N} \to \mathbb{C}$, $\rho \in \mathbb{C}$ and $\sigma \in \mathbb{R}$. If the one-based
partial sums $A(n) = \sum_{k=1}^{n} a(k)$ satisfy $A(n) - n\rho = O(n^{\sigma})$ as
$n \to \infty$, then $\sum_{k=1}^{n} (a(k) - \rho) = O(n^{\sigma})$ as $n \to \infty$. -/
theorem isBigO_abelPartialSum_sub_const (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ}
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) :
    (fun n => abelPartialSum (fun k => a k - ρ) n) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ) := by
  simpa only [abelPartialSum_sub_const] using hO

/-- **Analyticity of the linear asymptotic continuation away from $1$.** Let
$a : \mathbb{N} \to \mathbb{C}$, $\rho \in \mathbb{C}$ and $\sigma \in \mathbb{R}$, and suppose
that the one-based partial sums $A(n) = \sum_{k=1}^{n} a(k)$ satisfy
$A(n) - n\rho = O(n^{\sigma})$ as $n \to \infty$. Then the linear asymptotic Dirichlet
continuation $L_{a,\rho}$ of $a$ with constant $\rho$ is complex analytic at every
$s \in \mathbb{C}$ with $\operatorname{Re} s > \sigma$ and $s \neq 1$. -/
theorem analyticAt_linearAsymptoticDirichletContinuation_of_ne_one
    (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ}
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ))
    {s : ℂ} (hs : σ < s.re) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (linearAsymptoticDirichletContinuation a ρ) s := by
  have hremO := isBigO_abelPartialSum_sub_const a ρ hO
  have hrem : AnalyticAt ℂ (abelContinuation (fun n => a n - ρ)) s :=
    (analyticOn_abelContinuation (fun n => a n - ρ) hremO).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hzeta : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs1)
  change AnalyticAt ℂ
    (fun z => ρ * riemannZeta z + abelContinuation (fun n => a n - ρ) z) s
  have hconst : AnalyticAt ℂ (fun _ : ℂ => ρ) s := analyticAt_const
  exact (hconst.mul hzeta).add hrem

/-- Numerator of the linear asymptotic continuation cleared of denominators. -/
private def linearAsymptoticNumerator (a : ℕ → ℂ) (ρ s : ℂ) : ℂ :=
  ρ * riemannZeta₁ s + (s - 1) * abelContinuation (fun n => a n - ρ) s

/-- The cleared numerator is analytic at `1`. -/
private theorem analyticAt_linearAsymptoticNumerator
    (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ}
    (hσ1 : σ < 1)
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) :
    AnalyticAt ℂ (linearAsymptoticNumerator a ρ) 1 := by
  have hremO := isBigO_abelPartialSum_sub_const a ρ hO
  have h1mem : (1 : ℂ) ∈ {s : ℂ | σ < s.re} := by simpa using hσ1
  have hrem : AnalyticAt ℂ (abelContinuation (fun n => a n - ρ)) 1 :=
    (analyticOn_abelContinuation (fun n => a n - ρ) hremO).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1mem)
  have hzeta : AnalyticAt ℂ riemannZeta₁ 1 :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Eventually.of_forall fun x => differentiable_riemannZeta₁ x)
  change AnalyticAt ℂ
    (fun z => ρ * riemannZeta₁ z + (z - 1) * abelContinuation (fun n => a n - ρ) z) 1
  have hconst : AnalyticAt ℂ (fun _ : ℂ => ρ) 1 := analyticAt_const
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 :=
    analyticAt_id.sub analyticAt_const
  exact (hconst.mul hzeta).add (hsub.mul hrem)

/-- The cleared numerator evaluates to `ρ` at `1`. -/
private theorem linearAsymptoticNumerator_one (a : ℕ → ℂ) (ρ : ℂ) :
    linearAsymptoticNumerator a ρ 1 = ρ := by
  unfold linearAsymptoticNumerator
  simp [riemannZeta₁_one]

/-- **Cleared-denominator form of the linear asymptotic continuation.** Let
$a : \mathbb{N} \to \mathbb{C}$ and $\rho \in \mathbb{C}$, let $L_{a,\rho}$ be the linear
asymptotic Dirichlet continuation of $a$ with constant $\rho$, and let $F_{a-\rho}$ be the Abel
continuation of the sequence $n \mapsto a(n) - \rho$. Let $\zeta_1 : \mathbb{C} \to \mathbb{C}$ be
the function with $\zeta_1(s) = (s - 1)\,\zeta(s)$ for $s \neq 1$ and $\zeta_1(1) = 1$, where
$\zeta$ is the Riemann zeta function. Then for every $s \in \mathbb{C}$ with $s \neq 1$,
$$
L_{a,\rho}(s) = (s - 1)^{-1} \bigl(\rho\,\zeta_1(s) + (s - 1)\,F_{a-\rho}(s)\bigr).
$$
-/
theorem linearAsymptoticDirichletContinuation_eq_inv_sub_mul
    (a : ℕ → ℂ) (ρ : ℂ) {s : ℂ} (hs : s ≠ 1) :
    linearAsymptoticDirichletContinuation a ρ s =
      (s - 1)⁻¹ *
        (ρ * riemannZeta₁ s + (s - 1) * abelContinuation (fun n => a n - ρ) s) := by
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold linearAsymptoticDirichletContinuation
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp

/-- Eventual normal form of the continuation near `1`. -/
private theorem linearAsymptoticDirichletContinuation_eventuallyEq
    (a : ℕ → ℂ) (ρ : ℂ) :
    linearAsymptoticDirichletContinuation a ρ =ᶠ[𝓝[≠] (1 : ℂ)]
      fun s => (s - 1) ^ (-1 : ℤ) • linearAsymptoticNumerator a ρ s := by
  change ∀ᶠ s in 𝓝[≠] (1 : ℂ),
    linearAsymptoticDirichletContinuation a ρ s =
      (s - 1) ^ (-1 : ℤ) • linearAsymptoticNumerator a ρ s
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s ≠ 1 := by simpa using hs
  rw [linearAsymptoticDirichletContinuation_eq_inv_sub_mul a ρ hne]
  unfold linearAsymptoticNumerator
  rw [zpow_neg_one, smul_eq_mul]

/-- **Meromorphy of the linear asymptotic continuation at $1$.** Let
$a : \mathbb{N} \to \mathbb{C}$, $\rho \in \mathbb{C}$ and $\sigma \in \mathbb{R}$ with
$\sigma < 1$, and suppose that the one-based partial sums $A(n) = \sum_{k=1}^{n} a(k)$ satisfy
$A(n) - n\rho = O(n^{\sigma})$ as $n \to \infty$. Then the linear asymptotic Dirichlet
continuation $L_{a,\rho}$ of $a$ with constant $\rho$ is meromorphic at $s = 1$. -/
theorem meromorphicAt_linearAsymptoticDirichletContinuation_one
    (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ} (hσ1 : σ < 1)
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) :
    MeromorphicAt (linearAsymptoticDirichletContinuation a ρ) 1 := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  exact ⟨-1, linearAsymptoticNumerator a ρ,
    analyticAt_linearAsymptoticNumerator a ρ hσ1 hO,
    linearAsymptoticDirichletContinuation_eventuallyEq a ρ⟩

/-- **The linear asymptotic continuation has a simple pole at $1$.** Let
$a : \mathbb{N} \to \mathbb{C}$, $\rho \in \mathbb{C}$ with $\rho \neq 0$ and
$\sigma \in \mathbb{R}$ with $\sigma < 1$, and suppose that the one-based partial sums
$A(n) = \sum_{k=1}^{n} a(k)$ satisfy $A(n) - n\rho = O(n^{\sigma})$ as $n \to \infty$. Then the
meromorphic order at $s = 1$ of the linear asymptotic Dirichlet continuation $L_{a,\rho}$ of $a$
with constant $\rho$ is $-1$. -/
theorem meromorphicOrderAt_linearAsymptoticDirichletContinuation_one
    (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ} (hσ1 : σ < 1)
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) (hρ : ρ ≠ 0) :
    meromorphicOrderAt (linearAsymptoticDirichletContinuation a ρ) 1 =
      ((-1 : ℤ) : WithTop ℤ) := by
  have hmero := meromorphicAt_linearAsymptoticDirichletContinuation_one a ρ hσ1 hO
  have hval : linearAsymptoticNumerator a ρ 1 ≠ 0 := by
    rw [linearAsymptoticNumerator_one]; exact hρ
  exact ((meromorphicOrderAt_eq_int_iff (n := -1) hmero).2
    ⟨linearAsymptoticNumerator a ρ,
      analyticAt_linearAsymptoticNumerator a ρ hσ1 hO, hval,
      linearAsymptoticDirichletContinuation_eventuallyEq a ρ⟩)

/-- **Limit of the linear asymptotic continuation times $s - 1$ at $1$.** Let
$a : \mathbb{N} \to \mathbb{C}$, $\rho \in \mathbb{C}$ and $\sigma \in \mathbb{R}$ with
$\sigma < 1$, and suppose that the one-based partial sums $A(n) = \sum_{k=1}^{n} a(k)$ satisfy
$A(n) - n\rho = O(n^{\sigma})$ as $n \to \infty$. Let $L_{a,\rho}$ be the linear asymptotic
Dirichlet continuation of $a$ with constant $\rho$. Then $(s - 1)\,L_{a,\rho}(s) \to \rho$ as
$s \to 1$ with $s \neq 1$. -/
theorem tendsto_sub_one_mul_linearAsymptoticDirichletContinuation
    (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ} (hσ1 : σ < 1)
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) :
    Tendsto (fun s : ℂ =>
      (s - 1) * linearAsymptoticDirichletContinuation a ρ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
  have hnum : AnalyticAt ℂ (linearAsymptoticNumerator a ρ) 1 :=
    analyticAt_linearAsymptoticNumerator a ρ hσ1 hO
  have hlim : Tendsto (linearAsymptoticNumerator a ρ) (𝓝[≠] (1 : ℂ)) (𝓝 ρ) := by
    have h := hnum.continuousAt.tendsto
    rw [linearAsymptoticNumerator_one a ρ] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : s ≠ 1 := by simpa using hs
    rw [linearAsymptoticDirichletContinuation_eq_inv_sub_mul a ρ hs1]
    unfold linearAsymptoticNumerator
    field_simp [sub_ne_zero.mpr hs1])

/-- **Meromorphy of the linear asymptotic continuation on a half-plane.** Let
$a : \mathbb{N} \to \mathbb{C}$, $\rho \in \mathbb{C}$ and $\sigma \in \mathbb{R}$ with
$\sigma < 1$, and suppose that the one-based partial sums $A(n) = \sum_{k=1}^{n} a(k)$ satisfy
$A(n) - n\rho = O(n^{\sigma})$ as $n \to \infty$. Then the linear asymptotic Dirichlet
continuation $L_{a,\rho}$ of $a$ with constant $\rho$ is meromorphic at every point of the
half-plane $\{s \in \mathbb{C} : \operatorname{Re} s > \sigma\}$. -/
theorem meromorphicOn_linearAsymptoticDirichletContinuation
    (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ} (hσ1 : σ < 1)
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ)) :
    MeromorphicOn (linearAsymptoticDirichletContinuation a ρ)
      {s : ℂ | σ < s.re} := by
  intro s hs
  by_cases hs1 : s = 1
  · subst hs1
    exact meromorphicAt_linearAsymptoticDirichletContinuation_one a ρ hσ1 hO
  · exact (analyticAt_linearAsymptoticDirichletContinuation_of_ne_one
      a ρ hO hs hs1).meromorphicAt

/-- **Convergence of the Dirichlet series to the linear asymptotic continuation.** Let
$a : \mathbb{N} \to \mathbb{C}$, $\rho \in \mathbb{C}$ and $\sigma \in \mathbb{R}$ with
$\sigma < 1$, and suppose that the one-based partial sums $A(n) = \sum_{k=1}^{n} a(k)$ satisfy
$A(n) - n\rho = O(n^{\sigma})$ as $n \to \infty$. Then for every $s \in \mathbb{C}$ with
$\operatorname{Re} s > 1$, the partial sums $\sum_{n=1}^{N} a(n)\, n^{-s}$ converge, as
$N \to \infty$, to $L_{a,\rho}(s)$, where $L_{a,\rho}$ is the linear asymptotic Dirichlet
continuation of $a$ with constant $\rho$. -/
theorem tendsto_linearAsymptoticDirichletContinuation_Icc
    (a : ℕ → ℂ) (ρ : ℂ) {σ : ℝ} (hσ1 : σ < 1)
    (hO : (fun n => abelPartialSum a n - n • ρ) =O[atTop]
      fun n => ((n : ℝ) ^ σ : ℝ))
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, LSeries.term a s n) atTop
      (𝓝 (linearAsymptoticDirichletContinuation a ρ s)) := by
  have hrem := tendsto_abelContinuation_Icc (fun n => a n - ρ) (hσ1.trans hs)
    (isBigO_abelPartialSum_sub_const a ρ hO)
  have hrange := (tendsto_add_atTop_iff_nat 1).mpr (LSeriesHasSum_one hs).tendsto_sum_nat
  have hzeta : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N,
      LSeries.term (1 : ℕ → ℂ) s n) atTop (𝓝 (riemannZeta s)) := by
    have hconv : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1),
      LSeries.term (1 : ℕ → ℂ) s n) atTop (𝓝 (riemannZeta s)) := hrange
    have heq : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), LSeries.term (1 : ℕ → ℂ) s n =
        LSeries.term (1 : ℕ → ℂ) s 0 +
          ∑ n ∈ Finset.Icc 1 N, LSeries.term (1 : ℕ → ℂ) s n := by
      intro N
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_add_one_left_eq_Icc N.zero_le,
        Finset.sum_insert (by simp)]
      simp only [Nat.zero_add]
    simp only [LSeries.term_zero] at heq
    exact hconv.congr' (Filter.Eventually.of_forall fun N => (heq N).trans (zero_add _))
  have hsplit : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, LSeries.term a s n =
      ρ * (∑ n ∈ Finset.Icc 1 N, LSeries.term (1 : ℕ → ℂ) s n) +
        ∑ n ∈ Finset.Icc 1 N, LSeries.term (fun n => a n - ρ) s n := by
    intro N
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    simp only [LSeries.term_of_ne_zero hn0, Pi.one_apply, div_eq_mul_inv]
    ring
  have hlim := (hzeta.const_mul ρ).add hrem
  simpa only [linearAsymptoticDirichletContinuation] using
    hlim.congr' (Filter.Eventually.of_forall fun N => (hsplit N).symm)

end

end
