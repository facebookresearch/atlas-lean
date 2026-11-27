/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Modulus of continuity

For a function `f : ℝ → ℝ` and an interval `[a, b]`, the modulus of continuity
`ω_f(η)` is the supremum of `|f x - f y|` over pairs `x, y ∈ [a, b]` with
`|x - y| ≤ η`. It quantifies uniform continuity: for `f` continuous on
`[a, b]`, `ω_f(η) → 0` as `η → 0⁺`. Mathlib has no modulus-of-continuity API;
this file adds the definition and its basic properties. It is the form of the
concept used in the book's proof of convergence of Riemann sums.

## Main definitions

* `modulusOfContinuity f a b η`: `sup {|f x - f y| | x, y ∈ [a, b], |x - y| ≤ η}`.

## Main results

* `modulusOfContinuity_tendsto_zero`: `ω_f(η) → 0` as `η → 0⁺`, for `f`
  continuous on `[a, b]`.
* `le_modulusOfContinuity`: each `|f x - f y|` with `x, y ∈ [a, b]` and
  `|x - y| ≤ η` is bounded by `ω_f(η)`.
* `modulusOfContinuity_nonneg`: `0 ≤ ω_f(η)` for `η ≥ 0`.
* `modulusOfContinuity_mono`: `ω_f` is monotone in `η`.
* `modulusOfContinuity_bddAbove`: the defining set is bounded above.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Modulus of
Continuity) and Theorem I, "The Riemann Integral section": for `f ∈ C([a, b])`
and `η > 0`, `w_f(η) = sup {|f(x) - f(y)| | |x - y| ≤ η}` and
`lim_{η → 0} w_f(η) = 0`. The v1 formalization is in
`v1/Atlas/RealAnalysis/code/Integration/ModulusContinuity.lean`. The
nonnegativity and monotonicity lemmas are not in v1; they are the basic API
lemmas for the definition.
-/

@[expose] public section

open scoped Topology

/-- **Modulus of continuity.** For a function $f : \mathbb{R} \to \mathbb{R}$, real numbers $a$
and $b$, and a scale $\eta \in \mathbb{R}$, the modulus of continuity of $f$ on $[a, b]$ at scale
$\eta$ is

$$\omega_f(\eta) = \sup \{|f(x) - f(y)| : x, y \in [a, b],\ |x - y| \le \eta\},$$

where the supremum is taken in $\mathbb{R}$ with the convention that it is $0$ when the set is
empty or not bounded above.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Modulus of
Continuity), "The Riemann Integral section". -/
noncomputable def modulusOfContinuity (f : ℝ → ℝ) (a b η : ℝ) : ℝ :=
  sSup {|f x - f y| | (x ∈ Set.Icc a b) (y ∈ Set.Icc a b) (_ : |x - y| ≤ η)}

/-- **The set defining the modulus of continuity is bounded above.** Let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$. Then for every $\eta \in \mathbb{R}$ the
set $\{|f(x) - f(y)| : x, y \in [a, b],\ |x - y| \le \eta\}$ is bounded above. -/
theorem modulusOfContinuity_bddAbove (f : ℝ → ℝ) (a b η : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    BddAbove {|f x - f y| | (x ∈ Set.Icc a b) (y ∈ Set.Icc a b) (_ : |x - y| ≤ η)} := by
  obtain ⟨C, hC⟩ :=
    Metric.isBounded_iff.mp (isCompact_Icc.image_of_continuousOn hf |>.isBounded)
  refine ⟨C, ?_⟩
  rintro d ⟨x, hx, y, hy, _, rfl⟩
  have h := hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  rwa [Real.dist_eq] at h

/-- **The modulus of continuity bounds increments.** Let $f : \mathbb{R} \to \mathbb{R}$ be
continuous on $[a, b]$, let $\eta \in \mathbb{R}$, and let $\omega_f(\eta)$ be the modulus of
continuity of $f$ on $[a, b]$ at scale $\eta$. For all $x, y \in [a, b]$ with $|x - y| \le \eta$,
we have $|f(x) - f(y)| \le \omega_f(\eta)$. -/
theorem le_modulusOfContinuity (f : ℝ → ℝ) (a b : ℝ) (η : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    {x : ℝ} (hx : x ∈ Set.Icc a b) {y : ℝ} (hy : y ∈ Set.Icc a b) (hxy : |x - y| ≤ η) :
    |f x - f y| ≤ modulusOfContinuity f a b η :=
  le_csSup (modulusOfContinuity_bddAbove f a b η hf) ⟨x, hx, y, hy, hxy, rfl⟩

/-- **Nonnegativity of the modulus of continuity.** Let $a \le b$ and let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$. For every $\eta \ge 0$, the modulus of
continuity $\omega_f(\eta)$ of $f$ on $[a, b]$ at scale $\eta$ satisfies $0 \le \omega_f(\eta)$.

The defining set contains $|f(a) - f(a)| = 0$. -/
theorem modulusOfContinuity_nonneg (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ modulusOfContinuity f a b η := by
  have hmem : (0 : ℝ) ∈
      {|f x - f y| | (x ∈ Set.Icc a b) (y ∈ Set.Icc a b) (_ : |x - y| ≤ η)} := by
    refine ⟨a, ⟨le_rfl, hab⟩, a, ⟨le_rfl, hab⟩, ?_, ?_⟩
    · simp only [sub_self, abs_zero]
      exact hη
    · simp
  exact le_csSup (modulusOfContinuity_bddAbove f a b η hf) hmem

/-- **Monotonicity of the modulus of continuity.** Let $a \le b$, let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$, and write $\omega_f(\eta)$ for the
modulus of continuity of $f$ on $[a, b]$ at scale $\eta$. If $0 \le \eta_1 \le \eta_2$, then
$\omega_f(\eta_1) \le \omega_f(\eta_2)$.

A smaller scale takes the supremum over a smaller set of pairs. -/
theorem modulusOfContinuity_mono (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) {η₁ η₂ : ℝ} (hη₁ : 0 ≤ η₁) (h : η₁ ≤ η₂) :
    modulusOfContinuity f a b η₁ ≤ modulusOfContinuity f a b η₂ := by
  apply csSup_le_csSup (modulusOfContinuity_bddAbove f a b η₂ hf) _ _
  · refine ⟨|f a - f a|, a, ⟨le_rfl, hab⟩, a, ⟨le_rfl, hab⟩, ?_, rfl⟩
    simp only [sub_self, abs_zero]
    exact hη₁
  · rintro d ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, hx, y, hy, le_trans hxy h, rfl⟩

/-- **Theorem I (Modulus of continuity vanishes).** Let $a \le b$ and let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$. Then the modulus of continuity
$\omega_f(\eta)$ of $f$ on $[a, b]$ tends to $0$ as $\eta \to 0^+$.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorem I, "The Riemann
Integral section": for all `f ∈ C([a, b])`, `lim_{η → 0} w_f(η) = 0`. -/
theorem modulusOfContinuity_tendsto_zero (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Filter.Tendsto (modulusOfContinuity f a b) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hfδ⟩ := huc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun η hη_mem hη_dist => ?_⟩
  simp only [Real.dist_eq, sub_zero] at hη_dist ⊢
  have hη_pos : (0 : ℝ) < η := hη_mem
  have hη_lt_δ : η < δ := by linarith [abs_of_pos hη_pos]
  have hle : ∀ d ∈
      {|f x - f y| | (x ∈ Set.Icc a b) (y ∈ Set.Icc a b) (_ : |x - y| ≤ η)},
      d ≤ ε / 2 := by
    rintro d ⟨x, hx, y, hy, hxy, rfl⟩
    have hdist : dist x y < δ := by
      rw [Real.dist_eq]
      linarith
    have h := hfδ x hx y hy hdist
    rw [Real.dist_eq] at h
    linarith
  have hne : ({|f x - f y| | (x ∈ Set.Icc a b) (y ∈ Set.Icc a b) (_ : |x - y| ≤ η)} :
      Set ℝ).Nonempty :=
    ⟨|f a - f a|, a, ⟨le_refl a, hab⟩, a, ⟨le_refl a, hab⟩, by simp; linarith⟩
  have hsup_le : sSup
      {|f x - f y| | (x ∈ Set.Icc a b) (y ∈ Set.Icc a b) (_ : |x - y| ≤ η)} ≤
      ε / 2 :=
    csSup_le hne hle
  have hsup_nonneg : 0 ≤ sSup
      {|f x - f y| | (x ∈ Set.Icc a b) (y ∈ Set.Icc a b) (_ : |x - y| ≤ η)} :=
    modulusOfContinuity_nonneg f a b hab hf hη_pos.le
  show |modulusOfContinuity f a b η| < ε
  unfold modulusOfContinuity
  rw [abs_of_nonneg hsup_nonneg]
  linarith
