/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Algebra.Ring.Periodic

/-!
# Local geodesics in metric spaces

A local geodesic of speed `c ≥ 0` in a (pseudo-e)metric space is a curve that locally realizes
distances, `d(γ t₁, γ t₂) = c |t₁ - t₂|` for `t₁`, `t₂` close to any given time: a (linearly
reparametrized) local geodesic in the sense of Bridson–Haefliger, *Metric Spaces of Non-positive
Curvature* (1999), Ch. I.1, Def. 1.3, and the metric-geometry definition of a geodesic in
Wikipedia's "Geodesic" (§Metric geometry). A closed local geodesic (Bridson–Haefliger,
Ch. I.3, Def. 3.15) is a periodic one. Constant curves are local geodesics of speed `0`.

## Riemannian manifolds

Mathlib has no covariant derivative along curves yet, so the geodesic equation `∇_{γ'} γ' = 0`
cannot be stated directly; these metric definitions are the way to talk about Riemannian geodesics.
On a `C^∞` Riemannian manifold without boundary whose distance is the Riemannian distance (that is,
`[IsRiemannianManifold I M]`, see `Mathlib.Geometry.Manifold.Riemannian.Basic`), every Riemannian
geodesic is a local geodesic: geodesics are locally length minimizing (Lang, *Lecture Notes on
Riemannian Geometry*, ETH Zürich 2020, Cor. 1.22). Conversely a piecewise `C¹` curve realizing the
distance between nearby points is a reparametrization of a geodesic (Lang, Prop. 1.21), so the
piecewise `C¹` local geodesics are the Riemannian geodesics; that a merely continuous local
geodesic is smooth is the standard length-space argument and is not formalized here. With boundary
the notions differ (a curve along a concave part of the boundary can locally minimize). The
definitions must be used with the Riemannian distance: on a submanifold such as
`Metric.sphere (0 : E) 1`, the subspace (chordal) distance is not the Riemannian distance.

Completeness of a Riemannian manifold is `CompleteSpace M` for the Riemannian distance; for a
finite-dimensional manifold without boundary this is equivalent to geodesic completeness (every
geodesic extends to all of `ℝ`) by the Hopf–Rinow theorem, which fails with boundary (a closed
interval is complete) and in infinite dimensions. The diameter is `Metric.ediam univ` (or
`Metric.diam univ`).

## Main definitions

* `Metric.IsGeodesicOnWithSpeed γ s c`: `γ : ℝ → X` is a local geodesic of speed `c` on the set of
  times `s`.
* `Metric.IsGeodesicOn γ s`: `γ : ℝ → X` is a local geodesic (of some speed) on `s`.
* `Metric.IsGeodesic γ`: `γ` is a local geodesic defined on all of `ℝ`.
* `Metric.IsClosedGeodesic γ`: `γ` is a non-constant periodic local geodesic.

The set of times `s` is meant to be an interval, as in Bridson–Haefliger: on a set of isolated
times every curve satisfies the condition. Closed geodesics are meant for emetric spaces, where they
have positive speed; in a pseudo-emetric space a speed-`0` curve can jump between points at distance
`0`.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal

noncomputable section

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-- **Geodesics of a given speed on a set of times.** Let $X$ be a pseudo-extended metric space
with extended distance $d$, let $\gamma : \mathbb{R} \to X$ be a curve, $s \subseteq \mathbb{R}$ a
set of times and $c \ge 0$ a real number. The curve $\gamma$ is a geodesic of speed $c$ on $s$ if
every $t \in s$ has some $\varepsilon > 0$ such that $d(\gamma(t_1), \gamma(t_2)) = c\,|t_1 - t_2|$
for all $t_1, t_2 \in s$ with $|t_1 - t| < \varepsilon$ and $|t_2 - t| < \varepsilon$. -/
def IsGeodesicOnWithSpeed (γ : ℝ → X) (s : Set ℝ) (c : ℝ≥0) : Prop :=
  ∀ t ∈ s, ∃ ε > (0 : ℝ), ∀ t₁ ∈ s, ∀ t₂ ∈ s, |t₁ - t| < ε → |t₂ - t| < ε →
    edist (γ t₁) (γ t₂) = c * edist t₁ t₂

/-- **Geodesic on a set of times.** Let $X$ be a pseudo-extended metric space. A curve
$\gamma : \mathbb{R} \to X$ is a geodesic on a set of times $s \subseteq \mathbb{R}$ if, for some
real number $c \ge 0$, it is a geodesic of speed $c$ on $s$.

On a Riemannian manifold without boundary, with its Riemannian distance, every Riemannian geodesic
is a geodesic in this sense, and the piecewise $C^1$ geodesics in this sense are the Riemannian
geodesics. -/
def IsGeodesicOn (γ : ℝ → X) (s : Set ℝ) : Prop :=
  ∃ c : ℝ≥0, IsGeodesicOnWithSpeed γ s c

/-- **Geodesics defined for all times.** Let $X$ be a pseudo-extended metric space. A curve
$\gamma : \mathbb{R} \to X$ is a geodesic if it is a geodesic on the set of all times
$\mathbb{R}$. -/
def IsGeodesic (γ : ℝ → X) : Prop :=
  IsGeodesicOn γ univ

/-- **Closed geodesic.** Let $X$ be a pseudo-extended metric space. A curve
$\gamma : \mathbb{R} \to X$ is a closed geodesic if it is a geodesic defined on all of $\mathbb{R}$,
it is periodic with some period $T > 0$ (that is, $\gamma(t + T) = \gamma(t)$ for all
$t \in \mathbb{R}$), and it is not constant: $\gamma(t_1) \ne \gamma(t_2)$ for some
$t_1, t_2 \in \mathbb{R}$.

Periodicity of a geodesic defined on all of $\mathbb{R}$ encodes both $\gamma(0) = \gamma(T)$ and
the matching of the velocities at $0$ and $T$. For a closed geodesic of speed $1$, every period
$T > 0$ is the length of $\gamma$ traversed over one period; its smallest positive period is the
length of the underlying prime closed geodesic. -/
def IsClosedGeodesic (γ : ℝ → X) : Prop :=
  IsGeodesic γ ∧ (∃ T > 0, Function.Periodic γ T) ∧ ∃ t₁ t₂, γ t₁ ≠ γ t₂

theorem IsGeodesicOnWithSpeed.mono {γ : ℝ → X} {s t : Set ℝ} {c : ℝ≥0}
    (h : IsGeodesicOnWithSpeed γ t c) (hst : s ⊆ t) : IsGeodesicOnWithSpeed γ s c := by
  intro τ hτ
  obtain ⟨ε, hε, h⟩ := h τ (hst hτ)
  exact ⟨ε, hε, fun t₁ ht₁ t₂ ht₂ ↦ h t₁ (hst ht₁) t₂ (hst ht₂)⟩

theorem IsGeodesicOn.mono {γ : ℝ → X} {s t : Set ℝ} (h : IsGeodesicOn γ t) (hst : s ⊆ t) :
    IsGeodesicOn γ s :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.mono hst⟩

theorem IsGeodesic.isGeodesicOn {γ : ℝ → X} (h : IsGeodesic γ) (s : Set ℝ) :
    IsGeodesicOn γ s :=
  IsGeodesicOn.mono h (subset_univ s)

/-- **Constant curves are geodesics.** Let $X$ be a pseudo-extended metric space. For every point
$p \in X$, the constant curve $\mathbb{R} \to X$, $t \mapsto p$, is a geodesic.

Its speed is $0$. -/
theorem isGeodesic_const (p : X) : IsGeodesic (fun _ : ℝ ↦ p) :=
  ⟨0, fun _ _ ↦ ⟨1, one_pos, fun _ _ _ _ _ _ ↦ by simp⟩⟩

/-- **Constant curves are not closed geodesics.** Let $X$ be a pseudo-extended metric space. For
every point $p \in X$, the constant curve $\mathbb{R} \to X$, $t \mapsto p$, is not a closed
geodesic. -/
theorem not_isClosedGeodesic_const (p : X) : ¬ IsClosedGeodesic (fun _ : ℝ ↦ p) :=
  fun ⟨_, _, _, _, h⟩ ↦ h rfl

/-- **Straight lines are geodesics of constant speed.** Let $F$ be a real normed space and
$p, v \in F$. For every set of times $s \subseteq \mathbb{R}$, the straight line
$t \mapsto p + t v$ is a geodesic of speed $\|v\|$ on $s$. -/
theorem isGeodesicOnWithSpeed_lineMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p v : F) (s : Set ℝ) : IsGeodesicOnWithSpeed (fun t : ℝ ↦ p + t • v) s ‖v‖₊ := by
  refine fun _ _ ↦ ⟨1, one_pos, fun t₁ _ t₂ _ _ _ ↦ ?_⟩
  rw [edist_add_left, edist_eq_enorm_sub, ← sub_smul, enorm_smul, edist_eq_enorm_sub, mul_comm]
  rfl

/-- **Straight lines are geodesics.** Let $F$ be a real normed space. For all $p, v \in F$, the
straight line $\mathbb{R} \to F$, $t \mapsto p + t v$, is a geodesic. -/
theorem isGeodesic_lineMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p v : F) :
    IsGeodesic (fun t : ℝ ↦ p + t • v) :=
  ⟨_, isGeodesicOnWithSpeed_lineMap p v univ⟩

/-- **Closed geodesics are not constant.** Let $X$ be a pseudo-extended metric space. If
$\gamma : \mathbb{R} \to X$ is a closed geodesic, then for every $p \in X$, $\gamma$ is not the
constant curve $t \mapsto p$. -/
theorem IsClosedGeodesic.not_const {γ : ℝ → X} (h : IsClosedGeodesic γ) (p : X) :
    γ ≠ fun _ ↦ p := by
  rintro rfl
  obtain ⟨t₁, t₂, h⟩ := h.2.2
  exact h rfl

end Metric
