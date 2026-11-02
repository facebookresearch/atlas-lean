/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import MathlibExt.Analysis.InnerProductSpace.NormSqHessian

/-!
# Finsler metrics

A Finsler metric on a manifold `M` assigns to every tangent space a Minkowski norm, depending
smoothly on the point: a continuous function `F : TM → ℝ`, smooth off the zero section, positively
homogeneous of degree one on each fiber and strongly convex, i.e. the fiberwise Hessian of `F²` is
positive definite at every nonzero vector (Bao–Chern–Shen, *An Introduction to Riemann–Finsler
Geometry* (GTM 200, 2000), §1.1). It need not be reversible (`F(-v) ≠ F(v)` is allowed).

The Finsler length of a `C¹` path is `∫ F(γ'(t)) dt` and the Finsler distance
`Manifold.FinslerMetric.edist` is the infimum of lengths of `C¹` paths (Bao–Chern–Shen, §6.2); it
is not symmetric unless `F` is reversible. Geodesics are the constant-speed curves that locally
realize the forward distance: `d_F(γ t₁, γ t₂) = c (t₂ - t₁)` for `t₁ ≤ t₂` close to any time.

These definitions only use the distance. On a Hausdorff manifold without boundary (`[T2Space M]`
and `[I.Boundaryless]`, e.g. the model `𝓡 n`), the setting of Bao–Chern–Shen (whose manifolds are
boundaryless throughout, cf. their Exercise 12.2.6), they describe the geodesics of the smooth
Finsler metric: short geodesics are minimizing, and a piecewise `C^∞` curve with the same length
and endpoints as a short geodesic is a reparametrization of it (Bao–Chern–Shen, Thm. 6.3.1). With
boundary the notions differ: on the closed exterior of the unit disk in `ℝ²` with the Euclidean
norm, the unit-speed boundary circle is a closed geodesic in this sense but does not solve the
geodesic equation. Statements should also assume `[T2Space M]`: on a non-Hausdorff manifold a
discontinuous curve can be a closed geodesic of speed `0`.

Finsler metrics are defined for finite-dimensional models (`[FiniteDimensional ℝ E]`), where
positive definiteness of the fiberwise Hessian is the usual strong convexity condition.

## Main definitions and results

* `Manifold.FinslerMetric I M`: a `C^∞` Finsler metric on `M`.
* `Manifold.FinslerMetric.IsReversible`: `F(-v) = F(v)`.
* `Manifold.FinslerMetric.edist`: the (forward) Finsler distance.
* `Manifold.FinslerMetric.IsGeodesicOnWithSpeed`, `IsGeodesic`, `IsClosedGeodesic`.
* `Manifold.FinslerMetric.euclidean`: the norm of an inner product space is a reversible Finsler
  metric (`euclidean_isReversible`), a check that the axioms are satisfiable.
-/

@[expose] public section

open Bundle Set
open scoped Manifold ContDiff ENNReal NNReal

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Finsler metric.** Let $M$ be a $C^\infty$ manifold (possibly with boundary or corners)
modelled on a finite-dimensional real normed space $E$, so that each tangent space $T_xM$ is $E$.
A $C^\infty$ Finsler metric on $M$ is a continuous function $F : TM \to \mathbb{R}$ that is
$C^\infty$ off the zero section, satisfies $F(x, v) > 0$ for every $x \in M$ and every nonzero
$v \in T_xM$, is positively homogeneous of degree one on each fiber, that is
$F(x, cv) = c\,F(x, v)$ for all $x \in M$, $v \in T_xM$ and real $c > 0$, and is strongly convex:
for every $x \in M$ and all nonzero $v, w \in E$, the second derivative at $v$ of the function
$u \mapsto F(x, u)^2$ on $E$ satisfies $D^2\big(F(x, \cdot)^2\big)(v)(w, w) > 0$.

Source: Bao–Chern–Shen, *An Introduction to Riemann–Finsler Geometry*, §1.1, where $F$ takes
values in $[0, \infty)$ and the Hessian is that of $F^2/2$. -/
structure FinslerMetric [FiniteDimensional ℝ E] where
  /-- The Finsler function `F : TM → ℝ`. -/
  toFun : TangentBundle I M → ℝ
  continuous_toFun : Continuous toFun
  contMDiffOn_toFun : ContMDiffOn I.tangent 𝓘(ℝ, ℝ) ∞ toFun {v | v.2 ≠ 0}
  pos : ∀ v : TangentBundle I M, v.2 ≠ 0 → 0 < toFun v
  homogeneous : ∀ (x : M) (v : TangentSpace I x) (c : ℝ), 0 < c →
    toFun ⟨x, c • v⟩ = c * toFun ⟨x, v⟩
  hessian_pos : ∀ (x : M) (v w : E), v ≠ 0 → w ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ fun u : E ↦ toFun ⟨x, u⟩ ^ 2) v w w

namespace FinslerMetric

variable {I M}

instance : CoeFun (FinslerMetric I M) fun _ ↦ TangentBundle I M → ℝ := ⟨toFun⟩

/-- **Reversible Finsler metric.** A Finsler metric $F$ on a manifold $M$ is reversible if
$F(x, -v) = F(x, v)$ for every point $x \in M$ and every tangent vector $v \in T_xM$. -/
def IsReversible (F : FinslerMetric I M) : Prop :=
  ∀ v : TangentBundle I M, F ⟨v.proj, -v.2⟩ = F v

/-- **Forward Finsler distance.** Let $F$ be a Finsler metric on a manifold $M$. The forward
Finsler distance from $x \in M$ to $y \in M$ is the value in $[0, \infty]$
$$
d_F(x, y) = \inf_\gamma \int_0^1 F(\gamma(t), \gamma'(t))\, dt,
$$
the infimum over all $C^1$ paths $\gamma : [0, 1] \to M$ from $x$ to $y$; it is $\infty$ when
there is no such path.

It is not symmetric unless $F$ is reversible.

Source: Bao–Chern–Shen, *An Introduction to Riemann–Finsler Geometry*, §6.2. The formula is that
of Mathlib's `riemannianEDist` with `‖v‖ₑ` replaced by `F v`. -/
def edist (F : FinslerMetric I M) (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : CMDiff 1 γ), ∫⁻ t, ENNReal.ofReal (F ⟨γ t, mfderiv% γ t 1⟩)

/-- **Finsler geodesic of given speed on a set of times.** Let $F$ be a Finsler metric on a
manifold $M$ with forward distance $d_F$, let $\gamma : \mathbb{R} \to M$ be a curve, let
$s \subseteq \mathbb{R}$ be a set of times and let $c \ge 0$ be a real number. Then $\gamma$ is a
geodesic of speed $c$ of $F$ on $s$ if for every $t \in s$ there is $\varepsilon > 0$ such that
$d_F(\gamma(t_1), \gamma(t_2)) = c\,(t_2 - t_1)$ for all $t_1, t_2 \in s$ with $t_1 \le t_2$,
$|t_1 - t| < \varepsilon$ and $|t_2 - t| < \varepsilon$. -/
def IsGeodesicOnWithSpeed (F : FinslerMetric I M) (γ : ℝ → M) (s : Set ℝ) (c : ℝ≥0) : Prop :=
  ∀ t ∈ s, ∃ ε > (0 : ℝ), ∀ t₁ ∈ s, ∀ t₂ ∈ s, |t₁ - t| < ε → |t₂ - t| < ε → t₁ ≤ t₂ →
    F.edist (γ t₁) (γ t₂) = c * ENNReal.ofReal (t₂ - t₁)

/-- **Finsler geodesic.** Let $F$ be a Finsler metric on a manifold $M$. A curve
$\gamma : \mathbb{R} \to M$ is a geodesic of $F$ if there is a real number $c \ge 0$ such that
$\gamma$ is a geodesic of speed $c$ of $F$ on all of $\mathbb{R}$. -/
def IsGeodesic (F : FinslerMetric I M) (γ : ℝ → M) : Prop :=
  ∃ c : ℝ≥0, F.IsGeodesicOnWithSpeed γ univ c

/-- **Closed Finsler geodesic.** Let $F$ be a Finsler metric on a manifold $M$. A curve
$\gamma : \mathbb{R} \to M$ is a closed geodesic of $F$ if it is a geodesic of $F$, it is periodic
with some period $T > 0$, that is $\gamma(t + T) = \gamma(t)$ for all real $t$, and it is not
constant: $\gamma(t_1) \ne \gamma(t_2)$ for some real $t_1, t_2$. -/
def IsClosedGeodesic (F : FinslerMetric I M) (γ : ℝ → M) : Prop :=
  F.IsGeodesic γ ∧ (∃ T > 0, Function.Periodic γ T) ∧ ∃ t₁ t₂, γ t₁ ≠ γ t₂

end FinslerMetric

end Manifold

namespace Manifold.FinslerMetric

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Euclidean Finsler metric.** Let $V$ be a finite-dimensional real inner product space,
viewed as a smooth manifold whose tangent spaces are $V$ itself. The Euclidean Finsler metric on
$V$ is $F(x, v) = \|v\|$ for $x \in V$ and $v \in T_xV = V$. -/
def euclidean : FinslerMetric 𝓘(ℝ, F) F where
  toFun v := ‖@id F v.2‖
  continuous_toFun := continuous_norm.comp
    ((contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F) (n := 0)).continuous)
  contMDiffOn_toFun := by
    intro v hv
    have h1 := (contMDiff_snd_tangentBundle_modelSpace F 𝓘(ℝ, F) (n := ∞)).contMDiffAt (x := v)
    have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun w : F ↦ ‖w‖) (@id F v.2) :=
      (contDiffAt_norm ℝ (show @id F v.2 ≠ 0 from hv)).contMDiffAt
    exact (h2.comp v h1).contMDiffWithinAt
  pos v hv := norm_pos_iff.mpr (show @id F v.2 ≠ 0 from hv)
  homogeneous x v c hc := by
    change ‖c • @id F v‖ = c * ‖@id F v‖
    rw [norm_smul, Real.norm_of_nonneg hc.le]
  hessian_pos x v w hv hw := by
    simp only [id_eq]
    rw [fderiv_fderiv_norm_sq_apply]
    have := real_inner_self_pos.mpr hw
    positivity

/-- **The Euclidean Finsler metric is reversible.** For every finite-dimensional real inner
product space $V$, the Euclidean Finsler metric $F(x, v) = \|v\|$ on $V$ is reversible:
$F(x, -v) = F(x, v)$ for all $x, v \in V$. -/
theorem euclidean_isReversible : (euclidean : FinslerMetric 𝓘(ℝ, F) F).IsReversible :=
  fun v ↦ norm_neg (@id F v.2)

end Manifold.FinslerMetric
