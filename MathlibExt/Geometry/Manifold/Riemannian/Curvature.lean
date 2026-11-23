/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature

/-!
# Riemann, Ricci, scalar and sectional curvature of a Riemannian manifold

Let `M` be a `C^∞` manifold with a `C^∞` Riemannian metric `g`, given as in
`Mathlib.Geometry.Manifold.Riemannian.Basic` by
```
[IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
[IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
```
and let `∇` be its Levi-Civita connection `CovariantDerivative.leviCivitaConnection I M`.
We define the curvature quantities of `(M, g)`. References with the same conventions: Lang,
*Lecture Notes on Riemannian Geometry* (ETH Zürich, 2020) [Lang]; Gudmundsson, *An Introduction to
Riemannian Geometry* (Lund University lecture notes) [Gud]; Lee, *Introduction to Riemannian
Manifolds* (2nd ed., GTM 176, 2018), Ch. 7-8.

* `Manifold.riemannCurvature I x u v w`: the Riemann curvature endomorphism
  `R(u, v) w = ∇_u ∇_v w - ∇_v ∇_u w - ∇_[u, v] w` of the Levi-Civita connection
  (`CovariantDerivative.extendCurvature`; [Lang, Def. 2.1], [Gud, Def. 8.8]). The opposite sign
  convention is also common.
* `Manifold.sectionalCurvature I x u v = ⟪R(u, v) v, u⟫ / (‖u‖² ‖v‖² - ⟪u, v⟫²)`, the sectional
  curvature of the plane spanned by linearly independent `u` and `v` ([Lang, Def. 2.4],
  [Gud, Def. 8.14]). The round unit sphere has sectional curvature `1` ([Gud, Example 8.23]).
* `Manifold.ricci I x v w = tr (z ↦ R(z, v) w)`, the Ricci tensor ([Lang, Def. 2.7]): the
  metric-free Ricci contraction `CovariantDerivative.extendRicci` of the Levi-Civita connection.
* `Manifold.scalarCurvature I x = ∑ i, Ric(eᵢ, eᵢ)`, the metric trace of the Ricci tensor over an
  orthonormal basis ([Gud, Def. 8.32], [Lang, Def. 2.8]). Constant sectional curvature `κ` gives
  `Ric = (n - 1) κ g` and scalar curvature `n (n - 1) κ` ([Gud, Cor. 8.33]); the round unit
  `n`-sphere has `n (n - 1)`.
* The curvature-bound predicates `Manifold.SectionalCurvatureGE`,
  `Manifold.SectionalCurvatureLE`, `Manifold.RicciGE` (`Ric ≥ k g`) and
  `Manifold.ScalarCurvatureGE`, and the Einstein condition `Manifold.IsEinstein` (`Ric = λ g`).

## Implementation notes

The curvature is computed pointwise from extensions of tangent vectors to vector fields
(`CovariantDerivative.extendCurvature`). This is the textbook curvature of `(M, g)` because the
Levi-Civita connection of a `C^∞` metric is `C^∞` (its Christoffel symbols in a chart are smooth
functions of the `g_ij` and their first derivatives), so it sends the smooth extensions to smooth
vector fields, where it is uniquely determined
(`CovariantDerivative.IsLeviCivitaConnection.uniqueness`), and the curvature expression is
tensorial. Mathlib does not yet prove that regularity of its
`leviCivitaConnection` (see the TODO in `LeviCivita.lean`); until it does, this agreement is a
standard fact that is not formalized here, and `riemannCurvature` is a function of its three
tangent arguments rather than a bundled trilinear map. For the same reason `ricci` takes its trace
through the basis `Module.finBasis ℝ (TangentSpace I x)` and `scalarCurvature` takes the metric
trace through the orthonormal basis `stdOrthonormalBasis ℝ (TangentSpace I x)`; for the textbook
curvature tensor (which is trilinear) these traces do not depend on the bases.

The declarations that do not use the metric (`CovariantDerivative.extendCurvature` and
`CovariantDerivative.extendRicci`, in
`MathlibExt.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature`) apply to any covariant
derivative on `TM`, for instance the Levi-Civita connection of a pseudo-Riemannian metric; this file
only adds the Riemannian specializations and the notions that use the inner product.

All definitions assume a `C^∞` manifold and a `C^∞` metric, as in the textbooks: this is the
hypothesis under which the identification above holds (the Levi-Civita connection itself only
needs a `C²` manifold and a `C¹` metric).
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Riemann curvature endomorphism.** For a point $x$ of a $C^\infty$ Riemannian manifold $(M, g)$
with Levi-Civita connection $\nabla$, and tangent vectors $u, v, w \in T_x M$,
$$R(u, v) w = (\nabla_X \nabla_Y W - \nabla_Y \nabla_X W - \nabla_{[X, Y]} W)(x),$$
where $X$, $Y$, $W$ are the vector fields extending $u$, $v$, $w$ that have constant coordinates
in the preferred chart at $x$. Since the Levi-Civita connection of a $C^\infty$ metric is
$C^\infty$, this is the textbook curvature endomorphism and does not depend on the extensions.

This is the sign convention of [Lang, Def. 2.1] and [Gud, Def. 8.8]; the opposite sign convention
is also common. -/
def riemannCurvature (x : M) (u v w : TangentSpace I x) : TangentSpace I x :=
  (CovariantDerivative.leviCivitaConnection I M).extendCurvature x u v w

/-- **Antisymmetry of the Riemann curvature.** Let $(M, g)$ be a $C^\infty$ Riemannian manifold.
Its Riemann curvature endomorphism $R$ is antisymmetric in its first two arguments:
$R(u, v) w = -R(v, u) w$ for every point $x \in M$ and all tangent vectors $u, v, w \in T_x M$. -/
theorem riemannCurvature_antisymm (x : M) (u v w : TangentSpace I x) :
    riemannCurvature I x u v w = - riemannCurvature I x v u w :=
  (CovariantDerivative.leviCivitaConnection I M).extendCurvature_antisymm x u v w

/-- **Sectional curvature.** Let $(M, g)$ be a $C^\infty$ Riemannian manifold modeled on a
finite-dimensional real space (boundary and corners allowed), with Riemann curvature
endomorphism $R$, and let $x \in M$. The sectional curvature of tangent vectors
$u, v \in T_x M$ is
$$K(u, v) = \frac{\langle R(u, v) v, u \rangle}{\|u\|^2 \|v\|^2 - \langle u, v \rangle^2},$$
the sectional curvature of the plane spanned by $u$ and $v$ when they are linearly independent
([Lang, Def. 2.4], [Gud, Def. 8.14]). When $u$ and $v$ are linearly dependent the denominator
vanishes and $K(u, v)$ is $0$ by definition.

With the sign convention used here for $R$, the round unit sphere has $K = 1$. -/
def sectionalCurvature (x : M) (u v : TangentSpace I x) : ℝ :=
  inner ℝ (riemannCurvature I x u v v) u / (‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2)

/-- **Sectional curvature vanishes on a vector and a multiple of it.** Let $(M, g)$ be a
$C^\infty$ Riemannian manifold modeled on a finite-dimensional real space (boundary and corners
allowed), and let $x \in M$, $u \in T_x M$ and $c \in \mathbb{R}$. Then the sectional curvature
at $x$ satisfies $K(u, cu) = 0$: the denominator $\|u\|^2 \|cu\|^2 - \langle u, cu \rangle^2$ of
its defining formula vanishes, and the quotient is then $0$ by definition. -/
theorem sectionalCurvature_smul_right (x : M) (u : TangentSpace I x) (c : ℝ) :
    sectionalCurvature I x u (c • u) = 0 := by
  have h : ‖u‖ ^ 2 * ‖c • u‖ ^ 2 - inner ℝ u (c • u) ^ 2 = 0 := by
    rw [norm_smul, inner_smul_right, real_inner_self_eq_norm_sq, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  rw [sectionalCurvature, h, div_zero]

/-- **Sectional curvature vanishes on equal vectors.** For every point $x$ of a $C^\infty$
Riemannian manifold $(M, g)$ and every tangent vector $u \in T_x M$, the sectional curvature formula
$K$ gives $K(u, u) = 0$: its denominator $\|u\|^2 \|u\|^2 - \langle u, u \rangle^2$ vanishes, where
$\langle \cdot, \cdot \rangle$ and $\|\cdot\|$ are the inner product and norm on $T_x M$ given by
$g$, and a quotient by $0$ is taken to be $0$. -/
@[simp]
theorem sectionalCurvature_self (x : M) (u : TangentSpace I x) :
    sectionalCurvature I x u u = 0 := by
  simpa using sectionalCurvature_smul_right I x u 1

/-- **Ricci curvature.** For a point $x$ of a $C^\infty$ Riemannian manifold $(M, g)$ and tangent
vectors $v, w \in T_x M$, the Ricci curvature is
$\operatorname{Ric}_x(v, w) = \sum_i e_i^*(R(e_i, v) w)$, where $R$ is the Riemann curvature
endomorphism of the Levi-Civita connection of $g$, $(e_i)$ is a fixed basis of $T_x M$ and
$(e_i^*)$ is its dual basis; the contraction itself uses no metric. Since $z \mapsto R(z, v) w$ is
linear, this is its trace and does not depend on the basis ([Lang, Def. 2.7]). The unit
$n$-sphere has $\operatorname{Ric} = (n - 1) g$. -/
def ricci (x : M) (v w : TangentSpace I x) : ℝ :=
  (CovariantDerivative.leviCivitaConnection I M).extendRicci x v w

/-- **Scalar curvature.** The scalar curvature of a $C^\infty$ Riemannian manifold $(M, g)$ at a
point $x$ is $\sum_i \operatorname{Ric}_x(e_i, e_i)$, the metric trace of the Ricci curvature
$\operatorname{Ric}$, where $(e_i)$ is a fixed orthonormal basis of $T_x M$ ([Gud, Def. 8.32]).
The unit $n$-sphere has scalar curvature $n (n - 1)$. -/
def scalarCurvature (x : M) : ℝ :=
  ∑ i, ricci I x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

variable (M)

/-- **Sectional curvature bounded below.** A $C^\infty$ Riemannian manifold $M$ has sectional
curvature at least $k \in \mathbb{R}$ when $K(u, v) \ge k$ for every point $x \in M$ and all
linearly independent tangent vectors $u, v \in T_x M$, where $K(u, v)$ is the sectional curvature
of the plane spanned by $u$ and $v$. -/
def SectionalCurvatureGE (k : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
    k ≤ sectionalCurvature I x u v

/-- **Sectional curvature bounded above.** A $C^\infty$ Riemannian manifold $M$ has sectional
curvature at most $k \in \mathbb{R}$ when $K(u, v) \le k$ for every point $x \in M$ and all
linearly independent tangent vectors $u, v \in T_x M$, where $K(u, v)$ is the sectional curvature
of the plane spanned by $u$ and $v$. -/
def SectionalCurvatureLE (k : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), LinearIndependent ℝ ![u, v] →
    sectionalCurvature I x u v ≤ k

/-- **Ricci curvature bounded below.** A $C^\infty$ Riemannian manifold $(M, g)$ has Ricci curvature
at least $k \in \mathbb{R}$, written $\operatorname{Ric} \ge k g$, when
$\operatorname{Ric}_x(v, v) \ge k \|v\|^2$ for every point $x \in M$ and every tangent vector
$v \in T_x M$, where $\operatorname{Ric}$ is the Ricci curvature and $\|v\|$ is the norm of $v$
given by $g$. -/
def RicciGE (k : ℝ) : Prop :=
  ∀ (x : M) (v : TangentSpace I x), k * ‖v‖ ^ 2 ≤ ricci I x v v

/-- **Scalar curvature bounded below.** A $C^\infty$ Riemannian manifold $M$ has scalar curvature at
least $k \in \mathbb{R}$ when its scalar curvature at every point $x \in M$ is at least $k$. -/
def ScalarCurvatureGE (k : ℝ) : Prop :=
  ∀ x : M, k ≤ scalarCurvature I x

/-- **Einstein metric.** A $C^\infty$ Riemannian manifold $(M, g)$ is Einstein when there is a real
constant $\lambda$ such that $\operatorname{Ric}_x(v, w) = \lambda \, g_x(v, w)$ for every point
$x \in M$ and all tangent vectors $v, w \in T_x M$, where $\operatorname{Ric}$ is the Ricci
curvature ([Lang], Einstein manifolds). Ricci-flat is the case $\lambda = 0$. -/
def IsEinstein : Prop :=
  ∃ c : ℝ, ∀ (x : M) (v w : TangentSpace I x), ricci I x v w = c * inner ℝ v w

end Manifold
