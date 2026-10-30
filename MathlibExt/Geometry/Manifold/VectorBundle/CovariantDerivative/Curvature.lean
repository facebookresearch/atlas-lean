/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The curvature expression of a covariant derivative on extensions

For a covariant derivative `∇` on a vector bundle `V → M`, the curvature is
```
R(X, Y) σ = ∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X, Y] σ
```
with the sign convention of Lang, *Lecture Notes on Riemannian Geometry* (ETH Zürich, 2020),
Def. 2.1, and Gudmundsson, *An Introduction to Riemannian Geometry* (Lund University lecture
notes), Def. 8.8 (also Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Ch. 7). The opposite
sign convention is also common.

We define `CovariantDerivative.extendCurvature`, the value of this expression at a point `x` on the
extensions `FiberBundle.extend` of tangent vectors `u v : T_x M` and of a vector `σ : V x`, in the
way Mathlib computes torsion (`Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion`).
For the tangent bundle these extensions are the vector fields whose coordinates in the preferred
chart at `x` are constant, so the formula is the usual expression of the curvature in that chart.

## Regularity

The term `∇_X ∇_Y σ` applies `∇` to the section `∇_Y σ`. A covariant derivative is only constrained
on sections that are differentiable, so `extendCurvature` is the curvature `R(u, v) σ`, and is
independent of the chosen extensions, only for connections that send `C²` sections to `C¹`
sections, for instance the Levi-Civita connection of a `C^∞` metric
(`Manifold.riemannCurvature`). For other connections the value can depend on values of `∇` that the
covariant-derivative axioms leave unconstrained, which is why the definition carries the explicit
name `extendCurvature` rather than `curvature`. Mathlib does not yet prove the regularity of its
Levi-Civita connection, so this file does not build a trilinear curvature tensor.

## Main definitions and results

* `CovariantDerivative.extendCurvature`: the curvature expression `R(u, v) σ ∈ V x` on extensions.
* `CovariantDerivative.extendCurvature_antisymm`: `R(u, v) σ = - R(v, u) σ`.
* `CovariantDerivative.extendRicci`: for a covariant derivative on `TM`, the Ricci contraction
  `Ric(v, w) = tr (z ↦ R(z, v) w)` (Lang, Def. 2.7), a trace that uses no metric.
-/

@[expose] public section

open Bundle FiberBundle VectorField
open scoped Manifold

noncomputable section

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/-- The curvature expression of a covariant derivative `cov` on a vector bundle `V`, at a point `x`,
on tangent vectors `u v : T_x M` and a vector `σ : V x`:
`(∇_X ∇_Y S - ∇_Y ∇_X S - ∇_[X, Y] S)(x)`, where `X`, `Y`, `S` are the extensions
`extend E u`, `extend E v`, `extend F σ`.

When `cov` sends `C²` sections to `C¹` sections (for instance the Levi-Civita connection of a `C^∞`
metric), this is the curvature `R(u, v) σ` with the sign convention of the module docstring, and
it does not depend on the extensions. For other connections it can
depend on unconstrained values of `cov`; see the module docstring. -/
def extendCurvature (cov : CovariantDerivative I F V) (x : M) (u v : TangentSpace I x) (σ : V x) :
    V x :=
  cov (fun y ↦ cov (extend F σ) y (extend E v y)) x u
    - cov (fun y ↦ cov (extend F σ) y (extend E u y)) x v
    - cov (extend F σ) x (mlieBracket I (extend E u) (extend E v) x)

/-- The curvature expression is antisymmetric in its two tangent arguments:
`R(u, v) σ = - R(v, u) σ`. -/
theorem extendCurvature_antisymm (cov : CovariantDerivative I F V) (x : M)
    (u v : TangentSpace I x) (σ : V x) :
    cov.extendCurvature x u v σ = - cov.extendCurvature x v u σ := by
  simp only [extendCurvature]
  rw [mlieBracket_swap_apply (V := extend E v), map_neg]
  abel

section Ricci

variable [FiniteDimensional 𝕜 E]

/-- The Ricci contraction of the curvature expression of a covariant derivative on the tangent
bundle: `Ric(v, w) = tr (z ↦ R(z, v) w)` (Lang, *Lecture Notes on Riemannian Geometry*, Def. 2.7),
with the trace computed in the basis `Module.finBasis 𝕜 (T_x M)` and its coordinate
functionals. No metric is involved. For a connection to which `extendCurvature` applies (see the
module docstring), `z ↦ R(z, v) w` is linear and this is its trace, independent of the basis. -/
def extendRicci (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (v w : TangentSpace I x) : 𝕜 :=
  ∑ i, (Module.finBasis 𝕜 (TangentSpace I x)).coord i
    (cov.extendCurvature x (Module.finBasis 𝕜 (TangentSpace I x) i) v w)

end Ricci

end CovariantDerivative
