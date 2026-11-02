/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Killing vector fields on a Riemannian manifold

Let `M` be a `C^∞` manifold with a `C^∞` Riemannian metric, given by `IsManifold`,
`RiemannianBundle` and `IsContMDiffRiemannianBundle` instances, and let `∇` be its
Levi-Civita connection. This file defines Killing fields via Killing's equation.

## Main definitions

* `Manifold.IsKillingVectorField I X`: `C^∞` plus `⟪∇_u X, v⟫ + ⟪u, ∇_v X⟫ = 0`.
* `Manifold.killingVectorFields I M`: the submodule of Killing fields.

## Main results

* `inner_leviCivitaConnection_self` and the polarization iff.
* `mvfderiv_inner_sub_inner_mlieBracket`: the `(L_X g)(Y, Z)` identity.
* `isKillingVectorField_iff_mvfderiv_inner`: Killing iff `L_X g = 0`.
* Zero, addition, scaling, membership and extensionality for Killing fields.

## Implementation notes

Killing's equation is the definition because Mathlib has the Levi-Civita connection
but no Lie derivative of tensors; `isKillingVectorField_iff_mvfderiv_inner` identifies
it with `L_X g = 0`. Smoothness is required (the textbook hypothesis); it excludes
fields where the connection takes its junk value `0`.

## References

* B. O'Neill, Semi-Riemannian Geometry with Applications to Relativity (1983).
* P. Petersen, Riemannian Geometry (3rd ed., GTM 171, Springer, 2016).
* Burns and Matveev, Open problems and questions about geodesics, Ergodic Theory
  Dynam. Systems 41 (2021), §10.2.
-/

@[expose] public section

open Bundle CovariantDerivative
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Killing vector field.** Let $M$ be a finite-dimensional smooth manifold, possibly with
boundary or corners, with a smooth Riemannian metric $g = \langle \cdot, \cdot \rangle$ and its
Levi-Civita connection $\nabla$. A vector field $X$ on $M$ is a Killing vector field if $X$ is
smooth and satisfies Killing's equation: for every point $x \in M$ and all tangent vectors
$u, v \in T_x M$,
$$\langle \nabla_u X, v \rangle + \langle u, \nabla_v X \rangle = 0.$$

In index notation this is $\nabla_i X_j + \nabla_j X_i = 0$, and it is equivalent to the
vanishing of the Lie derivative $L_X g$ of the metric. Smoothness is part of the definition, as
in the textbook definition.

Source: Burns and Matveev (2021), §10.2, for motivation: a Killing field $V$ gives the linear
first integral $\xi \mapsto g(V, \xi)$ of geodesic flow, not formalized here. That the flow of
a Killing field consists of isometries is not proved here. -/
structure IsKillingVectorField (X : (x : M) → TangentSpace I x) : Prop where
  contMDiff : CMDiff ∞ (T% X)
  inner_leviCivitaConnection_add : ∀ (x : M) (u v : TangentSpace I x),
    inner ℝ (leviCivitaConnection I M X x u) v +
      inner ℝ u (leviCivitaConnection I M X x v) = 0

/-- **Killing's equation on the diagonal.** Let $X$ be a Killing vector field on a smooth
Riemannian manifold $M$ with Levi-Civita connection $\nabla$. Then
$\langle \nabla_u X, u \rangle = 0$ for every point $x \in M$ and every tangent vector
$u \in T_x M$: a Killing field preserves lengths infinitesimally. -/
theorem IsKillingVectorField.inner_leviCivitaConnection_self
    {X : (x : M) → TangentSpace I x} (hX : IsKillingVectorField I X)
    (x : M) (u : TangentSpace I x) :
    inner ℝ (leviCivitaConnection I M X x u) u = 0 := by
  have hAdd : inner ℝ (leviCivitaConnection I M X x u) u +
      inner ℝ u (leviCivitaConnection I M X x u) = 0 :=
    hX.inner_leviCivitaConnection_add x u u
  have hSym : inner ℝ u (leviCivitaConnection I M X x u) =
      inner ℝ (leviCivitaConnection I M X x u) u := real_inner_comm _ _
  rw [hSym] at hAdd
  linarith

/-- **Killing fields via the diagonal of Killing's equation.** Let $M$ be a smooth Riemannian
manifold with Levi-Civita connection $\nabla$. A vector field $X$ on $M$ is a Killing vector
field if and only if $X$ is smooth and $\langle \nabla_u X, u \rangle = 0$ for every point
$x \in M$ and every tangent vector $u \in T_x M$.

The converse direction is a polarization argument. -/
theorem isKillingVectorField_iff_inner_leviCivitaConnection_self
    {X : (x : M) → TangentSpace I x} :
    IsKillingVectorField I X ↔ CMDiff ∞ (T% X) ∧
      ∀ (x : M) (u : TangentSpace I x),
        inner ℝ (leviCivitaConnection I M X x u) u = 0 := by
  constructor
  · intro hX
    exact ⟨hX.contMDiff,
      fun x u ↦ IsKillingVectorField.inner_leviCivitaConnection_self I hX x u⟩
  · intro h
    obtain ⟨hSmooth, hSelf⟩ := h
    refine ⟨hSmooth, fun x u v ↦ ?_⟩
    have hUV : inner ℝ (leviCivitaConnection I M X x (u + v)) (u + v) = 0 :=
      hSelf x (u + v)
    have hU : inner ℝ (leviCivitaConnection I M X x u) u = 0 := hSelf x u
    have hV : inner ℝ (leviCivitaConnection I M X x v) v = 0 := hSelf x v
    have hAdd : leviCivitaConnection I M X x (u + v) =
        (leviCivitaConnection I M X x u) + (leviCivitaConnection I M X x v) :=
      map_add _ _ _
    simp only [hAdd, inner_add_left, inner_add_right] at hUV
    have hSym : inner ℝ (leviCivitaConnection I M X x v) u =
        inner ℝ u (leviCivitaConnection I M X x v) := real_inner_comm _ _
    rw [hU, hV, hSym] at hUV
    linear_combination hUV

/-- **The Lie derivative of the metric via the Levi-Civita connection.** Let $M$ be a smooth
manifold modeled on a finite-dimensional real normed space (possibly with corners), with a smooth
Riemannian metric $g = \langle \cdot, \cdot \rangle$ and Levi-Civita connection $\nabla$, and let
$X$, $Y$, $Z$ be vector fields on $M$ that are differentiable at a point $x$. Write $[\cdot, \cdot]$
for the Lie bracket of vector fields and $X_x \langle Y, Z \rangle$ for the derivative at $x$ of
the function $y \mapsto \langle Y_y, Z_y \rangle$ in the direction $X_x$. Then
$$
X_x \langle Y, Z \rangle - \langle [X, Y]_x, Z_x \rangle - \langle Y_x, [X, Z]_x \rangle
= \langle \nabla_{Y_x} X, Z_x \rangle + \langle Y_x, \nabla_{Z_x} X \rangle.
$$
The left-hand side is $(\mathcal{L}_X g)(Y, Z)$ at $x$. -/
theorem mvfderiv_inner_sub_inner_mlieBracket
    {X Y Z : (x : M) → TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    ((d% (fun y ↦ inner ℝ (Y y) (Z y)) x) (X x)) -
        inner ℝ (VectorField.mlieBracket I X Y x) (Z x) -
        inner ℝ (Y x) (VectorField.mlieBracket I X Z x) =
      inner ℝ (leviCivitaConnection I M X x (Y x)) (Z x) +
        inner ℝ (Y x) (leviCivitaConnection I M X x (Z x)) := by
  have hcov := isMetricCompatible_leviCivitaConnection I (M := M)
  have hMetric : ((d% (fun y ↦ inner ℝ (Y y) (Z y)) x) (X x)) =
      inner ℝ (leviCivitaConnection I M Y x (X x)) (Z x) +
        inner ℝ (Y x) (leviCivitaConnection I M Z x (X x)) :=
    hcov.mvfderiv_inner_eq X hY hZ
  have hTXY : (leviCivitaConnection I M Y x (X x)) -
      (leviCivitaConnection I M X x (Y x)) = VectorField.mlieBracket I X Y x :=
    (torsion_eq_zero_iff (leviCivitaConnection I M)).mp
      (torsion_leviCivitaConnection_eq_zero I (M := M)) hX hY
  have hTXZ : (leviCivitaConnection I M Z x (X x)) -
      (leviCivitaConnection I M X x (Z x)) = VectorField.mlieBracket I X Z x :=
    (torsion_eq_zero_iff (leviCivitaConnection I M)).mp
      (torsion_leviCivitaConnection_eq_zero I (M := M)) hX hZ
  rw [hMetric, ← hTXY, ← hTXZ, inner_sub_left, inner_sub_right]
  ring

/-- **Killing fields are those with vanishing Lie derivative of the metric.** Let $M$ be a smooth
Riemannian manifold with metric $g = \langle \cdot, \cdot \rangle$. A vector field $X$ on $M$ is
a Killing vector field if and only if $X$ is smooth and, for every point $x \in M$ and all vector
fields $Y$ and $Z$ on $M$ that are differentiable at $x$,
$$X_x \langle Y, Z \rangle - \langle [X, Y]_x, Z_x \rangle - \langle Y_x, [X, Z]_x \rangle = 0,$$
where $X_x \langle Y, Z \rangle$ is the derivative at $x$ of the function
$y \mapsto \langle Y_y, Z_y \rangle$ in the direction $X_x$, and $[X, Y]$ is the Lie bracket.
The left-hand side is $(L_X g)(Y, Z)$ at $x$, where $L_X g$ is the Lie derivative of $g$ along
$X$. -/
theorem isKillingVectorField_iff_mvfderiv_inner
    {X : (x : M) → TangentSpace I x} :
    IsKillingVectorField I X ↔ CMDiff ∞ (T% X) ∧
      ∀ (x : M) (Y Z : (x : M) → TangentSpace I x), MDiffAt (T% Y) x →
        MDiffAt (T% Z) x → ((d% (fun y ↦ inner ℝ (Y y) (Z y)) x) (X x)) -
          inner ℝ (VectorField.mlieBracket I X Y x) (Z x) -
          inner ℝ (Y x) (VectorField.mlieBracket I X Z x) = 0 := by
  constructor
  · intro hX
    refine ⟨hX.contMDiff, fun x Y Z hY hZ ↦ ?_⟩
    have hXx : MDiffAt (T% X) x := hX.contMDiff.mdifferentiableAt (by simp)
    have hC1 := mvfderiv_inner_sub_inner_mlieBracket I hXx hY hZ
    have hKill := hX.inner_leviCivitaConnection_add x (Y x) (Z x)
    rw [hC1]
    exact hKill
  · intro h
    obtain ⟨hSmooth, hVanish⟩ := h
    refine ⟨hSmooth, fun x u v ↦ ?_⟩
    have hXx : MDiffAt (T% X) x := hSmooth.mdifferentiableAt (by simp)
    have hY : MDiffAt (T% (FiberBundle.extend E u)) x :=
      FiberBundle.mdifferentiableAt_extend I E u
    have hZ : MDiffAt (T% (FiberBundle.extend E v)) x :=
      FiberBundle.mdifferentiableAt_extend I E v
    have hV := hVanish x (FiberBundle.extend E u) (FiberBundle.extend E v) hY hZ
    have hC1 := mvfderiv_inner_sub_inner_mlieBracket I hXx hY hZ
    have hYu : FiberBundle.extend E u x = u := FiberBundle.extend_apply_self E u
    have hZv : FiberBundle.extend E v x = v := FiberBundle.extend_apply_self E v
    rw [hC1] at hV
    rw [hYu, hZv] at hV
    exact hV

/-- **The zero field is Killing.** On a smooth Riemannian manifold, the zero vector field is a
Killing vector field. -/
theorem isKillingVectorField_zero :
    IsKillingVectorField I (0 : (x : M) → TangentSpace I x) := by
  have hSmooth : CMDiff ∞ (T% (0 : (x : M) → TangentSpace I x)) :=
    contMDiff_zeroSection ℝ _
  refine ⟨hSmooth, fun x u v ↦ ?_⟩
  have hCov0 : leviCivitaConnection I M (0 : (x : M) → TangentSpace I x) = 0 :=
    CovariantDerivative.zero (leviCivitaConnection I M)
  have hU : leviCivitaConnection I M (0 : (x : M) → TangentSpace I x) x u = 0 := by
    simp [hCov0]
  have hV : leviCivitaConnection I M (0 : (x : M) → TangentSpace I x) x v = 0 := by
    simp [hCov0]
  rw [hU, hV]
  simp

/-- **Sum of Killing fields.** On a smooth Riemannian manifold, the sum $X + Y$ of two Killing
vector fields $X$ and $Y$ is a Killing vector field. -/
theorem IsKillingVectorField.add {X Y : (x : M) → TangentSpace I x}
    (hX : IsKillingVectorField I X) (hY : IsKillingVectorField I Y) :
    IsKillingVectorField I (X + Y) := by
  have hSmooth : CMDiff ∞ (T% (X + Y)) := hX.contMDiff.add_section hY.contMDiff
  refine ⟨hSmooth, fun x u v ↦ ?_⟩
  have hXx : MDiffAt (T% X) x := hX.contMDiff.mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := hY.contMDiff.mdifferentiableAt (by simp)
  have hAddCov : leviCivitaConnection I M (X + Y) x =
      (leviCivitaConnection I M X x) + (leviCivitaConnection I M Y x) :=
    (isCovariantDerivativeOn (leviCivitaConnection I M)).add hXx hYx
  have hU : leviCivitaConnection I M (X + Y) x u =
      (leviCivitaConnection I M X x u) + (leviCivitaConnection I M Y x u) := by
    simp [hAddCov]
  have hV : leviCivitaConnection I M (X + Y) x v =
      (leviCivitaConnection I M X x v) + (leviCivitaConnection I M Y x v) := by
    simp [hAddCov]
  have hXeq : inner ℝ (leviCivitaConnection I M X x u) v +
      inner ℝ u (leviCivitaConnection I M X x v) = 0 :=
    hX.inner_leviCivitaConnection_add x u v
  have hYeq : inner ℝ (leviCivitaConnection I M Y x u) v +
      inner ℝ u (leviCivitaConnection I M Y x v) = 0 :=
    hY.inner_leviCivitaConnection_add x u v
  rw [hU, hV, inner_add_left, inner_add_right]
  linarith

/-- **Real multiples of Killing fields.** On a smooth Riemannian manifold, if $X$ is a Killing
vector field and $c$ is a real number, then $c X$ is a Killing vector field. -/
theorem IsKillingVectorField.const_smul {X : (x : M) → TangentSpace I x}
    (hX : IsKillingVectorField I X) (c : ℝ) : IsKillingVectorField I (c • X) := by
  have hSmooth : CMDiff ∞ (T% (c • X)) := hX.contMDiff.const_smul_section
  refine ⟨hSmooth, fun x u v ↦ ?_⟩
  have hXx : MDiffAt (T% X) x := hX.contMDiff.mdifferentiableAt (by simp)
  have hSmulCov : leviCivitaConnection I M (c • X) x =
      c • (leviCivitaConnection I M X x) :=
    (isCovariantDerivativeOn (leviCivitaConnection I M)).smul_const c hXx
  have hU : leviCivitaConnection I M (c • X) x u =
      c • (leviCivitaConnection I M X x u) := by simp [hSmulCov]
  have hV : leviCivitaConnection I M (c • X) x v =
      c • (leviCivitaConnection I M X x v) := by simp [hSmulCov]
  have hXeq : inner ℝ (leviCivitaConnection I M X x u) v +
      inner ℝ u (leviCivitaConnection I M X x v) = 0 :=
    hX.inner_leviCivitaConnection_add x u v
  rw [hU, hV, inner_smul_left, inner_smul_right]
  simp
  linear_combination c * hXeq

variable (M)

/-- **Space of Killing vector fields.** For a smooth Riemannian manifold $M$, the Killing vector
fields on $M$ form a real linear subspace of the real vector space of all (not necessarily
continuous) vector fields on $M$. -/
def killingVectorFields : Submodule ℝ (Π x : M, TangentSpace I x) where
  carrier := {X | IsKillingVectorField I X}
  zero_mem' := isKillingVectorField_zero I
  add_mem' := fun hX hY ↦ IsKillingVectorField.add I hX hY
  smul_mem' := fun c _X hX ↦ IsKillingVectorField.const_smul I hX c

/-- **Membership in the space of Killing fields.** A vector field $X$ on a smooth Riemannian
manifold $M$ lies in the space of Killing vector fields on $M$ if and only if $X$ is a Killing
vector field. -/
@[simp]
theorem mem_killingVectorFields {X : (x : M) → TangentSpace I x} :
    X ∈ killingVectorFields I M ↔ IsKillingVectorField I X :=
  Iff.rfl

/-- **Extensionality for Killing fields.** Two elements $a$ and $b$ of the space of
Killing vector fields on a smooth Riemannian manifold $M$ that agree at every point
$x \in M$ are equal. -/
@[ext]
theorem killingVectorFields.ext {a b : killingVectorFields I M}
    (h : ∀ x : M, (a : Π x : M, TangentSpace I x) x = (b : Π x : M, TangentSpace I x) x) :
    a = b := by
  apply Subtype.ext
  funext x
  exact h x

end Manifold
