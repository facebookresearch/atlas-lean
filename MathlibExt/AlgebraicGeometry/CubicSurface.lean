/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Cubic surfaces in ℙ³

A *cubic surface* is a degree-`3` hypersurface in projective `3`-space `ℙ³` over a field `k`.
Following the same hypersurface pattern used for higher-dimensional cubics (a cubic fourfold is
a degree-`3` hypersurface in `ℙ⁵`, and so on), we present such a surface by its **defining
equation**: a nonzero homogeneous polynomial of degree `3` in the four homogeneous coordinates
`x₀, x₁, x₂, x₃`. The surface itself is the projective zero locus `V(f) ⊆ ℙ³`.

Clause-by-clause mapping from the informal notion to `AlgebraicGeometry.CubicSurface`:

* "cubic form in the four coordinates of `ℙ³`" ↦ `defining : MvPolynomial (Fin 4) k`;
* "of degree `3`" ↦ `defining.IsHomogeneous 3`;
* "cuts out an honest hypersurface (the equation is not identically zero)" ↦ `defining ≠ 0`.
  The zero polynomial is vacuously homogeneous of every degree, so this last clause is what pins
  the degree to exactly `3` (see `CubicSurface.totalDegree_defining`).

## Main definitions

* `AlgebraicGeometry.CubicSurface`: a cubic surface in `ℙ³` over `k`, i.e. its defining cubic form.
* `AlgebraicGeometry.CubicSurface.IsSingularPoint`: a singular point of the affine cone.
* `AlgebraicGeometry.CubicSurface.IsSmooth`: the Jacobian smoothness criterion.

## Implementation notes

The scheme `Proj (k[x₀,x₁,x₂,x₃] / (f))` is not constructible from the Mathlib API at this pin
(there is no graded-ring structure on the quotient by a homogeneous ideal), so scheme-level
smoothness is unavailable. Instead we record the classical **Jacobian criterion**:
`CubicSurface.IsSmooth` asks that the only common zero of the defining cubic and all of its
partial derivatives is the coordinate origin. This is exactly nonsingularity of the projective
surface `V(f)` over an algebraically closed field, so `IsSmooth` is only defined under an
`[IsAlgClosed k]` hypothesis; over a general field, smoothness must be checked after base
change to `AlgebraicClosure k` (checking `k`-rational points alone is strictly weaker). By Euler's identity, when `3` is invertible in
`k` the condition `f = 0` is redundant given that all partials vanish
(`CubicSurface.isSingularPoint_iff`). The definition is built purely by composing existing
Mathlib API (`MvPolynomial.IsHomogeneous`, `MvPolynomial.pderiv`, `MvPolynomial.aeval`) rather
than introducing any new primitive.
-/

@[expose] public section

namespace AlgebraicGeometry

open MvPolynomial

variable (k : Type*) [Field k]

/-- **Cubic surface.** A cubic surface over a field $k$ is a nonzero homogeneous polynomial
$f \in k[x_0, x_1, x_2, x_3]$ of degree $3$ in the four homogeneous coordinates of
$\mathbb{P}^3$, its defining equation. The surface it describes is the projective zero locus
$V(f) \subseteq \mathbb{P}^3$. -/
@[ext]
structure CubicSurface where
  /-- The homogeneous cubic form cutting out the surface. -/
  defining : MvPolynomial (Fin 4) k
  /-- The defining form has degree `3`. -/
  isHomogeneous : defining.IsHomogeneous 3
  /-- The defining form is not identically zero, so it cuts out a genuine hypersurface. -/
  defining_ne_zero : defining ≠ 0

namespace CubicSurface

variable {k}

/-- **The defining cubic has total degree three.** The defining cubic form of a cubic surface
over a field $k$ has total degree exactly $3$. -/
lemma totalDegree_defining (S : CubicSurface k) : S.defining.totalDegree = 3 :=
  S.isHomogeneous.totalDegree S.defining_ne_zero

/-- **The partial derivatives of a cubic form are quadratic.** Let $S$ be a cubic surface over a
field $k$ with defining cubic form $f \in k[x_0, x_1, x_2, x_3]$. For each $i \in \{0, 1, 2, 3\}$,
the partial derivative $\partial f / \partial x_i$ is homogeneous of degree $2$. -/
lemma isHomogeneous_pderiv (S : CubicSurface k) (i : Fin 4) :
    (pderiv i S.defining).IsHomogeneous 2 :=
  S.isHomogeneous.pderiv

/-- **Singular point of a cubic surface.** Let $S$ be a cubic surface over a field $k$ with
defining cubic form $f \in k[x_0, x_1, x_2, x_3]$. A point $x \in k^4$ is a singular point of the
affine cone over $S$ when $f(x) = 0$ and $\partial f / \partial x_i$ vanishes at $x$ for every
$i \in \{0, 1, 2, 3\}$.

Over an algebraically closed field, $S$ is a smooth projective surface exactly when the origin is
its only such point. -/
def IsSingularPoint (S : CubicSurface k) (x : Fin 4 → k) : Prop :=
  aeval x S.defining = 0 ∧ ∀ i, aeval x (pderiv i S.defining) = 0

/-- **Smooth cubic surface.** Let $k$ be an algebraically closed field and $S$ a cubic surface
over $k$ with defining cubic form $f \in k[x_0, x_1, x_2, x_3]$. The surface $S$ is smooth when
every point $x \in k^4$ at which $f$ and all its partial derivatives $\partial f / \partial x_i$
vanish is the origin, that is, when the origin is the only singular point of the affine cone
over $S$.

This is the Jacobian criterion for smoothness of the projective surface
$V(f) \subseteq \mathbb{P}^3$ cut out by $f$. -/
def IsSmooth [IsAlgClosed k] (S : CubicSurface k) : Prop :=
  ∀ x : Fin 4 → k, S.IsSingularPoint x → x = 0

/-- **Vanishing partial derivatives force the cubic to vanish when $3 \neq 0$.** Let $S$ be a
cubic surface over a field $k$ in which $3 \neq 0$, and let $f \in k[x_0, x_1, x_2, x_3]$ be its
defining cubic form. If $x \in k^4$ is a point at which every partial derivative
$\partial f / \partial x_i$ vanishes, then $f(x) = 0$.

This follows from Euler's identity $\sum_i x_i \, \partial f / \partial x_i = 3 f$. -/
lemma aeval_defining_eq_zero_of_pderiv (h3 : (3 : k) ≠ 0) (S : CubicSurface k)
    {x : Fin 4 → k} (hx : ∀ i, aeval x (pderiv i S.defining) = 0) :
    aeval x S.defining = 0 := by
  have euler := S.isHomogeneous.sum_X_mul_pderiv
  apply_fun aeval x at euler
  rw [map_sum, map_nsmul, nsmul_eq_mul] at euler
  simp only [map_mul, aeval_X, hx, mul_zero, Finset.sum_const_zero] at euler
  rw [Nat.cast_ofNat] at euler
  rcases mul_eq_zero.1 euler.symm with h | h
  · exact absurd h h3
  · exact h

/-- **Singular points via partial derivatives.** Let $S$ be a cubic surface over a field $k$ in
which $3 \neq 0$, and let $f \in k[x_0, x_1, x_2, x_3]$ be its defining cubic form. A point
$x \in k^4$ is a singular point of the affine cone over $S$ if and only if every partial
derivative $\partial f / \partial x_i$ vanishes at $x$.

The condition $f(x) = 0$ in the definition of a singular point is then automatic, by Euler's
identity. -/
lemma isSingularPoint_iff (h3 : (3 : k) ≠ 0) (S : CubicSurface k) (x : Fin 4 → k) :
    S.IsSingularPoint x ↔ ∀ i, aeval x (pderiv i S.defining) = 0 :=
  ⟨fun h => h.2, fun h => ⟨aeval_defining_eq_zero_of_pderiv h3 S h, h⟩⟩

end CubicSurface

section Examples

/-- **Fermat cubic surface.** Over a field $k$, the Fermat cubic surface is the cubic surface in
$\mathbb{P}^3$ with defining cubic form $x_0^3 + x_1^3 + x_2^3 + x_3^3$.

It is smooth when the characteristic of $k$ is not $3$. -/
noncomputable def fermatCubicSurface : CubicSurface k where
  defining := X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 + X 3 ^ 3
  isHomogeneous := by
    have h : ∀ i : Fin 4, ((X i : MvPolynomial (Fin 4) k) ^ 3).IsHomogeneous 3 := fun i => by
      simpa using (isHomogeneous_X k i).pow 3
    exact (((h 0).add (h 1)).add (h 2)).add (h 3)
  defining_ne_zero := by
    intro h
    have := congrArg (aeval (![1, 0, 0, 0] : Fin 4 → k)) h
    simp at this

/-- **Triple plane.** Over a field $k$, the triple plane is the cubic surface in $\mathbb{P}^3$
with defining cubic form $x_0^3 \in k[x_0, x_1, x_2, x_3]$, that is, the plane $x_0 = 0$
counted three times.

It is non-reduced, and every point of the plane $x_0 = 0$ is a singular point. -/
noncomputable def triplePlane : CubicSurface k where
  defining := X 0 ^ 3
  isHomogeneous := by simpa using (isHomogeneous_X k 0).pow 3
  defining_ne_zero := pow_ne_zero 3 (X_ne_zero 0)

end Examples

end AlgebraicGeometry

end
