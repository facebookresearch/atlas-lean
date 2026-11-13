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
change to `AlgebraicClosure k` (checking `k`-rational points alone is strictly weaker). By Euler's
identity, when `3` is invertible in
`k` the condition `f = 0` is redundant given that all partials vanish
(`CubicSurface.isSingularPoint_iff`). The definition is built purely by composing existing
Mathlib API (`MvPolynomial.IsHomogeneous`, `MvPolynomial.pderiv`, `MvPolynomial.aeval`) rather
than introducing any new primitive.
-/

@[expose] public section

namespace AlgebraicGeometry

open MvPolynomial

variable (k : Type*) [Field k]

/-- A cubic surface in `ℙ³` over `k`, presented by its defining equation: a nonzero homogeneous
polynomial of degree `3` in the four homogeneous coordinates. The surface is the projective zero
locus `V(defining) ⊆ ℙ³`. -/
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

/-- The defining cubic of a cubic surface has total degree exactly `3`. -/
lemma totalDegree_defining (S : CubicSurface k) : S.defining.totalDegree = 3 :=
  S.isHomogeneous.totalDegree S.defining_ne_zero

/-- Each partial derivative of the defining cubic is homogeneous of degree `2`: the gradient of a
cubic surface is quadratic. -/
lemma isHomogeneous_pderiv (S : CubicSurface k) (i : Fin 4) :
    (pderiv i S.defining).IsHomogeneous 2 :=
  S.isHomogeneous.pderiv

/-- A point `x` is a singular point of the affine cone over `S` when the defining cubic and all of
its partial derivatives vanish at `x`. Over an algebraically closed field, `S` is a smooth
projective surface exactly when its only such point is the origin. -/
def IsSingularPoint (S : CubicSurface k) (x : Fin 4 → k) : Prop :=
  aeval x S.defining = 0 ∧ ∀ i, aeval x (pderiv i S.defining) = 0

/-- The Jacobian smoothness criterion: the coordinate origin is the only common zero of the
defining cubic and its partial derivatives. -/
@[nolint unusedArguments] -- `IsAlgClosed k` is intended; see the module docstring.
def IsSmooth [IsAlgClosed k] (S : CubicSurface k) : Prop :=
  ∀ x : Fin 4 → k, S.IsSingularPoint x → x = 0

/-- Euler's identity: when `3` is invertible in `k`, the vanishing of every partial derivative of
the defining cubic at a point forces the cubic itself to vanish there. -/
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

/-- When `3` is invertible in `k`, a point is singular exactly when all partial derivatives of the
defining cubic vanish there; the equation `f = 0` is then automatic (Euler's identity). -/
lemma isSingularPoint_iff (h3 : (3 : k) ≠ 0) (S : CubicSurface k) (x : Fin 4 → k) :
    S.IsSingularPoint x ↔ ∀ i, aeval x (pderiv i S.defining) = 0 :=
  ⟨fun h => h.2, fun h => ⟨aeval_defining_eq_zero_of_pderiv h3 S h, h⟩⟩

end CubicSurface

section Examples

/-- The Fermat cubic surface `x₀³ + x₁³ + x₂³ + x₃³ = 0`, the standard ordinary example (smooth
over fields of characteristic other than `3`). -/
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

/-- The triple hyperplane `x₀³ = 0`, a degenerate (non-reduced) boundary example that is a cubic
surface but is singular. -/
noncomputable def triplePlane : CubicSurface k where
  defining := X 0 ^ 3
  isHomogeneous := by simpa using (isHomogeneous_X k 0).pow 3
  defining_ne_zero := pow_ne_zero 3 (X_ne_zero 0)

end Examples

end AlgebraicGeometry

end
