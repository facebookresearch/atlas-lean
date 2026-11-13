/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pencils of quadrics in eight variables split off three hyperbolic planes (AIM Question 3(b))

AIM workshop Rational and integral points on higher dimensional varieties (2002), problem list,
Question 3(b) (Colliot-Thélène): given two quadratic forms `f₁, f₂` as above in `8` variables over a
`p`-adic field `k`, with `f₁ = f₂ = 0` smooth (so that `det(λ f₁ + μ f₂)` is separable), does there
exist `(λ, μ) ∈ ℙ¹(k)` such that `λ f₁ + μ f₂` contains `3` hyperbolic planes? A solution would give
a local-global principle for smooth intersections of two quadrics in `ℙ⁷`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public section

namespace MathlibExt.NumberTheory.PencilHyperbolicPlanesAIMAlgebraicNumberTheoryProblem87Wanted

/-!
Source: AIM workshop Rational and integral points on higher dimensional varieties (ARCC, December
2002), problem list, Question 3(b) (Colliot-Thélène),
https://aimath.org/WWN/qptsurface2/qptsurface2.pdf. UnsolvedMath record UM-20000435
(`AIM-ALGEBRAIC_NUMBER_THEORY-0087`), dataset ulamai/UnsolvedMath v1.8.0.

Forms are `fᵢ(x) = xᵀ Mᵢ x` (Mathlib's `Matrix.toQuadraticForm' Mᵢ`) with `Mᵢ` symmetric (`k` has
characteristic `0`); smoothness of `f₁ = f₂ = 0 ⊂ ℙ⁷` is the Jacobian criterion over an algebraic
closure (at every nonzero common zero the gradients `2 M₁ x, 2 M₂ x` are independent); a `p`-adic
field is a finite extension of `ℚ_p`. Containing (splitting off) three hyperbolic planes is having a
`3`-dimensional totally isotropic subspace, for the nondegenerate member `λ f₁ + μ f₂` the theorem
provides. The resolving theorems (Colliot-Thélène's Théorème 7.3, Heath-Brown's Theorem 2) assume a
nontrivial common zero over `k` (`X(k) ≠ ∅`), the situation of the local-global application the
problem names; Heath-Brown presents his Theorem 2 as the resolution of this local problem of
Colliot-Thélène, Sansuc and Swinnerton-Dyer. The problem as printed does not state the hypothesis,
and the case `X(k) = ∅` is not formalized.
-/

open Matrix

/-- The intersection `f₁ = f₂ = 0` of the quadrics `fᵢ(x) = xᵀ Mᵢ x` (`Matrix.toQuadraticForm' Mᵢ`)
in `ℙ⁷` is nonsingular: at every nonzero common zero over an algebraic closure of `k`, the gradients
`2 M₁ x` and `2 M₂ x` are linearly independent. -/
def IsNonsingularPencil {k : Type*} [Field k] (M₁ M₂ : Matrix (Fin 8) (Fin 8) k) : Prop :=
  ∀ x : Fin 8 → AlgebraicClosure k, x ≠ 0 →
    (M₁.map (algebraMap k (AlgebraicClosure k))).toQuadraticForm' x = 0 →
    (M₂.map (algebraMap k (AlgebraicClosure k))).toQuadraticForm' x = 0 →
    LinearIndependent (AlgebraicClosure k)
      ![M₁.map (algebraMap k (AlgebraicClosure k)) *ᵥ x,
        M₂.map (algebraMap k (AlgebraicClosure k)) *ᵥ x]

/-- The local theorem for pencils of quadrics in eight variables (Heath-Brown; Colliot-Thélène):
over every `p`-adic field `k`, if `f₁ = xᵀ M₁ x` and `f₂ = xᵀ M₂ x` (`M₁, M₂` symmetric) define a
nonsingular intersection in `ℙ⁷` with a nontrivial common zero over `k`, then some nondegenerate
form `λ f₁ + μ f₂` of the pencil splits off three hyperbolic planes, i.e. has a `3`-dimensional
totally isotropic subspace. -/
def pencilSplitsThreeHyperbolicPlanes : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]
    (M₁ M₂ : Matrix (Fin 8) (Fin 8) k), M₁.IsSymm → M₂.IsSymm → IsNonsingularPencil M₁ M₂ →
    (∃ x : Fin 8 → k, x ≠ 0 ∧ M₁.toQuadraticForm' x = 0 ∧ M₂.toQuadraticForm' x = 0) →
    ∃ a b : k, (a • M₁ + b • M₂).det ≠ 0 ∧ ∃ W : Submodule k (Fin 8 → k),
      Module.finrank k W = 3 ∧ ∀ w ∈ W, (a • M₁ + b • M₂).toQuadraticForm' w = 0

/--
Resolved true (for pencils with a common zero over `k`): Colliot-Thélène proved that over every
`p`-adic field `k` a smooth intersection `f = g = 0` of two quadrics in `ℙ⁷` with a `k`-point has a
nondegenerate member `λ f + μ g` of its pencil containing three hyperbolic planes; Heath-Brown had
proved it when the residue field has at least `32` elements. Source: AIM workshop Rational and
integral points on higher dimensional varieties (ARCC, December 2002), problem list, Question 3(b)
(Colliot-Thélène), https://aimath.org/WWN/qptsurface2/qptsurface2.pdf; resolution: J.-L.
Colliot-Thélène, Retour sur l'arithmétique des intersections de deux quadriques (with an appendix by
A. Kuznetsov), J. reine angew. Math. (2024), doi:10.1515/crelle-2023-0081, arXiv:2208.04121; D. R.
Heath-Brown, Zeros of pairs of quadratic forms, J. reine angew. Math. 739 (2018), 41-80,
arXiv:1304.3894, Colliot-Thélène, Théorème 7.3 of arXiv:2208.04121v4 (the version carrying the
Crelle DOI): for k a p-adic field and X ⊂ ℙ⁷_k a smooth complete intersection of two quadrics f = g
= 0 with X(k) non-empty, (b) there is a nondegenerate quadratic form λf + μg, with λ, μ ∈ k, that
contains 3H (three hyperbolic planes); the paragraph before it recalls that Heath-Brown [HB18, Thm.
2] proved this under the additional hypotheses X(k) ≠ ∅ and residue field of cardinality at least
32. Heath-Brown, Theorem 2: k_v the completion of a number field at a finite place with residue
field of size at least 32, Q1, Q2 in 8 variables over k_v with Q1 = Q2 = 0 nonsingular and a
non-trivial common zero over k_v; then some form a1 Q1 + a2 Q2 contains at least 3 hyperbolic
planes; his introduction calls this 'a purely local problem concerning the forms Q1 and Q2' left
open by Colliot-Thélène, Sansuc and Swinnerton-Dyer: 'This we now resolve in the following theorem',
https://doi.org/10.1515/crelle-2023-0081.
-/
public theorem_wanted pencilSplitsThreeHyperbolicPlanes_holds : pencilSplitsThreeHyperbolicPlanes

end MathlibExt.NumberTheory.PencilHyperbolicPlanesAIMAlgebraicNumberTheoryProblem87Wanted
