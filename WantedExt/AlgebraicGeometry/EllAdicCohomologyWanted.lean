/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.EllAdicCohomology

@[expose] public noncomputable section

/-!
# Finiteness and vanishing of ℓ-adic cohomology

For a proper smooth scheme `X` over an algebraically closed field in which `ℓ` is invertible,
the integral `ℓ`-adic cohomology `H^n(X, ℤ_ℓ)` is a finitely generated `ℤ_ℓ`-module (torsion is
allowed) and the rational cohomology `ℚ_ℓ ⊗ H^n(X, ℤ_ℓ)` is finite-dimensional; if `X` has pure
relative dimension `d`, both vanish for `n > 2d`. The rational statements follow from the integral
ones by base change.

References: finiteness of cohomology with finite coefficients for proper morphisms, SGA 4,
Exposé XIV, §1; the bound `2d` on cohomological dimension, SGA 4, Exposé X, Corollary 4.3; the
passage to `ℓ`-adic coefficients on the pro-étale site, Bhatt–Scholze, *The pro-étale topology for
schemes* (2015), §6.8.
-/

namespace WantedExt.AlgebraicGeometry.EllAdicCohomologyWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open _root_.MathlibExt.AlgebraicGeometry.EllAdicCohomology

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Integral cohomology is finitely generated over integral coefficients in the
proper smooth algebraically closed setting. Torsion is permitted. -/
public theorem_wanted integralFinite
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (n : ℕ)
    [IsProper X.hom] [Smooth X.hom]
    (hℓ : ℓ ≠ ringChar k) :
    Module.Finite ℤ_[ℓ] (X.left.EllAdicCohomology ℓ n)

/-- Let $\ell$ be a prime, $k$ an algebraically closed field of characteristic different from
$\ell$, and $X$ a proper smooth $k$-scheme. Then for every $n$ the rational $\ell$-adic cohomology
$\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} H^n(X, \mathbb{Z}_\ell)$ is finite-dimensional over
$\mathbb{Q}_\ell$. -/
public theorem_wanted rationalFinite
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (n : ℕ)
    [IsProper X.hom] [Smooth X.hom]
    (hℓ : ℓ ≠ ringChar k) :
    FiniteDimensional ℚ_[ℓ] (RationalCohomology ℓ X.left n)

/-- Let $\ell$ be a prime, $k$ an algebraically closed field of characteristic different from
$\ell$, and $X$ a proper $k$-scheme that is smooth of relative dimension $d$. Then
$H^n(X, \mathbb{Z}_\ell) = 0$ for every $n > 2d$. -/
public theorem_wanted integralVanish
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) (hn : 2 * d < n) :
    Subsingleton (X.left.EllAdicCohomology ℓ n)

/-- Let $\ell$ be a prime, $k$ an algebraically closed field of characteristic different from
$\ell$, and $X$ a proper $k$-scheme that is smooth of relative dimension $d$. Then
$\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} H^n(X, \mathbb{Z}_\ell) = 0$ for every $n > 2d$. -/
public theorem_wanted rationalVanish
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) (hn : 2 * d < n) :
    Subsingleton (RationalCohomology ℓ X.left n)

end WantedExt.AlgebraicGeometry.EllAdicCohomologyWanted
