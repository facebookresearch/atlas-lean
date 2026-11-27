/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AbsoluteLissePurity
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public noncomputable section

/-!
# Purity for absolutely irreducible finite-determinant lisse coefficients

Authors: Laurent Lafforgue, Pierre Deligne.
Source: Laurent Lafforgue, Chtoucas de Drinfeld et correspondance de Langlands,
Inventiones Mathematicae 147 (2002), 1--241, Theorem VII.6(ii), p. 198;
https://www.laurentlafforgue.org/math/fulltext.pdf,
https://doi.org/10.1007/s002220100174.
This packet retains the primary smooth finite-field curve scope.

The hypotheses are absolute irreducibility over Qbar_ell and finite order
of the full arithmetic determinant. The group, representation, closed
point, field Frobenius and fibre path are actual objects with prescribed
maps. No purity or HasDeligneConclusions result is an input.
-/

namespace WantedExt.AlgebraicGeometry.AbsoluteLissePurity

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.EtaleFibreFrobenius
open MathlibExt.AlgebraicGeometry.AbsoluteLissePurity

universe u

/-- **Lafforgue's purity theorem for lisse sheaves on curves.** Theorem VII.6(ii): let ℓ be a prime,
$k$ a finite field in which ℓ is nonzero, and $X$ a $k$-scheme that is smooth of relative dimension
one, quasi-compact, separated and geometrically connected, with a geometric point $x$ over an
algebraically closed field $K$. Let $\rho$ be a continuous representation of the arithmetic
fundamental group $\pi_1(X, x)$ in $\mathrm{GL}_r(\mathbb{Q}_\ell)$ that is absolutely irreducible
($r > 0$ and irreducible over the algebraic closure of $\mathbb{Q}_\ell$) and whose determinant has
finite order on the whole arithmetic group. Let $\kappa$ be a finite field and
$y : \operatorname{Spec} \kappa \to X$ a closed immersion over $k$, with $K$ a $\kappa$-algebra,
$\sigma$ an arithmetic Frobenius of $K$ over $\kappa$ and an isomorphism of fibre functors from $x$
to the geometric point over $y$. Then for every ring homomorphism
$\iota : \mathbb{Q}_\ell \to \mathbb{C}$, every complex root of the ι-image of the characteristic
polynomial of $\rho$ at the geometric Frobenius element at $y$ (defined by σ and the isomorphism)
has absolute value 1. -/
public theorem_wanted absoluteLissePureWeightZero
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [Fintype k]
    (ellInvertible : (ell : k) ≠ 0)
    (X : Over (Spec (.of k))) [SmoothOfRelativeDimension 1 X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [GeometricallyConnected X.hom]
    (K : Type u) [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ X.left)
    (r : ℕ) (ρ : LisseRepresentation ell x r)
    (absolutelyIrreducible : AbsolutelyIrreducible ell x r ρ)
    (finiteArithmeticDeterminant : FiniteArithmeticDeterminant ell x r ρ)
    (κ : Type u) [Field κ] [Fintype κ] [Algebra k κ] [Algebra κ K]
    (y : Spec (.of κ) ⟶ X.left) [IsClosedImmersion y]
    (pointOverBase : y ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    (σ : ArithmeticFrobenius κ K)
    (path : fibreFunctor x ≅ fibreFunctor (closedPointGeometricPoint (K := K) y))
    (ι : ℚ_[ell] →+* ℂ) (α : ℂ)
    (root : (frobeniusPolynomial ell x r ρ y σ path ι).IsRoot α) :
    ‖α‖ = 1

end WantedExt.AlgebraicGeometry.AbsoluteLissePurity
