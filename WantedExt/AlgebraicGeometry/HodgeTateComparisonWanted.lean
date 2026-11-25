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
public import MathlibExt.AlgebraicGeometry.HodgeTateComparison

/-!
# Hodge–Tate comparison for actual proper smooth schemes over Q_p

Construct the C_p-linear, Galois-equivariant comparison between the
actual rational pro-étale cohomology of the geometric fibre and the
coherent cohomology of its actual differential-form sheaves. The identity
and composition laws of the étale Galois operators are requested
separately; with them, both sides carry semilinear Galois actions
(`MathlibExt.AlgebraicGeometry.HodgeTateComparison`). The negative
Tate twist in Hodge degree i uses the constructed cyclotomic character.

The fields, coefficient sheaves, scheme Galois operators, completed field
action, differential sheaves and right-derived coherent sections are
fixed constructions. No replacement representation, free period ring or
chosen Galois character is assumed.

Reference: Peter Scholze, *p-adic Hodge theory for rigid-analytic varieties*,
Corollary 1.8, p. 4, and preceding Theorem 1.6 for Galois equivariance;
the algebraic scheme case follows by the comparisons described on p. 5.
https://arxiv.org/abs/1205.3463
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HodgeTateComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.HodgeTateComparison

/-- For a prime $p$, a scheme $X$ over $\mathbb{Q}_p$ and $n \in \mathbb{N}$: the operator of the
identity element of $\mathrm{Gal}(\bar{\mathbb{Q}}_p/\mathbb{Q}_p)$ on the rational pro-étale
cohomology $H^n$ of the geometric fibre $X_{\bar{\mathbb{Q}}_p}$, inverse image along
$\mathrm{id}_X \times \mathrm{Spec}\,1$ (`etaleGalois`), is the identity (functoriality of sheaf
cohomology under inverse image). -/
public theorem_wanted etaleGalois_one
    (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of.{0} ℚ_[p]))) (n : ℕ) :
    etaleGalois p X 1 n = LinearMap.id

/-- For a prime $p$, a scheme $X$ over $ℚ_p$, elements $σ, τ$ of $\mathrm{Gal}(\bar{ℚ}_p/ℚ_p)$ and
$n ∈ ℕ$: the operators on the rational pro-étale cohomology $H^n$ of the geometric fibre
$X_{\bar{ℚ}_p}$ given by inverse image along $\mathrm{id}_X × \mathrm{Spec}\,σ$ (`etaleGalois`)
form a left action: the operator of $στ$ is the operator of $σ$ composed after that of $τ$
(functoriality of sheaf cohomology, since inverse image reverses composition). -/
public theorem_wanted etaleGalois_mul
    (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of.{0} ℚ_[p]))) (σ τ : Galois p) (n : ℕ) :
    etaleGalois p X (σ * τ) n = etaleGalois p X σ n ∘ₗ etaleGalois p X τ n

/-- Hodge–Tate comparison: for a prime $p$, a proper smooth scheme $X$ over $ℚ_p$ and $n ∈ ℕ$: a
$ℂ_p$-linear isomorphism (`Comparison`) from $ℂ_p ⊗_{ℚ_p} H^n$, where $H^n$ is the rational
pro-étale cohomology of the geometric fibre $X_{\bar{ℚ}_p}$, to
$\bigoplus_{i=0}^{n} ℂ_p ⊗_{ℚ_p} H^{n-i}(X, Ω^i_X)$, equivariant for the actions of
$\mathrm{Gal}(\bar{ℚ}_p/ℚ_p)$: diagonally on the source, and on the summand of degree $i$ through
the action on $ℂ_p$ twisted by $χ^{-i}$, for $χ$ the cyclotomic character. -/
public def_wanted hodgeTateComparison
    (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))
    [IsProper X.hom] [Smooth X.hom] (n : ℕ) : Comparison p X n

end WantedExt.AlgebraicGeometry.HodgeTateComparison
