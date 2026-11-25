/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ToricCoxCoordinates

/-!
# Cox uniformization with literal fan-monomial normalization

For an actual smooth complete finite lattice fan, identify the actual
Cox-open orbit quotient with the analytification of its existing toric
chart scheme. The group is the kernel of the actual ray-matrix character
map; its coordinate action and the quotient topology are already constructed.
Every chart normalization uses actual Spec C[σ∨∩M] complex points and
literal products of coordinate powers. The points are morphisms over
Spec C, so the coefficient scalar structure is fixed as well.

Reference: D. Cox, *The homogeneous coordinate ring of a toric variety*,
https://arxiv.org/abs/alg-geom/9210008v3, §2 Theorem 2.1(ii--iii),
Lemmas 2.2--2.3, pp.5--9. The paper states the analytic quotient version.

The fan, its rays, charts and realization are the shared
`FiniteToricCoordinates` and `CoxGradedSheaves` data. The complete finite-fan
scheme/gluing and mixed-monomial constructors in TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
Geometry/Toric/Algebraic/Fan/Scheme.lean and
Geometry/Toric/Analytic/MixedMonomial.lean, are positively covered and supply
that realization. The target is the whole all-ray Cox-open quotient-to-chart
uniformization, rather than those primitive constructions. General toric
cohomology/intersection and spherical geometry remain residual scope.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ToricCoxUniformizationWanted

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.CoxGradedSheaves
open MathlibExt.AlgebraicGeometry.ToricCoxCoordinates

/-- **Cox's quotient construction of a smooth complete toric variety.** Cox, Theorem 2.1: let $F$
be a finite fan in $\mathbb{R}^n$, smooth (every cone is spanned by the primitive generators of its
rays, and these are part of a basis of $\mathbb{Z}^n$) and complete, with rays
$\rho_1, \dots, \rho_r$ and primitive generators $v_1, \dots, v_r$ (`Rays F`), and let $X$ be a
complex realization of $F$ by affine charts
$U_\sigma = \operatorname{Spec} \mathbb{C}[\sigma^\vee \cap \mathbb{Z}^n]$. Let
$G \subseteq (\mathbb{C}^\times)^r$ be the kernel of
$g \mapsto (\prod_i g_i^{(v_i)_j})_{1 \le j \le n}$, acting by coordinate scaling on the set of
$z \in \mathbb{C}^r$ for which some cone contains every ray $\rho_i$ with $z_i = 0$. Then there is
a homeomorphism from the orbit space of this action to $X(\mathbb{C})$ that, for every cone
$\sigma$ and every such $z$ with $z_i \ne 0$ whenever $\rho_i \not\subseteq \sigma$, sends the orbit
of $z$ to a point of $U_\sigma(\mathbb{C})$ at which every character
$u \in \sigma^\vee \cap \mathbb{Z}^n$ takes the value $\prod_i z_i^{\langle u, v_i \rangle}$. -/
public def_wanted coxUniformization {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (_smoothComplete : SmoothComplete R) (T : Realization ℂ F) : CoxUniformization R T

end WantedExt.AlgebraicGeometry.ToricCoxUniformizationWanted
