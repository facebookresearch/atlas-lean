/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.WittLoopIndGeometry

/-!
# Geometric realization of the actual Witt loop quotients

Zhu, arXiv:1407.8519v3, Theorem1.4 and Proposition1.20, constructs the
mixed-characteristic Grassmannian over an unramified prime-field base;
the convolution uses the actual twisted quotient of Section1.4.
The real perfect schemes and their ordinary deperfections are distinct.
Generic source perfection and quotient descent are not requested again.

These geometric constructors assume no Satake equivalence. A geometric
Satake target additionally needs algebraically closed residue base and
ell distinct from p, with its actual equivariant perverse/fibre functor;
Frobenius or Weil descent over the rational base is a separate comparison.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.WittLoopIndGeometry

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.WittLoopIndGeometry
open MathlibExt.AlgebraicGeometry.ReductiveGroupSchemeModels

/-- The Witt vector affine Grassmannian is ind-perfectly proper (Zhu, arXiv:1407.8519, Theorem 1.4):
let $p$ be a prime and $G$ a reductive group scheme over $\mathbb{Z}_p$. Then the Witt vector affine
Grassmannian of $G$, an fpqc sheaf on perfect $\mathbb{F}_p$-algebras, is the colimit of the sheaves
represented by a sequence of perfect $\mathbb{F}_p$-schemes with closed immersions as transition
maps, each the perfection of a proper $\mathbb{F}_p$-scheme of finite presentation
(`IndPerfectGeometry`). -/
public def_wanted grassmannianGeometry
    (p : ℕ) [Fact p.Prime] (G : Over (Spec (.of ℤ_[p]))) [GrpObj G]
    [IsReductive (Spec (.of ℤ_[p])) G] : GrassmannianGeometry p G

/-- The convolution Grassmannian is ind-perfectly proper, compatibly with multiplication (Zhu,
arXiv:1407.8519, Proposition 1.20): let $p$ be a prime, $G$ a reductive group scheme over
$\mathbb{Z}_p$, and $M$ a presentation of its Witt vector affine Grassmannian as a colimit of
perfections of proper $\mathbb{F}_p$-schemes (`GrassmannianGeometry`). Then the twofold convolution
Grassmannian has a presentation of the same kind (`IndPerfectGeometry`), with maps from its stages
to stages of $M$ that realize the convolution map to the Grassmannian (`ConvolutionGeometry`). -/
public def_wanted convolutionGeometry
    (p : ℕ) [Fact p.Prime] (G : Over (Spec (.of ℤ_[p]))) [GrpObj G]
    [IsReductive (Spec (.of ℤ_[p])) G] (M : GrassmannianGeometry p G) :
    ConvolutionGeometry p G M

end WantedExt.AlgebraicGeometry.WittLoopIndGeometry
