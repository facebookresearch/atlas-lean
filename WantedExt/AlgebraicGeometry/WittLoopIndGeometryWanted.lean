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

/-- Realize the fixed fpqc quotient by actual ind-perfect proper geometry. -/
public def_wanted grassmannianGeometry
    (p : ℕ) [Fact p.Prime] (G : Over (Spec (.of ℤ_[p]))) [GrpObj G]
    [IsReductive (Spec (.of ℤ_[p])) G] : GrassmannianGeometry p G

/-- Realize multiplication on the actual twofold twisted quotient. -/
public def_wanted convolutionGeometry
    (p : ℕ) [Fact p.Prime] (G : Over (Spec (.of ℤ_[p]))) [GrpObj G]
    [IsReductive (Spec (.of ℤ_[p])) G] (M : GrassmannianGeometry p G) :
    ConvolutionGeometry p G M

end WantedExt.AlgebraicGeometry.WittLoopIndGeometry
