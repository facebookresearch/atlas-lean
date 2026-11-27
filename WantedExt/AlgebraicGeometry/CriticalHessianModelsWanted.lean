/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CriticalHessianModels
public import Batteries.Util.ProofWanted

/-!
# Native critical Hessian and sheaf-dual construction requests

The normal module is the actual dual-derivative cokernel. Its form is
fixed at every point of the critical scheme by the half-Hessian on
Hessian-orthogonal vectors, which determines it on the reduction (the form on
the nonreduced critical scheme is not constrained here). The generic sheaf-Hom
adapter is distinct from the paper's Hessian producer. No canonical-line or
transition-gluing conclusion is an input.

Reference: Joyce, arXiv:1304.4508v3, Propositions 2.23 and 2.25.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CriticalHessianModelsWanted

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CriticalSchemeCharts
open MathlibExt.AlgebraicGeometry.CriticalFunctionSheafModels
open MathlibExt.AlgebraicGeometry.CriticalHessianModels
open MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks

def_wanted nativeSheafDualPrecomposition (T : Scheme) (M N : T.Modules) (f : M ⟶ N) :
    DualPrecomposition f

def_wanted criticalHessianForm (k : Type) [Field k] [IsAlgClosed k]
    (_two_ne_zero : (2 : k) ≠ 0) (X : CategoryTheory.Over (Spec (.of k)))
    (E F : AffineCriticalChart X) (r : CriticalAffineRefinement E F)
    (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))
    (P : DualPrecomposition (chartCotangentMap r D)) : HessianForm r D P

end WantedExt.AlgebraicGeometry.CriticalHessianModelsWanted
