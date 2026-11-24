/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CriticalCanonicalLineModels
public import Batteries.Util.ProofWanted

/-!
# Critical Hessian determinant transitions and canonical-line gluing

Generic exterior pullback and normal exact-sequence adapters are separated
from Joyce's transition and canonical-line constructions. All source maps
and half-Hessian determinants are fixed; no transition independence,
internal chart-gluing or canonical-line existence theorem is an input.

Reference: Joyce, arXiv:1304.4508v3, Definition 2.26, Proposition 2.27
and Theorem 2.28. Algebraic characteristic is different from two.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CriticalCanonicalLineModelsWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CriticalSchemeCharts
open MathlibExt.AlgebraicGeometry.CriticalFunctionSheafModels
open MathlibExt.AlgebraicGeometry.CriticalHessianModels
open MathlibExt.AlgebraicGeometry.ReducedCriticalHessianModels
open MathlibExt.AlgebraicGeometry.CriticalCanonicalLineModels
open MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks
open MathlibExt.AlgebraicGeometry.SheafExteriorSectionModels

def_wanted nativeExteriorPullback (T U : Scheme.{0}) (f : T ⟶ U) : PullbackExterior f

def_wanted nativeCriticalNormalReindex (k : Type) [Field k]
    (X : Over (Spec (.of k))) (E F : AffineCriticalChart X)
    (r : CriticalAffineRefinement E F)
    (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))
    (P : DualPrecomposition (chartCotangentMap r D))
    (P' : DualPrecomposition (cotangentMap r D)) : NormalReindex r D P P'

def_wanted nativeCriticalConormal (k : Type) [Field k]
    (X : Over (Spec (.of k))) (E F : AffineCriticalChart X)
    (r : CriticalAffineRefinement E F)
    (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))
    (P' : DualPrecomposition (cotangentMap r D)) : ConormalData r D P'

def_wanted criticalHessianTransition (k : Type) [Field k] [IsAlgClosed k]
    (_two_ne_zero : (2 : k) ≠ 0) (X : Over (Spec (.of k)))
    (E F : AffineCriticalChart X) (r : CriticalAffineRefinement E F)
    (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))
    (P : DualPrecomposition (chartCotangentMap r D)) (Q : HessianForm r D P)
    (m n : ℕ) (_source_rank : CotangentRank E.toAffineEmbedding m)
    (_target_rank : CotangentRank F.toAffineEmbedding (m + n)) : HessianTransition r D P Q m n

def_wanted criticalCanonicalLine (k : Type) [Field k] [IsAlgClosed k]
    (_two_ne_zero : (2 : k) ≠ 0) (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (B : CriticalSheafModel X) (R : FunctionRestriction (reductionArrow X))
    (Z : ZeroCriticalSheafModel B R) (S : DCriticalStructure B R Z) : CanonicalLineCandidate S

def_wanted canonicalLineComparison (k : Type) [Field k] [IsAlgClosed k]
    (_two_ne_zero : (2 : k) ≠ 0) (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (B : CriticalSheafModel X) (R : FunctionRestriction (reductionArrow X))
    (Z : ZeroCriticalSheafModel B R) (S : DCriticalStructure B R Z)
    (C D : CanonicalLineCandidate S) : CanonicalLineIso S C D

theorem_wanted canonicalLineComparisonUnique (k : Type) [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (B : CriticalSheafModel X) (R : FunctionRestriction (reductionArrow X))
    (Z : ZeroCriticalSheafModel B R) (S : DCriticalStructure B R Z)
    (C D : CanonicalLineCandidate S) (a b : CanonicalLineIso S C D) : a.iso = b.iso

end WantedExt.AlgebraicGeometry.CriticalCanonicalLineModelsWanted
