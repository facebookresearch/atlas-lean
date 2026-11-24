/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CriticalFunctionSheafModels
public import Batteries.Util.ProofWanted

/-!
# Critical-function kernel comparisons and sheaf construction

All local quotients, derivatives, reductions and refinement maps are
computed in MathlibExt. The two algebraic comparisons fix their values
on all representatives. The global constructor asks for the source's
actual critical sheaf; it does not assume Joyce's internal gluing or
canonical-line theorem as a background hypothesis.

Reference: Joyce, arXiv:1304.4508v3, Theorem 2.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CriticalFunctionSheafModelsWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AffineCriticalFunctions
open MathlibExt.AlgebraicGeometry.AffineCriticalKernelModels
open MathlibExt.AlgebraicGeometry.CriticalSchemeCharts
open MathlibExt.AlgebraicGeometry.CriticalFunctionSheafModels

def_wanted criticalKernelEquivalence (k P : Type) [CommRing k] [CommRing P]
    [Algebra k P] (I : Ideal P) :
    {e : localCriticalModule k P I ≃ₗ[k] CriticalKernel (k := k) I //
      ∀ a, (e a).val = criticalInclusion I a}

def_wanted zeroCriticalKernelEquivalence (k P : Type) [CommRing k] [CommRing P]
    [Algebra k P] (I : Ideal P) :
    {e : localZeroCriticalModule k P I ≃ₗ[k] ZeroCriticalKernel (k := k) I //
      ∀ (f : P) (hd : KaehlerDifferential.D k P f ∈ idealDifferentials k P I)
        (hr : f ∈ I.radical),
        (e (criticalClass I f hd hr)).val = (squareDenominator k P I).mkQ ⟨f, hd⟩}

/-- Native scalar restriction integration, normalized by every actual app map. -/
def_wanted nativeFunctionRestriction (k : Type) [Field k]
    (X Y : Over (Spec (.of k))) (f : Y ⟶ X) : FunctionRestriction f

def_wanted criticalFunctionSheaf (k : Type) [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    (R : FunctionRestriction (reductionArrow X)) :
    Σ B : CriticalSheafModel X, ZeroCriticalSheafModel B R

end WantedExt.AlgebraicGeometry.CriticalFunctionSheafModelsWanted
