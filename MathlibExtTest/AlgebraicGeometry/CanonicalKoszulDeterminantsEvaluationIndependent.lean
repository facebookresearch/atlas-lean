/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminantsEvaluationIndependent

/-!
# Canonical evaluation values form a singleton

Tests derive a singleton range for evaluation values from evaluation independence.

Sources: Knudsen--Mumford, *The projectivity of the moduli space of stable
curves I*, Sections 1--2; Yuan--Zhang, arXiv:2105.13587v9, Section 4.2.1,
pp108--110.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.CanonicalKoszulDeterminantsEvaluationIndependent

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open BoundedProjectiveDeterminants GlobalBoundedDeterminantModels
open MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants

example [FourierMukai.HasDerivedPullbacks.{0}]
    [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
    [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
    [∀ R : CommRingCat.{0}, ProjectiveSources R]
    (R : CommRingCat.{0}) (I : DeterminantSources)
    (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
    (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
    (T : TermAssembly R C Q) (E : CanonicalEvaluation I Q C T) :
    Set.range (fun F : CanonicalEvaluation I Q C T ↦ F.value) = {E.value} := by
  ext x
  constructor
  · rintro ⟨F, rfl⟩
    exact Set.mem_singleton_iff.mpr
      (WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants.evaluation_independent R I C m Q T F E)
  · intro hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨E, rfl⟩

end MathlibExtTest.AlgebraicGeometry.CanonicalKoszulDeterminantsEvaluationIndependent
