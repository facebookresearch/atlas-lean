/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants
public import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminantsTorsionIndependent
public import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminantsEvaluationIndependent

/-!
# Direct construction and independence of actual acyclic torsion

Every request retains the actual bounded cochain, actual differentials,
original subset modules, fixed term assembly and native scalar/exterior
sources. No source word or freely assigned determinant trivialization is
an input. Sources: Knudsen--Mumford, Sections 1--2; Yuan--Zhang,
arXiv:2105.13587v9, Section 4.2.1, pp108--110.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open BoundedProjectiveDeterminants GlobalBoundedDeterminantModels
open MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants

variable [FourierMukai.HasDerivedPullbacks.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

/-- Construct the canonical comparison, actual torsion and genuine localization cover. -/
public def_wanted canonicalEvaluation (R : CommRingCat.{0}) (I : DeterminantSources)
    (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
    (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
    (T : TermAssembly R C Q)
    (acyclic : ∀ i : ℤ, Function.Surjective (boundaryMap R C i)) :
    CanonicalEvaluation I Q C T

end WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants
