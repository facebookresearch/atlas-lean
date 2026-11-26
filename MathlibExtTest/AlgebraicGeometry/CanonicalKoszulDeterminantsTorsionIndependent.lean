/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminantsTorsionIndependent

/-!
# Uniqueness of actual acyclic torsion

An adapted basis determines the unique vector equal to the torsion of every
adapted basis of the same complex.

Sources: Knudsen--Mumford, Sections 1--2; Yuan--Zhang,
arXiv:2105.13587v9, Section 4.2.1, pp108--110.
-/

set_option autoImplicit false

namespace MathlibExtTest.AlgebraicGeometry.CanonicalKoszulDeterminantsTorsionIndependent

open MathlibExt.AlgebraicGeometry
open BoundedProjectiveDeterminants CanonicalKoszulDeterminants

example (R : Type) [CommRing R] (C : BoundedProjectiveDeterminants.Complex R)
    (A : AdaptedBases R C) :
    ∃! t : determinantObject R C, ∀ B : AdaptedBases R C, t = acyclicTorsion R C B := by
  refine ⟨acyclicTorsion R C A, ?_, ?_⟩
  · intro B
    exact WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants.torsion_independent R C A B
  · intro t ht
    exact ht A

end MathlibExtTest.AlgebraicGeometry.CanonicalKoszulDeterminantsTorsionIndependent
