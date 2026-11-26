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

Sources: Knudsen--Mumford, *The projectivity of the moduli space of stable
curves I: preliminaries on 'det' and 'Div'*, Math. Scand. 39 (1976), 19--55,
Chapter I, pp. 21 and 31--34 (the determinant construction). The Lean proof
keeps its own fixed degree order.
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
