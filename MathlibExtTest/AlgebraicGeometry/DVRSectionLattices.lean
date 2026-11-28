/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DVRSectionLattices

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.DVRSectionLattices

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.DVRSectionLattices

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Over (Spec (.of R))} {M : X.left.Modules}

/-- Reduction uses the same R-section that produced the generic-fibre lattice element. -/
example (B : SectionBaseChange (K := K) X M)
    (h : Function.Injective (genericSectionMap B)) (S : SpecialSectionMap X M)
    (s : Sections X M) :
    latticeReduction B h S ⟨genericSectionMap B s, ⟨s, rfl⟩⟩ = S.map s := by
  change S.map ((LinearEquiv.ofInjective (genericSectionMap B) h).symm
    ((LinearEquiv.ofInjective (genericSectionMap B) h) s)) = S.map s
  rw [LinearEquiv.symm_apply_apply]

end MathlibExtTest.AlgebraicGeometry.DVRSectionLattices
