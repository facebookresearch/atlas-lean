/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointParameterLifting

/-!
# The SAME original marked Cartesian endpoint is a coefficient trivial cofibration

The actual original endpoint and whole fully marked interval retain
their point-slice records through the original coefficient equivalence.
Their genuine intrinsic mapping weakness and original monicity prove
the coefficient trivial cofibration. No endpoint weak outcome or model
comparison is supplied as a premise.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked
attribute [local instance] coefficientMarkedModelCategory

/-- The entire ORIGINAL target-endpoint marked interval cell is genuinely trivial-cofibrant in the actual
coefficient model. -/
theorem coefficientOriginalCartesianEndpoint_trivialCofibration :
    trivialCofibrations Marked.{u} cartesianEndpointCell.{u} := by
  refine ⟨?_, ?_⟩
  · rw [coefficientMarkedCofibrations_eq]
    let _ : Mono cartesianEndpointCell.{u}.hom :=
      inferInstanceAs (Mono (SSet.stdSimplex.δ.{u} (0 : Fin 2)))
    exact Hom.mono_of_underlying _
  · change cartesianWeakEquivalences (Δ[0] : SSet.{u})
      (coefficientPointEquivalence.functor.map cartesianEndpointCell.{u})
    let _ : (cartesianWeakEquivalences (Δ[0] : SSet.{u})).RespectsIso := by
      unfold cartesianWeakEquivalences
      infer_instance
    let r : max (Δ[1] : SSet.{u}) ⟶ max (Δ[0] : SSet.{u}) :=
      (parameterZeroIsTerminal .maximal).from _
    let e : Arrow.mk (coefficientPointEquivalence.functor.map cartesianEndpointCell.{u}) ≅
        Arrow.mk (cartesianEndpointOver r) :=
      Arrow.isoMk
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (by apply Over.OverMorphism.ext; apply Hom.ext; rfl)
    exact ((cartesianWeakEquivalences (Δ[0] : SSet.{u})).arrow_mk_iso_iff e).mpr
      (cartesianEndpointOver_weak r)

end SSet.Marked
