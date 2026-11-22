/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductSymmetry
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinder

/-!
# The actual marked product point unit and original interval endpoints

The native original marked coordinate swap and zero-parameter unit give
the same original right product unit. Its original endpoint equation
identifies the cylinder graph with the fully marked point-to-interval
map, retaining every original simplex and marking.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The native original right product point unit retains the same original projection and inverse. -/
def rightPointUnitIso (X : Marked.{u}) : prod X (max (Δ[0] : SSet.{u})) ≅ X :=
  prodSwapIso X (max (Δ[0] : SSet.{u})) ≪≫ zeroParameterUnitIso .maximal X

/-- The original marked right unit is natural in the entire original source map. -/
theorem rightPointUnitIso_natural {X Y : Marked.{u}} (f : X ⟶ Y) :
    prodMap f (𝟙 (max (Δ[0] : SSet.{u}))) ≫ (rightPointUnitIso Y).hom =
      (rightPointUnitIso X).hom ≫ f := Hom.ext rfl

/-- The original marked point-to-interval map selects the same original ordered endpoint. -/
def markedIntervalEndpoint (ε : Fin 2) : max (Δ[0] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) :=
  maximal.map (SSet.stdSimplex.δ ε.rev)

/-- The original cylinder endpoint is the same whole marked point-parameter product map through its native unit. -/
theorem rightPointUnitIso_endpoint (X : Marked.{u}) (ε : Fin 2) :
    (rightPointUnitIso X).hom ≫ intervalCylinderEndpoint X ε =
      prodMap (𝟙 X) (markedIntervalEndpoint.{u} ε) := by
  apply Hom.ext
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro i
    fin_cases ε
    · change (0 : Fin 2) = (1 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.2 i)
      rw [Fin.eq_zero (SSet.stdSimplex.asOrderHom z.2 i)]
      rfl
    · change (1 : Fin 2) = (0 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.2 i)
      rw [Fin.eq_zero (SSet.stdSimplex.asOrderHom z.2 i)]
      rfl

end SSet.Marked
