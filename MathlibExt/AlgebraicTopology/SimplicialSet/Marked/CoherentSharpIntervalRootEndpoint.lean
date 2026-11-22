/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientOriginalEndpointCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOneIntervalEndpoints
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeSharpRootMarkCell

/-!
# The SAME original sharp interval root endpoint cell

The entire original positive root coefficient is its actual full
two-vertex cone subset. Its original sharp target is the SAME whole
interval nerve with maximal marking. Actual point and interval carrier
isomorphisms retain the original upper endpoint map, giving its genuine
coefficient trivial cofibration without changing the original cone.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq
  coefficientMarkedModelCategory

/-- Every entire original positive interval-root subset is precisely the original full two-vertex target. -/
theorem coneSharpEndpoint_positive_eq_target (a : ConeAfter (zeroOne.{u}) ⊥) : a.val = coefficientTarget := by
  rcases a.val.zero_cases with h | h
  · have ha : (⊥ : Vertex.{u} 1) < coefficientSource.maximum := h ▸ a.property
    exact False.elim ((by decide : ¬ (⊥ : Vertex.{u} 1) < coefficientSource.maximum) ha)
  · exact h

/-- The SAME full original positive root coefficient is genuinely a terminal marked object on its actual original
carrier. -/
def coneSharpEndpointPositiveIsTerminal : IsTerminal (coneAfterWeight (zeroOne.{u}) ⊥) :=
  IsTerminal.ofUniqueHom
    (fun X =>
      { hom :=
          { app q := ↾fun _ => (Functor.const _).obj
              (⟨coefficientTarget, by decide⟩ : ConeAfter (zeroOne.{u}) ⊥)
            naturality q r f := by ext x; rfl }
        preserve _ := rfl })
    (fun X f => by
      apply Hom.ext
      ext q a
      refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
      exact Subtype.ext (coneSharpEndpoint_positive_eq_target ((f.hom.app q a).obj t)))

/-- The complete original positive coefficient has its actual marked point isomorphism, with the entire original
singleton carrier retained. -/
def coneSharpEndpointPositivePointIso : coneAfterWeight (zeroOne.{u}) ⊥ ≅ min (Δ[0] : SSet.{u}) :=
  coneSharpEndpointPositiveIsTerminal.uniqueUpToIso (parameterZeroIsTerminal .minimal)

/-- The SAME full original sharp root coefficient has its actual original fully marked interval carrier. -/
def coneSharpEndpointRootIntervalIso : max (coneWeight (zeroOne.{u})).toSSet ≅ max (Δ[1] : SSet.{u}) :=
  maximal.mapIso (forget.mapIso coneZeroIntervalIso)

/-- The SAME original positive root endpoint enters the whole original sharp interval coefficient. -/
def coneSharpEndpointRootCell : coneAfterWeight (zeroOne.{u}) ⊥ ⟶ max (coneWeight (zeroOne.{u})).toSSet :=
  coneAfterInclusion zeroOne ⊥ ≫ coneSharpRootMarkCell

/-- Both actual original carrier isomorphisms retain precisely the SAME entire original marked target-endpoint cell. -/
theorem coneSharpEndpointRootCell_interval :
    coneSharpEndpointPositivePointIso.{u}.hom ≫ cartesianEndpointCell =
      coneSharpEndpointRootCell ≫ coneSharpEndpointRootIntervalIso.hom := by
  apply Hom.ext
  ext q a
  rcases q with ⟨⟨m⟩⟩
  apply SSet.stdSimplex.ext
  intro t
  let b : (Δ[0] : SSet.{u}) _⦋m⦌ := coneSharpEndpointPositivePointIso.hom.hom.app (op ⦋m⦌) a
  change (0 : Fin 2).succAbove (b t) = (a.obj t).val.maximum.down
  have h₀ : b t = 0 := by
    apply Fin.ext
    have h := (b t).isLt
    omega
  rw [h₀, coneSharpEndpoint_positive_eq_target (a.obj t)]
  rfl

/-- The SAME entire original positive-to-sharp root endpoint arrow is genuinely isomorphic to its original physical
marked endpoint cell. -/
def coneSharpEndpointRootArrowIso : Arrow.mk coneSharpEndpointRootCell.{u} ≅ Arrow.mk cartesianEndpointCell.{u} :=
  Arrow.isoMk coneSharpEndpointPositivePointIso coneSharpEndpointRootIntervalIso coneSharpEndpointRootCell_interval

/-- The SAME original sharp interval root endpoint is an actual coefficient trivial cofibration through its exact
original attaching-arrow isomorphism. -/
theorem coneSharpEndpointRootCell_trivialCofibration :
    trivialCofibrations Marked.{u} coneSharpEndpointRootCell.{u} :=
  ((trivialCofibrations Marked.{u}).arrow_iso_iff coneSharpEndpointRootArrowIso).mpr
    coefficientOriginalCartesianEndpoint_trivialCofibration

end SSet.Marked.CoherentWeight
