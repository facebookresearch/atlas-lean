/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.TestingBoundaryRecognition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The original fixed-base cotensor boundary at scalar degree zero

The original maximal zero-parameter unit is a natural isomorphism of the
same slice tensor with the identity. Its native right adjoint is therefore
naturally isomorphic to the identity. The cotensor of the actual empty
boundary is terminal by the same represented scalar adjunction. Together
these identify the whole original degree-zero cotensor boundary with the
original terminal arrow, retaining the chosen adjunction and base.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The same original maximal zero-parameter product is the identity action on the actual marked slice. -/
def overScalarTensorZeroNatIso (Z : Marked.{u}) : overScalarTensor Z (Δ[0] : SSet.{u}) ≅ 𝟭 (Over Z) :=
  NatIso.ofComponents (fun X => Over.isoMk (zeroParameterUnitIso .maximal X.left) rfl)
    (fun f => by apply Over.OverMorphism.ext; apply Hom.ext; rfl)

/-- The actual zero cotensor is naturally the original object, through uniqueness of the same native right
  adjunction. -/
def overCotensorZeroNatIso (Z : Marked.{u}) : overCotensor Z (Δ[0] : SSet.{u}) ≅ 𝟭 (Over Z) :=
  ((overScalarTensorAdjunction Z (Δ[0] : SSet.{u})).ofNatIsoLeft
    (overScalarTensorZeroNatIso Z)).rightAdjointUniq Adjunction.id

/-- The actual cotensor of the original degree-zero boundary is terminal in the supplied marked slice. -/
def overCotensorBoundaryZeroIsTerminal (Z : Marked.{u}) (Y : Over Z) :
    IsTerminal ((overCotensor Z (boundary.{u} 0 : SSet.{u})).obj Y) := by
  let G := overCotensorLeft Z Y
  let _ : PreservesColimitsOfSize.{0, 0} G :=
    (overCotensorMappingAdjunction Z Y).leftAdjoint_preservesColimits
  let _ : PreservesColimit (Functor.empty SSet.{u}) G :=
    (inferInstance : PreservesColimitsOfShape (Discrete PEmpty) G).preservesColimit
  have h : IsInitial (boundary.{u} 0 : SSet.{u}) := by
    rw [boundary_zero]
    exact Subcomplex.isInitialBot
  exact terminalUnopOfInitial (h.isInitialObj G (boundary.{u} 0 : SSet.{u}))

/-- The complete original scalar degree-zero cotensor boundary is the same terminal-target arrow through the
  actual source and terminal isomorphisms. -/
def overCotensorBoundaryZeroArrowIso (Z : Marked.{u}) (Y : Over Z) :
    Arrow.mk (overCotensorBoundary Z Y 0) ≅ Arrow.mk (Over.mkIdTerminal.from Y) :=
  Arrow.isoMk ((overCotensorZeroNatIso Z).app Y)
    ((overCotensorBoundaryZeroIsTerminal Z Y).uniqueUpToIso Over.mkIdTerminal)
    (Over.mkIdTerminal.hom_ext _ _)

end SSet.Marked
