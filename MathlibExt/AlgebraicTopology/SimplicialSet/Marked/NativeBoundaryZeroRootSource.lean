/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryZero
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryRootLatching

/-!
# The actual original empty native boundary source and root attachment

The original minimally marked zero-dimensional boundary is genuinely
initial in the same original base slice. Actual native straightening
and actual enriched left extension preserve these original initial
universal properties. Their genuine source isomorphism retains the
original attaching map and proves its actual projective left class.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole original minimally marked empty zero-dimensional boundary is genuinely initial over the unchanged
original base simplex. -/
def nativeBoundaryZeroBasisIsInitial (B : SSet.{u}) (σ : B _⦋0⦌) :
    IsInitial (nativeSubcomplexBasis B 0 σ (boundary 0)) := by
  let _ : PreservesColimitsOfSize.{0, 0} minimal.{u} := minimalAdjunction.leftAdjoint_preservesColimits
  have h : IsInitial (boundary.{u} 0 : SSet.{u}) := by
    rw [SSet.boundary_zero]
    exact Subcomplex.isInitialBot
  apply isColimitOfReflects (Over.forget (max B))
  exact isColimitChangeEmptyCocone Marked.{u} (h.isInitialObj minimal _) _ (Iso.refl _)

/-- The actual straightened original empty boundary is genuinely initial through the original native straightening
adjunction. -/
def nativeBoundaryZeroChartIsInitial (B : SSet.{u}) (σ : B _⦋0⦌) :
    IsInitial (nativeSubcomplexChart B 0 σ (boundary 0)) := by
  let _ : PreservesColimitsOfSize.{0, 0} (nativeStraightening B) :=
    (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
  exact (nativeBoundaryZeroBasisIsInitial B σ).isInitialObj (nativeStraightening B) _

/-- The actual native root-boundary chart in dimension zero is genuinely initial through the original enriched
left-extension adjunction. -/
def nativeRootBoundaryZeroChartIsInitial (B : SSet.{u}) (σ : B _⦋0⦌) :
    IsInitial (nativeRootBoundaryChart B 0 σ) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let L := EnrichedLeftKan.leftExtension j
  let _ : PreservesColimitsOfSize.{0, 0} L := (EnrichedLeftKan.adjunction j).leftAdjoint_preservesColimits
  exact coneRootBoundaryZeroIsInitial.isInitialObj L _

/-- The actual original empty native boundary source is genuinely isomorphic to the same original empty
root-boundary chart. -/
def nativeBoundaryZeroRootSourceIso (B : SSet.{u}) (σ : B _⦋0⦌) :
    nativeSubcomplexChart B 0 σ (boundary 0) ≅ nativeRootBoundaryChart B 0 σ :=
  (nativeBoundaryZeroChartIsInitial B σ).uniqueUpToIso (nativeRootBoundaryZeroChartIsInitial B σ)

/-- The genuine original empty-source comparison retains exactly the unchanged original zero-dimensional boundary
attaching map. -/
theorem nativeBoundaryZeroRootSourceIso_attachment (B : SSet.{u}) (σ : B _⦋0⦌) :
    (nativeBoundaryZeroRootSourceIso B σ).hom ≫ nativeRootBoundaryChartMap B 0 σ = nativeBoundaryChartMap B 0 σ :=
  (nativeBoundaryZeroChartIsInitial B σ).hom_ext _ _

/-- The same original zero-dimensional boundary attaching map has the genuine projective left class through its
actual empty-source isomorphism and original free-root pushout. -/
theorem nativeBoundaryZeroChartMap_projectiveLeft (B : SSet.{u}) (σ : B _⦋0⦌) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp (nativeBoundaryChartMap B 0 σ) := by
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  let e := nativeBoundaryZeroRootSourceIso B σ
  have h := G.rlp.llp.comp_mem e.hom (nativeRootBoundaryChartMap B 0 σ)
    (G.rlp.llp_of_isIso e.hom) (nativeRootBoundaryChartMap_projectiveLeft B 0 σ)
  exact (nativeBoundaryZeroRootSourceIso_attachment B σ) ▸ h

end SSet.Marked
