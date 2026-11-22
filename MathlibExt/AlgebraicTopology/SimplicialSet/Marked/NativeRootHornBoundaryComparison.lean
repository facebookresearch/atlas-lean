/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornAllPairColimit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornBoundaryInclusion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootHornWeakAttachment
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryRootSourceMap
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningCofibrations

/-!
# Actual original native horn and supported-horn comparisons with the full boundary

The ORIGINAL native horn chart enters the ORIGINAL all-face boundary
chart through the literal minimally marked horn inclusion. Native mono
preservation makes this original map projectively left and componentwise
monic. The SAME supported enriched horn enters the complete original
root-boundary chart by its literal original support inclusion. Its full
attaching factorization through the actual native supported-horn trivial
cofibration proves its whole and component monicity. Both comparisons
retain the original face injections and full attaching maps.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq
  coefficientMarkedModelCategory

/-- The SAME original horn is a subcomplex of the full original standard boundary through all its literal eligible
faces. -/
theorem originalHorn_le_boundary (n : ℕ) (k : Fin (n + 2)) :
    (horn.{u} (n + 1) k) ≤ boundary (n + 1) := by
  rw [horn_eq_iSup, boundary_eq_iSup]
  exact iSup_le (fun i => le_iSup
    (fun j : Fin (n + 2) => (SSet.stdSimplex.face (n := n + 1) {j}ᶜ : (Δ[n + 1] : SSet.{u}).Subcomplex)) i.val)

/-- The ORIGINAL native horn source enters the ORIGINAL all-face boundary source through its literal same-base
minimally marked horn inclusion. -/
def nativeOriginalHornToBoundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeOriginalHornChart B σ k ⟶ nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)) :=
  (nativeSubcomplexChartFunctor B (n + 1) σ).map (homOfLE (originalHorn_le_boundary n k))

/-- The SAME original native horn-to-boundary map has the genuine full projective left class by actual original
native marked mono preservation. -/
theorem nativeOriginalHornToBoundary_projectiveLeft {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp
      (nativeOriginalHornToBoundary B σ k) := by
  let h := homOfLE (originalHorn_le_boundary.{u} n k)
  let f := (nativeSubcomplexBasisFunctor B (n + 1) σ).map h
  let _ : Mono (minimal.map (Subcomplex.homOfLE (originalHorn_le_boundary.{u} n k))) :=
    (mono_iff_underlying _).mpr (inferInstance : Mono (Subcomplex.homOfLE (originalHorn_le_boundary.{u} n k)))
  let _ : Mono f.left := by
    change Mono (minimal.map (Subcomplex.homOfLE (originalHorn_le_boundary.{u} n k)))
    infer_instance
  let _ : Mono f := Over.mono_of_mono_left f
  exact nativeStraightening_mono_projectiveLeft B f

/-- The SAME original native horn comparison is monic as its entire original enriched map. -/
instance nativeOriginalHornToBoundary_mono {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    Mono (nativeOriginalHornToBoundary B σ k) :=
  coherentDiagram_projectiveLeft_mono B _ (nativeOriginalHornToBoundary_projectiveLeft B σ k)

/-- Every whole original native horn-to-boundary coefficient component is genuinely monic through the SAME actual
native projective class. -/
theorem nativeOriginalHornToBoundary_component_mono {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (x : (realization B)ᵒᵖ) : Mono ((nativeOriginalHornToBoundary B σ k).app x) :=
  coherentDiagram_projectiveLeft_component_mono B _ (nativeOriginalHornToBoundary_projectiveLeft B σ k) x

/-- Every SAME original eligible native face injection retains its exact original full-boundary face injection under
the literal horn-to-boundary comparison. -/
theorem nativeOriginalHornToBoundary_face {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (i : ({k}ᶜ : Set (Fin (n + 2)))) :
    (nativeOriginalHornFaceChartCocone B σ k).π i ≫ nativeOriginalHornToBoundary B σ k =
      (nativeBoundaryFaceChartCocone B n σ).π i.val := by
  let F := nativeSubcomplexChartFunctor B (n + 1) σ
  let a := (nativeOriginalHornFaceSubcomplexDiagram.{u} k).multicofork.π i
  let b := (nativeBoundaryFaceSubcomplexDiagram.{u} n).multicofork.π i.val
  let h := homOfLE (originalHorn_le_boundary.{u} n k)
  have hab : a ≫ h = b := Subsingleton.elim _ _
  exact (F.map_comp a h).symm.trans (congrArg F.map hab)

/-- Each complete original eligible coherent coface chart retains the SAME literal original boundary coface map
under the whole horn source comparison. -/
theorem nativeOriginalHornToBoundary_coface {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k i : Fin (n + 2))
    (hi : i ≠ k) :
    nativeOriginalHornCofaceChartMap B σ k i hi ≫ nativeOriginalHornToBoundary B σ k =
      nativeBoundaryCofaceChartMap B n σ i :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => (nativeSingleFaceChartIso B n i σ).hom ≫ f)
      (nativeOriginalHornToBoundary_face B σ k
        ⟨i, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hi⟩))

/-- The SAME supported enriched horn enters the complete original root-boundary chart by its unchanged full original
support inclusion and base simplex. -/
def nativeSupportedRootHornToBoundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeSupportedRootHornChart B σ k ⟶ nativeRootBoundaryChart B (n + 1) σ :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map
    (coneRootHornToBoundaryDiagramMap k)

/-- The entire original supported horn-to-boundary comparison keeps the SAME original full native attaching map. -/
theorem nativeSupportedRootHornToBoundary_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeSupportedRootHornToBoundary B σ k ≫ nativeRootBoundaryChartMap B (n + 1) σ =
      nativeSupportedRootHornChartMap B σ k := by
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  exact (L.map_comp (coneRootHornToBoundaryDiagramMap k) (coneRootBoundaryDiagramInclusion (n + 1))).symm.trans
    (congrArg L.map (coneRootHornToBoundaryDiagramMap_inclusion k))

/-- The SAME original supported horn comparison is monic through its actual original native coherent-model
trivial-cofibration attaching factorization. -/
theorem nativeSupportedRootHornToBoundary_mono {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (hk : 0 < k) (hk' : k < Fin.last (n + 1)) : Mono (nativeSupportedRootHornToBoundary B σ k) := by
  let _ := coherentDiagramModelCategory B
  have ht := nativeRootHornAttachment_trivialCofibration B σ k hk hk'
  let _ : Mono (nativeSupportedRootHornChartMap B σ k) :=
    coherentDiagram_projectiveLeft_mono B _ ht.1
  exact mono_of_mono_fac (nativeSupportedRootHornToBoundary_attachment B σ k)

/-- Every complete original supported-horn comparison coefficient is actually monic, retaining the SAME original
component and attaching factorization. -/
theorem nativeSupportedRootHornToBoundary_component_mono {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) (x : (realization B)ᵒᵖ) :
    Mono ((nativeSupportedRootHornToBoundary B σ k).app x) := by
  let _ := coherentDiagramModelCategory B
  have ht := nativeRootHornAttachment_trivialCofibration B σ k hk hk'
  let _ : Mono ((nativeSupportedRootHornChartMap B σ k).app x) :=
    coherentDiagram_projectiveLeft_component_mono B _ ht.1 x
  exact mono_of_mono_fac (congrArg (fun f => f.app x) (nativeSupportedRootHornToBoundary_attachment B σ k))

end SSet.Marked
