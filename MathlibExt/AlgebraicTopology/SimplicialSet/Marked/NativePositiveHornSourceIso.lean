/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativePositiveHornSourceMap

/-!
# The same original positive native horn source, including the terminal horn

The complete genuine original marked coordinate inverse and entire
enriched inverse retain every positive omitted coordinate. The actual
projective monomorphism of its supported comparison detects both whole
source identities, including the original terminal coordinate. All
original cofaces, full intersections, base transports and attaching
maps remain. The original terminal horn keeps its unchanged marking.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every same original positive horn source identity follows from the actual whole native comparison monomorphism
and the genuine full original boundary source inverse. -/
theorem nativePositiveHornRootInverse_horn {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeSupportedHornSourceMap B σ k ≫ nativeHornRootChartInverse B σ k hk = 𝟙 _ := by
  let κ := nativeSupportedHornSourceMap B σ k
  let β := nativeHornRootChartInverse B σ k hk
  let μ := nativeOriginalHornToBoundary B σ k
  let ν := nativeSupportedRootHornToBoundary B σ k
  let κB := nativeBoundaryRootSourceMap B n σ
  let βB := nativeRootBoundaryChartInverse B n σ
  apply (cancel_mono μ).mp
  calc
    (κ ≫ β) ≫ μ = κ ≫ (β ≫ μ) := Category.assoc _ _ _
    _ = κ ≫ (ν ≫ βB) := congrArg (fun f => κ ≫ f) (nativeHornRootChartInverse_boundary B σ k hk)
    _ = (κ ≫ ν) ≫ βB := (Category.assoc _ _ _).symm
    _ = (μ ≫ κB) ≫ βB := congrArg (fun f => f ≫ βB) (nativeSupportedHornSourceMap_boundary B σ k)
    _ = μ ≫ (κB ≫ βB) := Category.assoc _ _ _
    _ = μ ≫ 𝟙 _ := congrArg (fun f => μ ≫ f) (nativeRootBoundaryChartInverse_boundary B n σ)
    _ = μ := Category.comp_id _
    _ = 𝟙 _ ≫ μ := (Category.id_comp _).symm

/-- Every same entire supported positive-horn source identity follows from actual projective comparison monicity and
both unchanged full original boundary squares. -/
theorem nativePositiveHornRootInverse_supported {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeHornRootChartInverse B σ k hk ≫ nativeSupportedHornSourceMap B σ k = 𝟙 _ := by
  let κ := nativeSupportedHornSourceMap B σ k
  let β := nativeHornRootChartInverse B σ k hk
  let μ := nativeOriginalHornToBoundary B σ k
  let ν := nativeSupportedRootHornToBoundary B σ k
  let κB := nativeBoundaryRootSourceMap B n σ
  let βB := nativeRootBoundaryChartInverse B n σ
  let _ : Mono ν := nativeSupportedRootHornToBoundary_mono_all B σ k
  apply (cancel_mono ν).mp
  calc
    (β ≫ κ) ≫ ν = β ≫ (κ ≫ ν) := Category.assoc _ _ _
    _ = β ≫ (μ ≫ κB) := congrArg (fun f => β ≫ f) (nativeSupportedHornSourceMap_boundary B σ k)
    _ = (β ≫ μ) ≫ κB := (Category.assoc _ _ _).symm
    _ = (ν ≫ βB) ≫ κB := congrArg (fun f => f ≫ κB) (nativeHornRootChartInverse_boundary B σ k hk)
    _ = ν ≫ (βB ≫ κB) := Category.assoc _ _ _
    _ = ν ≫ 𝟙 _ := congrArg (fun f => ν ≫ f) (nativeRootBoundaryChartInverse_source B n σ)
    _ = ν := Category.comp_id _
    _ = 𝟙 _ ≫ ν := (Category.id_comp _).symm

/-- The SAME entire original minimally marked positive horn, including its original terminal coordinate, has its
genuine full source isomorphism with the SAME supported enriched horn. -/
def nativePositiveHornSourceIso {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) : nativeOriginalHornChart B σ k ≅ nativeSupportedRootHornChart B σ k where
  hom := nativeSupportedHornSourceMap B σ k
  inv := nativeHornRootChartInverse B σ k hk
  hom_inv_id := nativePositiveHornRootInverse_horn B σ k hk
  inv_hom_id := nativePositiveHornRootInverse_supported B σ k hk

/-- The SAME original eligible face and full ordered-intersection cocones are identified by the genuine whole
positive-horn source isomorphism. -/
def nativePositiveHornSourceFaceCoconeIso {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeOriginalHornFaceChartCocone B σ k ≅ nativeSupportedHornSourceFaceCocone B σ k :=
  Multicofork.ext (nativePositiveHornSourceIso B σ k hk) (nativeSupportedHornSourceMap_leg B σ k)

/-- Every original positive native horn, including the same terminal horn, retains its genuine whole original
face/intersection colimit in the SAME supported enriched source. -/
def nativePositiveHornSourceFaceIsColimit {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) : IsColimit (nativeSupportedHornSourceFaceCocone B σ k) :=
  IsColimit.ofIsoColimit (nativeOriginalHornFaceChartIsColimit B σ k) (nativePositiveHornSourceFaceCoconeIso B σ k hk)

/-- The same entire original eligible coface is recovered by the genuine full positive-horn inverse, with its
unchanged original base and unit maps. -/
theorem nativePositiveHornSourceIso_coface_inv {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeHornProperFaceMap B σ k j hjk ≫ (nativePositiveHornSourceIso B σ k hk).inv =
      nativeOriginalHornCofaceChartMap B σ k j hjk :=
  (congrArg (fun f => f ≫ nativeHornRootChartInverse B σ k hk) (nativeSupportedHornSourceMap_coface B σ k j
    hjk).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => nativeOriginalHornCofaceChartMap B σ k j hjk ≫ f) (nativePositiveHornRootInverse_horn B σ
        k hk)).trans
        (Category.comp_id _)))

/-- The same entire positive native horn source isomorphism retains precisely its literal whole original minimally
marked attaching map. -/
theorem nativePositiveHornSourceIso_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    (nativePositiveHornSourceIso B σ k hk).hom ≫ nativeSupportedRootHornChartMap B σ k = nativeHornChartMap B (n +
      1) k σ :=
  nativeSupportedHornSourceMap_attachment B σ k

/-- Both same whole original positive-horn attaching arrows are genuinely isomorphic through the complete source
isomorphism and the literal original simplex target identity. -/
def nativePositiveHornAttachmentIso {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    Arrow.mk (nativeHornChartMap B (n + 1) k σ) ≅ Arrow.mk (nativeSupportedRootHornChartMap B σ k) :=
  Arrow.isoMk (nativePositiveHornSourceIso B σ k hk) (Iso.refl _)
    ((nativePositiveHornSourceIso_attachment B σ k hk).trans (Category.comp_id _).symm)

end SSet.Marked
