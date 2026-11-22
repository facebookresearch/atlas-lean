/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativePositiveHornCofibrancy

/-!
# The original whole horn source comparison at positive terminal coordinates

The genuine projective mono class of the same supported attachment
detects every original eligible face/intersection relation. The same
actual full original native horn colimit gives its entire source
comparison at every omitted coordinate. Its original cofaces, whole
boundary comparison and literal native attaching map remain unchanged.
The original inner comparison is recovered by colimit uniqueness.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every entire original eligible face pair satisfies its actual whole supported-horn relation through the genuine
full projective monomorphism. -/
theorem nativeSupportedHornSourceFace_condition {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (p : (MultispanShape.prod ({k}ᶜ : Set (Fin (n + 2)))).L) :
    (nativeOriginalHornFaceChartSpan B σ k).fst p ≫ nativeHornFaceToSupported B σ k p.1 =
      (nativeOriginalHornFaceChartSpan B σ k).snd p ≫ nativeHornFaceToSupported B σ k p.2 := by
  let s := nativeOriginalHornFaceChartSpan B σ k
  let m := nativeSupportedRootHornChartMap B σ k
  let _ : Mono m := nativeSupportedRootHornChartMap_mono_all B σ k
  apply (cancel_mono m).mp
  have h₁ : (s.fst p ≫ nativeHornFaceToSupported B σ k p.1) ≫ m =
      s.fst p ≫ nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.1.val}ᶜ) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => s.fst p ≫ f) (nativeHornFaceToSupported_attachment B σ k p.1))
  have h₂ : (s.snd p ≫ nativeHornFaceToSupported B σ k p.2) ≫ m =
      s.snd p ≫ nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.2.val}ᶜ) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => s.snd p ≫ f) (nativeHornFaceToSupported_attachment B σ k p.2))
  exact h₁.trans ((nativeOriginalHornFaceChartSpan_attachment B σ k p).trans h₂.symm)

/-- Every unchanged original eligible whole face and full ordered intersection gives the actual complete
supported-horn multicofork at the original omitted coordinate. -/
def nativeSupportedHornSourceFaceCocone {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    Multicofork (nativeOriginalHornFaceChartSpan B σ k) :=
  Multicofork.ofπ _ (nativeSupportedRootHornChart B σ k) (nativeHornFaceToSupported B σ k)
    (nativeSupportedHornSourceFace_condition B σ k)

/-- The same actual original native horn source enters the complete supported enriched horn through its genuine
whole original face/intersection colimit. -/
def nativeSupportedHornSourceMap {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeOriginalHornChart B σ k ⟶ nativeSupportedRootHornChart B σ k :=
  (nativeOriginalHornFaceChartIsColimit B σ k).desc (nativeSupportedHornSourceFaceCocone B σ k)

/-- Every full original eligible native face retains its exact same original supported-horn coface map under the
actual source comparison. -/
theorem nativeSupportedHornSourceMap_leg {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (i : ({k}ᶜ : Set (Fin (n + 2)))) :
    (nativeOriginalHornFaceChartCocone B σ k).π i ≫ nativeSupportedHornSourceMap B σ k = nativeHornFaceToSupported B
      σ k i :=
  (nativeOriginalHornFaceChartIsColimit B σ k).fac (nativeSupportedHornSourceFaceCocone B σ k) (.right i)

/-- The same entire original horn source comparison retains both literal original full-boundary comparison maps. -/
theorem nativeSupportedHornSourceMap_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeSupportedHornSourceMap B σ k ≫ nativeSupportedRootHornToBoundary B σ k =
      nativeOriginalHornToBoundary B σ k ≫ nativeBoundaryRootSourceMap B n σ := by
  apply Multicofork.IsColimit.hom_ext (nativeOriginalHornFaceChartIsColimit B σ k)
  intro i
  have h₁ : (nativeOriginalHornFaceChartCocone B σ k).π i ≫
      (nativeSupportedHornSourceMap B σ k ≫ nativeSupportedRootHornToBoundary B σ k) = nativeBoundaryFaceToRoot B n
        σ i.val :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ nativeSupportedRootHornToBoundary B σ k) (nativeSupportedHornSourceMap_leg B σ k
        i)).trans
        (nativeHornFaceToSupported_boundary B σ k i))
  have h₂ : (nativeOriginalHornFaceChartCocone B σ k).π i ≫
      (nativeOriginalHornToBoundary B σ k ≫ nativeBoundaryRootSourceMap B n σ) = nativeBoundaryFaceToRoot B n σ i.val :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ nativeBoundaryRootSourceMap B n σ) (nativeOriginalHornToBoundary_face B σ k i)).trans
        (nativeBoundaryRootSourceMap_leg B n σ i.val))
  exact h₁.trans h₂.symm

/-- Every entire original eligible coherent coface keeps its genuine same supported-horn unit mate and full base
transport under the actual comparison. -/
theorem nativeSupportedHornSourceMap_coface {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k j : Fin (n + 2))
    (hjk : j ≠ k) :
    nativeOriginalHornCofaceChartMap B σ k j hjk ≫ nativeSupportedHornSourceMap B σ k = nativeHornProperFaceMap B σ
      k j hjk := by
  let e := nativeSingleFaceChartIso B n j σ
  let i : ({k}ᶜ : Set (Fin (n + 2))) := ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hjk⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => e.hom ≫ f) (nativeSupportedHornSourceMap_leg B σ k i)).trans
      (e.hom_inv_id_assoc (nativeHornProperFaceMap B σ k j hjk)))

/-- The actual entire source comparison retains precisely the same literal original native horn attaching map at
every omitted coordinate. -/
theorem nativeSupportedHornSourceMap_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2)) :
    nativeSupportedHornSourceMap B σ k ≫ nativeSupportedRootHornChartMap B σ k = nativeHornChartMap B (n + 1) k σ := by
  let κ := nativeSupportedHornSourceMap B σ k
  let μ := nativeOriginalHornToBoundary B σ k
  let ν := nativeSupportedRootHornToBoundary B σ k
  let κB := nativeBoundaryRootSourceMap B n σ
  let b := nativeRootBoundaryChartMap B (n + 1) σ
  let m := nativeSupportedRootHornChartMap B σ k
  let g := nativeBoundaryChartMap B (n + 1) σ
  have hm : ν ≫ b = m := nativeSupportedRootHornToBoundary_attachment B σ k
  have hκ : κ ≫ ν = μ ≫ κB := nativeSupportedHornSourceMap_boundary B σ k
  have hb : κB ≫ b = g := nativeBoundaryRootSourceMap_attachment B n σ
  have hμ : μ ≫ g = nativeHornChartMap B (n + 1) k σ := nativeOriginalHornToBoundary_attachment B σ k
  exact (congrArg (fun f => κ ≫ f) hm.symm).trans
    ((Category.assoc κ ν b).symm.trans
      ((congrArg (fun f => f ≫ b) hκ).trans
        ((Category.assoc μ κB b).trans ((congrArg (fun f => μ ≫ f) hb).trans hμ))))

/-- At every original inner coordinate the same complete original colimit detects precisely the already frozen whole
source comparison. -/
theorem nativeSupportedHornSourceMap_inner {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeSupportedHornSourceMap B σ k = nativeHornSourceMap B σ k hk hk' := by
  apply Multicofork.IsColimit.hom_ext (nativeOriginalHornFaceChartIsColimit B σ k)
  intro i
  exact (nativeSupportedHornSourceMap_leg B σ k i).trans (nativeHornSourceMap_leg B σ k hk hk' i).symm

end SSet.Marked
