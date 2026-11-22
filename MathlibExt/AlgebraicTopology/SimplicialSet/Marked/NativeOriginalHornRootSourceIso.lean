/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornRootInverse

/-!
# The original native partial horn is the same supported enriched horn

The actual native horn inclusion in the original boundary and the
actual supported-horn inclusion are monic. Their proved whole forward
and inverse comparison squares with the genuine original full-boundary
source isomorphism detect both entire source identities. The resulting
isomorphism preserves every original face and intersection, whole
positive entry and the literal original native horn attaching arrow.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual original horn source identity follows from both unchanged whole comparison squares and the genuine
original full-boundary inverse. -/
theorem nativeHornRootChartInverse_horn {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeHornSourceMap B σ k hk hk' ≫ nativeHornRootChartInverse B σ k hk = 𝟙 _ := by
  let κ := nativeHornSourceMap B σ k hk hk'
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
    _ = (μ ≫ κB) ≫ βB := congrArg (fun f => f ≫ βB) (nativeHornSourceMap_boundary B σ k hk hk')
    _ = μ ≫ (κB ≫ βB) := Category.assoc _ _ _
    _ = μ ≫ 𝟙 _ := congrArg (fun f => μ ≫ f) (nativeRootBoundaryChartInverse_boundary B n σ)
    _ = μ := Category.comp_id _
    _ = 𝟙 _ ≫ μ := (Category.id_comp _).symm

/-- The same entire original supported-horn source identity follows from its actual native monicity and both
unchanged full original boundary comparison squares. -/
theorem nativeHornRootChartInverse_source {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeHornRootChartInverse B σ k hk ≫ nativeHornSourceMap B σ k hk hk' = 𝟙 _ := by
  let κ := nativeHornSourceMap B σ k hk hk'
  let β := nativeHornRootChartInverse B σ k hk
  let μ := nativeOriginalHornToBoundary B σ k
  let ν := nativeSupportedRootHornToBoundary B σ k
  let κB := nativeBoundaryRootSourceMap B n σ
  let βB := nativeRootBoundaryChartInverse B n σ
  let _ : Mono ν := nativeSupportedRootHornToBoundary_mono B σ k hk hk'
  apply (cancel_mono ν).mp
  calc
    (β ≫ κ) ≫ ν = β ≫ (κ ≫ ν) := Category.assoc _ _ _
    _ = β ≫ (μ ≫ κB) := congrArg (fun f => β ≫ f) (nativeHornSourceMap_boundary B σ k hk hk')
    _ = (β ≫ μ) ≫ κB := (Category.assoc _ _ _).symm
    _ = (ν ≫ βB) ≫ κB := congrArg (fun f => f ≫ κB) (nativeHornRootChartInverse_boundary B σ k hk)
    _ = ν ≫ (βB ≫ κB) := Category.assoc _ _ _
    _ = ν ≫ 𝟙 _ := congrArg (fun f => ν ≫ f) (nativeRootBoundaryChartInverse_source B n σ)
    _ = ν := Category.comp_id _
    _ = 𝟙 _ ≫ ν := (Category.id_comp _).symm

/-- The same original native horn chart is genuinely isomorphic to the same entire supported original horn, through
the actual original full face colimit comparison and genuine whole enriched inverse. -/
def nativeOriginalHornRootSourceIso {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeOriginalHornChart B σ k ≅ nativeSupportedRootHornChart B σ k where
  hom := nativeHornSourceMap B σ k hk hk'
  inv := nativeHornRootChartInverse B σ k hk
  hom_inv_id := nativeHornRootChartInverse_horn B σ k hk hk'
  inv_hom_id := nativeHornRootChartInverse_source B σ k hk hk'

/-- The full original native horn source comparison is an actual whole enriched isomorphism. -/
instance nativeHornSourceMap_isIso {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    IsIso (nativeHornSourceMap B σ k hk hk') := (nativeOriginalHornRootSourceIso B σ k hk hk').isIso_hom

/-- Every entire original eligible native face and ordered pair is retained under the same actual whole horn source
isomorphism. -/
def nativeOriginalHornRootFaceCoconeIso {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeOriginalHornFaceChartCocone B σ k ≅ nativeHornSourceFaceCocone B σ k hk hk' :=
  Multicofork.ext (nativeOriginalHornRootSourceIso B σ k hk hk') (nativeHornSourceMap_leg B σ k hk hk')

/-- The actual supported enriched horn is genuinely the full colimit of all original eligible native faces and every
complete original ordered intersection. -/
def nativeOriginalHornRootFaceIsColimit {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    IsColimit (nativeHornSourceFaceCocone B σ k hk hk') :=
  IsColimit.ofIsoColimit (nativeOriginalHornFaceChartIsColimit B σ k) (nativeOriginalHornRootFaceCoconeIso B σ k hk hk')

/-- The actual whole source inverse retains every same original eligible coherent coface injection in the true
original native horn. -/
theorem nativeOriginalHornRootSourceIso_coface_inv {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) (j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeHornProperFaceMap B σ k j hjk ≫ (nativeOriginalHornRootSourceIso B σ k hk hk').inv =
      nativeOriginalHornCofaceChartMap B σ k j hjk :=
  (congrArg (fun f => f ≫ nativeHornRootChartInverse B σ k hk) (nativeHornSourceMap_coface B σ k hk hk' j
    hjk).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => nativeOriginalHornCofaceChartMap B σ k j hjk ≫ f) (nativeHornRootChartInverse_horn B σ k
        hk hk')).trans
        (Category.comp_id _)))

/-- The original entire positive chart enters the same supported horn through its genuine original tail source
inverse and unchanged eligible zeroth coface unit map. -/
def nativeHornSupportedPositiveEntry {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) : nativePositiveRootChart B (n + 1) σ ⟶ nativeSupportedRootHornChart B σ k :=
  (nativeTailFaceSourceIso B n σ).inv ≫ nativeHornProperFaceMap B σ k 0 (ne_of_lt hk)

/-- The entire same original positive source entry retains its actual independent whole supported-horn map under the
genuine source isomorphism. -/
theorem nativeOriginalHornRootSourceIso_positive {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeHornPositiveInverse B σ k hk ≫ (nativeOriginalHornRootSourceIso B σ k hk hk').hom =
      nativeHornSupportedPositiveEntry B σ k hk :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => (nativeTailFaceSourceIso B n σ).inv ≫ f) (nativeHornSourceMap_coface B σ k hk hk' 0
      (ne_of_lt hk)))

/-- The entire original supported positive entry is recovered by the same genuine whole native horn inverse. -/
theorem nativeOriginalHornRootSourceIso_positive_inv {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeHornSupportedPositiveEntry B σ k hk ≫ (nativeOriginalHornRootSourceIso B σ k hk hk').inv =
      nativeHornPositiveInverse B σ k hk :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => (nativeTailFaceSourceIso B n σ).inv ≫ f)
      (nativeOriginalHornRootSourceIso_coface_inv B σ k hk hk' 0 (ne_of_lt hk)))

/-- The literal original native horn inclusion in the full boundary retains precisely its unchanged complete native
simplex attachment. -/
theorem nativeOriginalHornToBoundary_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) :
    nativeOriginalHornToBoundary B σ k ≫ nativeBoundaryChartMap B (n + 1) σ = nativeHornChartMap B (n + 1) k σ := by
  let X := nativeSubcomplexBasisFunctor B (n + 1) σ
  let T := nativeStraightening B
  let h := homOfLE (originalHorn_le_boundary.{u} n k)
  let b := nativeSubcomplexInclusion B (n + 1) σ (boundary (n + 1))
  let c := nativeSubcomplexInclusion B (n + 1) σ (horn (n + 1) k)
  let e := (nativeSimplexImageIso B (n + 1) σ).hom
  have hc : X.map h ≫ b = c := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ e) (T.map_comp (X.map h) b).symm).trans (congrArg (fun f => T.map f ≫ e) hc))

/-- The same full original source isomorphism retains the literal entire original native horn attaching map over the
unchanged original base simplex. -/
theorem nativeOriginalHornRootSourceIso_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    (nativeOriginalHornRootSourceIso B σ k hk hk').hom ≫ nativeSupportedRootHornChartMap B σ k =
      nativeHornChartMap B (n + 1) k σ := by
  let κ := nativeHornSourceMap B σ k hk hk'
  let μ := nativeOriginalHornToBoundary B σ k
  let ν := nativeSupportedRootHornToBoundary B σ k
  let κB := nativeBoundaryRootSourceMap B n σ
  let b := nativeRootBoundaryChartMap B (n + 1) σ
  let m := nativeSupportedRootHornChartMap B σ k
  let g := nativeBoundaryChartMap B (n + 1) σ
  have hm : ν ≫ b = m := nativeSupportedRootHornToBoundary_attachment B σ k
  have hκ : κ ≫ ν = μ ≫ κB := nativeHornSourceMap_boundary B σ k hk hk'
  have hb : κB ≫ b = g := nativeBoundaryRootSourceMap_attachment B n σ
  have hμ : μ ≫ g = nativeHornChartMap B (n + 1) k σ := nativeOriginalHornToBoundary_attachment B σ k
  exact (congrArg (fun f => κ ≫ f) hm.symm).trans
    ((Category.assoc κ ν b).symm.trans
      ((congrArg (fun f => f ≫ b) hκ).trans
        ((Category.assoc μ κB b).trans ((congrArg (fun f => μ ≫ f) hb).trans hμ))))

/-- Both entire original native horn attaching arrows are genuinely isomorphic through the same actual source
isomorphism and the literal identity of their whole native simplex target. -/
def nativeOriginalHornRootAttachmentIso {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    Arrow.mk (nativeHornChartMap B (n + 1) k σ) ≅ Arrow.mk (nativeSupportedRootHornChartMap B σ k) :=
  Arrow.isoMk (nativeOriginalHornRootSourceIso B σ k hk hk') (Iso.refl _)
    ((nativeOriginalHornRootSourceIso_attachment B σ k hk hk').trans (Category.comp_id _).symm)

end SSet.Marked
