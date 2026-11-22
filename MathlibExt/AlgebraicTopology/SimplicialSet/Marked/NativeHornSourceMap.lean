/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornProperFaceSource

/-!
# The SAME ORIGINAL native partial-face horn source comparison

Every original eligible whole coface chart enters the actual supported
horn through its original marked unit mate. Genuine native supported-horn
monicity detects the complete original face/intersection compatibility.
The actual ORIGINAL native horn colimit therefore gives the entire source
map, retaining all original cofaces, pair intersections, base transports
and the literal original attaching map. Its inverse is a separate proof.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Each SAME entire original eligible marked face chart enters the actual original supported horn through its
original full coface isomorphism and unit mate. -/
def nativeHornFaceToSupported {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (i : ({k}ᶜ : Set (Fin (n + 2)))) :
    nativeSubcomplexChart B (n + 1) σ (SSet.stdSimplex.face {i.val}ᶜ) ⟶ nativeSupportedRootHornChart B σ k :=
  (nativeSingleFaceChartIso B n i.val σ).inv ≫ nativeHornProperFaceMap B σ k i.val
    (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using i.property)

/-- Every entire original eligible supported-horn face map retains its SAME original full-boundary face map under
the literal support comparison. -/
theorem nativeHornFaceToSupported_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (i : ({k}ᶜ : Set (Fin (n + 2)))) :
    nativeHornFaceToSupported B σ k i ≫ nativeSupportedRootHornToBoundary B σ k =
      nativeBoundaryFaceToRoot B n σ i.val :=
  (Category.assoc _ _ _).trans
    (congrArg (fun f => (nativeSingleFaceChartIso B n i.val σ).inv ≫ f)
      (nativeHornProperFaceMap_boundary B σ k i.val
        (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using i.property)))

/-- The SAME entire original eligible face map retains exactly its unchanged complete original native simplex
attaching map. -/
theorem nativeHornFaceToSupported_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (i : ({k}ᶜ : Set (Fin (n + 2)))) :
    nativeHornFaceToSupported B σ k i ≫ nativeSupportedRootHornChartMap B σ k =
      nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {i.val}ᶜ) :=
  (congrArg (fun f => nativeHornFaceToSupported B σ k i ≫ f)
    (nativeSupportedRootHornToBoundary_attachment B σ k).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ nativeRootBoundaryChartMap B (n + 1) σ)
          (nativeHornFaceToSupported_boundary B σ k i)).trans
            (nativeBoundaryFaceToRoot_attachment B n σ i.val)))

/-- Both original whole eligible face-intersection maps retain the SAME exact original native attaching composite. -/
theorem nativeOriginalHornFaceChartSpan_attachment {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌) (k : Fin (n + 2))
    (p : (MultispanShape.prod ({k}ᶜ : Set (Fin (n + 2)))).L) :
    (nativeOriginalHornFaceChartSpan B σ k).fst p ≫
        nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.1.val}ᶜ) =
      (nativeOriginalHornFaceChartSpan B σ k).snd p ≫
        nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.2.val}ᶜ) := by
  let d := nativeOriginalHornFaceSubcomplexDiagram.{u} k
  let X := nativeSubcomplexBasisFunctor B (n + 1) σ
  let T := nativeStraightening B
  let a := d.multispanIndex.fst p
  let b := d.multispanIndex.snd p
  let g₁ := nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {p.1.val}ᶜ)
  let g₂ := nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {p.2.val}ᶜ)
  let e := (nativeSimplexImageIso B (n + 1) σ).hom
  have hx : X.map a ≫ g₁ = X.map b ≫ g₂ := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl
  have h₁ : T.map (X.map a) ≫ (T.map g₁ ≫ e) = T.map (X.map a ≫ g₁) ≫ e :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ e) (T.map_comp (X.map a) g₁).symm)
  have h₂ : T.map (X.map b) ≫ (T.map g₂ ≫ e) = T.map (X.map b ≫ g₂) ≫ e :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ e) (T.map_comp (X.map b) g₂).symm)
  exact h₁.trans ((congrArg (fun f => T.map f ≫ e) hx).trans h₂.symm)

/-- Every SAME original entire eligible face pair satisfies the actual supported-horn cocone relation through
genuine native monicity and unchanged full attaching maps. -/
theorem nativeHornSourceFace_condition {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1))
    (p : (MultispanShape.prod ({k}ᶜ : Set (Fin (n + 2)))).L) :
    (nativeOriginalHornFaceChartSpan B σ k).fst p ≫ nativeHornFaceToSupported B σ k p.1 =
      (nativeOriginalHornFaceChartSpan B σ k).snd p ≫ nativeHornFaceToSupported B σ k p.2 := by
  let _ := coherentDiagramModelCategory B
  have ht := nativeRootHornAttachment_trivialCofibration B σ k hk hk'
  let _ : Mono (nativeSupportedRootHornChartMap B σ k) := coherentDiagram_projectiveLeft_mono B _ ht.1
  apply (cancel_mono (nativeSupportedRootHornChartMap B σ k)).mp
  let s := nativeOriginalHornFaceChartSpan B σ k
  let m := nativeSupportedRootHornChartMap B σ k
  have h₁ : (s.fst p ≫ nativeHornFaceToSupported B σ k p.1) ≫ m =
      s.fst p ≫ nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.1.val}ᶜ) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => s.fst p ≫ f) (nativeHornFaceToSupported_attachment B σ k p.1))
  have h₂ : (s.snd p ≫ nativeHornFaceToSupported B σ k p.2) ≫ m =
      s.snd p ≫ nativeSubcomplexChartMap B (n + 1) σ (SSet.stdSimplex.face {p.2.val}ᶜ) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun f => s.snd p ≫ f) (nativeHornFaceToSupported_attachment B σ k p.2))
  exact h₁.trans ((nativeOriginalHornFaceChartSpan_attachment B σ k p).trans h₂.symm)

/-- All SAME original full eligible faces and intersections give the actual complete original supported-horn source
cocone. -/
def nativeHornSourceFaceCocone {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    Multicofork (nativeOriginalHornFaceChartSpan B σ k) :=
  Multicofork.ofπ _ (nativeSupportedRootHornChart B σ k) (nativeHornFaceToSupported B σ k)
    (nativeHornSourceFace_condition B σ k hk hk')

/-- The SAME ORIGINAL native partial-face horn source maps to the actual entire original supported horn through its
genuine full marked face/intersection colimit. -/
def nativeHornSourceMap {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeOriginalHornChart B σ k ⟶ nativeSupportedRootHornChart B σ k :=
  (nativeOriginalHornFaceChartIsColimit B σ k).desc (nativeHornSourceFaceCocone B σ k hk hk')

/-- Every SAME original native eligible face injection retains exactly its actual full original supported-horn face
map under the completed source comparison. -/
theorem nativeHornSourceMap_leg {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1))
    (i : ({k}ᶜ : Set (Fin (n + 2)))) :
    (nativeOriginalHornFaceChartCocone B σ k).π i ≫ nativeHornSourceMap B σ k hk hk' =
      nativeHornFaceToSupported B σ k i :=
  (nativeOriginalHornFaceChartIsColimit B σ k).fac (nativeHornSourceFaceCocone B σ k hk hk') (.right i)

/-- The SAME original native partial-face source comparison retains the literal original full-boundary comparison
square. -/
theorem nativeHornSourceMap_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) :
    nativeHornSourceMap B σ k hk hk' ≫ nativeSupportedRootHornToBoundary B σ k =
      nativeOriginalHornToBoundary B σ k ≫ nativeBoundaryRootSourceMap B n σ := by
  apply Multicofork.IsColimit.hom_ext (nativeOriginalHornFaceChartIsColimit B σ k)
  intro i
  have h₁ : (nativeOriginalHornFaceChartCocone B σ k).π i ≫
      (nativeHornSourceMap B σ k hk hk' ≫ nativeSupportedRootHornToBoundary B σ k) =
        nativeBoundaryFaceToRoot B n σ i.val :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ nativeSupportedRootHornToBoundary B σ k) (nativeHornSourceMap_leg B σ k hk hk' i)).trans
        (nativeHornFaceToSupported_boundary B σ k i))
  have h₂ : (nativeOriginalHornFaceChartCocone B σ k).π i ≫
      (nativeOriginalHornToBoundary B σ k ≫ nativeBoundaryRootSourceMap B n σ) =
        nativeBoundaryFaceToRoot B n σ i.val :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ nativeBoundaryRootSourceMap B n σ) (nativeOriginalHornToBoundary_face B σ k i)).trans
        (nativeBoundaryRootSourceMap_leg B n σ i.val))
  exact h₁.trans h₂.symm

/-- The SAME whole original eligible coherent coface source injection retains its exact entire original native
supported-horn unit mate. -/
theorem nativeHornSourceMap_coface {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (hk' : k < Fin.last (n + 1)) (j : Fin (n + 2)) (hjk : j ≠ k) :
    nativeOriginalHornCofaceChartMap B σ k j hjk ≫ nativeHornSourceMap B σ k hk hk' =
      nativeHornProperFaceMap B σ k j hjk := by
  let e := nativeSingleFaceChartIso B n j σ
  let i : ({k}ᶜ : Set (Fin (n + 2))) := ⟨j, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hjk⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => e.hom ≫ f) (nativeHornSourceMap_leg B σ k hk hk' i)).trans
      (e.hom_inv_id_assoc (nativeHornProperFaceMap B σ k j hjk)))

end SSet.Marked
