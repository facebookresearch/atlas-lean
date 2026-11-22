/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornCoordinateCocone
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornSourceMap
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryRootSourceIso

/-!
# The genuine entire original enriched horn source inverse

The actual complete marked coordinate inverse supplies the original
root coefficient, and the actual whole positive section supplies every
original coefficient above the root. Their proved whole inclusions in
the original boundary detect full enriched naturality at every original
path and scalar simplex. The same native universal unit then constructs
the entire source inverse with its original boundary comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The genuine complete root-coordinate inverse and the same whole original positive section supply every entire
original supported-horn coefficient. -/
def nativeHornRootInverseAt {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (i : Vertex.{u} (n + 1)) :
    coneRootHornMarked k i ⟶
      (nativeOriginalHornChart B σ k).obj
        ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk i))) :=
  if hi : i = ⊥ then
    (eqToHom (congrArg (coneRootHornMarked k) hi) ≫ nativeHornRootCoordinateInverse B σ k hk) ≫
      eqToHom (congrArg (fun j : Vertex.{u} (n + 1) =>
        (nativeOriginalHornChart B σ k).obj
          ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk j)))) hi.symm)
  else
    coneRootHornToBoundary k i ≫
      ((coneRootBoundaryAfterAboveIso (lt_of_le_of_ne bot_le (Ne.symm hi))).inv ≫
        (nativeHornPositiveSection B σ k hk).app (op (SimplicialThickening.mk i)))

/-- At the unchanged original root the entire coefficient inverse is precisely the actual whole marked
coordinate-colimit inverse. -/
theorem nativeHornRootInverseAt_root {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeHornRootInverseAt B σ k hk (⊥ : Vertex.{u} (n + 1)) = nativeHornRootCoordinateInverse B σ k hk := by
  let γ := nativeHornRootCoordinateInverse B σ k hk
  have h : nativeHornRootInverseAt B σ k hk (⊥ : Vertex.{u} (n + 1)) = (𝟙 _ ≫ γ) ≫ 𝟙 _ :=
    dite_eq_left rfl
  exact h.trans ((congrArg (fun f => f ≫ 𝟙 _) (Category.id_comp γ)).trans (Category.comp_id γ))

/-- Every complete original horn coefficient recovers the original full enriched boundary inverse after the literal
native component inclusion. -/
theorem nativeHornRootInverseAt_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (i : Vertex.{u} (n + 1)) :
    nativeHornRootInverseAt B σ k hk i ≫
      (nativeOriginalHornToBoundary B σ k).app
        ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk i))) =
      coneRootHornToBoundary k i ≫
        (nativeRootBoundaryInverseSection B n σ).app (op (SimplicialThickening.mk i)) := by
  by_cases hi : i = ⊥
  · subst i
    exact (congrArg (fun f => f ≫ (nativeOriginalHornToBoundary B σ k).app
      ((EnrichedFunctor.opposite (simplexInto B σ)).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))))
          (nativeHornRootInverseAt_root B σ k hk)).trans
      ((nativeHornRootCoordinateInverse_boundary B σ k hk).trans
        (congrArg (fun f => coneRootHornToBoundary k (⊥ : Vertex.{u} (n + 1)) ≫ f)
          (nativeRootBoundaryInverseSection_root B n σ).symm))
  · let e := coneRootBoundaryAfterAboveIso (lt_of_le_of_ne bot_le (Ne.symm hi))
    let c := op (SimplicialThickening.mk i)
    let p := (nativeHornPositiveSection B σ k hk).app c
    let q := (nativePositiveRootBoundarySection B σ).app c
    let a := (nativeRootBoundaryInverseSection B n σ).app c
    let μ := (nativeOriginalHornToBoundary B σ k).app
      ((EnrichedFunctor.opposite (simplexInto B σ)).obj c)
    have hp : p ≫ μ = q := congrArg (fun f => f.app c) (nativeHornPositiveSection_boundary B σ k hk)
    have he : e.hom ≫ a = q :=
      (congrArg (fun f => f ≫ a) (coneRootBoundaryAfterAboveIso_hom (lt_of_le_of_ne bot_le (Ne.symm hi)))).trans
        (congrArg (fun f => f.app c) (nativeRootBoundaryInverseSection_positive B n σ))
    have h : (e.inv ≫ p) ≫ μ = a :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => e.inv ≫ f) hp).trans
          ((congrArg (fun f => e.inv ≫ f) he.symm).trans (e.inv_hom_id_assoc a)))
    have hvalue : nativeHornRootInverseAt B σ k hk i = coneRootHornToBoundary k i ≫ (e.inv ≫ p) :=
      dite_eq_right hi
    exact (congrArg (fun f => f ≫ μ) hvalue).trans
      ((Category.assoc _ _ _).trans (congrArg (fun f => coneRootHornToBoundary k i ≫ f) h))

/-- The same genuine complete coefficient maps form an actual whole enriched horn section, with all original Hom
simplices, actions and markings retained. -/
def nativeHornRootInverseSection {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    coneRootHornDiagram k ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj (nativeOriginalHornChart B σ k) where
  app i := nativeHornRootInverseAt B σ k hk i.unop.as
  naturality x y := by
    ext q p
    let j := EnrichedFunctor.opposite (simplexInto B σ)
    let D := coneRootHornDiagram.{u} k
    let G := (enrichedDiagramRestrict j).obj (nativeOriginalHornChart B σ k)
    let H := (enrichedDiagramRestrict j).obj (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
    let μ := (enrichedDiagramRestrict j).map (nativeOriginalHornToBoundary B σ k)
    let s := coneRootHornToBoundaryDiagramMap k ≫ nativeRootBoundaryInverseSection B n σ
    let f := nativeHornRootInverseAt B σ k hk x.unop.as
    let g := nativeHornRootInverseAt B σ k hk y.unop.as
    let P := max (Δ[q.unop.len] : SSet.{u})
    let A := (D.map x y).app q p
    let C := (G.map x y).app q p
    let E := (H.map x y).app q p
    have hf : f ≫ μ.app x = s.app x := nativeHornRootInverseAt_boundary B σ k hk x.unop.as
    have hg : g ≫ μ.app y = s.app y := nativeHornRootInverseAt_boundary B σ k hk y.unop.as
    have hs : A ≫ s.app y = prodMap (𝟙 P) (s.app x) ≫ E :=
      congr($(s.naturality x y).app q p)
    have hμ : C ≫ μ.app y = prodMap (𝟙 P) (μ.app x) ≫ E :=
      congr($(μ.naturality x y).app q p)
    have hp : prodMap (𝟙 P) (f ≫ μ.app x) = prodMap (𝟙 P) f ≫ prodMap (𝟙 P) (μ.app x) := by
      simpa only [Category.id_comp] using prodMap_comp (𝟙 P) (𝟙 P) f (μ.app x)
    let _ : Mono (μ.app y) := nativeOriginalHornToBoundary_component_mono B σ k (j.obj y)
    change A ≫ g = prodMap (𝟙 P) f ≫ C
    apply (cancel_mono (μ.app y)).mp
    have hl : (A ≫ g) ≫ μ.app y = A ≫ s.app y :=
      (Category.assoc _ _ _).trans (congrArg (fun t => A ≫ t) hg)
    have hr : (prodMap (𝟙 P) f ≫ C) ≫ μ.app y = prodMap (𝟙 P) (s.app x) ≫ E :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t => prodMap (𝟙 P) f ≫ t) hμ).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ E) hp.symm).trans
              (congrArg (fun t => prodMap (𝟙 P) t ≫ E) hf))))
    exact hl.trans (hs.trans hr.symm)

/-- The same entire enriched inverse section retains precisely the literal original support inclusion and full
original boundary inverse. -/
theorem nativeHornRootInverseSection_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeHornRootInverseSection B σ k hk ≫
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map (nativeOriginalHornToBoundary B σ k) =
      coneRootHornToBoundaryDiagramMap k ≫ nativeRootBoundaryInverseSection B n σ := by
  apply EnrichedDiagramMap.ext
  funext i
  exact nativeHornRootInverseAt_boundary B σ k hk i.unop.as

/-- The same genuine entire original enriched inverse has its actual native left Kan adjoint into the original
partial horn source. -/
def nativeHornRootChartInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) : nativeSupportedRootHornChart B σ k ⟶ nativeOriginalHornChart B σ k :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootHornDiagram k)
    (nativeOriginalHornChart B σ k)).symm (nativeHornRootInverseSection B σ k hk)

/-- The same actual native source inverse retains exactly its genuine entire original enriched unit section. -/
theorem nativeHornRootChartInverse_homEquiv {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootHornDiagram k)
      (nativeOriginalHornChart B σ k) (nativeHornRootChartInverse B σ k hk) = nativeHornRootInverseSection B σ k hk :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootHornDiagram k)
    (nativeOriginalHornChart B σ k)).apply_symm_apply (nativeHornRootInverseSection B σ k hk)

/-- The entire same original native horn inverse retains the full original boundary inverse through both literal
original native support comparisons. -/
theorem nativeHornRootChartInverse_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeHornRootChartInverse B σ k hk ≫ nativeOriginalHornToBoundary B σ k =
      nativeSupportedRootHornToBoundary B σ k ≫ nativeRootBoundaryChartInverse B n σ := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneRootHornDiagram.{u} k
  let S := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let U := EnrichedLeftKan.universalHomEquiv j W S
  have hl : U (nativeHornRootChartInverse B σ k hk ≫ nativeOriginalHornToBoundary B σ k) =
      nativeHornRootInverseSection B σ k hk ≫ (enrichedDiagramRestrict j).map (nativeOriginalHornToBoundary B σ k) :=
    (EnrichedLeftKan.universalHomEquiv_natural_right j W (nativeHornRootChartInverse B σ k hk)
      (nativeOriginalHornToBoundary B σ k)).trans
        (congrArg (fun f => f ≫ (enrichedDiagramRestrict j).map (nativeOriginalHornToBoundary B σ k))
          (nativeHornRootChartInverse_homEquiv B σ k hk))
  have hr : U (nativeSupportedRootHornToBoundary B σ k ≫ nativeRootBoundaryChartInverse B n σ) =
      coneRootHornToBoundaryDiagramMap k ≫ nativeRootBoundaryInverseSection B n σ :=
    (enrichedLeftKan_universal_map_post j (coneRootHornToBoundaryDiagramMap k) (nativeRootBoundaryChartInverse B n
      σ)).trans
      (congrArg (fun f => coneRootHornToBoundaryDiagramMap k ≫ f) (nativeRootBoundaryChartInverse_homEquiv B n σ))
  exact U.injective (hl.trans ((nativeHornRootInverseSection_boundary B σ k hk).trans hr.symm))

end SSet.Marked
