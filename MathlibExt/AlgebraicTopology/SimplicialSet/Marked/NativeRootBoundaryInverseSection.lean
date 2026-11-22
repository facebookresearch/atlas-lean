/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryPositivePushout
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryCoordinateInverse

/-!
# The genuine whole original enriched root-boundary inverse section

The complete original marked root inverse and whole original positive
section satisfy the actual positive/free-root square by their proved
original root equality and genuine free/evaluation units. The true
enriched pushout descends both maps into one whole original section.
The same native source comparison recovers its entire original unit.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The complete original marked root inverse extends through the actual original root free/evaluation adjunction
into the unchanged native source restriction. -/
def nativeRootBoundaryInverseFreeLeg (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    enrichedFreeDiagram (Index.{u} (n + 1))ᵒᵖ (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
      (coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1))) ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) :=
  enrichedFreeExtend _ _ _ _ (nativeRootBoundaryCoordinateInverse B n σ)

/-- The genuine complete marked root inverse and actual whole positive section satisfy their same original entire
free-root square. -/
theorem nativeRootBoundaryInverse_condition (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    conePositiveBoundaryFreeMap (n + 1) ≫ nativeRootBoundaryInverseFreeLeg B n σ =
      conePositiveRootFreeLeg (n + 1) ≫ nativePositiveRootBoundarySection B σ := by
  let C := (Index.{u} (n + 1))ᵒᵖ
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let A := coneAfterWeight (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))
  let D := (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
  let γ := nativeRootBoundaryCoordinateInverse B n σ
  let b := coneRootBoundaryAfterInclusion (⊥ : Vertex.{u} (n + 1))
  let P := nativePositiveRootBoundarySection B σ
  apply (enrichedFreeHomEquiv C c A D).injective
  have hl := enrichedFreeHomEquiv_pre C c b D (nativeRootBoundaryInverseFreeLeg B n σ)
  have hr := enrichedFreeHomEquiv_post C c A (conePositiveRootFreeLeg (n + 1)) P
  have hγ : enrichedFreeHomEquiv C c (coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1))) D
      (nativeRootBoundaryInverseFreeLeg B n σ) = γ :=
    enrichedFreeExtend_unit C c (coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1))) D γ
  have hp : enrichedFreeHomEquiv C c A (coneAfterDiagram (⊥ : Vertex.{u} (n + 1)))
      (conePositiveRootFreeLeg (n + 1)) = 𝟙 _ := conePositiveRootFreeLeg_unit (n + 1)
  have hleft := hl.trans ((congrArg (fun f => b ≫ f) hγ).trans (nativeRootBoundaryCoordinateInverse_positive B n σ))
  have hright := hr.trans ((congrArg (fun f => f ≫ P.app c) hp).trans (Category.id_comp _))
  exact hleft.trans hright.symm

/-- The actual original positive/free-root inverse maps form the whole marked enriched cocone into the unchanged
original native source restriction. -/
def nativeRootBoundaryInverseCocone (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    PushoutCocone (conePositiveBoundaryFreeMap (n + 1)) (conePositiveRootFreeLeg (n + 1)) :=
  PushoutCocone.mk (nativeRootBoundaryInverseFreeLeg B n σ) (nativePositiveRootBoundarySection B σ)
    (nativeRootBoundaryInverse_condition B n σ)

/-- The same complete original root-boundary enriched diagram has its genuine whole section in the actual native
source by actual positive/free-root enriched pushout descent. -/
def nativeRootBoundaryInverseSection (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    coneRootBoundaryDiagram (n + 1) ⟶
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) :=
  (coneRootBoundaryPositiveEnrichedIsColimit (n + 1)).desc (nativeRootBoundaryInverseCocone B n σ)

/-- The actual whole enriched inverse section retains its original complete marked root free leg exactly. -/
theorem nativeRootBoundaryInverseSection_free (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    coneRootBoundaryFreeLeg (n + 1) ≫ nativeRootBoundaryInverseSection B n σ = nativeRootBoundaryInverseFreeLeg B n σ :=
  (coneRootBoundaryPositiveEnrichedIsColimit (n + 1)).fac (nativeRootBoundaryInverseCocone B n σ) .left

/-- The actual whole enriched inverse section retains its same original complete positive section exactly. -/
theorem nativeRootBoundaryInverseSection_positive (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    coneRootBoundaryAfterMap (n + 1) ≫ nativeRootBoundaryInverseSection B n σ = nativePositiveRootBoundarySection B σ :=
  (coneRootBoundaryPositiveEnrichedIsColimit (n + 1)).fac (nativeRootBoundaryInverseCocone B n σ) .right

/-- Actual original free/evaluation units identify the whole enriched inverse section at the original root with the
same complete genuine marked coordinate inverse. -/
theorem nativeRootBoundaryInverseSection_root (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeRootBoundaryInverseSection B n σ).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) =
      nativeRootBoundaryCoordinateInverse B n σ := by
  let C := (Index.{u} (n + 1))ᵒᵖ
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let A := coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1))
  let D := (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).obj
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
  let a := (nativeRootBoundaryInverseSection B n σ).app c
  let l := (coneRootBoundaryFreeLeg (n + 1)).app c
  let u := enrichedFreeUnit C c A
  have hf : u ≫ (l ≫ a) = u ≫ (nativeRootBoundaryInverseFreeLeg B n σ).app c :=
    congrArg (fun f => u ≫ f.app c) (nativeRootBoundaryInverseSection_free B n σ)
  have hl : u ≫ (l ≫ a) = a :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ a) (coneRootBoundaryFreeLeg_unit (n + 1))).trans (Category.id_comp _))
  have hr : u ≫ (nativeRootBoundaryInverseFreeLeg B n σ).app c = nativeRootBoundaryCoordinateInverse B n σ :=
    enrichedFreeExtend_unit C c A D (nativeRootBoundaryCoordinateInverse B n σ)
  exact hl.symm.trans (hf.trans hr)

/-- The same actual original native boundary source comparison recovers the unchanged entire native root-boundary
unit from the genuine full enriched inverse section. -/
theorem nativeRootBoundaryInverseSection_source (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeRootBoundaryInverseSection B n σ ≫
      (enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map (nativeBoundaryRootSourceMap B n σ) =
      EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1)) := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let C := (Index.{u} (n + 1))ᵒᵖ
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let A := coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1))
  let D := (enrichedDiagramRestrict j).obj (nativeRootBoundaryChart B (n + 1) σ)
  let a := nativeRootBoundaryInverseSection B n σ
  let η := EnrichedLeftKan.unit j (coneRootBoundaryDiagram (n + 1))
  let κ := (enrichedDiagramRestrict j).map (nativeBoundaryRootSourceMap B n σ)
  apply PushoutCocone.IsColimit.hom_ext (coneRootBoundaryPositiveEnrichedIsColimit (n + 1))
  · apply (enrichedFreeHomEquiv C c A D).injective
    let l := (coneRootBoundaryFreeLeg (n + 1)).app c
    let u := enrichedFreeUnit C c A
    have hu : u ≫ l = 𝟙 _ := coneRootBoundaryFreeLeg_unit (n + 1)
    have hl : u ≫ (l ≫ (a.app c ≫ κ.app c)) = η.app c :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (a.app c ≫ κ.app c)) hu).trans
          ((Category.id_comp _).trans
            ((congrArg (fun f => f ≫ κ.app c) (nativeRootBoundaryInverseSection_root B n σ)).trans
              (nativeRootBoundaryCoordinateInverse_source B n σ))))
    have hr : u ≫ (l ≫ η.app c) = η.app c :=
      (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ η.app c) hu).trans (Category.id_comp _))
    exact hl.trans hr.symm
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ κ) (nativeRootBoundaryInverseSection_positive B n σ)).trans
        (nativePositiveRootBoundarySection_source B σ))

end SSet.Marked
