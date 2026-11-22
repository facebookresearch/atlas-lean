/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalEdgeComposition
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalOverMarkingPushouts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSharpMarkingImage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRelativeChartRestriction

/-!
# Original critical marking spans and their exact native basis records

The original full critical source and target pushouts lie over the
whole supplied base simplex. Each original minimal interval, sharp
interval and minimal horn or simplex record is identified with its
actual native basis through the unchanged entire carrier identity.
Both original span arrows and the actual critical edge are retained.
Every supplied original marked base map is recovered by original Yoneda.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole original critical target lies over precisely the supplied original base simplex. -/
def nativeCriticalProjection (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    cartesianCriticalTarget n ⟶ max B := toMax (SSet.yonedaEquiv.symm σ)

/-- Every original whole marked target-to-base map is recovered exactly by its original Yoneda simplex. -/
theorem nativeCriticalProjection_original (B : SSet.{u}) (n : ℕ)
    (r : cartesianCriticalTarget n ⟶ max B) :
    nativeCriticalProjection B n (SSet.yonedaEquiv r.hom) = r :=
  Hom.ext (Equiv.symm_apply_apply SSet.yonedaEquiv r.hom)

/-- The SAME actual critical horn edge retains its whole original base-edge projection. -/
theorem nativeCriticalHornEdge_projection (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    SSet.yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) ≫
      (horn (n + 2) (Fin.last (n + 2))).ι ≫ SSet.yonedaEquiv.symm σ =
        SSet.yonedaEquiv.symm (nativeCriticalBaseEdge B n σ) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The original target critical edge image has exactly the SAME whole original base-edge projection. -/
theorem nativeCriticalImageEdge_projection (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    SSet.yonedaEquiv.symm (cartesianCriticalImageEdge.{u} n) ≫ SSet.yonedaEquiv.symm σ =
      SSet.yonedaEquiv.symm (nativeCriticalBaseEdge B n σ) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The entire original critical horn edge followed by its inclusion is the SAME actual ordinal simplex map. -/
theorem nativeCriticalHornEdge_simplex (n : ℕ) :
    SSet.yonedaEquiv.symm (rightHornEdgeSimplex.{u} n) ≫
      (horn (n + 2) (Fin.last (n + 2))).ι = SSet.stdSimplex.map (nativeCriticalEdgeOperator.{u} n) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_map]
  exact (Equiv.symm_apply_apply stdSimplex.objEquiv (cartesianCriticalImageEdge.{u} n)).symm

/-- The SAME entire original minimal critical edge enters the actual whole native terminal-horn basis. -/
def nativeCriticalMinimalHornEdgeOverMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeSimplexBasis B 1 (nativeCriticalBaseEdge B n σ) ⟶
      nativeSubcomplexBasis B (n + 2) σ (horn (n + 2) (Fin.last (n + 2))) :=
  Over.homMk
    (selectedEdgeMinimalMap (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) (rightHornEdgeSimplex n))
    (Hom.ext (nativeCriticalHornEdge_projection B n σ))

/-- The actual whole minimal critical edge-to-horn map retains precisely the original simplex restriction after
inclusion. -/
theorem nativeCriticalMinimalHornEdgeOverMap_inclusion (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalMinimalHornEdgeOverMap B n σ ≫
      nativeSubcomplexInclusion B (n + 2) σ (horn (n + 2) (Fin.last (n + 2))) =
        nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n) σ := by
  apply CostructuredArrow.hom_ext
  exact Hom.ext (nativeCriticalHornEdge_simplex n)

/-- The original critical SOURCE marking span's whole minimal interval record is its exact native base-edge basis. -/
def nativeCriticalSourceIntervalBasisIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ)).obj WalkingSpan.zero ≅
      nativeSimplexBasis B 1 (nativeCriticalBaseEdge B n σ) :=
  Over.isoMk (Iso.refl _) (by
    apply Hom.ext
    change 𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (nativeCriticalBaseEdge B n σ) =
      (𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (rightHornEdgeSimplex n)) ≫
        ((horn (n + 2) (Fin.last (n + 2))).ι ≫ SSet.yonedaEquiv.symm σ)
    rw [Category.id_comp, Category.id_comp]
    exact (nativeCriticalHornEdge_projection B n σ).symm)

/-- The SAME original SOURCE sharp interval record is the entire native sharp basis over its actual critical base
edge. -/
def nativeCriticalSourceSharpBasisIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ)).obj WalkingSpan.left ≅
      nativeSharpBasis B (nativeCriticalBaseEdge B n σ) :=
  Over.isoMk (Iso.refl _) (by
    apply Hom.ext
    change 𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (nativeCriticalBaseEdge B n σ) =
      SSet.yonedaEquiv.symm (rightHornEdgeSimplex n) ≫
        ((horn (n + 2) (Fin.last (n + 2))).ι ≫ SSet.yonedaEquiv.symm σ)
    exact (Category.id_comp _).trans (nativeCriticalHornEdge_projection B n σ).symm)

/-- The SOURCE's complete original minimal horn record is the SAME full native terminal-horn basis. -/
def nativeCriticalSourceHornBasisIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ)).obj WalkingSpan.right ≅
      nativeSubcomplexBasis B (n + 2) σ (horn (n + 2) (Fin.last (n + 2))) :=
  Over.isoMk (Iso.refl _) (Hom.ext rfl)

/-- The original critical TARGET span's full minimal interval record is the exact SAME native critical base-edge
basis. -/
def nativeCriticalTargetIntervalBasisIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ)).obj WalkingSpan.zero ≅
      nativeSimplexBasis B 1 (nativeCriticalBaseEdge B n σ) :=
  Over.isoMk (Iso.refl _) (by
    apply Hom.ext
    change 𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (nativeCriticalBaseEdge B n σ) =
      (𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (cartesianCriticalImageEdge n)) ≫ SSet.yonedaEquiv.symm σ
    rw [Category.id_comp, Category.id_comp]
    exact (nativeCriticalImageEdge_projection B n σ).symm)

/-- The TARGET's entire original sharp critical edge record is the SAME actual native sharp interval basis. -/
def nativeCriticalTargetSharpBasisIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ)).obj WalkingSpan.left ≅
      nativeSharpBasis B (nativeCriticalBaseEdge B n σ) :=
  Over.isoMk (Iso.refl _) (by
    apply Hom.ext
    change 𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (nativeCriticalBaseEdge B n σ) =
      SSet.yonedaEquiv.symm (cartesianCriticalImageEdge n) ≫ SSet.yonedaEquiv.symm σ
    exact (Category.id_comp _).trans (nativeCriticalImageEdge_projection B n σ).symm)

/-- The TARGET's complete original minimal simplex record is precisely the whole original native simplex basis. -/
def nativeCriticalTargetSimplexBasisIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ)).obj WalkingSpan.right ≅
      nativeSimplexBasis B (n + 2) σ :=
  Over.isoMk (Iso.refl _) (Hom.ext rfl)

/-- Both whole SOURCE interval basis identities retain the SAME actual original interval marking map. -/
theorem nativeCriticalSourceBasisIso_marking (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ)).map WalkingSpan.Hom.fst ≫
      (nativeCriticalSourceSharpBasisIso B n σ).hom =
    (nativeCriticalSourceIntervalBasisIso B n σ).hom ≫ nativeMarkingCell B (nativeCriticalBaseEdge B n σ) := by
  apply CostructuredArrow.hom_ext
  exact Hom.ext rfl

/-- Both full SOURCE basis records keep precisely the SAME actual original minimal critical edge-to-horn map. -/
theorem nativeCriticalSourceBasisIso_edge (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalSourceOverMarkingDiagram B n (nativeCriticalProjection B n σ)).map WalkingSpan.Hom.snd ≫
      (nativeCriticalSourceHornBasisIso B n σ).hom =
    (nativeCriticalSourceIntervalBasisIso B n σ).hom ≫ nativeCriticalMinimalHornEdgeOverMap B n σ := by
  apply CostructuredArrow.hom_ext
  exact Hom.ext rfl

/-- The TARGET interval identities retain exactly the SAME original physical interval marking cell. -/
theorem nativeCriticalTargetBasisIso_marking (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ)).map WalkingSpan.Hom.fst ≫
      (nativeCriticalTargetSharpBasisIso B n σ).hom =
    (nativeCriticalTargetIntervalBasisIso B n σ).hom ≫ nativeMarkingCell B (nativeCriticalBaseEdge B n σ) := by
  apply CostructuredArrow.hom_ext
  exact Hom.ext rfl

/-- The TARGET's whole basis records preserve the exact original critical ordinal simplex restriction. -/
theorem nativeCriticalTargetBasisIso_edge (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalTargetOverMarkingDiagram B n (nativeCriticalProjection B n σ)).map WalkingSpan.Hom.snd ≫
      (nativeCriticalTargetSimplexBasisIso B n σ).hom =
    (nativeCriticalTargetIntervalBasisIso B n σ).hom ≫ nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n)
      σ := by
  apply CostructuredArrow.hom_ext
  apply Hom.ext
  change SSet.yonedaEquiv.symm (cartesianCriticalImageEdge n) = SSet.stdSimplex.map (nativeCriticalEdgeOperator.{u} n)
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_map]
  exact (Equiv.symm_apply_apply stdSimplex.objEquiv (cartesianCriticalImageEdge.{u} n)).symm

end SSet.Marked
