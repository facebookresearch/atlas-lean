/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.SmallProducts
import MathlibExt.Algebra.Category.Grp.FilteredColimits.FiniteProducts
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePi
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Evaluation

/-!
# The original integer stable-pi functor and finite products

Every original finite spectrum projection induces the full original
integer-diagonal projection. Actual level evaluation and the native
positive homotopy product comparison identify every stage. The same
native Group quotient then retains all original integer stable-pi maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.FiniteProductGeometry

open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {ι : Type} [Fintype ι] (X : ι → PointedCGWH.SequentialSpectrum.{u, v}) [HasProduct X]

/-- The full original finite family of coordinate integer diagrams. -/
def diagrams (q : ℤ) : ι → ℕ ⥤ GrpCat.{v} := fun i => (integerDiagonalDiagramFunctor q).obj (X i)

/-- Every actual spectrum projection gives the same whole original integer-diagonal projection. -/
def diagramProjection (q : ℤ) (i : ι) :
    (integerDiagonalDiagramFunctor q).obj (∏ᶜ X) ⟶ diagrams X q i :=
  (integerDiagonalDiagramFunctor q).map (Pi.π X i)

/-- The actual whole integer-diagonal comparison retains every original coordinate projection map. -/
def diagramComparison (q : ℤ) : (integerDiagonalDiagramFunctor q).obj (∏ᶜ X) ⟶
    GrpCat.FilteredColimits.FiniteProducts.diagram (diagrams X q) where
  app n := GrpCat.ofHom {
    toFun := fun z i => ((diagramProjection X q i).app n).hom z
    map_one' := by funext i; exact map_one _
    map_mul' := by intro a b; funext i; exact map_mul _ _ _ }
  naturality n m f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro z
    funext i
    exact ConcreteCategory.congr_hom ((diagramProjection X q i).naturality f) z

/-- The physical level of the same chosen spectrum product is the actual product of its original levels. -/
def levelIso (r : ℕ) : level (∏ᶜ X) r ≅ ∏ᶜ fun i => level (X i) r :=
  PreservesProduct.iso (evaluation.{u, v} r) X

/-- Every entire physical product projection is the original evaluated spectrum projection. -/
theorem levelIso_projection (r : ℕ) (i : ι) :
    (levelIso X r).hom ≫ Pi.π (fun i => level (X i) r) i = levelMap (Pi.π X i) r :=
  piComparison_comp_π (evaluation.{u, v} r) X i

/-- The original positive homotopy product comparison identifies the same entire diagonal stage. -/
def stageIso (q : ℤ) (n : ℕ) :
    ((integerDiagonalDiagramFunctor q).obj (∏ᶜ X)).obj n ≅
      (GrpCat.FilteredColimits.FiniteProducts.diagram (diagrams X q)).obj n :=
  (PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).mapIso
    (levelIso X (integerTailLevel q + n)) ≪≫
      PointedCGWH.SmallHomotopyProductGeometry.comparisonIso
        (fun i => level (X i) (integerTailLevel q + n)) (integerTailPositiveIndex q + n)

/-- The full stage Iso has the actual original spectrum-projection diagonal map as its forward morphism. -/
theorem stageIso_hom (q : ℤ) (n : ℕ) :
    (stageIso X q n).hom = (diagramComparison X q).app n := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  funext i
  have h := PointedCGWH.SmallHomotopyProductGeometry.equiv_projection
    (fun i => level (X i) (integerTailLevel q + n)) (integerTailPositiveIndex q + n)
      (((PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (levelIso X (integerTailLevel q + n)).hom).hom z) i
  have hm := ConcreteCategory.congr_hom
    ((PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).map_comp
      (levelIso X (integerTailLevel q + n)).hom
      (Pi.π (fun i => level (X i) (integerTailLevel q + n)) i)) z
  exact h.trans (hm.symm.trans (ConcreteCategory.congr_hom
    ((PointedCGWH.piNPositiveFunctor (integerTailPositiveIndex q + n)).congr_map
      (levelIso_projection X (integerTailLevel q + n) i)) z))

/-- All original varying-level and varying-degree transitions belong to the same whole product diagram Iso. -/
def diagramIso (q : ℤ) : (integerDiagonalDiagramFunctor q).obj (∏ᶜ X) ≅
    GrpCat.FilteredColimits.FiniteProducts.diagram (diagrams X q) :=
  NatIso.ofComponents (stageIso X q) (by
    intro n m f
    rw [stageIso_hom, stageIso_hom]
    exact (diagramComparison X q).naturality f)

/-- The entire diagonal Iso retains the full original projection natural transformation. -/
theorem diagramIso_hom (q : ℤ) : (diagramIso X q).hom = diagramComparison X q := by
  apply NatTrans.ext
  funext n
  exact stageIso_hom X q n

/-- Every original stable-pi projection is retained in the full finite coordinate comparison. -/
def comparison (q : ℤ) : (integerStablePiFunctor q).obj (∏ᶜ X) ⟶
    GrpCat.of (∀ i, (integerStablePiFunctor q).obj (X i)) :=
  GrpCat.ofHom {
    toFun := fun z i => ((integerStablePiFunctor q).map (Pi.π X i)).hom z
    map_one' := by funext i; exact map_one _
    map_mul' := by intro a b; funext i; exact map_mul _ _ _ }

/-- The actual native integer stable-pi functor preserves the entire finite product. -/
def comparisonIso (q : ℤ) : (integerStablePiFunctor q).obj (∏ᶜ X) ≅
    GrpCat.of (∀ i, (integerStablePiFunctor q).obj (X i)) :=
  GrpCat.FilteredColimits.colimitFunctor.mapIso (diagramIso X q) ≪≫
    GrpCat.FilteredColimits.FiniteProducts.comparisonIso (diagrams X q)

omit [Fintype ι] in
private theorem diagramComparison_projection (q : ℤ) (i : ι) :
    diagramComparison X q ≫
      GrpCat.FilteredColimits.FiniteProducts.projection (diagrams X q) i = diagramProjection X q i := by
  apply NatTrans.ext
  funext n
  rfl

/-- The entire original comparison hom retains the diagonal quotient map and finite quotient comparison. -/
theorem comparisonIso_factor (q : ℤ) :
    (comparisonIso X q).hom = GrpCat.FilteredColimits.colimitMap (diagramComparison X q) ≫
      (GrpCat.FilteredColimits.FiniteProducts.comparisonIso (diagrams X q)).hom := by
  exact congrArg (fun f => GrpCat.FilteredColimits.colimitMap f ≫
    (GrpCat.FilteredColimits.FiniteProducts.comparisonIso (diagrams X q)).hom) (diagramIso_hom X q)

/-- The whole comparison Iso hom is the actual native stable-pi map of each original spectrum projection. -/
theorem comparisonIso_hom (q : ℤ) : (comparisonIso X q).hom = comparison X q := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  funext i
  have h := GrpCat.FilteredColimits.colimitMap_comp (diagramComparison X q)
    (GrpCat.FilteredColimits.FiniteProducts.projection (diagrams X q) i)
  have hp := congrArg GrpCat.FilteredColimits.colimitMap (diagramComparison_projection X q i)
  rw [comparisonIso_factor]
  let z' : GrpCat.FilteredColimits.colimit ((integerDiagonalDiagramFunctor q).obj (∏ᶜ X)) := z
  have hc := GrpCat.FilteredColimits.FiniteProducts.comparisonIso_coordinate (diagrams X q)
    ((GrpCat.FilteredColimits.colimitMap (diagramComparison X q)).hom z') i
  exact hc.trans ((ConcreteCategory.congr_hom h z').symm.trans (ConcreteCategory.congr_hom hp z'))

omit [Fintype ι] in
/-- Every entire original integer stage leg retains the same coordinate stage map and quotient leg. -/
theorem comparison_stage_leg (q : ℤ) (n : ℕ)
    (z : PointedCGWH.piN (integerTailPositiveIndex q + n + 1)
      (level (∏ᶜ X) (integerTailLevel q + n))) (i : ι) :
    (comparison X q).hom ((integerStablePiLeg q (∏ᶜ X) n).hom z) i =
      (integerStablePiLeg q (X i) n).hom
        (PointedCGWH.piNMap (integerTailPositiveIndex q + n + 1)
          (levelMap (Pi.π X i) (integerTailLevel q + n)) z) := by
  have h := ConcreteCategory.congr_hom (integerStablePiLeg_naturality q (Pi.π X i) n) z
  exact h.trans (congrArg (integerStablePiLeg q (X i) n).hom
    (PointedCGWH.piNPositiveMap_apply (integerTailPositiveIndex q + n)
      (levelMap (Pi.π X i) (integerTailLevel q + n)) z))

/-- Every whole original finite family of spectrum maps acts coordinatewise on the integer groups. -/
def coordinateMap {X Y : ι → PointedCGWH.SequentialSpectrum.{u, v}}
    (f : ∀ i, X i ⟶ Y i) (q : ℤ) :
    GrpCat.of (∀ i, (integerStablePiFunctor q).obj (X i)) ⟶
      GrpCat.of (∀ i, (integerStablePiFunctor q).obj (Y i)) :=
  GrpCat.ofHom {
    toFun := fun z i => ((integerStablePiFunctor q).map (f i)).hom (z i)
    map_one' := by funext i; exact map_one _
    map_mul' := by intro a b; funext i; exact map_mul _ _ _ }

omit [Fintype ι] in
/-- The original finite product comparison is natural in every complete original spectrum map. -/
theorem comparison_naturality {X Y : ι → PointedCGWH.SequentialSpectrum.{u, v}}
    [HasProduct X] [HasProduct Y] (f : ∀ i, X i ⟶ Y i) (q : ℤ) :
    (integerStablePiFunctor q).map (CategoryTheory.Limits.Pi.map f) ≫ comparison Y q =
      comparison X q ≫ coordinateMap f q := by
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro z
  funext i
  have h := (integerStablePiFunctor q).congr_map (CategoryTheory.Limits.Pi.map_π f i)
  have hm := (integerStablePiFunctor q).map_comp (CategoryTheory.Limits.Pi.map f) (Pi.π Y i)
  have hn := (integerStablePiFunctor q).map_comp (Pi.π X i) (f i)
  exact (ConcreteCategory.congr_hom hm z).symm.trans
    ((ConcreteCategory.congr_hom h z).trans (ConcreteCategory.congr_hom hn z))

end PointedCGWH.SequentialSpectrum.MappingTelescope.FiniteProductGeometry
