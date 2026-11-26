/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryFaceCompatibility
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxGlue

/-!
# The complete original coherent boundary Hom map

The actual all-positive/all-negative face multicoequalizer glues the
full original boundary map. Its original source inclusion is monic.
Every original inner-horn box embeds in this same full boundary
subcomplex, and its original map is recovered exactly.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomGlue
open SimplicialEnrichment HornBoxFaces BoundaryHomFaceCompatibility
variable {n : ℕ}

/-- The actual full original outer-Hom boundary subcomplex retains all positive and negative original faces. -/
def boundary : (outerHom.{u} n).Subcomplex := ⨆ x : BoundaryHomFaceCompatibility.Index.{u} n, face x

/-- The actual full original face multicoequalizer and all same pairwise intersections. -/
theorem diagram : SSet.Subcomplex.MulticoequalizerDiagram (boundary.{u} (n := n)) (face (n := n))
    (fun x y : BoundaryHomFaceCompatibility.Index.{u} n => face x ⊓ face y) where
  eq_inf _ _ := rfl
  iSup_eq := rfl

/-- Each whole original face has its literal inclusion into the complete boundary subcomplex. -/
def inclusion (x : BoundaryHomFaceCompatibility.Index.{u} n) : (face x : SSet.{u}) ⟶ (boundary.{u} (n := n)) :=
  SSet.Subcomplex.homOfLE (le_iSup face x)

variable {C : Carrier.{u}} (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The genuine complete original boundary Hom map obtained from every actual positive and negative face. -/
def map : (boundary.{u} (n := n) : SSet.{u}) ⟶
    (BoundaryFaces.object f 0 ⟶[SSet.{u}] BoundaryFaces.object f (Fin.last (n+2))) :=
  Multicofork.IsColimit.desc (diagram.{u} (n := n)).isColimit (maps f)
    (fun p => BoundaryHomFaceCompatibility.compatible f p.1 p.2)

/-- Every full original face of that same boundary map is read back literally. -/
theorem map_face (x : BoundaryHomFaceCompatibility.Index.{u} n) :
    inclusion x ≫ map f = maps f x :=
  Multicofork.IsColimit.fac (diagram.{u} (n := n)).isColimit (maps f)
    (fun p => BoundaryHomFaceCompatibility.compatible f p.1 p.2) x

/-- Each same original inner-horn Hom box lies in the full original boundary face union. -/
theorem hornBox_le (i : Fin (n+3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) :
    HornBoxGlue.box i hi₀ hiₙ ≤ boundary := by
  apply le_trans (HornBoxFaces.cover i hi₀ hiₙ).symm.le
  apply iSup_le
  intro x
  rcases x with b | k
  · exact le_iSup face (.inl b)
  · exact le_iSup face (.inr k.val)

/-- The actual inclusion of each original whole horn box in the same complete boundary subcomplex. -/
def hornBoxInclusion (i : Fin (n+3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) :
    (HornBoxGlue.box i hi₀ hiₙ : SSet.{u}) ⟶ (boundary.{u} (n := n)) :=
  SSet.Subcomplex.homOfLE (hornBox_le i hi₀ hiₙ)

/-- Each actual horn-box inclusion retains its literal full original ambient map. -/
theorem hornBoxInclusion_ι (i : Fin (n+3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) :
    hornBoxInclusion i hi₀ hiₙ ≫ (boundary.{u} (n := n)).ι = (HornBoxGlue.box i hi₀ hiₙ).ι :=
  SSet.Subcomplex.homOfLE_ι (hornBox_le i hi₀ hiₙ)

/-- Every actual original inner-horn restriction recovers the same entire original horn Hom-box map. -/
theorem map_hornBox (i : Fin (n+3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n+2)) :
    hornBoxInclusion i hi₀ hiₙ ≫ map f =
      HornBoxGlue.boxMap hi₀ hiₙ (BoundaryFaces.horn f i) := by
  apply Multicofork.IsColimit.hom_ext (HornBoxGlue.diagram i hi₀ hiₙ).isColimit
  intro x
  rcases x with b | k
  · have hι : HornBoxGlue.inclusion i hi₀ hiₙ (.inl b) ≫ hornBoxInclusion i hi₀ hiₙ =
        inclusion (.inl b) := rfl
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ map f) hι).trans
        ((map_face f (.inl b)).trans
          ((BoundaryHomFaces.positiveMap_horn f i hi₀ hiₙ b).symm.trans
            (HornBoxGlue.boxMap_face hi₀ hiₙ (BoundaryFaces.horn f i) (.inl b)).symm)))
  · have hι : HornBoxGlue.inclusion i hi₀ hiₙ (.inr k) ≫ hornBoxInclusion i hi₀ hiₙ =
        inclusion (.inr k.val) := rfl
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ map f) hι).trans
        ((map_face f (.inr k.val)).trans
          ((BoundaryHomFaces.negativeMap_horn f i k.val k.property).symm.trans
            (HornBoxGlue.boxMap_face hi₀ hiₙ (BoundaryFaces.horn f i) (.inr k)).symm)))

end CategoryTheory.CoherentRealization.BoundaryHomGlue
