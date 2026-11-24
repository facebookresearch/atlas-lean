/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryHigherFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentOneSimplexExt

/-!
# Every original two-simplex boundary face

The full negative face fixes the entire original forward Hom of the
middle one-simplex. Both original endpoint objects and the complete
Hom map therefore recover the same supplied middle face.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomAssembly
open SimplicialEnrichment HornBoxFaces

variable {C : Carrier.{u}}
  (f : (∂Δ[2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (g : outerHom.{u} 0 ⟶ (BoundaryFaces.object f 0 ⟶[SSet.{u}]
    BoundaryFaces.object f (Fin.last 2)))
  (hg : (BoundaryHomGlue.boundary.{u} (n := 0)).ι ≫ g = BoundaryHomGlue.map f)

/-- The actual full middle boundary face reads back its whole original retargeted forward Hom. -/
theorem simplex_middle_retarget :
    HornHomFaces.retargetMap
      (coherentSimplexMap (SimplexCategory.δ (1 : Fin 3)) ≫
        simplex f g hg 1 (by decide) (by decide))
      OneSimplexMaps.first OneSimplexMaps.last
      (by rfl) (by rfl) =
    HornHomFaces.retargetMap (BoundaryFaces.faceFunctor f (1 : Fin 3))
      OneSimplexMaps.first OneSimplexMaps.last
      ((BoundaryFaces.faceFunctor_obj f 1 _).trans
        (congrArg (BoundaryFaces.object f) (show (1 : Fin 3).succAbove 0 = 0 from rfl)))
      ((BoundaryFaces.faceFunctor_obj f 1 _).trans
        (congrArg (BoundaryFaces.object f) (show (1 : Fin 3).succAbove (Fin.last 1) = Fin.last 2 from rfl))) := by
  let k : Interior.{u} 0 := ⟨ULift.up (1 : Fin 3), by decide, by decide⟩
  have hι : BoundaryHomGlue.inclusion (.inr k) ≫
      (BoundaryHomGlue.boundary.{u} (n := 0)).ι =
      (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last 2))).ι := rfl
  have hFace : (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last 2))).ι ≫ g =
      BoundaryHomFaces.negativeMap f k :=
    (congrArg (fun q => q ≫ g) hι).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun q => BoundaryHomGlue.inclusion (.inr k) ≫ q) hg).trans
          (BoundaryHomGlue.map_face f (.inr k))))
  have hChart := (congrArg (fun q => q ≫ g) (HornNegativeMaps.chart_operator k)).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => (negativeChart k).hom ≫ q) hFace).trans
        (BoundaryHomFaces.negativeMap_readback f k)))
  have hOuter :
      (simplex f g hg 1 (by decide) (by decide)).map
        (.mk (ULift.up (0 : Fin 3))) (.mk (ULift.up (Fin.last 2))) = g :=
    HornAssembly.simplex_outer_map (BoundaryFaces.horn f 1) (by decide) (by decide) g
      (horn_extension f g hg 1 (by decide) (by decide))
  have hRetarget := HomRetargetAlgebra.restriction_reindex
    (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k)))
    (simplex f g hg 1 (by decide) (by decide))
    OneSimplexMaps.first OneSimplexMaps.last
    (congrArg (fun a : Fin 3 => (SimplicialThickening.mk (ULift.up.{u} a) : coherentSimplex.{u} ⦋2⦌))
      (source_zero k))
    (congrArg (fun a : Fin 3 => (SimplicialThickening.mk (ULift.up.{u} a) : coherentSimplex.{u} ⦋2⦌))
      (target_last k))
    (show (simplex f g hg 1 (by decide) (by decide)).obj (.mk (ULift.up (0 : Fin 3))) =
      BoundaryFaces.object f 0 from rfl)
    (show (simplex f g hg 1 (by decide) (by decide)).obj (.mk (ULift.up (Fin.last 2))) =
      BoundaryFaces.object f (Fin.last 2) from rfl)
  change (coherentSimplexMap (SimplexCategory.δ (1 : Fin 3))).map
      OneSimplexMaps.first OneSimplexMaps.last ≫ 𝟙 _ ≫
      (simplex f g hg 1 (by decide) (by decide)).map
        (.mk (ULift.up (0 : Fin 3))) (.mk (ULift.up (Fin.last 2))) ≫ 𝟙 _ = _ at hRetarget
  simp only [Category.id_comp] at hRetarget
  rw [hOuter] at hRetarget
  change (coherentSimplexMap (SimplexCategory.δ (1 : Fin 3))).map
      OneSimplexMaps.first OneSimplexMaps.last ≫ 𝟙 _ ≫ g = _ at hChart
  simp only at hChart
  exact hRetarget.symm.trans hChart

/-- The supplied middle face is recovered as the SAME whole original enriched one-simplex. -/
theorem simplex_middle_face :
    coherentSimplexMap (SimplexCategory.δ (1 : Fin 3)) ≫
      simplex f g hg 1 (by decide) (by decide) =
    BoundaryFaces.faceFunctor f (1 : Fin 3) := by
  let F := coherentSimplexMap (SimplexCategory.δ (1 : Fin 3)) ≫
    simplex f g hg 1 (by decide) (by decide)
  let G := BoundaryFaces.faceFunctor f (1 : Fin 3)
  have h₀ : G.obj OneSimplexMaps.first = F.obj OneSimplexMaps.first :=
    BoundaryFaces.faceFunctor_obj f 1 _
  have h₁ : G.obj OneSimplexMaps.last = F.obj OneSimplexMaps.last :=
    BoundaryFaces.faceFunctor_obj f 1 _
  apply OneSimplexMaps.ext F G h₀.symm h₁.symm
  let T := eqToIso (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) h₀ h₁)
  change F.map OneSimplexMaps.first OneSimplexMaps.last ≫ T.inv =
    G.map OneSimplexMaps.first OneSimplexMaps.last
  apply (Iso.comp_inv_eq T).mpr
  exact simplex_middle_retarget f g hg

/-- Every original boundary face is retained by the same two-simplex, including its middle face. -/
theorem simplex_two_all_faces (k : Fin 3) :
    coherentSimplexMap (SimplexCategory.δ k) ≫
      simplex f g hg 1 (by decide) (by decide) = BoundaryFaces.faceFunctor f k := by
  by_cases hk : k = 1
  · subst k
    exact simplex_middle_face f g hg
  · exact simplex_face_of_retained f g hg 1 k (by decide) (by decide) hk

end CategoryTheory.CoherentRealization.BoundaryHomAssembly
