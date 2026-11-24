/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxGlue

/-!
# The actual outer Hom extension of a supplied coherent inner horn

The whole box map has been constructed from the original supplied horn.
A genuine Kan structure on the target Hom extends that map across the
proved anodyne original Hom-box inclusion. Every original positive and
retained negative face reads back its actual supplied map.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornOuterMap
open SimplicialEnrichment HornBoxFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
  [SSet.KanComplex (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2)))]

/-- The actual original outer Hom admits an extension of its genuinely constructed whole horn box map. -/
theorem exists_map : ∃ g : outerHom.{u} n ⟶
    (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))),
    (HornBoxGlue.box i hi₀ hiₙ).ι ≫ g = HornBoxGlue.boxMap hi₀ hiₙ f :=
  HomOpenBox.exists_fill (show (ULift.up.{u} (0 : Fin (n + 3))) ≤ ULift.up (Fin.last (n + 2)) from Fin.zero_le _)
    (inner i hi₀ hiₙ) (HornBoxGlue.boxMap hi₀ hiₙ f)

/-- An actual chosen whole outer Hom extension, retaining the original endpoints and supplied inner horn. -/
def map : outerHom.{u} n ⟶
    (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))) :=
  Classical.choose (exists_map f hi₀ hiₙ)

/-- The chosen extension restricts to the whole actual original horn box map. -/
theorem map_box : (HornBoxGlue.box i hi₀ hiₙ).ι ≫ map f hi₀ hiₙ = HornBoxGlue.boxMap hi₀ hiₙ f :=
  Classical.choose_spec (exists_map f hi₀ hiₙ)

/-- Each original positive or retained negative face reads exactly the actual supplied-horn face map. -/
theorem face_map (x : Index.{u} i) : (face i x).ι ≫ map f hi₀ hiₙ = maps f hi₀ hiₙ x := by
  have hI : HornBoxGlue.inclusion i hi₀ hiₙ x ≫ (HornBoxGlue.box i hi₀ hiₙ).ι = (face i x).ι :=
    SSet.Subcomplex.homOfLE_ι ((le_iSup (face i) x).trans (cover i hi₀ hiₙ).le)
  exact (congrArg (fun g => g ≫ map f hi₀ hiₙ) hI).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun g => HornBoxGlue.inclusion i hi₀ hiₙ x ≫ g) (map_box f hi₀ hiₙ)).trans
        (HornBoxGlue.boxMap_face hi₀ hiₙ f x)))

/-- Composition through every original interior vertex is the actual composition of its two supplied short Hom maps. -/
theorem positive_comp (b : Interior.{u} n) :
    CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 3))) b.val (ULift.up.{u} (Fin.last (n + 2))) ≫
      map f hi₀ hiₙ =
      (leftMap f hi₀ hiₙ b ⊗ₘ rightMap f hi₀ hiₙ b) ≫
        eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (HornBoxFaces.vertex b))
          (HornFaces.object f (Fin.last (n + 2))) :=
  (congrArg (fun g => g ≫ map f hi₀ hiₙ)
    (CompositionFace.positiveIso_composition (ULift.up.{u} (0 : Fin (n + 3))) b.val (ULift.up.{u} (Fin.last
      (n + 2))))).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) b.val
          (ULift.up.{u} (Fin.last (n + 2)))).hom ≫ g) (face_map f hi₀ hiₙ (.inl b))).trans
            (positiveMap_readback f hi₀ hiₙ b)))

/-- Every retained original negative face reads its actual whole supplied face Hom map at the same two outer
  vertices. -/
theorem negative_readback (k : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
        (ULift.ext (source_zero k)) (ULift.ext (target_last k))) ≫ map f hi₀ hiₙ =
      HornHomFaces.retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
          (source_zero k)))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
          (target_last k))) :=
  (congrArg (fun g => g ≫ map f hi₀ hiₙ) (HornNegativeMaps.chart_operator k)).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun g => (negativeChart k).hom ≫ g) (face_map f hi₀ hiₙ (.inr ⟨k, hk⟩))).trans
        (HornBoxFaces.negativeMap_readback f k hk)))

end CategoryTheory.CoherentRealization.HornOuterMap
