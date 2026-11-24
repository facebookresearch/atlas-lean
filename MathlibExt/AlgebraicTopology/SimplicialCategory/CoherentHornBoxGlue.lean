/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFaceCompatibility
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The actual coherent Hom-box map of a supplied inner horn

The original face cover is a genuine multicoequalizer of its pairwise
intersections. All compatibility equations have been proved from the
supplied horn, so its whole positive and retained negative Hom maps glue
to an actual map from the original Hom box.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornBoxGlue
open SimplicialEnrichment HornBoxFaces
variable {n : ℕ} (i : Fin (n + 3)) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

/-- The literal original coherent Hom box at the supplied missing inner label. -/
abbrev box : (outerHom.{u} n).Subcomplex :=
  HomOpenBox.subcomplex (show (ULift.up.{u} (0 : Fin (n + 3))) ≤ ULift.up (Fin.last (n + 2)) from Fin.zero_le _)
    (inner i hi₀ hiₙ)

/-- The original actual face cover and its genuine pairwise intersections form the subcomplex
  multicoequalizer diagram. -/
def diagram : SSet.Subcomplex.MulticoequalizerDiagram (box i hi₀ hiₙ) (face i)
    (fun x y => face i x ⊓ face i y) where
  eq_inf _ _ := rfl
  iSup_eq := cover i hi₀ hiₙ

/-- The actual inclusion of a supplied original face in the whole original Hom box. -/
def inclusion (x : Index.{u} i) : (face i x : SSet.{u}) ⟶ box i hi₀ hiₙ :=
  SSet.Subcomplex.homOfLE ((le_iSup (face i) x).trans (cover i hi₀ hiₙ).le)

variable {i} {C : Carrier.{u}}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The genuine whole box map constructed from the supplied horn and its proved actual face agreements. -/
def boxMap : (box i hi₀ hiₙ : SSet.{u}) ⟶
    (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))) :=
  Multicofork.IsColimit.desc (diagram i hi₀ hiₙ).isColimit (maps f hi₀ hiₙ)
    (fun p => HornFaceCompatibility.compatible f hi₀ hiₙ p.1 p.2)

/-- Every original positive and retained negative face reads exactly its constructed supplied-horn map. -/
theorem boxMap_face (x : Index.{u} i) : inclusion i hi₀ hiₙ x ≫ boxMap hi₀ hiₙ f = maps f hi₀ hiₙ x :=
  Multicofork.IsColimit.fac (diagram i hi₀ hiₙ).isColimit (maps f hi₀ hiₙ)
    (fun p => HornFaceCompatibility.compatible f hi₀ hiₙ p.1 p.2) x

/-- The whole positive-face chart reads the original target composition of its two supplied short Hom maps. -/
theorem positive_readback (b : Interior.{u} n) :
    (CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) b.val (ULift.up.{u} (Fin.last (n + 2)))).hom ≫
      inclusion i hi₀ hiₙ (.inl b) ≫ boxMap hi₀ hiₙ f =
        (leftMap f hi₀ hiₙ b ⊗ₘ rightMap f hi₀ hiₙ b) ≫
          eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (HornBoxFaces.vertex b))
            (HornFaces.object f (Fin.last (n + 2))) :=
  (congrArg (fun g => (CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) b.val
    (ULift.up.{u} (Fin.last (n + 2)))).hom ≫ g) (boxMap_face hi₀ hiₙ f (.inl b))).trans
      (positiveMap_readback f hi₀ hiₙ b)

/-- The original whole negative Hom chart reads the actual supplied face functor at its exact outer endpoints. -/
theorem negative_readback (k : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    (negativeChart k).hom ≫ inclusion i hi₀ hiₙ (.inr ⟨k, hk⟩) ≫ boxMap hi₀ hiₙ f =
      HornHomFaces.retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
          (source_zero k)))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
          (target_last k))) :=
  (congrArg (fun g => (negativeChart k).hom ≫ g) (boxMap_face hi₀ hiₙ f (.inr ⟨k, hk⟩))).trans
    (HornBoxFaces.negativeMap_readback f k hk)

end CategoryTheory.CoherentRealization.HornBoxGlue
