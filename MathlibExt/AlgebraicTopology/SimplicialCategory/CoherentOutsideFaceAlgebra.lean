/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOutsideIntervals
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomTransportEndpoints

/-!
# Whole composition of actual supplied outside-face Hom maps

An original ordinal face whose omitted label lies outside each interval
has genuine Hom isomorphisms. The supplied horn face therefore gives
whole composition at those individual original endpoint labels.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OutsideFaceAlgebra
open SimplicialEnrichment
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The actual enriched Hom map of a supplied outside face is an isomorphism. -/
theorem outside_isIso (j : Fin (n + 3)) (a' b' : ULift.{u} (Fin (n + 2)))
    (h : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) b' < ULift.up j) :
    IsIso ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk a') (.mk b')) :=
  (IntervalFaceCover.outsideIso_operator j a' b' h) ▸ (IntervalFaceCover.outsideIso j a'
    b' h).isIso_hom

/-- The actual supplied outside-face map is the genuine Hom-isomorphism transport with its
two original
  endpoint equations. -/
theorem faceMap_eq_transport (j : Fin (n + 3)) (hj : j ≠ i) (a' b' : ULift.{u} (Fin (n + 2)))
    (h : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) b' < ULift.up j)
    {a b : Fin (n + 3)} (ha : j.succAbove a'.down = a) (hb : j.succAbove b'.down = b) :
    let _ : IsIso ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk a') (.mk b')) :=
      outside_isIso j a' b' h
    HornOutsideIntervals.faceMap f j hj a' b' h ha hb =
      HomTransportEndpoints.map (coherentSimplexMap (SimplexCategory.δ j))
        (HornFaces.faceFunctor f j hj)
        (.mk a') (.mk b')
        (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) ha)
        (congrArg (fun b : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} b)) hb)
        ((HornFaces.faceFunctor_obj f j hj (.mk a')).trans (congrArg (HornFaces.object f) ha))
        ((HornFaces.faceFunctor_obj f j hj (.mk b')).trans (congrArg (HornFaces.object f) hb)) := by
  let _ : IsIso ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk a') (.mk b')) :=
    outside_isIso j a' b' h
  subst a
  subst b
  have hInv : (IntervalFaceCover.outsideIso j a' b' h).inv =
      inv ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk a') (.mk b')) :=
    (Iso.inv_eq_inv (IntervalFaceCover.outsideIso j a' b' h)
      (@asIso SSet.{u} inferInstance _ _ ((coherentSimplexMap (SimplexCategory.δ j)).map
        (.mk a') (.mk b'))
        (outside_isIso j a' b' h))).mpr (IntervalFaceCover.outsideIso_operator j a' b' h)
  simp only [HornOutsideIntervals.faceMap, HomTransportEndpoints.map, HomTransport.map,
    HornHomFaces.faceMap, HornHomFaces.retargetMap, eqToHom_refl, Category.id_comp]
  rw [hInv]
  rfl

/-- The supplied outside-face maps preserve actual enriched composition with the same three
original vertices. -/
theorem faceMap_comp (j : Fin (n + 3)) (hj : j ≠ i) (a' b' c' : ULift.{u} (Fin (n + 2)))
    (hab : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) b' < ULift.up j)
    (hbc : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) b' ∨
      (OrdinalFace.embedding j) c' < ULift.up j)
    (hac : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) c' < ULift.up j)
    {a b c : Fin (n + 3)}
    (ha : j.succAbove a'.down = a) (hb : j.succAbove b'.down = b) (hc : j.succAbove c'.down = c) :
    eComp SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a))
        (SimplicialThickening.mk (ULift.up.{u} b)) (SimplicialThickening.mk (ULift.up.{u} c)) ≫
      HornOutsideIntervals.faceMap f j hj a' c' hac ha hc =
    (HornOutsideIntervals.faceMap f j hj a' b' hab ha hb ⊗ₘ
      HornOutsideIntervals.faceMap f j hj b' c' hbc hb hc) ≫
        eComp SSet.{u} (HornFaces.object f a) (HornFaces.object f b) (HornFaces.object f c) := by
  let _ : IsIso ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk a') (.mk b')) :=
    outside_isIso j a' b' hab
  let _ : IsIso ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk b') (.mk c')) :=
    outside_isIso j b' c' hbc
  let _ : IsIso ((coherentSimplexMap (SimplexCategory.δ j)).map (.mk a') (.mk c')) :=
    outside_isIso j a' c' hac
  rw [faceMap_eq_transport f j hj a' c' hac ha hc,
    faceMap_eq_transport f j hj a' b' hab ha hb, faceMap_eq_transport f j hj b' c' hbc hb hc]
  exact HomTransportEndpoints.map_comp (coherentSimplexMap (SimplexCategory.δ j))
    (HornFaces.faceFunctor f j hj) (SimplicialThickening.mk a') (SimplicialThickening.mk b')
      (SimplicialThickening.mk c')
    (congrArg (fun a : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} a)) ha)
    (congrArg (fun b : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} b)) hb)
    (congrArg (fun c : Fin (n + 3) => SimplicialThickening.mk (ULift.up.{u} c)) hc)
    ((HornFaces.faceFunctor_obj f j hj (.mk a')).trans (congrArg (HornFaces.object f) ha))
    ((HornFaces.faceFunctor_obj f j hj (.mk b')).trans (congrArg (HornFaces.object f) hb))
    ((HornFaces.faceFunctor_obj f j hj (.mk c')).trans (congrArg (HornFaces.object f) hc))

end CategoryTheory.CoherentRealization.OutsideFaceAlgebra
