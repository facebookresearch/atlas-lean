/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornArithmetic

/-!
# The two right join--horn factor maps

Colimit constructions for the two pieces of the boundary--horn pushout:
`Δ[p] ⋆ Λ[q+1,j]` and `∂Δ[p] ⋆ Δ[q+1]`.  The public `JoinHorn` module
glues these maps and packages the resulting Arrow isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet
namespace JoinHorn.Internal

attribute [local instance] joinHorn_isConnectedWalkingMultispan

/-- The right-factor horn index, shifted past the `p+1` vertices in the
left standard simplex. -/
def rightJoinHornIndex (p q : ℕ) (j : Fin (q + 2)) :
    Fin ((p + (q + 1) + 1) + 1) :=
  ⟨p + 1 + j.val, by have := j.isLt; omega⟩

/-- The left-factor horn index, regarded as a vertex of the joined standard
simplex. -/
def leftJoinHornIndex (p q : ℕ) (i : Fin (p + 2)) :
    Fin (((p + 1) + q + 1) + 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

lemma rightJoinHornIndex_ne (p q : ℕ) (j r : Fin (q + 2))
    (hr : r ≠ j) :
    rightJoinHornIndex p q r ≠ rightJoinHornIndex p q j := by
  intro h
  apply hr
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [rightJoinHornIndex] at this
  omega

lemma leftJoinHornIndex_ne (p q : ℕ) (i r : Fin (p + 2))
    (hr : r ≠ i) :
    leftJoinHornIndex p q r ≠ leftJoinHornIndex p q i := by
  intro h
  apply hr
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [leftJoinHornIndex] at this
  exact this

/-!
## Internal face-colimit construction
-/

/-- A right-factor codimension-one face, transported into the large horn. -/
noncomputable def joinBoundaryHornRightFaceMap (p q : ℕ)
    (j : Fin (q + 2)) (r : ↑({j}ᶜ : Set (Fin (q + 2)))) :
    (join.{u}.obj (Δ[p] : SSet.{u})).obj
        (stdSimplex.face {r.1}ᶜ : SSet.{u}) ⟶
      (horn.{u} (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) :=
  (join.obj (Δ[p] : SSet.{u})).map
      (stdSimplex.faceSingletonComplIso r.1).inv ≫
    (joinStdSimplexIso p q).hom ≫
      horn.ι (rightJoinHornIndex p q j)
        (rightJoinHornIndex p q r.1)
        (rightJoinHornIndex_ne p q j r.1 (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2))


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma joinBoundaryHornRightFaceMap_compatible (p q : ℕ)
    (j : Fin (q + 2))
    (a : (MultispanShape.ofLinearOrder ↑({j}ᶜ : Set (Fin (q + 2)))).L) :
    ((((horn.multicoequalizerDiagram j).multispanIndex.toLinearOrder.map
        Subcomplex.toSSetFunctor).map (join.obj (Δ[p] : SSet.{u}))).fst a) ≫
        joinBoundaryHornRightFaceMap p q j
          ((MultispanShape.ofLinearOrder ↑({j}ᶜ : Set (Fin (q + 2)))).fst a) =
      ((((horn.multicoequalizerDiagram j).multispanIndex.toLinearOrder.map
        Subcomplex.toSSetFunctor).map (join.obj (Δ[p] : SSet.{u}))).snd a) ≫
        joinBoundaryHornRightFaceMap p q j
          ((MultispanShape.ofLinearOrder ↑({j}ᶜ : Set (Fin (q + 2)))).snd a) := by
  rcases a with ⟨⟨⟨r, hr⟩, ⟨s, hs⟩⟩, hrs : r < s⟩
  obtain _ | q := q
  · simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hr hs
    fin_cases r <;> fin_cases s <;> omega
  · rw [MultispanIndex.map_fst, MultispanIndex.map_snd]
    rw [MultispanIndex.map_fst, MultispanIndex.map_snd]
    rw [MultispanIndex.toLinearOrder_fst, MultispanIndex.toLinearOrder_snd]
    rw [CompleteLattice.MulticoequalizerDiagram.multispanIndex_fst,
      CompleteLattice.MulticoequalizerDiagram.multispanIndex_snd]
    dsimp [joinBoundaryHornRightFaceMap] at hrs ⊢
    simp only [← Functor.map_comp_assoc]
    rw [stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred
          r s hrs,
      stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred
          r s hrs]
    simp only [Functor.map_comp, Category.assoc]
    rw [cancel_epi]
    rw [stdSimplex_δ_eq_map, stdSimplex_δ_eq_map,
      joinStdSimplexIso_natural_right_assoc,
      joinStdSimplexIso_natural_right_assoc,
      joinHorn_tensorHomOf_id_δ, joinHorn_tensorHomOf_id_δ,
      ← stdSimplex_δ_eq_map, ← stdSimplex_δ_eq_map]
    rw [cancel_epi]
    let R := rightJoinHornIndex p (q + 1) r
    let S := rightJoinHornIndex p (q + 1) s
    have hRS : R < S := by
      rw [Fin.lt_def]
      dsimp [R, S, rightJoinHornIndex]
      omega
    have eL : S.pred (Fin.ne_zero_of_lt hRS) =
        (⟨p + 1 + (s.pred (Fin.ne_zero_of_lt hrs)).val,
          by have := (s.pred (Fin.ne_zero_of_lt hrs)).isLt; omega⟩ :
          Fin (p + (q + 1 + 1) + 1)) := by
      apply Fin.ext
      dsimp [S, rightJoinHornIndex]
      omega
    have eR : R.castPred (Fin.ne_last_of_lt hRS) =
        (⟨p + 1 + (r.castPred (Fin.ne_last_of_lt hrs)).val,
          by have := (r.castPred (Fin.ne_last_of_lt hrs)).isLt; omega⟩ :
          Fin (p + (q + 1 + 1) + 1)) := by
      apply Fin.ext
      dsimp [R, rightJoinHornIndex]
    have hRne : R ≠ rightJoinHornIndex p (q + 1) j :=
      rightJoinHornIndex_ne p (q + 1) j r (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hr)
    have hSne : S ≠ rightJoinHornIndex p (q + 1) j :=
      rightJoinHornIndex_ne p (q + 1) j s (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs)
    have hcompat :=
      (horn.IsCompatible.of_hom
        (𝟙 (horn (p + (q + 1 + 1) + 1)
          (rightJoinHornIndex p (q + 1) j) : SSet.{u}))).δ_pred_comp
          R S (hj := hRne) (hk := hSne) (hjk := hRS)
    rw [eL, eR] at hcompat
    simpa only [Category.comp_id, R, S] using hcompat

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical map from `Δ[p] ⋆ Λ[q+1,j]` to the shifted horn. -/
noncomputable def joinBoundaryHornRightFactorMap (p q : ℕ)
    (j : Fin (q + 2)) :
    (Δ[p] : SSet.{u}) ⋆ (horn (q + 1) j : SSet.{u}) ⟶
      (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) := by
  let _ : Nonempty ↑({j}ᶜ : Set (Fin (q + 2))) :=
    (Set.nonempty_compl_of_nontrivial j).to_subtype
  exact Multicofork.IsColimit.desc
    (Multicofork.isColimitMapOfPreserves
      ((horn.multicoequalizerDiagram j).multicofork.toLinearOrder.map
        Subcomplex.toSSetFunctor)
      (join.obj (Δ[p] : SSet.{u})) (horn.isColimit j))
    (joinBoundaryHornRightFaceMap p q j)
    (joinBoundaryHornRightFaceMap_compatible p q j)
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma joinBoundaryHornRightFactorMap_face (p q : ℕ)
    (j r : Fin (q + 2)) (hr : r ≠ j) :
    (join.obj (Δ[p] : SSet.{u})).map (horn.ι j r hr) ≫
        joinBoundaryHornRightFactorMap p q j =
      (joinStdSimplexIso p q).hom ≫
        horn.ι (rightJoinHornIndex p q j) (rightJoinHornIndex p q r)
          (rightJoinHornIndex_ne p q j r hr) := by
  let _ : Nonempty ↑({j}ᶜ : Set (Fin (q + 2))) :=
    (Set.nonempty_compl_of_nontrivial j).to_subtype
  rw [← cancel_epi ((join.obj (Δ[p] : SSet.{u})).map
    (stdSimplex.faceSingletonComplIso r).inv)]
  rw [← Functor.map_comp_assoc, horn.faceSingletonComplIso_inv_ι]
  have hfac := Multicofork.IsColimit.fac
    (Multicofork.isColimitMapOfPreserves
      ((horn.multicoequalizerDiagram j).multicofork.toLinearOrder.map
        Subcomplex.toSSetFunctor)
      (join.obj (Δ[p] : SSet.{u})) (horn.isColimit j))
    (joinBoundaryHornRightFaceMap p q j)
    (joinBoundaryHornRightFaceMap_compatible p q j)
    (⟨r, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hr⟩ :
      ↑({j}ᶜ : Set (Fin (q + 2))))
  change (join.obj (Δ[p] : SSet.{u})).map (horn.faceι j r hr) ≫
      joinBoundaryHornRightFactorMap p q j =
    joinBoundaryHornRightFaceMap p q j
      (⟨r, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hr⟩ :
        ↑({j}ᶜ : Set (Fin (q + 2)))) at hfac
  simpa only [joinBoundaryHornRightFactorMap, joinBoundaryHornRightFaceMap,
    Category.assoc] using hfac

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma joinBoundaryHornRight_hom_ext (p q : ℕ) (j : Fin (q + 2))
    {X : SSet.{u}}
    {f g : ((Δ[p] : SSet.{u}) ⋆ (horn (q + 1) j : SSet.{u})) ⟶ X}
    (h : ∀ (r : Fin (q + 2)) (hr : r ≠ j),
      (join.obj (Δ[p] : SSet.{u})).map (horn.ι j r hr) ≫ f =
        (join.obj (Δ[p] : SSet.{u})).map (horn.ι j r hr) ≫ g) :
    f = g := by
  let _ : Nonempty ↑({j}ᶜ : Set (Fin (q + 2))) :=
    (Set.nonempty_compl_of_nontrivial j).to_subtype
  apply Multicofork.IsColimit.hom_ext
    (Multicofork.isColimitMapOfPreserves
      ((horn.multicoequalizerDiagram j).multicofork.toLinearOrder.map
        Subcomplex.toSSetFunctor)
      (join.obj (Δ[p] : SSet.{u})) (horn.isColimit j))
  intro r
  change (join.obj (Δ[p] : SSet.{u})).map (horn.faceι j r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2)) ≫ f =
    (join.obj (Δ[p] : SSet.{u})).map (horn.faceι j r.1 (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2)) ≫ g
  rw [← horn.faceSingletonComplIso_inv_ι,
    Functor.map_comp, Category.assoc, Category.assoc,
    h r.1 (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using r.2)]

@[reassoc]
lemma joinBoundaryHornRightFactorMap_ι (p q : ℕ)
    (j : Fin (q + 2)) :
    joinBoundaryHornRightFactorMap p q j ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (join.obj (Δ[p] : SSet.{u})).map (horn (q + 1) j).ι ≫
        (joinStdSimplexIso p (q + 1)).hom := by
  apply joinBoundaryHornRight_hom_ext p q j
  intro r hr
  rw [joinBoundaryHornRightFactorMap_face_assoc, horn.ι_ι]
  rw [← (join.obj (Δ[p] : SSet.{u})).map_comp_assoc,
    horn.ι_ι]
  symm
  change (join.obj (Δ[p] : SSet.{u})).map
      (stdSimplex.map (SimplexCategory.δ r)) ≫
        (joinStdSimplexIso p (q + 1)).hom =
    (joinStdSimplexIso p q).hom ≫
      stdSimplex.map (SimplexCategory.δ (rightJoinHornIndex p q r))
  rw [joinStdSimplexIso_natural_right,
    joinHorn_tensorHomOf_id_δ]
  rfl

/-- The boundary multicoequalizer after joining on the right with `Δ[q+1]`. -/
noncomputable def joinHornBoundaryMappedCocone (p q : ℕ) :=
  ((boundary.multicoequalizerDiagram.{u} (p + 1)).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor).map
      (join.flip.obj (Δ[q + 1] : SSet.{u}))

/-- Joining on the right with `Δ[q+1]` preserves the boundary colimit. -/
noncomputable def joinHornBoundaryMappedIsColimit (p q : ℕ) :
    IsColimit (joinHornBoundaryMappedCocone.{u} p q) :=
  Multicofork.isColimitMapOfPreserves
    ((boundary.multicoequalizerDiagram (p + 1)).multicofork.toLinearOrder.map
        Subcomplex.toSSetFunctor)
    (join.flip.obj (Δ[q + 1] : SSet.{u}))
    (boundary.isColimit (p + 1))

/-- The index of a face contributed by the left boundary block. -/
def rightJoinFrontFaceIndex (p q : ℕ) (r : Fin (p + 2)) :
    Fin (((p + 1) + (q + 1) + 1) + 1) :=
  ⟨r.val, by have := r.isLt; omega⟩

lemma rightJoinFrontFaceIndex_ne (p q : ℕ) (j : Fin (q + 2))
    (r : Fin (p + 2)) :
    rightJoinFrontFaceIndex p q r ≠ rightJoinHornIndex (p + 1) q j := by
  intro h
  have := congrArg Fin.val h
  dsimp [rightJoinFrontFaceIndex, rightJoinHornIndex] at this
  have := r.isLt
  omega

/-- A left-boundary face mapped into the shifted horn. -/
noncomputable def joinBoundaryHornRightBoundaryFaceMap
    (p q : ℕ) (j : Fin (q + 2)) (r : Fin (p + 2)) :
    (join.flip.obj (Δ[q + 1] : SSet.{u})).obj
        (stdSimplex.face {r}ᶜ : SSet.{u}) ⟶
      (horn ((p + 1) + (q + 1) + 1)
        (rightJoinHornIndex (p + 1) q j) : SSet.{u}) :=
  (join.flip.obj (Δ[q + 1] : SSet.{u})).map
      (stdSimplex.faceSingletonComplIso r).inv ≫
    (joinStdSimplexIso p (q + 1)).hom ≫
      joinHornΔcast (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1)) ≫
        horn.ι (rightJoinHornIndex (p + 1) q j)
          (rightJoinFrontFaceIndex p q r)
          (rightJoinFrontFaceIndex_ne p q j r)

@[reassoc]
lemma joinBoundaryHornRightBoundaryFaceMap_ι
    (p q : ℕ) (j : Fin (q + 2)) (r : Fin (p + 2)) :
    joinBoundaryHornRightBoundaryFaceMap.{u} p q j r ≫
        (horn ((p + 1) + (q + 1) + 1)
          (rightJoinHornIndex (p + 1) q j)).ι =
      (join.flip.obj (Δ[q + 1] : SSet.{u})).map
          (stdSimplex.face {r}ᶜ).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom := by
  unfold joinBoundaryHornRightBoundaryFaceMap
  rw [Category.assoc, Category.assoc, Category.assoc, horn.ι_ι]
  have hface : (stdSimplex.faceSingletonComplIso r).inv ≫
      stdSimplex.δ r = (stdSimplex.face {r}ᶜ).ι := by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso r).hom,
      Iso.hom_inv_id_assoc, stdSimplex.faceSingletonComplIso_hom_ι]
  rw [← hface, Functor.map_comp, Category.assoc, cancel_epi]
  exact (joinHorn_dualFrontPush r (rightJoinFrontFaceIndex p q r) rfl
    (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1))).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma joinBoundaryHornRightBoundaryFaceMap_compatible
    (p q : ℕ) (j : Fin (q + 2))
    (a : (MultispanShape.ofLinearOrder (Fin (p + 2))).L) :
    ((((boundary.multicoequalizerDiagram.{u} (p + 1)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor).map
          (join.flip.obj (Δ[q + 1] : SSet.{u}))).fst a) ≫
        joinBoundaryHornRightBoundaryFaceMap.{u} p q j
          ((MultispanShape.ofLinearOrder (Fin (p + 2))).fst a) =
      ((((boundary.multicoequalizerDiagram.{u} (p + 1)).multispanIndex.toLinearOrder.map
          Subcomplex.toSSetFunctor).map
          (join.flip.obj (Δ[q + 1] : SSet.{u}))).snd a) ≫
        joinBoundaryHornRightBoundaryFaceMap.{u} p q j
          ((MultispanShape.ofLinearOrder (Fin (p + 2))).snd a) := by
  rcases a with ⟨⟨r, s⟩, hrs : r < s⟩
  rw [MultispanIndex.map_fst, MultispanIndex.map_snd]
  rw [MultispanIndex.map_fst, MultispanIndex.map_snd]
  rw [MultispanIndex.toLinearOrder_fst, MultispanIndex.toLinearOrder_snd]
  rw [CompleteLattice.MulticoequalizerDiagram.multispanIndex_fst,
    CompleteLattice.MulticoequalizerDiagram.multispanIndex_snd]
  dsimp only [MultispanShape.ofLinearOrder_fst,
    MultispanShape.ofLinearOrder_snd]
  rw [← cancel_mono
    (horn ((p + 1) + (q + 1) + 1)
      (rightJoinHornIndex (p + 1) q j)).ι]
  simp only [Category.assoc]
  rw [joinBoundaryHornRightBoundaryFaceMap_ι,
    joinBoundaryHornRightBoundaryFaceMap_ι]
  simp only [← Functor.map_comp_assoc]
  rfl


set_option maxHeartbeats 1000000 in
/-- Colimit data defining the positive-dimensional boundary factor map. -/
structure JoinBoundaryHornRightBoundaryFactorData
    (p q : ℕ) (j : Fin (q + 2)) where
  /-- The induced map from the joined boundary. -/
  map : (join.flip.obj (Δ[q + 1] : SSet.{u})).obj (boundary (p + 1) : SSet.{u}) ⟶
    (horn ((p + 1) + (q + 1) + 1)
      (rightJoinHornIndex (p + 1) q j) : SSet.{u})
  /-- The induced map agrees with every boundary-face map. -/
  face (r : Fin (p + 2)) :
    (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary.faceι r) ≫ map =
      joinBoundaryHornRightBoundaryFaceMap p q j r

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The chosen positive-dimensional boundary factor and its face equations. -/
noncomputable def joinBoundaryHornRightBoundaryFactorData
    (p q : ℕ) (j : Fin (q + 2)) :
    JoinBoundaryHornRightBoundaryFactorData p q j := by
  let m := Multicofork.IsColimit.desc
    (joinHornBoundaryMappedIsColimit.{u} p q)
    (joinBoundaryHornRightBoundaryFaceMap.{u} p q j)
    (joinBoundaryHornRightBoundaryFaceMap_compatible.{u} p q j)
  refine { map := m, face := fun r => ?_ }
  have hfac := Multicofork.IsColimit.fac
    (joinHornBoundaryMappedIsColimit.{u} p q)
    (joinBoundaryHornRightBoundaryFaceMap.{u} p q j)
    (joinBoundaryHornRightBoundaryFaceMap_compatible.{u} p q j) r
  change (join.flip.obj (Δ[q + 1] : SSet.{u})).map
      (boundary.faceι r) ≫ m =
    joinBoundaryHornRightBoundaryFaceMap p q j r at hfac
  exact hfac


set_option maxHeartbeats 1000000 in
/-- The factor map for a nonzero left boundary dimension. -/
@[no_expose]
noncomputable def joinBoundaryHornRightBoundaryFactorMapSucc
    (p q : ℕ) (j : Fin (q + 2)) :
    (join.flip.obj (Δ[q + 1] : SSet.{u})).obj (boundary (p + 1) : SSet.{u}) ⟶
      (horn ((p + 1) + (q + 1) + 1)
        (rightJoinHornIndex (p + 1) q j) : SSet.{u}) :=
  (joinBoundaryHornRightBoundaryFactorData p q j).map

set_option maxHeartbeats 1000000 in
@[reassoc]
lemma joinBoundaryHornRightBoundaryFactorMapSucc_face
    (p q : ℕ) (j : Fin (q + 2)) (r : Fin (p + 2)) :
    (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary.ι r) ≫
        joinBoundaryHornRightBoundaryFactorMapSucc p q j =
      (joinStdSimplexIso p (q + 1)).hom ≫
        joinHornΔcast (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1)) ≫
          horn.ι (rightJoinHornIndex (p + 1) q j)
            (rightJoinFrontFaceIndex p q r)
            (rightJoinFrontFaceIndex_ne p q j r) := by
  rw [← cancel_epi ((join.flip.obj (Δ[q + 1] : SSet.{u})).map
    (stdSimplex.faceSingletonComplIso r).inv)]
  rw [← Functor.map_comp_assoc, boundary.faceSingletonComplIso_inv_ι]
  exact (joinBoundaryHornRightBoundaryFactorData p q j).face r

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma joinBoundaryHornRightBoundary_hom_ext
    (p q : ℕ) {X : SSet.{u}}
    {f g : ((join.flip.obj (Δ[q + 1] : SSet.{u})).obj (boundary (p + 1) : SSet.{u})) ⟶ X}
    (h : ∀ r : Fin (p + 2),
      (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary.ι r) ≫ f =
        (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary.ι r) ≫ g) :
    f = g := by
  apply Multicofork.IsColimit.hom_ext
    (joinHornBoundaryMappedIsColimit.{u} p q)
  intro r
  change (join.flip.obj (Δ[q + 1] : SSet.{u})).map
      (boundary.faceι r) ≫ f =
    (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary.faceι r) ≫ g
  rw [← boundary.faceSingletonComplIso_inv_ι,
    Functor.map_comp, Category.assoc, Category.assoc, h r]

@[reassoc]
lemma joinBoundaryHornRightBoundaryFactorMapSucc_ι
    (p q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightBoundaryFactorMapSucc.{u} p q j ≫
        (horn ((p + 1) + (q + 1) + 1)
          (rightJoinHornIndex (p + 1) q j)).ι =
      (join.map (boundary (p + 1)).ι).app (Δ[q + 1] : SSet.{u}) ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom := by
  apply joinBoundaryHornRightBoundary_hom_ext.{u} p q
  intro r
  rw [joinBoundaryHornRightBoundaryFactorMapSucc_face_assoc, horn.ι_ι]
  change (joinStdSimplexIso p (q + 1)).hom ≫
      joinHornΔcast _ ≫ stdSimplex.δ (rightJoinFrontFaceIndex p q r) =
    (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary.ι r) ≫
      (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary (p + 1)).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom
  rw [← (join.flip.obj (Δ[q + 1] : SSet.{u})).map_comp_assoc,
    boundary.ι_ι]
  have hdual := joinHorn_dualFrontPush r (rightJoinFrontFaceIndex p q r)
    rfl (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1))
  change (joinStdSimplexIso p (q + 1)).hom ≫
      joinHornΔcast _ ≫ stdSimplex.δ (rightJoinFrontFaceIndex p q r) =
    (join.map (stdSimplex.δ r)).app (Δ[q + 1] : SSet.{u}) ≫
      (joinStdSimplexIso (p + 1) (q + 1)).hom
  exact hdual.symm

/-- The zero-simplex boundary is the initial simplicial set. -/
def joinHornBoundaryZeroIso :
    (boundary 0 : SSet.{u}) ≅ (⊥_ SSet.{u}) :=
  (Subcomplex.eqToIso boundary_zero) ≪≫
    (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).uniqueUpToIso
      initialIsInitial

lemma rightJoinZeroFaceIndex_ne (q : ℕ) (j : Fin (q + 2)) :
    (0 : Fin ((0 + (q + 1) + 1) + 1)) ≠ rightJoinHornIndex 0 q j := by
  intro h
  have := congrArg Fin.val h
  dsimp [rightJoinHornIndex] at this
  omega

lemma joinHorn_joinInr_zero (q : ℕ) :
    joinInr (Δ[0] : SSet.{u}) (Δ[q + 1] : SSet.{u}) ≫
        (joinStdSimplexIso 0 (q + 1)).hom =
      joinHornΔcast (by omega : q + 1 = 0 + (q + 1)) ≫
        stdSimplex.δ (0 : Fin ((0 + (q + 1)) + 2)) := by
  rw [joinInr_comp_joinStdSimplexIso_hom]
  rw [stdSimplex_δ_eq_map, joinHornΔcast, joinHornΔcastIso,
    Functor.mapIso_hom, ← Functor.map_comp]
  congr 1
  ext r : 3
  apply Fin.ext
  simp [SimplexCategory.comp_toOrderHom,
    AugmentedSimplexCategory.inr'_eval,
    SimplexCategory.eqToHom_toOrderHom]
  change 1 + r.val =
    (Fin.succAbove (0 : Fin (0 + (q + 1) + 2))
      (Fin.cast (by omega : (q + 1) + 1 = 0 + (q + 1) + 1) r)).val
  rw [Fin.succAbove_zero]
  simp only [Fin.val_succ, Fin.val_cast]
  omega

set_option maxHeartbeats 4000000 in
/-- The boundary factor map in zero left dimension. -/
noncomputable def joinBoundaryHornRightBoundaryFactorMapZero
    (q : ℕ) (j : Fin (q + 2)) :
    (join.flip.obj (Δ[q + 1] : SSet.{u})).obj (boundary 0 : SSet.{u}) ⟶
      (horn (0 + (q + 1) + 1) (rightJoinHornIndex 0 q j) : SSet.{u}) :=
  (join.flip.obj (Δ[q + 1] : SSet.{u})).map joinHornBoundaryZeroIso.hom ≫
    (botJoinIso (Δ[q + 1] : SSet.{u})).hom ≫
      joinHornΔcast (by omega : q + 1 = 0 + (q + 1)) ≫
        horn.ι (rightJoinHornIndex 0 q j) 0
          (rightJoinZeroFaceIndex_ne q j)

@[reassoc]
lemma joinBoundaryHornRightBoundaryFactorMapZero_ι
    (q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightBoundaryFactorMapZero q j ≫
        (horn (0 + (q + 1) + 1) (rightJoinHornIndex 0 q j)).ι =
      (join.map (boundary 0).ι).app (Δ[q + 1] : SSet.{u}) ≫
        (joinStdSimplexIso 0 (q + 1)).hom := by
  rw [← cancel_epi ((join.flip.obj (Δ[q + 1] : SSet.{u})).map
    joinHornBoundaryZeroIso.inv)]
  unfold joinBoundaryHornRightBoundaryFactorMapZero
  simp only [Category.assoc]
  rw [horn.ι_ι]
  rw [← (join.flip.obj (Δ[q + 1] : SSet.{u})).map_comp_assoc,
    Iso.inv_hom_id]
  rw [(join.flip.obj (Δ[q + 1] : SSet.{u})).map_id, Category.id_comp]
  change (botJoinIso (Δ[q + 1] : SSet.{u})).hom ≫
      joinHornΔcast _ ≫ stdSimplex.δ 0 =
    (join.flip.obj (Δ[q + 1] : SSet.{u})).map joinHornBoundaryZeroIso.inv ≫
      (join.flip.obj (Δ[q + 1] : SSet.{u})).map (boundary 0).ι ≫
        (joinStdSimplexIso 0 (q + 1)).hom
  have hinit : joinHornBoundaryZeroIso.inv ≫ (boundary 0).ι =
      initial.to (Δ[0] : SSet.{u}) := initialIsInitial.hom_ext _ _
  rw [← (join.flip.obj (Δ[q + 1] : SSet.{u})).map_comp_assoc,
    hinit]
  rw [← joinHorn_joinInr_zero q]
  unfold joinInr
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The boundary-piece map to the shifted horn in every left dimension. -/
noncomputable def joinBoundaryHornRightBoundaryFactorMap
    (p q : ℕ) (j : Fin (q + 2)) :
    (join.flip.obj (Δ[q + 1] : SSet.{u})).obj (boundary p : SSet.{u}) ⟶
      (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j) : SSet.{u}) :=
  match p with
  | 0 => joinBoundaryHornRightBoundaryFactorMapZero q j
  | p + 1 => joinBoundaryHornRightBoundaryFactorMapSucc.{u} p q j

@[simp]
lemma joinBoundaryHornRightBoundaryFactorMap_succ
    (p q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightBoundaryFactorMap.{u} (p + 1) q j =
      joinBoundaryHornRightBoundaryFactorMapSucc p q j :=
  rfl

@[simp]
lemma joinBoundaryHornRightBoundaryFactorMap_zero
    (q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightBoundaryFactorMap.{u} 0 q j =
      joinBoundaryHornRightBoundaryFactorMapZero q j :=
  rfl

@[reassoc]
lemma joinBoundaryHornRightBoundaryFactorMap_ι
    (p q : ℕ) (j : Fin (q + 2)) :
    joinBoundaryHornRightBoundaryFactorMap p q j ≫
        (horn (p + (q + 1) + 1) (rightJoinHornIndex p q j)).ι =
      (join.map (boundary p).ι).app (Δ[q + 1] : SSet.{u}) ≫
        (joinStdSimplexIso p (q + 1)).hom := by
  obtain _ | p := p
  · exact joinBoundaryHornRightBoundaryFactorMapZero_ι q j
  · exact joinBoundaryHornRightBoundaryFactorMapSucc_ι p q j



end JoinHorn.Internal
end SSet
