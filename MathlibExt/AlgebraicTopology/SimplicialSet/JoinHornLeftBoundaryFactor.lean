/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftFactorInclusion

/-!
# Positive right-boundary factor in the left join--horn decomposition
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

attribute [local instance] joinHorn_isConnectedWalkingMultispan

/-- The index of a face contributed by the right boundary block. -/
def leftJoinBackFaceIndex (p q : ℕ) (r : Fin (q + 2)) :
    Fin ((((p + 1) + (q + 1) + 1) + 1)) :=
  ⟨p + 2 + r.val, by have := r.isLt; omega⟩

lemma leftJoinBackFaceIndex_ne (p q : ℕ) (i : Fin (p + 2))
    (r : Fin (q + 2)) :
    leftJoinBackFaceIndex p q r ≠ leftJoinHornIndex p (q + 1) i := by
  intro h
  have hh := congrArg Fin.val h
  dsimp [leftJoinBackFaceIndex, leftJoinHornIndex] at hh
  have := i.isLt
  omega

/-- A right-boundary face mapped into the shifted horn. -/
noncomputable def joinHornBoundaryLeftBoundaryFaceMap
    (p q : ℕ) (i : Fin (p + 2)) (r : Fin (q + 2)) :
    (join.obj (Δ[p + 1] : SSet.{u})).obj
        (stdSimplex.face {r}ᶜ : SSet.{u}) ⟶
      (horn ((p + 1) + (q + 1) + 1)
        (leftJoinHornIndex p (q + 1) i) : SSet.{u}) :=
  (join.obj (Δ[p + 1] : SSet.{u})).map
      (stdSimplex.faceSingletonComplIso r).inv ≫
    (joinStdSimplexIso (p + 1) q).hom ≫
      joinHornΔcast (by omega : (p + 1) + q + 1 = (p + 1) + (q + 1)) ≫
        horn.ι (leftJoinHornIndex p (q + 1) i)
          (leftJoinBackFaceIndex p q r)
          (leftJoinBackFaceIndex_ne p q i r)

@[reassoc]
lemma joinHornBoundaryLeftBoundaryFaceMap_ι
    (p q : ℕ) (i : Fin (p + 2)) (r : Fin (q + 2)) :
    joinHornBoundaryLeftBoundaryFaceMap p q i r ≫
        (horn ((p + 1) + (q + 1) + 1)
          (leftJoinHornIndex p (q + 1) i)).ι =
      (join.obj (Δ[p + 1] : SSet.{u})).map
          (stdSimplex.face {r}ᶜ).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom := by
  unfold joinHornBoundaryLeftBoundaryFaceMap
  rw [Category.assoc, Category.assoc, Category.assoc, horn.ι_ι]
  have hface : (stdSimplex.faceSingletonComplIso r).inv ≫
      stdSimplex.δ r = (stdSimplex.face {r}ᶜ).ι := by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso r).hom,
      Iso.hom_inv_id_assoc, stdSimplex.faceSingletonComplIso_hom_ι]
  rw [← hface, Functor.map_comp, Category.assoc, cancel_epi]
  exact (joinHorn_dualBackPush r (leftJoinBackFaceIndex p q r) rfl
    (by omega : (p + 1) + q + 1 = (p + 1) + (q + 1))).symm

set_option backward.isDefEq.respectTransparency false in
lemma joinHornBoundaryLeftBoundaryFaceMap_compatible
    (p q : ℕ) (i : Fin (p + 2))
    (a : (MultispanShape.ofLinearOrder (Fin (q + 2))).L) :
    ((((boundary.multicoequalizerDiagram.{u} (q + 1)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor).map
          (join.obj (Δ[p + 1] : SSet.{u}))).fst a) ≫
        joinHornBoundaryLeftBoundaryFaceMap p q i
          ((MultispanShape.ofLinearOrder (Fin (q + 2))).fst a) =
      ((((boundary.multicoequalizerDiagram.{u} (q + 1)).multispanIndex.toLinearOrder.map
          Subcomplex.toSSetFunctor).map
          (join.obj (Δ[p + 1] : SSet.{u}))).snd a) ≫
        joinHornBoundaryLeftBoundaryFaceMap p q i
          ((MultispanShape.ofLinearOrder (Fin (q + 2))).snd a) := by
  rcases a with ⟨⟨r, s⟩, hrs : r < s⟩
  rw [MultispanIndex.map_fst, MultispanIndex.map_snd]
  rw [MultispanIndex.map_fst, MultispanIndex.map_snd]
  rw [MultispanIndex.toLinearOrder_fst, MultispanIndex.toLinearOrder_snd]
  rw [CompleteLattice.MulticoequalizerDiagram.multispanIndex_fst,
    CompleteLattice.MulticoequalizerDiagram.multispanIndex_snd]
  dsimp only [MultispanShape.ofLinearOrder_fst, MultispanShape.ofLinearOrder_snd]
  rw [← cancel_mono
    (horn ((p + 1) + (q + 1) + 1) (leftJoinHornIndex p (q + 1) i)).ι]
  simp only [Category.assoc]
  rw [joinHornBoundaryLeftBoundaryFaceMap_ι,
    joinHornBoundaryLeftBoundaryFaceMap_ι]
  simp only [← Functor.map_comp_assoc]
  rfl

/-- The right-boundary multicoequalizer after joining on the left. -/
noncomputable def joinHornLeftBoundaryMappedCocone
    (p q : ℕ) :=
  ((boundary.multicoequalizerDiagram.{u} (q + 1)).multicofork.toLinearOrder.map
    Subcomplex.toSSetFunctor).map (join.obj (Δ[p + 1] : SSet.{u}))

/-- Joining on the left preserves the right-boundary colimit. -/
noncomputable def joinHornLeftBoundaryMappedIsColimit
    (p q : ℕ) : IsColimit (joinHornLeftBoundaryMappedCocone.{u} p q) :=
  Multicofork.isColimitMapOfPreserves
    ((boundary.multicoequalizerDiagram (q + 1)).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor)
    (join.obj (Δ[p + 1] : SSet.{u})) (boundary.isColimit (q + 1))

/-- Colimit data defining the positive right-boundary factor map. -/
structure JoinHornBoundaryLeftBoundaryFactorData
    (p q : ℕ) (i : Fin (p + 2)) where
  /-- The induced map from the joined boundary. -/
  map : (join.obj (Δ[p + 1] : SSet.{u})).obj
      (boundary (q + 1) : SSet.{u}) ⟶
    (horn ((p + 1) + (q + 1) + 1)
      (leftJoinHornIndex p (q + 1) i) : SSet.{u})
  face (r : Fin (q + 2)) :
    (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι r) ≫ map =
      joinHornBoundaryLeftBoundaryFaceMap p q i r

set_option backward.isDefEq.respectTransparency false in
/-- The chosen positive right-boundary factor and its face equations. -/
noncomputable def joinHornBoundaryLeftBoundaryFactorData
    (p q : ℕ) (i : Fin (p + 2)) :
    JoinHornBoundaryLeftBoundaryFactorData.{u} p q i := by
  let m := Multicofork.IsColimit.desc (joinHornLeftBoundaryMappedIsColimit p q)
    (joinHornBoundaryLeftBoundaryFaceMap p q i)
    (joinHornBoundaryLeftBoundaryFaceMap_compatible p q i)
  refine { map := m, face := fun r => ?_ }
  have hfac := Multicofork.IsColimit.fac
    (joinHornLeftBoundaryMappedIsColimit p q)
    (joinHornBoundaryLeftBoundaryFaceMap p q i)
    (joinHornBoundaryLeftBoundaryFaceMap_compatible p q i) r
  change (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι r) ≫ m =
    joinHornBoundaryLeftBoundaryFaceMap p q i r at hfac
  exact hfac

/-- The boundary factor map for a nonzero right boundary dimension. -/
@[no_expose]
noncomputable def joinHornBoundaryLeftBoundaryFactorMapSucc
    (p q : ℕ) (i : Fin (p + 2)) :
    (join.obj (Δ[p + 1] : SSet.{u})).obj
        (boundary (q + 1) : SSet.{u}) ⟶
      (horn ((p + 1) + (q + 1) + 1)
        (leftJoinHornIndex p (q + 1) i) : SSet.{u}) :=
  (joinHornBoundaryLeftBoundaryFactorData p q i).map

lemma joinHornBoundaryLeftBoundaryFactorMapSucc_face_raw
    (p q : ℕ) (i : Fin (p + 2)) (r : Fin (q + 2)) :
    (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι r) ≫
        joinHornBoundaryLeftBoundaryFactorMapSucc p q i =
      joinHornBoundaryLeftBoundaryFaceMap p q i r :=
  (joinHornBoundaryLeftBoundaryFactorData p q i).face r

@[reassoc]
lemma joinHornBoundaryLeftBoundaryFactorMapSucc_face
    (p q : ℕ) (i : Fin (p + 2)) (r : Fin (q + 2)) :
    (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.ι r) ≫
        joinHornBoundaryLeftBoundaryFactorMapSucc p q i =
      (joinStdSimplexIso (p + 1) q).hom ≫
        joinHornΔcast (by omega : (p + 1) + q + 1 = (p + 1) + (q + 1)) ≫
          horn.ι (leftJoinHornIndex p (q + 1) i)
            (leftJoinBackFaceIndex p q r)
            (leftJoinBackFaceIndex_ne p q i r) := by
  rw [← cancel_epi ((join.obj (Δ[p + 1] : SSet.{u})).map
    (stdSimplex.faceSingletonComplIso r).inv)]
  rw [← Functor.map_comp_assoc, boundary.faceSingletonComplIso_inv_ι]
  exact joinHornBoundaryLeftBoundaryFactorMapSucc_face_raw p q i r

set_option backward.isDefEq.respectTransparency false in
lemma joinHornBoundaryLeftBoundary_hom_ext
    (p q : ℕ) {X : SSet.{u}}
    {f g : (join.obj (Δ[p + 1] : SSet.{u})).obj
      (boundary (q + 1) : SSet.{u}) ⟶ X}
    (h : ∀ r : Fin (q + 2),
      (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.ι r) ≫ f =
        (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.ι r) ≫ g) :
    f = g := by
  apply Multicofork.IsColimit.hom_ext (joinHornLeftBoundaryMappedIsColimit p q)
  intro r
  change (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι r) ≫ f =
    (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι r) ≫ g
  rw [← boundary.faceSingletonComplIso_inv_ι, Functor.map_comp,
    Category.assoc, Category.assoc, h r]

@[reassoc]
lemma joinHornBoundaryLeftBoundaryFactorMapSucc_ι
    (p q : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftBoundaryFactorMapSucc p q i ≫
        (horn ((p + 1) + (q + 1) + 1)
          (leftJoinHornIndex p (q + 1) i)).ι =
      (join.obj (Δ[p + 1] : SSet.{u})).map (boundary (q + 1)).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom := by
  apply Multicofork.IsColimit.hom_ext (joinHornLeftBoundaryMappedIsColimit p q)
  intro r
  let rr : Fin (q + 2) := ⟨r.val, by simpa using r.isLt⟩
  change (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι rr) ≫
      (joinHornBoundaryLeftBoundaryFactorMapSucc p q i ≫
        (horn ((p + 1) + (q + 1) + 1)
          (leftJoinHornIndex p (q + 1) i)).ι) =
    (join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι rr) ≫
      ((join.obj (Δ[p + 1] : SSet.{u})).map (boundary (q + 1)).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom)
  calc
    _ = ((join.obj (Δ[p + 1] : SSet.{u})).map (boundary.faceι rr) ≫
          joinHornBoundaryLeftBoundaryFactorMapSucc p q i) ≫
        (horn ((p + 1) + (q + 1) + 1)
          (leftJoinHornIndex p (q + 1) i)).ι := by rw [Category.assoc]
    _ = joinHornBoundaryLeftBoundaryFaceMap p q i rr ≫
        (horn ((p + 1) + (q + 1) + 1)
          (leftJoinHornIndex p (q + 1) i)).ι := by
          rw [joinHornBoundaryLeftBoundaryFactorMapSucc_face_raw]
    _ = (join.obj (Δ[p + 1] : SSet.{u})).map
          (stdSimplex.face {rr}ᶜ).ι ≫
        (joinStdSimplexIso (p + 1) (q + 1)).hom :=
          joinHornBoundaryLeftBoundaryFaceMap_ι p q i rr
    _ = _ := by
      rw [← boundary.faceι_ι rr, Functor.map_comp, Category.assoc]


end JoinHorn.Internal
end SSet
