/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHorn
import all MathlibExt.AlgebraicTopology.SimplicialSet.JoinHorn
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
import all MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLifting
import all MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLifting

/-!
# Boundary joins with the source endpoint

The source-endpoint inclusion on the left joined with the original
boundary on the right is the left outer horn. This specializes the
existing join-horn isomorphism, retaining its whole join map.
-/

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false



noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet

private lemma horn_one_zero_eq_face_zero :
    horn (n := 1) (0 : Fin 2) = stdSimplex.face (n := 1) {0} := by
  have h : horn (n := 1) (0 : Fin 2) =
      stdSimplex.face (n := 1) ({1}ᶜ : Finset (Fin 2)) := by
    ext m x
    simp [horn_eq_iSup]
  have hc : ({1}ᶜ : Finset (Fin 2)) = {0} := by decide
  rw [hc] at h
  exact h

/-- The original source endpoint is the first one-dimensional horn. -/
def sourceEndpointHornIso : (Δ[0] : SSet.{u}) ≅ (horn 1 (0 : Fin 2) : SSet.{u}) :=
  stdSimplex.faceSingletonIso (0 : Fin 2) ≪≫
    Subcomplex.eqToIso horn_one_zero_eq_face_zero.symm

/-- This isomorphism retains the literal source-endpoint inclusion. -/
@[reassoc] theorem sourceEndpointHornIso_hom_ι :
    sourceEndpointHornIso.{u}.hom ≫ (horn 1 (0 : Fin 2)).ι =
      stdSimplex.δ (1 : Fin 2) := by
  simp [sourceEndpointHornIso, stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]

/-- The same source-endpoint map, as an isomorphism of actual arrows. -/
def sourceEndpointHornArrowIso :
    Arrow.mk (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≅
      Arrow.mk (horn 1 (0 : Fin 2)).ι :=
  Arrow.isoMk sourceEndpointHornIso (Iso.refl _) sourceEndpointHornIso_hom_ι

/-- The original source-endpoint boundary corner in the native join-horn indexing. -/
def joinBoundarySourceEndpointArrowIsoRaw (n : ℕ) :
    Arrow.mk (joinUnderPushoutObjObj (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι).ι ≅
      Arrow.mk (horn ((0 + 1) + n + 1) (leftJoinHornIndex 0 n (0 : Fin 2))).ι :=
  Functor.PushoutObjObj.ι_iso_of_iso_left
      (F := join.{u})
      (f₁ := Arrow.mk (stdSimplex.δ (1 : Fin 2)))
      (f₁' := Arrow.mk (horn 1 (0 : Fin 2)).ι)
      (f₂ := Arrow.mk (boundary.{u} n).ι)
      (joinUnderPushoutObjObj (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι)
      (joinHornBoundaryLeftPushoutObjObj 0 n (0 : Fin 2)) sourceEndpointHornArrowIso ≪≫
    joinHornBoundaryLeftArrowIso 0 n (0 : Fin 2)

/-- The whole comparison retains the existing standard-simplex join isomorphism. -/
@[simp] theorem joinBoundarySourceEndpointArrowIsoRaw_hom_right (n : ℕ) :
    (joinBoundarySourceEndpointArrowIsoRaw.{u} n).hom.right =
      (joinStdSimplexIso 1 n).hom := by
  unfold joinBoundarySourceEndpointArrowIsoRaw
  rw [Iso.trans_hom, Arrow.comp_right]
  change (join.map sourceEndpointHornArrowIso.hom.right).app (Δ[n] : SSet.{u}) ≫
    (joinStdSimplexIso 1 n).hom = _
  simp [sourceEndpointHornArrowIso]

/-- The same native corner is the left outer horn of its actual dimension. -/
def joinBoundarySourceEndpointArrowIso (n : ℕ) :
    Arrow.mk (joinUnderPushoutObjObj (stdSimplex.δ (1 : Fin 2)) (boundary.{u} n).ι).ι ≅
      Arrow.mk (horn (n + 2) (0 : Fin (n + 3))).ι := by
  have hd : (0 + 1) + n + 1 = n + 2 := by omega
  exact joinBoundarySourceEndpointArrowIsoRaw.{u} n ≪≫
    eqToIso (congrArg (fun i : Fin (((0 + 1) + n + 1) + 1) =>
      Arrow.mk (horn.{u} ((0 + 1) + n + 1) i).ι)
        (show leftJoinHornIndex 0 n (0 : Fin 2) = 0 from Fin.ext rfl)) ≪≫
    eqToIso (congrArg (fun k : ℕ => Arrow.mk (horn.{u} k (0 : Fin (k + 1))).ι) hd)

end SSet
