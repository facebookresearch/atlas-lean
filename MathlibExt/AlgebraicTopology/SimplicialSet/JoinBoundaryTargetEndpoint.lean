/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHorn
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceLifting
public import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan

/-!
# Boundary joins with the target endpoint

This file specializes the boundary--positive-horn join isomorphism to the
target endpoint `Δ[0] → Δ[1]`.  The resulting corner is the right outer horn,
and the canonical interval becomes its critical final edge.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

lemma horn_one_one_eq_face_one :
    horn (n := 1) (1 : Fin 2) = stdSimplex.face (n := 1) {1} := by
  have h0 : horn (n := 1) (1 : Fin 2) =
      stdSimplex.face (n := 1) ({0}ᶜ : Finset (Fin 2)) := by
    ext m x
    simp [horn_eq_iSup]
  have h1 : ({0}ᶜ : Finset (Fin 2)) = {1} := by decide
  rw [h0, h1]

/-- The target endpoint, regarded as the last one-dimensional horn. -/
noncomputable def targetEndpointHornIso :
    (Δ[0] : SSet.{u}) ≅ (horn 1 (1 : Fin 2) : SSet.{u}) :=
  stdSimplex.faceSingletonIso (1 : Fin 2) ≪≫
    Subcomplex.eqToIso horn_one_one_eq_face_one.symm

@[reassoc]
lemma targetEndpointHornIso_hom_ι :
    targetEndpointHornIso.{u}.hom ≫ (horn 1 (1 : Fin 2)).ι =
      stdSimplex.δ (0 : Fin 2) := by
  simp [targetEndpointHornIso,
    stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]

/-- Arrow isomorphism from the target endpoint inclusion to the last
one-dimensional horn inclusion. -/
noncomputable def targetEndpointHornArrowIso :
    Arrow.mk (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≅
      Arrow.mk (horn 1 (1 : Fin 2)).ι :=
  Arrow.isoMk targetEndpointHornIso (Iso.refl _)
    targetEndpointHornIso_hom_ι

@[simp]
lemma rightJoinHornIndex_zero_one_eq_last (n : ℕ) :
    rightJoinHornIndex n 0 (1 : Fin 2) = Fin.last (n + 2) := by
  apply Fin.ext
  simp [rightJoinHornIndex_val]

/-- The target-endpoint boundary pushout join, in the canonical shifted-horn
indexing retained by the general join-horn theorem. -/
noncomputable def joinBoundaryTargetEndpointArrowIsoRaw (n : ℕ) :
    Arrow.mk
        (joinUnderPushoutObjObj (boundary n).ι
          (stdSimplex.δ (0 : Fin 2))).ι ≅
      Arrow.mk (horn (n + (0 + 1) + 1)
        (rightJoinHornIndex n 0 (1 : Fin 2))).ι :=
  Functor.PushoutObjObj.ι_iso_of_iso_right
      (F := join.{u})
      (f₁ := Arrow.mk (boundary.{u} n).ι)
      (f₂ := Arrow.mk (stdSimplex.δ (0 : Fin 2)))
      (f₂' := Arrow.mk (horn 1 (1 : Fin 2)).ι)
      (joinUnderPushoutObjObj (boundary.{u} n).ι
        (stdSimplex.δ (0 : Fin 2)))
      (joinBoundaryHornRightPushoutObjObj n 0 (1 : Fin 2))
      targetEndpointHornArrowIso ≪≫
    joinBoundaryHornRightArrowIso n 0 (1 : Fin 2)

@[simp]
lemma joinBoundaryTargetEndpointArrowIsoRaw_hom_right (n : ℕ) :
    (joinBoundaryTargetEndpointArrowIsoRaw.{u} n).hom.right =
      (joinStdSimplexIso n 1).hom := by
  unfold joinBoundaryTargetEndpointArrowIsoRaw
  rw [Iso.trans_hom, Arrow.comp_right]
  change (join.obj (Δ[n] : SSet.{u})).map
      targetEndpointHornArrowIso.hom.right ≫
        (joinStdSimplexIso n 1).hom = _
  simp [targetEndpointHornArrowIso]

end SSet
