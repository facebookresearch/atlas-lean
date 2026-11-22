/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConePointedCoproducts
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConePushoutGluing
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.JoinPointMonomorphisms
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# Actual comparison on every native finite skeleton

The native relative boundary-cell complex supplies every original
pushout square. Its boundary summands are already complete at the
previous finite skeleton. Induction uses the proved coproduct and
pushout gluing theorems, not a certificate for the stage comparison.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The actual comparison is transported along the supplied original source isomorphism by its whole naturality square. -/
theorem toJoin_of_iso {X Y : SSet.{u}} (e : X ≅ Y)
    (hX : categoricalEquivalences (toJoin X)) : categoricalEquivalences (toJoin Y) := by
  let _ : IsIso (map e.hom) := inferInstanceAs (IsIso (underlyingFunctor.map e.hom))
  let _ : IsIso ((join.map e.hom).app (Δ[0] : SSet.{u})) := inferInstance
  apply (categoricalEquivalences.precomp_iff (map e.hom) (toJoin Y)
    (categoricalEquivalences.of_isIso _)).mp
  rw [toJoin_naturality e.hom,
    categoricalEquivalences.postcomp_iff (toJoin X) ((join.map e.hom).app (Δ[0] : SSet.{u}))
      (categoricalEquivalences.of_isIso _)]
  exact hX

private def boundedSkeletonIso (X : SSet.{u}) (n : ℕ) [HasDimensionLT X n] :
    (X.skeleton n : SSet.{u}) ≅ X :=
  Subcomplex.eqToIso ((Subcomplex.eq_top_iff_of_hasDimensionLT (X.skeleton n) n).mpr
    (fun _ hi x _ => X.mem_skeleton x hi)) ≪≫ Subcomplex.topIso X

private def relativeStageIso (X : SSet.{u}) (n : ℕ) :
    (skeletonOfMono (Subcomplex.ι (⊥ : X.Subcomplex)) n : SSet.{u}) ≅ (X.skeleton n : SSet.{u}) :=
  Subcomplex.eqToIso (by simp [skeletonOfMono])

/-- Every original finite skeleton has its actual categorical fat/join comparison; the boundary and cell comparisons are derived in the induction. -/
theorem toJoin_skeleton (n : ℕ) (X : SSet.{u}) :
    categoricalEquivalences (toJoin (X.skeleton n : SSet.{u})) := by
  induction n generalizing X with
  | zero =>
      have hbot : categoricalEquivalences (toJoin (⊥ : X.Subcomplex)) := by
        let _ : IsIso (toJoin (⊥ : X.Subcomplex)) :=
          toJoin_isIso_of_isInitial _ (Subcomplex.isInitialBot (X := X))
        exact categoricalEquivalences.of_isIso _
      exact toJoin_of_iso (Subcomplex.eqToIso (X.skeleton_zero)).symm hbot
  | succ n ih =>
      have hboundary : categoricalEquivalences (toJoin (∂Δ[n] : SSet.{u})) :=
        toJoin_of_iso (boundedSkeletonIso (∂Δ[n] : SSet.{u}) n) (ih (∂Δ[n] : SSet.{u}))
      let i : ((⊥ : X.Subcomplex) : SSet.{u}) ⟶ X := Subcomplex.ι ⊥
      let B := relativeCellComplexOfMono.sigmaBoundary i n
      let D := relativeCellComplexOfMono.sigmaStdSimplex i n
      have hB : categoricalEquivalences (toJoin B) :=
        toJoin_of_coproduct (fun _ : relativeCellComplexOfMono.Cell i n => (∂Δ[n] : SSet.{u}))
          (fun _ => hboundary)
      have hD : categoricalEquivalences (toJoin D) :=
        toJoin_of_coproduct (fun _ : relativeCellComplexOfMono.Cell i n => (Δ[n] : SSet.{u}))
          (fun _ => toJoin_stdSimplex_categoricalEquivalence n)
      let l := relativeCellComplexOfMono.l i n
      let t := relativeCellComplexOfMono.t i n
      let b := relativeCellComplexOfMono.b i n
      let r := relativeCellComplexOfMono.r i n
      let sq := (relativeCellComplexOfMono.isPushout i n).flip
      have hprior : categoricalEquivalences (toJoin (skeletonOfMono i n : SSet.{u})) :=
        toJoin_of_iso (relativeStageIso X n).symm (ih X)
      let _ : Mono ((join.map l).app (Δ[0] : SSet.{u})) := mono_join_point l
      have hnext : categoricalEquivalences (toJoin (skeletonOfMono i (n + 1) : SSet.{u})) :=
        categoricalEquivalences_of_isPushouts (map_isPushout sq) (join_map_isPushout sq)
          (a := toJoin B) (b := toJoin D) (c := toJoin (skeletonOfMono i n : SSet.{u}))
          (d := toJoin (skeletonOfMono i (n + 1) : SSet.{u}))
          (toJoin_naturality l) (toJoin_naturality t) (toJoin_naturality b) (toJoin_naturality r)
          hB hD hprior
      exact toJoin_of_iso (relativeStageIso X (n + 1)) hnext

end SSet.WalkingAdjunction.FatCone
