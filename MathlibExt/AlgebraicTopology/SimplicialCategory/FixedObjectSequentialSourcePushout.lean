/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeBoundaryCellSourcePushoutWeak
import MathlibExt.AlgebraicTopology.RelativeCellComplex.CobaseChange
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The SAME original sequential boundary cells under actual source pushout

Every supplied original under-root stage is pushed out by the native
Under.pushout functor. Its literal original unit maps form the entire
source comparison, retaining both full pushout projections. Actual
boundary-cell occurrences are retained under cobase change. Honest
weakness of the original source map then proves weakness of every SAME
stage comparison, starting with the original bottom isomorphism.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.SequentialSourcePushout
variable {O : Type u} {C D : FixedObjects O} (U : ℕ ⥤ Under C) (F : C ⟶ D)

/-- The SAME full original stage diagram with its original root maps forgotten. -/
def source : ℕ ⥤ FixedObjects O := U ⋙ Under.forget C

/-- The actual full native source-pushed stage diagram, retaining both original projections. -/
def changed : ℕ ⥤ FixedObjects O := U ⋙ Under.pushout F ⋙ Under.forget D

/-- The SAME whole original pushout inclusion on each actual original stage. -/
def comparison : source U ⟶ changed U F where
  app n := pushout.inl (U.obj n).hom F
  naturality n m f := by
    change (U.map f).right ≫ pushout.inl (U.obj m).hom F =
      pushout.inl (U.obj n).hom F ≫
        pushout.desc ((U.map f).right ≫ pushout.inl (U.obj m).hom F)
          (pushout.inr (U.obj m).hom F) _
    exact (pushout.inl_desc _ _ _).symm

/-- Both original projections in each full stage are the actual native source pushout square. -/
theorem stage_isPushout (n : ℕ) :
    IsPushout (U.obj n).hom F ((comparison U F).app n) ((Under.pushout F).obj (U.obj n)).hom :=
  IsPushout.of_hasPushout _ _

/-- The SAME full successor-stage comparison square is an actual pushout. -/
theorem step_isPushout (n : ℕ) :
    IsPushout ((source U).map (homOfLE (n.le_add_right 1))) ((comparison U F).app n)
      ((comparison U F).app (n+1)) ((changed U F).map (homOfLE (n.le_add_right 1))) := by
  let f : n ⟶ n+1 := homOfLE (n.le_add_right 1)
  have hs : IsPushout ((U.obj n).hom ≫ (U.map f).right) F
      ((comparison U F).app (n+1))
      (((Under.pushout F).obj (U.obj n)).hom ≫ (changed U F).map f) := by
    change IsPushout ((U.obj n).hom ≫ (U.map f).right) F
      (pushout.inl (U.obj (n+1)).hom F)
      (pushout.inr (U.obj n).hom F ≫ ((Under.pushout F).map (U.map f)).right)
    have hroot : (U.obj n).hom ≫ (U.map f).right = (U.obj (n+1)).hom := (U.map f).w
    have hright : pushout.inr (U.obj n).hom F ≫ ((Under.pushout F).map (U.map f)).right =
        pushout.inr (U.obj (n+1)).hom F := ((Under.pushout F).map (U.map f)).w
    exact (congrArg₂ (fun (g : C ⟶ (U.obj (n+1)).right)
        (k : D ⟶ pushout (U.obj (n+1)).hom F) =>
      IsPushout g F (pushout.inl (U.obj (n+1)).hom F) k) hroot hright).mpr
        (IsPushout.of_hasPushout (U.obj (n+1)).hom F)
  exact hs.of_left ((comparison U F).naturality f) (stage_isPushout U F n)

/-- Actual source change retains the SAME whole original boundary-cell occurrence family at every step. -/
def changedCells (a : ∀ (n : ℕ), AttachCells.{u} (boundaryFamily O).homFamily
    ((source U).map (homOfLE (n.le_add_right 1)))) (n : ℕ) :
    AttachCells.{u} (boundaryFamily O).homFamily
      ((changed U F).map (homOfLE (n.le_add_right 1))) :=
  (a n).cobaseChange ((comparison U F).app n) ((comparison U F).app (n+1)) _
    (step_isPushout U F n)

/-- The SAME original bottom comparison is weak from the actual bottom isomorphism and genuine source weakness. -/
theorem comparison_zero_weak [IsIso (U.obj 0).hom]
    (hF : FixedObjectModel.weakEquivalences O F) :
    FixedObjectModel.weakEquivalences O ((comparison U F).app 0) := by
  let i : D ⟶ (changed U F).obj 0 := pushout.inr (U.obj 0).hom F
  let _ : IsIso i := (stage_isPushout U F 0).isIso_inr_of_isIso
  have h := (FixedObjectModel.weakEquivalences O).comp_mem _ _ hF
    ((FixedObjectModel.weakEquivalences O).of_isIso i)
  have he : (U.obj 0).hom ≫ (comparison U F).app 0 = F ≫ i := pushout.condition
  exact (FixedObjectModel.weakEquivalences O).of_precomp _ _
    ((FixedObjectModel.weakEquivalences O).of_isIso (U.obj 0).hom) (he.symm ▸ h)

/-- Every SAME whole original stage comparison is weak through genuine original boundary-cell gluing. -/
theorem comparison_weak [IsIso (U.obj 0).hom]
    (a : ∀ (n : ℕ), AttachCells.{u} (boundaryFamily O).homFamily
      ((source U).map (homOfLE (n.le_add_right 1))))
    (hF : FixedObjectModel.weakEquivalences O F) (n : ℕ) :
    FixedObjectModel.weakEquivalences O ((comparison U F).app n) := by
  induction n with
  | zero => exact comparison_zero_weak U F hF
  | succ n ih =>
    exact FreeBoundaryCells.sourcePushout_weak (a n) ((comparison U F).app n) ih
      ((comparison U F).app (n+1)) ((changed U F).map (homOfLE (n.le_add_right 1)))
      (step_isPushout U F n)

end CategoryTheory.SimplicialEnrichment.FixedObjects.SequentialSourcePushout
