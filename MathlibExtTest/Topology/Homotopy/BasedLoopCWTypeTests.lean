/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.BasedLoopCWType

/-!
# Consumers of actual based loop equivalence data

Check strict functor use, literal constant-loop preservation, and both
specified inverse homotopies at the actual loop points.
-/

open CategoryTheory Topology
open scoped unitInterval

noncomputable section

universe u

variable {X Y : PointedTopCat.{u}}

example (f : X ⟶ Y) :
    PointedTopCat.loopSpaceFunctor.map f = PointedTopCat.loopSpaceMap f := rfl

example {f₀ f₁ : X ⟶ Y}
    (H : ContinuousMap.HomotopyRel f₀.right.hom f₁.right.hom {X.hom PUnit.unit})
    (s : unitInterval) :
    PointedTopCat.loopSpaceMapHomotopyRel H (s, Path.refl (X.hom PUnit.unit)) =
      Path.refl (Y.hom PUnit.unit) := by
  apply Path.ext
  funext t
  rw [PointedTopCat.loopSpaceMapHomotopyRel_apply]
  exact (H.eq_fst s (Set.mem_singleton_iff.mpr rfl)).trans
    (PointedTopCat.map_basepoint f₀)

variable (e : TopPair.HomotopyEquiv
  (PointedTopCat.pointedPair.obj X) (PointedTopCat.pointedPair.obj Y))

example : e.loopSpaceHom (Path.refl (X.hom PUnit.unit)) =
    Path.refl (Y.hom PUnit.unit) := by
  let E := e.loopSpace (X := X) (Y := Y)
  have h := TopPair.Hom.w_apply E.hom PUnit.unit
  have hp : (TopPair.Hom.snd E.hom) PUnit.unit = PUnit.unit :=
    Subsingleton.elim (α := PUnit.{u + 1}) _ _
  rw [hp] at h
  exact h.symm

example : e.loopSpaceInv (Path.refl (Y.hom PUnit.unit)) =
    Path.refl (X.hom PUnit.unit) := by
  let E := e.loopSpace (X := X) (Y := Y)
  have h := TopPair.Hom.w_apply E.inv PUnit.unit
  have hp : (TopPair.Hom.snd E.inv) PUnit.unit = PUnit.unit :=
    Subsingleton.elim (α := PUnit.{u + 1}) _ _
  rw [hp] at h
  exact h.symm

example (s : unitInterval) :
    (e.loopSpace (X := X) (Y := Y)).homotopyHomInvId.fst
        (s, Path.refl (X.hom PUnit.unit)) = Path.refl (X.hom PUnit.unit) := by
  let E := e.loopSpace (X := X) (Y := Y)
  have h := E.homotopyHomInvId.w_apply' PUnit.unit s
  have hp : E.homotopyHomInvId.snd (s, PUnit.unit) = PUnit.unit :=
    Subsingleton.elim (α := PUnit.{u + 1}) _ _
  rw [hp] at h
  exact h

example (s : unitInterval) :
    (e.loopSpace (X := X) (Y := Y)).homotopyInvHomId.fst
        (s, Path.refl (Y.hom PUnit.unit)) = Path.refl (Y.hom PUnit.unit) := by
  let E := e.loopSpace (X := X) (Y := Y)
  have h := E.homotopyInvHomId.w_apply' PUnit.unit s
  have hp : E.homotopyInvHomId.snd (s, PUnit.unit) = PUnit.unit :=
    Subsingleton.elim (α := PUnit.{u + 1}) _ _
  rw [hp] at h
  exact h

#print axioms PointedTopCat.loopSpaceMap
#print axioms PointedTopCat.loopSpaceMapHomotopyRel
#print axioms TopPair.HomotopyEquiv.loopSpace
