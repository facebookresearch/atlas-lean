/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy equivalences from a split composite

A homotopy section of the first continuous map and a homotopy equivalence
of the composite supply an explicit inverse for the first map. The maps
and both full inverse homotopies retain the original spaces, with
independent universe levels.
-/

universe u v w

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A composite HE and actual homotopy section give an HE of the first map.
All inverse maps and full homotopies are derived, not supplied as the desired result. -/
def splitCompositeHomotopyEquiv (f : C(X, Y)) (g : C(Y, Z)) (i : C(Y, X))
    (e : HomotopyEquiv X Z) (hComposite : e.toFun = g.comp f)
    (hSection : Homotopy (f.comp i) (ContinuousMap.id Y)) : HomotopyEquiv X Y := by
  let r : C(Y, X) := e.invFun.comp g
  have hleft : Homotopy (r.comp f) (ContinuousMap.id X) := by
    have hMap : e.invFun.comp e.toFun = r.comp f := by
      rewrite [hComposite]
      rfl
    exact e.left_inv.some.cast hMap rfl
  have h0 : Homotopy (f.comp r) ((f.comp r).comp (f.comp i)) :=
    ((Homotopy.refl (f.comp r)).comp hSection.symm).cast (by rfl) rfl
  have h1 : Homotopy ((f.comp r).comp (f.comp i)) (f.comp i) :=
    (((Homotopy.refl f).comp hleft).compContinuousMap i).cast (by rfl) (by rfl)
  exact
    { toFun := f
      invFun := r
      left_inv := by exact ⟨hleft⟩
      right_inv := by exact ⟨h0.trans (h1.trans hSection)⟩ }

/-- The derived equivalence uses the original first map forward. -/
theorem splitCompositeHomotopyEquiv_toFun (f : C(X, Y)) (g : C(Y, Z)) (i : C(Y, X))
    (e : HomotopyEquiv X Z) (hComposite : e.toFun = g.comp f)
    (hSection : Homotopy (f.comp i) (ContinuousMap.id Y)) :
    (splitCompositeHomotopyEquiv f g i e hComposite hSection).toFun = f := rfl

end ContinuousMap
