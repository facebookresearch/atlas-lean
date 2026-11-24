/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Original whole-square cancellation through both genuine inverse families

An actual whole map square can be transported across two given genuine
homotopy equivalences, using their actual full inverse homotopies. This
primitive retains both original maps and the supplied whole family.
Exact Q/S consumers derive all equivalence data and square families internally.
-/

public section

noncomputable section

open scoped Topology

universe uA uB uX uY

namespace ContinuousMap.HomotopyEquiv

/-- An actual forward-square homotopy gives its actual inverse-square
homotopy, through BOTH original equivalences' full inverse families. -/
def originalInverseSquareHomotopy
    {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
    (eA : ContinuousMap.HomotopyEquiv A X) (eB : ContinuousMap.HomotopyEquiv B Y)
    (f : C(A, B)) (g : C(X, Y))
    (H : ContinuousMap.Homotopy (eB.toFun.comp f) (g.comp eA.toFun)) :
    ContinuousMap.Homotopy (f.comp eA.invFun) (eB.invFun.comp g) := by
  let A₁ := eB.left_inv.some.symm.compContinuousMap (f.comp eA.invFun)
  let A₂ := (ContinuousMap.Homotopy.refl eB.invFun).comp (H.compContinuousMap eA.invFun)
  let A₃ := (ContinuousMap.Homotopy.refl (eB.invFun.comp g)).comp eA.right_inv.some
  have h₁ : (ContinuousMap.id B).comp (f.comp eA.invFun) = f.comp eA.invFun := by
    apply ContinuousMap.ext
    intro a
    rfl
  have h₂ : (eB.invFun.comp eB.toFun).comp (f.comp eA.invFun) =
      eB.invFun.comp ((eB.toFun.comp f).comp eA.invFun) := by
    apply ContinuousMap.ext
    intro a
    rfl
  have h₃ : eB.invFun.comp ((g.comp eA.toFun).comp eA.invFun) =
      (eB.invFun.comp g).comp (eA.toFun.comp eA.invFun) := by
    apply ContinuousMap.ext
    intro a
    rfl
  have h₄ : (eB.invFun.comp g).comp (ContinuousMap.id X) = eB.invFun.comp g := by
    apply ContinuousMap.ext
    intro a
    rfl
  exact (A₁.cast h₁ h₂).trans (A₂.trans (A₃.cast h₃.symm h₄))

end ContinuousMap.HomotopyEquiv

end
