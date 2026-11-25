/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Locally finitely presented sheaves of modules on a space

A sheaf of modules is locally finitely presented if every point has an open
neighbourhood on which it is the cokernel of a map between finite free
sheaves. Used by the good filtrations of left and right differential modules.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LocalFinitePresentation

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable (M : Type) [TopologicalSpace M]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify
    ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective
    AddCommGrpCat.{0}]

/-- Local presentations use actual free sheaves and their universal cokernel. -/
def LocallyFinitelyPresented (R : Sheaf (Opens.grothendieckTopology M) RingCat.{0})
    (N : SheafOfModules.{0} R) : Prop :=
  ∀ x : M, ∃ U : Opens M, x ∈ U ∧
    ∃ (p q : ℕ)
      (f : SheafOfModules.free (R := R.over U) (Fin p) ⟶
        SheafOfModules.free (R := R.over U) (Fin q))
      (pi : SheafOfModules.free (R := R.over U) (Fin q) ⟶ N.over U)
      (h : f ≫ pi = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ pi h))

end MathlibExt.AlgebraicGeometry.LocalFinitePresentation
