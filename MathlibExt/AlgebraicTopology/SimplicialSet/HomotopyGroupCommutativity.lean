/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWUnit
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.Comparison.TopCatSingularHomotopyGroup

/-!
# Commutativity of native second homotopy

The actual realization–singular unit is injective on native second homotopy.
The singular second homotopy group is multiplicatively equivalent to the
cube-based second homotopy group, whose commutativity is already in Mathlib.
-/

@[expose] public section

noncomputable section

open CategoryTheory Simplicial
open scoped Simplicial

universe u

namespace SSet.KanComplex.π

/-- The established native second homotopy multiplication is commutative
for every Kan simplicial set, in every carrier universe. -/
theorem mul_comm_two
    {X : SSet.{u}} [KanComplex X] (x : X _⦋0⦌)
    (a b : π 2 X x) : a * b = b * a := by
  let Y : TopCat.{u} := SSet.toTop.obj X
  let η : X ⟶ TopCat.toSSet.obj Y := sSetTopAdj.unit.app X
  let _ : KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex Y
  let y : Y := TopCat.toSSetObj₀Equiv (η.app _ x)
  have hpoint : TopCat.toSSetObj₀Equiv.symm y = η.app _ x :=
    TopCat.toSSetObj₀Equiv.symm_apply_apply (η.app _ x)
  have hsing :
      ∀ c d : π 2 (TopCat.toSSet.obj Y)
        (TopCat.toSSetObj₀Equiv.symm y), c * d = d * c := by
    intro c d
    let e := TopCat.homotopyGroupSingularMulEquiv 1 Y y
    apply e.symm.injective
    rw [e.symm.map_mul, e.symm.map_mul, mul_comm]
  have hsing_image :
      ∀ c d : π 2 (TopCat.toSSet.obj Y) (η.app _ x),
        c * d = d * c := by
    exact hpoint ▸ hsing
  apply (SSet.KanComplex.bijective_piMap_sSetTopAdj_unit_app_succ
    1 X x).1
  rw [SSet.KanComplex.π.map_mul η rfl 1,
    SSet.KanComplex.π.map_mul η rfl 1]
  exact hsing_image _ _

end SSet.KanComplex.π
