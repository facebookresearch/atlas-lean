/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant

/-!
# Tests for scoped cofibrancy of every simplicial set

The all-universe selected SSet model owns one opt-in object instance.  These
clients pin no-scope behavior, named model and parent coherence, symbolic and
concrete universes, and disappearance of the instance after closing scope.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.SSetAllCofibrantTests

#check HomotopicalAlgebra.IsCofibrant
#check SSet.modelCategoryQuillen.instIsCofibrant

section NoScope

example (_X : SSet.{u}) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

example (_X : SSet.{1}) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

example (_X : SSet.{0}) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

end NoScope

section NamedModelWithoutScope

noncomputable local instance : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory

example (_X : SSet.{u}) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

end NamedModelWithoutScope

section OwnScope

open scoped SSet.modelCategoryQuillen

#synth ModelCategory SSet.{u}
#synth CategoryWithCofibrations SSet.{u}

example (X : SSet.{u}) : IsCofibrant X := inferInstance

example : IsCofibrant (Δ[0] : SSet.{u}) := inferInstance

example (X : SSet.{1}) : IsCofibrant X := inferInstance

example (X : SSet.{0}) : IsCofibrant X := inferInstance

example (X : SSet.{u}) :
    (inferInstance : IsCofibrant X) =
      SSet.modelCategoryQuillen.instIsCofibrant X := rfl

example : (inferInstance : ModelCategory SSet.{u}) =
    SSet.modelCategoryQuillen.modelCategory := rfl

example : (inferInstance : CategoryWithCofibrations SSet.{u}) =
    SSet.modelCategoryQuillen.modelCategory.categoryWithCofibrations := rfl

end OwnScope

section NoLeakAfterScope

example (_X : SSet.{u}) : True := by
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

end NoLeakAfterScope

#print axioms SSet.modelCategoryQuillen.instIsCofibrant

end MathlibExtTest.AlgebraicTopology.ModelCategory.SSetAllCofibrantTests

end
