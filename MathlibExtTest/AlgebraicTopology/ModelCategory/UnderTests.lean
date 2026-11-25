/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.Under
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
import Mathlib.Topology.Category.DeltaGenerated

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory

namespace HomotopicalAlgebra.UnderTests

section Generic

variable {C : Type u} [Category.{v} C] [ModelCategory C] (S : C)

#synth CategoryWithCofibrations (Under S)
#synth CategoryWithFibrations (Under S)
#synth CategoryWithWeakEquivalences (Under S)
#synth ModelCategory (Under S)

example : (inferInstance : ModelCategory (Under S)) = ModelCategory.under S := rfl

example {X Y : Under S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := cofibrations_under_iff S f

example {X Y : Under S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right := fibrations_under_iff S f

example {X Y : Under S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := weakEquivalences_under_iff S f

example : trivialCofibrations (Under S) = (trivialCofibrations C).under :=
  trivialCofibrations_under_eq S

example : trivialFibrations (Under S) = (trivialFibrations C).under :=
  trivialFibrations_under_eq S

#synth (trivialCofibrations (Under S)).HasFactorization (fibrations (Under S))
#synth (cofibrations (Under S)).HasFactorization (trivialFibrations (Under S))

example {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [WeakEquivalence i] [Fibration p] :
    HasLiftingProperty i p := by infer_instance

example {A B X Y : Under S} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p := by infer_instance

variable (S' : C)

example : ModelCategory (Under S') := inferInstance

end Generic

/-! No base model means no Under model. -/

example : True := by
  fail_if_success
    let _ : ModelCategory (Under (PUnit : Type)) := inferInstance
  trivial

/-! Opening the selected SSet scope installs both base and Under models. -/

section SelectedSSet

open scoped SSet.modelCategoryQuillen

variable (S : SSet.{u})

#synth ModelCategory SSet.{u}
#synth ModelCategory (Under S)

example : (inferInstance : ModelCategory (Under S)) = ModelCategory.under S := rfl

example {X Y : Under S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := weakEquivalences_under_iff S f

end SelectedSSet

/-! The scoped package tears down completely. -/

example : True := by
  fail_if_success
    let _ : ModelCategory SSet.{u} := inferInstance
  fail_if_success
    let _ (S : SSet.{u}) : ModelCategory (Under S) := inferInstance
  trivial

/-! A future selected Delta model is consumed only proof-locally. -/

example (S : DeltaGenerated.{u}) (h : ModelCategory DeltaGenerated.{u}) :
    ModelCategory (Under S) := by
  let _ := h
  infer_instance

example (_S : DeltaGenerated.{u}) : True := by
  fail_if_success
    let _ : ModelCategory (Under _S) := inferInstance
  trivial

/-! Explicit universe clients. -/

section UniverseOne

open scoped SSet.modelCategoryQuillen

example (S : SSet.{1}) : ModelCategory (Under S) := inferInstance

end UniverseOne

section UniverseZero

open scoped SSet.modelCategoryQuillen

example (S : SSet.{0}) : ModelCategory (Under S) := inferInstance

end UniverseZero

/-! All five implementation seams remain private. -/

example : True := by
  fail_if_success
    exact HomotopicalAlgebra.cofibrationsUnderRetracts
  fail_if_success
    exact HomotopicalAlgebra.fibrationsUnderRetracts
  fail_if_success
    exact HomotopicalAlgebra.weakEquivalencesUnderRetracts
  fail_if_success
    exact HomotopicalAlgebra.weakEquivalencesUnderTwoOfThree
  fail_if_success
    exact HomotopicalAlgebra.underFactorizations
  trivial

end HomotopicalAlgebra.UnderTests
