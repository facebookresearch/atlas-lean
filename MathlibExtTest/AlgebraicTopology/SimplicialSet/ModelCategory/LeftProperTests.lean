/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LeftProper
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AllCofibrant
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakCobaseChange
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure

/-!
# Selected SSet left-properness tests

These tests pin the all-universe scope boundary, direct raw-W1 priority,
generic properness clients, representative pushouts, and coexistence with the
selected TopCat model.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.LeftProperTests

section RawW1ExistsWithoutSelectedScope

#synth SSet.realizationWeakEquivalences.{u}.IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u})
#synth SSet.realizationWeakEquivalences.{1}.IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{1})
#synth SSet.realizationWeakEquivalences.{0}.IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{0})

end RawW1ExistsWithoutSelectedScope

section ManualModelsDoNotCreateWrapper

noncomputable local instance modelUAfter : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory
noncomputable local instance modelOneAfter : ModelCategory SSet.{1} :=
  SSet.modelCategoryQuillen.modelCategory
noncomputable local instance modelZeroAfter : ModelCategory SSet.{0} :=
  SSet.modelCategoryQuillen.modelCategory

example : True := by
  fail_if_success let _ : IsLeftProper SSet.{u} := inferInstance
  fail_if_success let _ : IsLeftProper SSet.{1} := inferInstance
  fail_if_success let _ : IsLeftProper SSet.{0} := inferInstance
  trivial

end ManualModelsDoNotCreateWrapper

section TopCatScopeDoesNotCreateSSetWrapper

open scoped TopCat.modelCategory

#synth ModelCategory TopCat.{u}
#synth ModelCategory TopCat.{1}
#synth ModelCategory TopCat.{0}

noncomputable local instance : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory

example : True := by
  fail_if_success let _ : IsLeftProper SSet.{u} := inferInstance
  trivial

end TopCatScopeDoesNotCreateSSetWrapper

section SelectedScope

open scoped SSet.modelCategoryQuillen

set_option maxRecDepth 128 in
#synth IsLeftProper SSet.{u}
set_option maxRecDepth 128 in
#synth IsLeftProper SSet.{1}
set_option maxRecDepth 128 in
#synth IsLeftProper SSet.{0}

-- Direct W1 remains the preferred raw-property provider; the wrapper field
-- projection has the reviewed lower priority 100.
#synth SSet.realizationWeakEquivalences.{u}.IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u})
#synth SSet.realizationWeakEquivalences.{1}.IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{1})
#synth SSet.realizationWeakEquivalences.{0}.IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{0})

example : (inferInstance : IsLeftProper SSet.{u}) =
    SSet.modelCategoryQuillen.instIsLeftProper := rfl
example : (inferInstance : IsLeftProper SSet.{1}) =
    SSet.modelCategoryQuillen.instIsLeftProper := rfl
example : (inferInstance : IsLeftProper SSet.{0}) =
    SSet.modelCategoryQuillen.instIsLeftProper := rfl

-- The generic all-cofibrant criterion is a separate proof, not a second
-- registered selected instance.
example : IsLeftProper SSet.{u} :=
  isLeftProper_of_all_objects_cofibrant (fun _ => inferInstance)
example : IsLeftProper SSet.{1} :=
  isLeftProper_of_all_objects_cofibrant (fun _ => inferInstance)
example : IsLeftProper SSet.{0} :=
  isLeftProper_of_all_objects_cofibrant (fun _ => inferInstance)

example {A B X Y : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Mono i]
    (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences f' := by
  let _ : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  let _ : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  exact (weakEquivalence_iff f').mp
    (IsLeftProper.weakEquivalence_of_isPushout sq)

example {A B X : SSet.{1}} (i : A ⟶ B) (f : A ⟶ X)
    [Mono i] (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences (pushout.inl i f) := by
  let _ : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  let _ : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  have h : WeakEquivalence (pushout.inl i f) :=
    IsLeftProper.weakEquivalence_of_isPushout
      (IsPushout.of_hasPushout i f)
  exact (weakEquivalence_iff _).mp h

example {A B X : SSet.{0}} (i : A ⟶ B) (f : A ⟶ X)
    [Mono i] (hf : SSet.realizationWeakEquivalences f) :
    SSet.realizationWeakEquivalences (pushout.inl i f) := by
  let _ : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  let _ : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  have h : WeakEquivalence (pushout.inl i f) :=
    IsLeftProper.weakEquivalence_of_isPushout
      (IsPushout.of_hasPushout i f)
  exact (weakEquivalence_iff _).mp h

example : SSet.realizationWeakEquivalences
    (pushout.inl (initial.to (Δ[0] : SSet.{u})) (𝟙 (⊥_ SSet.{u}))) := by
  have h : WeakEquivalence
      (pushout.inl (initial.to (Δ[0] : SSet.{u})) (𝟙 (⊥_ SSet.{u}))) :=
    IsLeftProper.weakEquivalence_of_isPushout
      (IsPushout.of_hasPushout
        (initial.to (Δ[0] : SSet.{u})) (𝟙 (⊥_ SSet.{u})))
  exact (weakEquivalence_iff _).mp h

example : True := by
  fail_if_success let _ : IsRightProper SSet.{u} := inferInstance
  fail_if_success let _ : IsRightProper SSet.{1} := inferInstance
  fail_if_success let _ : IsRightProper SSet.{0} := inferInstance
  fail_if_success
    let _ : SSet.realizationWeakEquivalences.{u}.IsStableUnderCobaseChange :=
      inferInstance
  trivial

end SelectedScope

section SSetAndTopCatScopesCoexist

open scoped SSet.modelCategoryQuillen TopCat.modelCategory

#synth IsLeftProper SSet.{u}
#synth IsLeftProper SSet.{1}
#synth IsLeftProper SSet.{0}
#synth ModelCategory TopCat.{u}
#synth ModelCategory TopCat.{1}
#synth ModelCategory TopCat.{0}

example : True := by
  fail_if_success let _ : IsLeftProper TopCat.{u} := inferInstance
  fail_if_success let _ : IsLeftProper TopCat.{1} := inferInstance
  fail_if_success let _ : IsLeftProper TopCat.{0} := inferInstance
  trivial

end SSetAndTopCatScopesCoexist

section NoLeakAfterScope

noncomputable local instance modelU : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory
noncomputable local instance modelOne : ModelCategory SSet.{1} :=
  SSet.modelCategoryQuillen.modelCategory
noncomputable local instance modelZero : ModelCategory SSet.{0} :=
  SSet.modelCategoryQuillen.modelCategory

example : True := by
  fail_if_success let _ : IsLeftProper SSet.{u} := inferInstance
  fail_if_success let _ : IsLeftProper SSet.{1} := inferInstance
  fail_if_success let _ : IsLeftProper SSet.{0} := inferInstance
  trivial

end NoLeakAfterScope

#check SSet.modelCategoryQuillen.instIsLeftProper
#print axioms SSet.modelCategoryQuillen.instIsLeftProper

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.LeftProperTests
