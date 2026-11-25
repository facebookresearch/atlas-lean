/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence

/-!
# Tests for the realization--singular Quillen equivalence

Public-only clients for the scoped Quillen adjunction and equivalence,
including scope, parent, triangle, preservation, and universe boundaries.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty Limits
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationQuillenEquivalenceTests

section PublicSurface

#check SSet.modelCategoryQuillen.realizationIsQuillenAdjunction
#check SSet.modelCategoryQuillen.realizationIsQuillenEquivalence
#check SSet.modelCategoryQuillen.modelCategory
#check TopCat.modelCategory

end PublicSurface

section NoScope

#synth CategoryWithWeakEquivalences TopCat.{0}

example : weakEquivalences TopCat.{0} =
    TopCat.weakHomotopyEquivalences := rfl

example : True := by
  fail_if_success
    let _ : CategoryWithCofibrations SSet.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithFibrations SSet.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithWeakEquivalences SSet.{u} := inferInstance
  fail_if_success
    let _ : ModelCategory SSet.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithCofibrations TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithFibrations TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithWeakEquivalences TopCat.{u} := inferInstance
  fail_if_success
    let _ : ModelCategory TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} :=
      inferInstance
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{u} :=
      inferInstance
  trivial

end NoScope

section NoGlobalQuillen

noncomputable local instance : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory

noncomputable local instance : ModelCategory TopCat.{u} :=
  TopCat.modelCategory

example : True := by
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} :=
      inferInstance
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{u} :=
      inferInstance
  trivial

end NoGlobalQuillen

section SSetOnly

open scoped SSet.modelCategoryQuillen

#synth CategoryWithCofibrations SSet.{u}
#synth CategoryWithFibrations SSet.{u}
#synth CategoryWithWeakEquivalences SSet.{u}
#synth ModelCategory SSet.{u}

example : True := by
  fail_if_success
    let _ : CategoryWithCofibrations TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithFibrations TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithWeakEquivalences TopCat.{u} := inferInstance
  fail_if_success
    let _ : ModelCategory TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} :=
      inferInstance
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{u} :=
      inferInstance
  trivial

end SSetOnly

section TopCatOnly

open scoped TopCat.modelCategory

#synth CategoryWithCofibrations TopCat.{u}
#synth CategoryWithFibrations TopCat.{u}
#synth CategoryWithWeakEquivalences TopCat.{u}
#synth ModelCategory TopCat.{u}

example : True := by
  fail_if_success
    let _ : CategoryWithCofibrations SSet.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithFibrations SSet.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithWeakEquivalences SSet.{u} := inferInstance
  fail_if_success
    let _ : ModelCategory SSet.{u} := inferInstance
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} :=
      inferInstance
  fail_if_success
    let _ : CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{u} :=
      inferInstance
  trivial

end TopCatOnly

section BothScopes

open scoped SSet.modelCategoryQuillen TopCat.modelCategory

#synth CategoryWithCofibrations SSet.{u}
#synth CategoryWithFibrations SSet.{u}
#synth CategoryWithWeakEquivalences SSet.{u}
#synth ModelCategory SSet.{u}
#synth CategoryWithCofibrations TopCat.{u}
#synth CategoryWithFibrations TopCat.{u}
#synth CategoryWithWeakEquivalences TopCat.{u}
#synth ModelCategory TopCat.{u}
#synth CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u}
#synth CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{u}

example : (inferInstance : ModelCategory SSet.{u}) =
    SSet.modelCategoryQuillen.modelCategory := rfl

example : (inferInstance : ModelCategory TopCat.{u}) =
    TopCat.modelCategory := rfl

example : (inferInstance :
      CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u}) =
    SSet.modelCategoryQuillen.realizationIsQuillenAdjunction := rfl

example : (inferInstance :
      CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{u}) =
    SSet.modelCategoryQuillen.realizationIsQuillenEquivalence := rfl

example : CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} :=
  (inferInstance : CategoryTheory.Adjunction.IsQuillenEquivalence
    sSetTopAdj.{u}).toIsQuillenAdjunction

example : cofibrations SSet.{u} = monomorphisms SSet.{u} := rfl
example : fibrations SSet.{u} =
    SSet.modelCategoryQuillen.J.{u}.rlp := rfl
example : weakEquivalences SSet.{u} =
    SSet.realizationWeakEquivalences.{u} := rfl

example : cofibrations TopCat.{u} =
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp := rfl
example : fibrations TopCat.{u} =
    TopCat.realizedHornInclusions.{u}.rlp := rfl
example : weakEquivalences TopCat.{u} =
    TopCat.weakHomotopyEquivalences := rfl

example : SSet.modelCategoryQuillen.modelCategory.categoryWithCofibrations =
    SSet.modelCategoryQuillen.instCategoryWithCofibrations := rfl
example : SSet.modelCategoryQuillen.modelCategory.categoryWithFibrations =
    SSet.modelCategoryQuillen.instCategoryWithFibrations := rfl
example :
    SSet.modelCategoryQuillen.modelCategory.categoryWithWeakEquivalences =
      SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences := rfl

example : (inferInstance : CategoryWithCofibrations SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithCofibrations := rfl
example : (inferInstance : CategoryWithFibrations SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithFibrations := rfl
example : (inferInstance : CategoryWithWeakEquivalences SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences := rfl

example : (inferInstance : CategoryWithCofibrations TopCat.{u}) =
    TopCat.modelCategory.categoryWithCofibrations := rfl
example : (inferInstance : CategoryWithFibrations TopCat.{u}) =
    TopCat.modelCategory.categoryWithFibrations := rfl
example : (inferInstance : CategoryWithWeakEquivalences TopCat.{u}) =
    TopCat.modelCategory.categoryWithWeakEquivalences := rfl

section Preservation

example : PreservesFibrations
    (C := TopCat.{u}) (D := SSet.{u}) TopCat.toSSet :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := sSetTopAdj.{u})

example : PreservesTrivialFibrations
    (C := TopCat.{u}) (D := SSet.{u}) TopCat.toSSet :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
    (adj := sSetTopAdj.{u})

example {X Y : TopCat.{u}} (p : X ⟶ Y)
    (hp : fibrations TopCat.{u} p) :
    fibrations SSet.{u} (TopCat.toSSet.map p) :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := sSetTopAdj.{u}) p hp

example {X Y : TopCat.{u}} (p : X ⟶ Y)
    (hp : trivialFibrations TopCat.{u} p) :
    trivialFibrations SSet.{u} (TopCat.toSSet.map p) :=
  CategoryTheory.Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
    (adj := sSetTopAdj.{u}) p hp

end Preservation

section HoveyCriterion

example {X : SSet.{u}} {Y : TopCat.{u}}
    [IsCofibrant X] [IsFibrant Y]
    (f : SSet.toTop.obj X ⟶ Y) :
    weakEquivalences TopCat.{u} f ↔
      weakEquivalences SSet.{u} (sSetTopAdj.{u}.homEquiv X Y f) :=
  CategoryTheory.Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
    (adj := sSetTopAdj.{u}) f

example {X : SSet.{u}} {Y : TopCat.{u}}
    [IsCofibrant X] [IsFibrant Y]
    (f : SSet.toTop.obj X ⟶ Y) :
    WeakEquivalence f ↔
      WeakEquivalence (sSetTopAdj.{u}.homEquiv X Y f) :=
  CategoryTheory.Adjunction.IsQuillenEquivalence.weakEquivalence_homEquiv_iff
    (adj := sSetTopAdj.{u}) f

end HoveyCriterion

section Triangles

example (X : SSet.{u}) :
    SSet.toTop.map (sSetTopAdj.{u}.unit.app X) ≫
        sSetTopAdj.{u}.counit.app (SSet.toTop.obj X) =
      𝟙 (SSet.toTop.obj X) :=
  sSetTopAdj.{u}.left_triangle_components X

example (Y : TopCat.{u}) :
    sSetTopAdj.{u}.unit.app (TopCat.toSSet.obj Y) ≫
        TopCat.toSSet.map (sSetTopAdj.{u}.counit.app Y) =
      𝟙 (TopCat.toSSet.obj Y) :=
  sSetTopAdj.{u}.right_triangle_components Y

end Triangles

section RepresentativeObjects

private theorem deltaZeroCofibrant :
    IsCofibrant (Δ[0] : SSet.{u}) := by
  rw [isCofibrant_iff, SSet.modelCategoryQuillen.cofibration_iff]
  exact monomorphisms.infer_property _

private theorem punitFibrant :
    IsFibrant (TopCat.of PUnit.{u + 1}) := by
  rw [isFibrant_iff_of_isTerminal (𝟙 _) TopCat.isTerminalPUnit]
  infer_instance

example : IsCofibrant (SSet.toTop.obj (Δ[0] : SSet.{u})) :=
  (CategoryTheory.Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := sSetTopAdj.{u})).isCofibrant deltaZeroCofibrant

example : IsFibrant
    (TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})) :=
  (CategoryTheory.Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := sSetTopAdj.{u})).isFibrant punitFibrant

example :
    weakEquivalences TopCat.{u}
        (TopCat.isTerminalPUnit.from
          (SSet.toTop.obj (Δ[0] : SSet.{u}))) ↔
      weakEquivalences SSet.{u}
        (sSetTopAdj.{u}.homEquiv
          (Δ[0] : SSet.{u}) (TopCat.of PUnit.{u + 1})
          (TopCat.isTerminalPUnit.from
            (SSet.toTop.obj (Δ[0] : SSet.{u})))) := by
  let _ : IsCofibrant (Δ[0] : SSet.{u}) := deltaZeroCofibrant
  let _ : IsFibrant (TopCat.of PUnit.{u + 1}) := punitFibrant
  exact
    CategoryTheory.Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
      (adj := sSetTopAdj.{u}) _

end RepresentativeObjects

section UnitAndCounit

example (X : SSet.{u}) :
    SSet.realizationWeakEquivalences (sSetTopAdj.{u}.unit.app X) :=
  SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X

example (X : SSet.{1}) :
    SSet.realizationWeakEquivalences (sSetTopAdj.{1}.unit.app X) :=
  SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X

example (X : SSet.{0}) :
    SSet.realizationWeakEquivalences (sSetTopAdj.{0}.unit.app X) :=
  SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X

example (Y : TopCat.{u}) :
    TopCat.weakHomotopyEquivalences (sSetTopAdj.{u}.counit.app Y) :=
  SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences Y

example (Y : TopCat.{1}) :
    TopCat.weakHomotopyEquivalences (sSetTopAdj.{1}.counit.app Y) :=
  SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences Y

example (Y : TopCat.{0}) :
    TopCat.weakHomotopyEquivalences (sSetTopAdj.{0}.counit.app Y) :=
  SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences Y

example {X : SSet.{u}} [IsCofibrant X]
    [IsFibrant (SSet.toTop.obj X)] :
    WeakEquivalence (sSetTopAdj.{u}.unit.app X) :=
  CategoryTheory.Adjunction.IsQuillenEquivalence.weakEquivalence_unit
    (adj := sSetTopAdj.{u}) X

example {Y : TopCat.{u}}
    [IsCofibrant (TopCat.toSSet.obj Y)] [IsFibrant Y] :
    WeakEquivalence (sSetTopAdj.{u}.counit.app Y) :=
  CategoryTheory.Adjunction.IsQuillenEquivalence.weakEquivalence_counit
    (adj := sSetTopAdj.{u}) Y

end UnitAndCounit

end BothScopes

section UniverseSpecializations

open scoped SSet.modelCategoryQuillen TopCat.modelCategory

#synth CategoryWithCofibrations SSet.{1}
#synth CategoryWithFibrations SSet.{1}
#synth CategoryWithWeakEquivalences SSet.{1}
#synth ModelCategory SSet.{1}
#synth CategoryWithCofibrations TopCat.{1}
#synth CategoryWithFibrations TopCat.{1}
#synth CategoryWithWeakEquivalences TopCat.{1}
#synth ModelCategory TopCat.{1}
#synth CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{1}
#synth CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{1}

example : (inferInstance :
      CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{1}) =
    SSet.modelCategoryQuillen.realizationIsQuillenAdjunction := rfl

example : (inferInstance :
      CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{1}) =
    SSet.modelCategoryQuillen.realizationIsQuillenEquivalence := rfl

#synth CategoryWithCofibrations SSet.{0}
#synth CategoryWithFibrations SSet.{0}
#synth CategoryWithWeakEquivalences SSet.{0}
#synth ModelCategory SSet.{0}
#synth CategoryWithCofibrations TopCat.{0}
#synth CategoryWithFibrations TopCat.{0}
#synth CategoryWithWeakEquivalences TopCat.{0}
#synth ModelCategory TopCat.{0}
#synth CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{0}
#synth CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{0}

example : (inferInstance :
      CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{0}) =
    SSet.modelCategoryQuillen.realizationIsQuillenAdjunction := rfl

example : (inferInstance :
      CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{0}) =
    SSet.modelCategoryQuillen.realizationIsQuillenEquivalence := rfl

end UniverseSpecializations

section PrivateSupport

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.preservesFibrations_toSSet

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.preservesTrivialFibrations_toSSet

#check SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences

#check SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.deltaRealizationAdjunction

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realSingCoreflectionIso

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalence_of_fibration_of_isPullback

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.minimal_I_rlp_of_realizationWeakEquivalence

end PrivateSupport

section PullRequest4615Boundaries

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.bkHocolimMap_mem_realizationWeakEquivalences

/-- Unknown identifier -/
#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_map_of_isPushouts_of_cofibrant

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isPushout_mono

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isColimit_nat_mono

end PullRequest4615Boundaries

#print axioms SSet.modelCategoryQuillen.realizationIsQuillenAdjunction
#print axioms SSet.modelCategoryQuillen.realizationIsQuillenEquivalence

end RealizationQuillenEquivalenceTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet
