/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPSimplicialHomotopyEquiv
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWColimits
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure

/-!
# Final TopCat model-structure consumers

Persistent clients for Kan weak-equivalence colimit stability, the two final
recognition inclusions, and the opt-in all-universe `TopCat` model structure.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelStructureTests

universe u

example :
    MorphismProperty.IsStableUnderFilteredColimits.{u, u}
      (SSet.KanComplex.W : MorphismProperty SSet.{u}) :=
  inferInstance

section Transfinite

variable (J : Type u) [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] [NoMaxOrder J]

example :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (SSet.KanComplex.W : MorphismProperty SSet.{u}) J :=
  inferInstance

end Transfinite

example :
    SSet.modelCategoryQuillen.I.{u}.rlp ≤
      SSet.realizationWeakEquivalences.{u} :=
  SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences

example :
    SSet.modelCategoryQuillen.I.{1}.rlp ≤
      SSet.realizationWeakEquivalences.{1} :=
  SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences

example :
    SSet.modelCategoryQuillen.I.{0}.rlp ≤
      SSet.realizationWeakEquivalences.{0} :=
  SSet.modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences

example :
    TopCat.realizedHornInclusions.{u}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences :=
  TopCat.horn_llp_le_weakHomotopyEquivalences

example :
    TopCat.realizedHornInclusions.{1}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences :=
  TopCat.horn_llp_le_weakHomotopyEquivalences

example :
    TopCat.realizedHornInclusions.{0}.rlp.llp ≤
      TopCat.weakHomotopyEquivalences :=
  TopCat.horn_llp_le_weakHomotopyEquivalences

noncomputable example : ModelCategory TopCat.{u} :=
  TopCat.modelCategory

noncomputable example : ModelCategory TopCat.{1} :=
  TopCat.modelCategory

noncomputable example : ModelCategory TopCat.{0} :=
  TopCat.modelCategory

section NoScope

#synth CategoryWithWeakEquivalences TopCat.{0}

example : weakEquivalences TopCat.{0} =
    TopCat.weakHomotopyEquivalences := rfl

example : True := by
  fail_if_success
    let _ : CategoryWithWeakEquivalences TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithWeakEquivalences TopCat.{1} := inferInstance
  fail_if_success
    let _ : CategoryWithCofibrations TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithFibrations TopCat.{u} := inferInstance
  fail_if_success
    let _ : ModelCategory TopCat.{u} := inferInstance
  fail_if_success
    let _ : CategoryWithCofibrations TopCat.{1} := inferInstance
  fail_if_success
    let _ : CategoryWithFibrations TopCat.{1} := inferInstance
  fail_if_success
    let _ : ModelCategory TopCat.{1} := inferInstance
  fail_if_success
    let _ : CategoryWithCofibrations TopCat.{0} := inferInstance
  fail_if_success
    let _ : CategoryWithFibrations TopCat.{0} := inferInstance
  fail_if_success
    let _ : ModelCategory TopCat.{0} := inferInstance
  trivial

end NoScope

section Scoped

open scoped TopCat.modelCategory

#synth ModelCategory TopCat.{u}
#synth CategoryWithFibrations TopCat.{u}
#synth CategoryWithCofibrations TopCat.{u}
#synth CategoryWithWeakEquivalences TopCat.{u}

#synth ModelCategory TopCat.{1}
#synth CategoryWithFibrations TopCat.{1}
#synth CategoryWithCofibrations TopCat.{1}
#synth CategoryWithWeakEquivalences TopCat.{1}

#synth ModelCategory TopCat.{0}
#synth CategoryWithFibrations TopCat.{0}
#synth CategoryWithCofibrations TopCat.{0}
#synth CategoryWithWeakEquivalences TopCat.{0}

example : (inferInstance : ModelCategory TopCat.{u}) =
    TopCat.modelCategory := rfl

example : (inferInstance : CategoryWithFibrations TopCat.{u}) =
    TopCat.modelCategory.categoryWithFibrations := rfl

example : (inferInstance : CategoryWithCofibrations TopCat.{u}) =
    TopCat.modelCategory.categoryWithCofibrations := rfl

example : (inferInstance : CategoryWithWeakEquivalences TopCat.{u}) =
    TopCat.modelCategory.categoryWithWeakEquivalences := rfl

example : fibrations TopCat.{u} =
    TopCat.realizedHornInclusions.{u}.rlp := rfl

example : cofibrations TopCat.{u} =
    TopCat.realizedBoundaryInclusions.{u}.rlp.llp := rfl

example : weakEquivalences TopCat.{u} =
    TopCat.weakHomotopyEquivalences := rfl

#synth IsWeakFactorizationSystem (cofibrations TopCat.{u})
  (trivialFibrations TopCat.{u})
#synth IsWeakFactorizationSystem (trivialCofibrations TopCat.{u})
  (fibrations TopCat.{u})
#synth HasFactorization (cofibrations TopCat.{u})
  (trivialFibrations TopCat.{u})
#synth HasFactorization (trivialCofibrations TopCat.{u})
  (fibrations TopCat.{u})

#synth (weakEquivalences TopCat.{u}).HasTwoOutOfThreeProperty
#synth (weakEquivalences TopCat.{u}).IsStableUnderRetracts
#synth (fibrations TopCat.{u}).IsStableUnderRetracts
#synth (cofibrations TopCat.{u}).IsStableUnderRetracts

#synth HasFiniteLimits TopCat.{u}
#synth HasFiniteColimits TopCat.{u}

example (X : TopCat.{u}) : weakEquivalences TopCat.{u} (𝟙 X) :=
  (weakEquivalences TopCat.{u}).id_mem X

end Scoped

section Coexistence

open scoped SSet.modelCategoryQuillen TopCat.modelCategory

#synth CategoryWithCofibrations SSet.{u}
#synth CategoryWithFibrations SSet.{u}
#synth ModelCategory TopCat.{u}

example : (inferInstance : ModelCategory TopCat.{u}) =
    TopCat.modelCategory := rfl

end Coexistence

#print axioms TopCat.modelCategory

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatModelStructureTests
