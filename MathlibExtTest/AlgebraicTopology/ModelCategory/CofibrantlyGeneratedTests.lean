/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.CofibrantlyGeneratedTests

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable (κ : Cardinal.{w}) [Fact κ.IsRegular]
variable [OrderBot κ.ord.ToType]
variable (G H : CofibrantGenerationData C κ)

example : MorphismProperty C := G.I
example : MorphismProperty C := G.J
example : G.I.IsCardinalForSmallObjectArgument κ := G.I_smallObject
example : G.J.IsCardinalForSmallObjectArgument κ := G.J_smallObject
example : G.I.rlp = trivialFibrations C := G.I_rlp
example : G.J.rlp = fibrations C := G.J_rlp

example : CofibrantGenerationData C κ where
  I := G.I
  J := G.J
  I_smallObject := G.I_smallObject
  J_smallObject := G.J_smallObject
  I_rlp := G.I_rlp
  J_rlp := G.J_rlp

example : G.I.rlp.llp = cofibrations C := by
  rw [G.I_rlp]
  exact llp_eq_of_wfs (cofibrations C) (trivialFibrations C)

example : G.J.rlp.llp = trivialCofibrations C := by
  rw [G.J_rlp]
  exact llp_eq_of_wfs (trivialCofibrations C) (fibrations C)

example : Nonempty
    (FunctorialFactorizationData G.I.rlp.llp G.I.rlp) := by
  let _ : G.I.IsCardinalForSmallObjectArgument κ := G.I_smallObject
  let _ : HasFunctorialFactorization G.I.rlp.llp G.I.rlp :=
    SmallObject.hasFunctorialFactorization G.I κ
  exact ⟨functorialFactorizationData G.I.rlp.llp G.I.rlp⟩

example : Nonempty
    (FunctorialFactorizationData G.J.rlp.llp G.J.rlp) := by
  let _ : G.J.IsCardinalForSmallObjectArgument κ := G.J_smallObject
  let _ : HasFunctorialFactorization G.J.rlp.llp G.J.rlp :=
    SmallObject.hasFunctorialFactorization G.J κ
  exact ⟨functorialFactorizationData G.J.rlp.llp G.J.rlp⟩

example : G.I.rlp = trivialFibrations C ∧
    H.I.rlp = trivialFibrations C :=
  ⟨G.I_rlp, H.I_rlp⟩

example : G.J.rlp = fibrations C ∧ H.J.rlp = fibrations C :=
  ⟨G.J_rlp, H.J_rlp⟩

example : G.I = H.I ∨ G.I ≠ H.I := eq_or_ne _ _
example : G.J = H.J ∨ G.J ≠ H.J := eq_or_ne _ _

example : True := by
  fail_if_success
    have _ : CofibrantGenerationData C κ := inferInstance
  trivial

end HomotopicalAlgebra.CofibrantlyGeneratedTests

#check HomotopicalAlgebra.CofibrantGenerationData
#print axioms HomotopicalAlgebra.CofibrantGenerationData
