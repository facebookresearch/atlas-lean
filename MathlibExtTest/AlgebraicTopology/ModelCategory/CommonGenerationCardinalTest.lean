/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe w v u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.CommonGenerationCardinal
variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C)
  [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]

-- No ModelCategory variable is available in this whole generic section.
-- The two full source-Hom preservation statements concern the supplied I/J.
theorem sourceHomConditions :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
      IsCardinalLocallyPresentable C κ ∧
      (∀ {A B X Y : C} (i : A ⟶ B), I i → ∀ (f : X ⟶ Y)
        (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ I.homFamily) f),
        PreservesColimit hf.F (coyoneda.obj (Opposite.op A))) ∧
      (∀ {A B X Y : C} (j : A ⟶ B), J j → ∀ (f : X ⟶ Y)
        (hf : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) ↦ J.homFamily) f),
        PreservesColimit hf.F (coyoneda.obj (Opposite.op A))) := by
  obtain ⟨κ, hκ, hBot, hC, hIκ, hJκ⟩ := exists_common_generation_cardinal I J
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hBot
  refine ⟨κ, hκ, hBot, hC, ?_, ?_⟩
  · intro A B X Y i hi f hf
    exact hIκ.preservesColimit i hi f hf
  · intro A B X Y j hj f hf
    exact hJκ.preservesColimit j hj f hf

section Model
variable [ModelCategory C]

-- This is the separate model application of the generic exact witness.
-- Literal I/J identities come from the actual data constructor, not from
-- the weaker existential combinatoriality proposition.
theorem namedModelData
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType)
      (d : CofibrantGenerationData C κ),
      IsCardinalLocallyPresentable C κ ∧ d.I = I ∧ d.J = J := by
  obtain ⟨κ, hκ, hBot, hC, hIκ, hJκ⟩ := exists_common_generation_cardinal I J
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hBot
  refine ⟨κ, hκ, hBot,
    { I := I, J := J, I_smallObject := hIκ, J_smallObject := hJκ,
      I_rlp := hI, J_rlp := hJ }, hC, rfl, rfl⟩
end Model
end MathlibExtTest.AlgebraicTopology.ModelCategory.CommonGenerationCardinal
