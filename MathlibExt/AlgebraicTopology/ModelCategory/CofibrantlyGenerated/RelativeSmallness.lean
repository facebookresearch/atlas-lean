/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.SmallObject.RelativeSourceSmallness
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Existence
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# A common generation cardinal from uniform relative source smallness

The original I and J families are genuinely small. Bound their actual
source ranks by one regular successor and retain that cardinal, its
ordinal bottom, both complete eligibility dictionaries and the original
right-class equations. No local presentability or cardinal-monotonicity
hypothesis enters.

The output datum stores the same original families. Explicit-data users
keep their input cardinal and factors; this theorem produces a new
justified common witness only from conventional relative-smallness input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w u v
open CategoryTheory Limits MorphismProperty Cardinal
open CategoryTheory.SmallObject

namespace CategoryTheory.SmallObject

variable {C : Type u} [Category.{v} C]

/-- The small union of actual I/J source ranks has one regular strict upper bound. -/
theorem exists_common_relative_source_bound
    (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallness.{w} J) :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧
      (∀ i : I.toSet, UniformRelativeSourceSmallness.sourceBound hI i < κ) ∧
      (∀ j : J.toSet, UniformRelativeSourceSmallness.sourceBound hJ j < κ) := by
  let K := I.toSet ⊕ J.toSet
  let β : K → Cardinal.{w} := fun s =>
    match s with
    | .inl i => UniformRelativeSourceSmallness.sourceBound hI i
    | .inr j => UniformRelativeSourceSmallness.sourceBound hJ j
  let ranks : K → Type w := fun s => (β s).ord.ToType
  obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w} ranks
  have hb (s : K) : β s < κ := by
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, ranks, Cardinal.mk_ord_toType] using h s
  exact ⟨κ, hκ, fun i => hb (.inl i), fun j => hb (.inr j)⟩

/-- Uniform source bounds supply the complete original eligibility at a sufficient κ. -/
theorem isCardinalForSmallObjectArgument_of_uniform_bounds
    (I : MorphismProperty C) [I.IsSmall.{w}] [LocallySmall.{w} C]
    [HasPushouts C] [HasCoproducts.{w} C]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [HasIterationOfShape κ.ord.ToType C]
    (hκ : ∀ i : I.toSet, UniformRelativeSourceSmallness.sourceBound hI i < κ) :
    I.IsCardinalForSmallObjectArgument κ where
  isSmall := inferInstance
  locallySmall := inferInstance
  hasPushouts := inferInstance
  hasCoproducts := inferInstance
  hasIterationOfShape := inferInstance
  preservesColimit i hi f c :=
    UniformRelativeSourceSmallness.preservesColimit_relativeCellComplex hI κ i hi
      (hκ ⟨Arrow.mk i, hi⟩) f c

/-- Both original families have all six fields at one produced regular cardinal and bottom. -/
theorem exists_common_relative_generation_cardinal
    (I J : MorphismProperty C) [I.IsSmall.{w}] [J.IsSmall.{w}]
    [LocallySmall.{w} C] [HasPushouts C] [HasCoproducts.{w} C]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallness.{w} J)
    (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
      I.IsCardinalForSmallObjectArgument κ ∧ J.IsCardinalForSmallObjectArgument κ := by
  obtain ⟨κ, hκ, hIκ, hJκ⟩ := exists_common_relative_source_bound I J hI hJ
  let _ : Fact κ.IsRegular := ⟨hκ⟩
  let _ : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType hκ.ne_zero
  let bottom : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let _ : OrderBot κ.ord.ToType := bottom
  let _ : HasIterationOfShape κ.ord.ToType C := hIteration κ
  exact ⟨κ, inferInstance, bottom,
    isCardinalForSmallObjectArgument_of_uniform_bounds I hI κ hIκ,
    isCardinalForSmallObjectArgument_of_uniform_bounds J hJ κ hJκ⟩

end CategoryTheory.SmallObject

namespace HomotopicalAlgebra

variable {M : Type u} [Category.{v} M] [ModelCategory M]

/-- Conventional uniform source smallness produces actual data with the same original I/J. -/
theorem exists_cofibrantGenerationData_of_uniform_relative_smallness
    (I J : MorphismProperty M) [I.IsSmall.{w}] [J.IsSmall.{w}]
    [LocallySmall.{w} M] [HasCoproducts.{w} M]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallness.{w} J)
    (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType M)
    (hIrlp : I.rlp = trivialFibrations M) (hJrlp : J.rlp = fibrations M) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
      ∃ d : CofibrantGenerationData M κ, d.I = I ∧ d.J = J := by
  obtain ⟨κ, hκ, hb, hIκ, hJκ⟩ :=
    exists_common_relative_generation_cardinal I J hI hJ hIteration
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hb
  exact ⟨κ, hκ, hb,
    { I := I, J := J, I_smallObject := hIκ, J_smallObject := hJκ,
      I_rlp := hIrlp, J_rlp := hJrlp }, rfl, rfl⟩

/-- The legitimate compatible-generation predicate follows without a presentability premise. -/
theorem hasCompatibleCofibrantGeneration_of_uniform_relative_smallness
    (I J : MorphismProperty M) [I.IsSmall.{w}] [J.IsSmall.{w}]
    [LocallySmall.{w} M] [HasCoproducts.{w} M]
    (hI : UniformRelativeSourceSmallness.{w} I)
    (hJ : UniformRelativeSourceSmallness.{w} J)
    (hIteration : ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular], HasIterationOfShape κ.ord.ToType M)
    (hIrlp : I.rlp = trivialFibrations M) (hJrlp : J.rlp = fibrations M) :
    HasCompatibleCofibrantGeneration.{w} M := by
  obtain ⟨κ, hκ, hb, d, hdI, hdJ⟩ :=
    exists_cofibrantGenerationData_of_uniform_relative_smallness I J hI hJ hIteration hIrlp hJrlp
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hb
  exact HasCompatibleCofibrantGeneration.ofData d

end HomotopicalAlgebra
