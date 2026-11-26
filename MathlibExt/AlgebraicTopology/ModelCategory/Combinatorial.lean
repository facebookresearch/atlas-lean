/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AccessibleMorphismProperty
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
public import MathlibExt.CategoryTheory.Presentable.OriginalDiagramCardinalScale
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

import Mathlib.CategoryTheory.Presentable.IsDiscrete
import MathlibExt.CategoryTheory.SmallObject.EndpointProfile
import Mathlib.CategoryTheory.Presentable.Uniformization

/-!
# Combinatorial model categories

Combinatoriality is recorded at one regular cardinal shared by local
presentability and both explicit generating families. No generator,
presentability, factorization, or model structure is installed by this file.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- A model category is combinatorial relative to a universe when local
presentability and two explicit generating families can be witnessed at one
regular cardinal. -/
@[pp_with_univ]
class IsCombinatorialModelCategory
    (C : Type u) [Category.{v} C] [ModelCategory C] : Prop where
  exists_cardinal :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular)
      (_ : OrderBot κ.ord.ToType),
      IsCardinalLocallyPresentable C κ ∧
        Nonempty (CofibrantGenerationData C κ)

/-- A common regular cardinal for local presentability and the two supplied
SOA families, without a model-category premise. -/
theorem exists_common_generation_cardinal
    [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C)
    [I.HasSmallObjectArgument.{w}]
    [J.HasSmallObjectArgument.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular)
      (_ : OrderBot κ.ord.ToType),
      IsCardinalLocallyPresentable C κ ∧
        I.IsCardinalForSmallObjectArgument κ ∧
        J.IsCardinalForSmallObjectArgument κ := by
  obtain ⟨κ₀, hκ₀, hC₀⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  let _ : Fact κ₀.IsRegular := hκ₀
  let _ : IsCardinalLocallyPresentable C κ₀ := hC₀
  have hISmall : I.IsSmall.{w} := by
    obtain ⟨κI, hκI, hbotI, hI⟩ :=
      HasSmallObjectArgument.exists_cardinal (I := I)
    let _ : Fact κI.IsRegular := hκI
    let _ : OrderBot κI.ord.ToType := hbotI
    exact hI.isSmall
  have hJSmall : J.IsSmall.{w} := by
    obtain ⟨κJ, hκJ, hbotJ, hJ⟩ :=
      HasSmallObjectArgument.exists_cardinal (I := J)
    let _ : Fact κJ.IsRegular := hκJ
    let _ : OrderBot κJ.ord.ToType := hbotJ
    exact hJ.isSmall
  let _ : I.IsSmall.{w} := hISmall
  let _ : J.IsSmall.{w} := hJSmall
  let D₀ : Type := Discrete PUnit
  let K := I.toSet ⊕ J.toSet
  let _ : Small.{w} K := by
    dsimp [K]
    infer_instance
  let source : K → C := fun k =>
    match k with
    | .inl f => f.1.left
    | .inr f => f.1.left
  let F : K → D₀ ⥤ C := fun k =>
    (Functor.const D₀).obj (source k)
  let _ (k : K) : Functor.IsAccessible.{w} (F k) := by
    dsimp [F]
    infer_instance
  obtain ⟨κ, hκ, hD₀, hC, _, hPres⟩ :=
    IsCardinalAccessibleCategory.uniformization_of_small F
  let _ : Fact κ.IsRegular := hκ
  let _ : IsCardinalAccessibleCategory D₀ κ := hD₀
  let _ : IsCardinalAccessibleCategory C κ := hC
  let hCLP : IsCardinalLocallyPresentable C κ :=
    { toHasCardinalFilteredGenerator := inferInstance
      toHasColimitsOfSize := inferInstance }
  have hne : Nonempty κ.ord.ToType := by
    simpa using Cardinal.IsRegular.ne_zero Fact.out
  let _ : Nonempty κ.ord.ToType := hne
  let hBot : OrderBot κ.ord.ToType :=
    WellFoundedLT.toOrderBot κ.ord.ToType
  let _ : OrderBot κ.ord.ToType := hBot
  have hSource (k : K) : IsCardinalPresentable (source k) κ := by
    let _ : (F k).PreservesCardinalPresentable κ := hPres k
    have h : IsCardinalPresentable ((F k).obj ⟨PUnit.unit⟩) κ :=
      inferInstance
    simpa [F] using h
  let hI : I.IsCardinalForSmallObjectArgument κ :=
    { isSmall := inferInstance
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := by
        intro A B X Y i hi f hf
        let k : K := .inl ⟨Arrow.mk i, hi⟩
        have hA : IsCardinalPresentable A κ := by
          simpa [k, source] using hSource k
        let _ : IsCardinalPresentable A κ := hA
        let _ : PreservesColimitsOfShape κ.ord.ToType
            (coyoneda.obj (Opposite.op A)) :=
          preservesColimitsOfShape_of_isCardinalPresentable
            A κ κ.ord.ToType
        infer_instance }
  let hJ : J.IsCardinalForSmallObjectArgument κ :=
    { isSmall := inferInstance
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := by
        intro A B X Y i hi f hf
        let k : K := .inr ⟨Arrow.mk i, hi⟩
        have hA : IsCardinalPresentable A κ := by
          simpa [k, source] using hSource k
        let _ : IsCardinalPresentable A κ := hA
        let _ : PreservesColimitsOfShape κ.ord.ToType
            (coyoneda.obj (Opposite.op A)) :=
          preservesColimitsOfShape_of_isCardinalPresentable
            A κ κ.ord.ToType
        infer_instance }
  exact ⟨κ, inferInstance, hBot, hCLP, hI, hJ⟩

/-- A common regular rank strictly above the given LP witness and a fixed working-sized type,
retaining every original I/J source and both complete native small-object dictionaries. -/
theorem exists_common_generation_cardinal_from_sources
    (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
    [IsCardinalLocallyPresentable C kappaLP]
    (I J : MorphismProperty C) [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]
    (fixed : Type w) :
    ∃ (rho : Cardinal.{w}) (_ : Fact rho.IsRegular) (_ : OrderBot rho.ord.ToType),
      kappaLP < rho ∧ HasCardinalLT fixed rho ∧ IsCardinalLocallyPresentable C rho ∧
      (∀ i : I.toSet, IsCardinalPresentable i.1.left rho) ∧
      (∀ j : J.toSet, IsCardinalPresentable j.1.left rho) ∧
      I.IsCardinalForSmallObjectArgument rho ∧ J.IsCardinalForSmallObjectArgument rho := by
  let : IsLocallyPresentable.{w} C := ⟨kappaLP, inferInstance, inferInstance⟩
  obtain ⟨mu, hmu, hbot, _, hI, hJ⟩ := exists_common_generation_cardinal I J
  let : Fact mu.IsRegular := hmu
  let : OrderBot mu.ord.ToType := hbot
  let : I.IsCardinalForSmallObjectArgument mu := hI
  let : J.IsCardinalForSmallObjectArgument mu := hJ
  let : IsAccessibleCategory.{w} C := ⟨kappaLP, inferInstance, inferInstance⟩
  let Fixed := kappaLP.ord.ToType ⊕ fixed
  obtain ⟨muI, hmuI, _, hFixedI, hEndpointsI⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal I mu Fixed
  obtain ⟨muJ, hmuJ, _, _, hEndpointsJ⟩ :=
    SmallObject.original_endpoints_have_common_presentability_cardinal J mu Fixed
  let : Fact muI.IsRegular := hmuI
  let : Fact muJ.IsRegular := hmuJ
  let Upper := muI.ord.ToType ⊕ muJ.ord.ToType
  obtain ⟨rho, hrho, hUpper⟩ := HasCardinalLT.exists_regular_cardinal Upper
  let : Fact rho.IsRegular := ⟨hrho⟩
  let : OrderBot rho.ord.ToType :=
    Presentable.OriginalDiagramCardinalScale.regularOrdinalBottom rho
  have hmuI' : muI < rho := by
    have h := hUpper.of_injective (Sum.inl : muI.ord.ToType → Upper) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hmuJ' : muJ < rho := by
    have h := hUpper.of_injective (Sum.inr : muJ.ord.ToType → Upper) Sum.inr_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hLP : kappaLP < rho := by
    have h := hFixedI.of_injective (Sum.inl : kappaLP.ord.ToType → Fixed) Sum.inl_injective
    have hk : kappaLP < muI := by
      simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
    exact hk.trans hmuI'
  have hfixed : HasCardinalLT fixed rho :=
    (hFixedI.of_injective (Sum.inr : fixed → Fixed) Sum.inr_injective).of_le hmuI'.le
  let : IsCardinalLocallyPresentable C rho := IsCardinalLocallyPresentable.of_le C hLP.le
  let : I.IsSmall.{w} := hI.isSmall
  let : J.IsSmall.{w} := hJ.isSmall
  have hSourceI (i : I.toSet) : IsCardinalPresentable i.1.left rho := by
    let : IsCardinalPresentable i.1.left muI := (hEndpointsI i).1
    exact isCardinalPresentable_of_le _ hmuI'.le
  have hSourceJ (j : J.toSet) : IsCardinalPresentable j.1.left rho := by
    let : IsCardinalPresentable j.1.left muJ := (hEndpointsJ j).1
    exact isCardinalPresentable_of_le _ hmuJ'.le
  exact ⟨rho, inferInstance, inferInstance, hLP, hfixed, inferInstance, hSourceI, hSourceJ,
    Presentable.OriginalDiagramCardinalScale.smallObjectFromSources I rho hSourceI,
    Presentable.OriginalDiagramCardinalScale.smallObjectFromSources J rho hSourceJ⟩

variable [ModelCategory C]

/-- Conventional locally-presentable and cofibrantly-generated hypotheses
produce combinatoriality after synchronizing the three witness cardinals.
The generator choices remain explicit and no instance is installed. -/
theorem isCombinatorialModelCategory_of_generators
    [IsLocallyPresentable.{w} C]
    (I J : MorphismProperty C)
    [I.HasSmallObjectArgument.{w}]
    [J.HasSmallObjectArgument.{w}]
    (hI : I.rlp = trivialFibrations C)
    (hJ : J.rlp = fibrations C) :
    IsCombinatorialModelCategory.{w} C := by
  obtain ⟨κ, hκ, hbot, hC, hIκ, hJκ⟩ :=
    exists_common_generation_cardinal I J
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  exact
    { exists_cardinal :=
        ⟨κ, hκ, hbot, hC,
          ⟨{
            I := I
            J := J
            I_smallObject := hIκ
            J_smallObject := hJκ
            I_rlp := hI
            J_rlp := hJ }⟩⟩ }

end HomotopicalAlgebra
