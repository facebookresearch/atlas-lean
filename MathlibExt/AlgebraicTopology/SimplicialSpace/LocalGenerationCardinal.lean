/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.Presentable
import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
import MathlibExt.AlgebraicTopology.ModelCategory.Combinatorial

/-!
# A common smallness cardinal for the literal local generators

One working-universe regular cardinal witnesses local presentability and
full native small-object eligibility for the original Reedy I/J and the
full auxiliary J. The horn inclusion is used by reindexing the actual
relative cell complex, retaining its original transfinite diagram, limit
and endpoint data. No SOA, cardinal, model or desired eligibility is supplied
by the caller. Full E and every scalar boundary remain in the literal family.

Source: Rezk, *A model for the homotopy theory of homotopy theory*, Section 9.1.
This is its fixed-family eligibility preparation, not global Rezk recognition.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra
namespace SimplicialSpace.LocalGenerators

-- This is derived from the actual horn-membership interface, not an assumed inclusion.
private theorem rawHorn_le_auxiliary : ReedyGeneratingFamilies.J.{u} ≤ J.{u} := by
  change MorphismProperty.ofHoms
    (fun h : ReedyGeneratingFamilies.HornIndex =>
      (ReedyGeneratingFamilies.hornFamily.{u} h).hom) ≤ J.{u}
  exact (MorphismProperty.ofHoms_le_iff _ _).2 (fun h => horn_mem h)

-- The whole original transfinite diagram and endpoint data are copied literally;
-- only the cell types are reindexed via identity isomorphisms of original arrows.
private def rawHornComplexAsAuxiliary (κ : Cardinal.{u})
    [OrderBot κ.ord.ToType]
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u}
      (fun (_ : κ.ord.ToType) => ReedyGeneratingFamilies.J.{u}.homFamily) f) :
    RelativeCellComplex.{u} (fun (_ : κ.ord.ToType) => J.{u}.homFamily) f :=
  let a : ReedyGeneratingFamilies.J.{u}.toSet → J.{u}.toSet :=
    fun t => ⟨t.1, rawHorn_le_auxiliary t.1.hom t.2⟩
  { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
    attachCells := fun j hj =>
      (hf.attachCells j hj).reindexCellTypes J.{u}.homFamily a
        (fun _ => Iso.refl _) }

private lemma rawHornComplexAsAuxiliary_F (κ : Cardinal.{u})
    [OrderBot κ.ord.ToType]
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u}
      (fun (_ : κ.ord.ToType) => ReedyGeneratingFamilies.J.{u}.homFamily) f) :
    (rawHornComplexAsAuxiliary κ f hf).F = hf.F := rfl

-- The entire original transfinite-composition data (including limits and endpoints)
-- is copied, not just an isomorphic functor or a replacement diagram.
private lemma rawHornComplexAsAuxiliary_base (κ : Cardinal.{u})
    [OrderBot κ.ord.ToType]
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u}
      (fun (_ : κ.ord.ToType) => ReedyGeneratingFamilies.J.{u}.homFamily) f) :
    (rawHornComplexAsAuxiliary κ f hf).toTransfiniteCompositionOfShape =
      hf.toTransfiniteCompositionOfShape := rfl

-- Subset alone does not prove preservesColimit; use the actual reindexed complex.
private theorem rawHornCardinal (κ : Cardinal.{u})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (h : J.{u}.IsCardinalForSmallObjectArgument κ) :
    ReedyGeneratingFamilies.J.{u}.IsCardinalForSmallObjectArgument κ where
  isSmall := ReedyGeneratingFamilies.isSmall_J
  locallySmall := h.locallySmall
  hasPushouts := h.hasPushouts
  hasCoproducts := h.hasCoproducts
  hasIterationOfShape := h.hasIterationOfShape
  preservesColimit := by
    intro A B X Y i hi f hf
    let hf' := rawHornComplexAsAuxiliary κ f hf
    have hF : hf'.F = hf.F := rawHornComplexAsAuxiliary_F κ f hf
    rw [← hF]
    exact h.preservesColimit i (rawHorn_le_auxiliary i hi) f hf'

/-- One same-u regular cardinal for LP and all THREE original literal families. -/
theorem exists_common_smallness_cardinal :
    ∃ (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      IsCardinalLocallyPresentable SimplicialSpace.{u} κ ∧
        ReedyGeneratingFamilies.I.{u}.IsCardinalForSmallObjectArgument κ ∧
        ReedyGeneratingFamilies.J.{u}.IsCardinalForSmallObjectArgument κ ∧
        J.{u}.IsCardinalForSmallObjectArgument κ := by
  let _ : IsLocallyPresentable.{u} SimplicialSpace.{u} := SimplicialSpace.isLocallyPresentable
  let _ : ReedyGeneratingFamilies.I.{u}.IsSmall.{u} := ReedyGeneratingFamilies.isSmall_I
  let _ : J.{u}.IsSmall.{u} := isSmall_J
  let _ : ReedyGeneratingFamilies.I.{u}.HasSmallObjectArgument.{u} :=
    hasSmallObjectArgument_of_isSmall ReedyGeneratingFamilies.I.{u}
  let _ : J.{u}.HasSmallObjectArgument.{u} := hasSmallObjectArgument_of_isSmall J.{u}
  obtain ⟨κ, hκ, hbot, hC, hI, hAux⟩ :=
    HomotopicalAlgebra.exists_common_generation_cardinal ReedyGeneratingFamilies.I.{u} J.{u}
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hbot
  exact ⟨κ, hκ, hbot, hC, hI, rawHornCardinal κ hAux, hAux⟩

end SimplicialSpace.LocalGenerators
