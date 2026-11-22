/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.Colimits.FilteredClosedColimit
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellSmallness
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# Bounded sources for the original closed-chain cardinal

Type-level cardinal presentability and the actual closed embedding of each
filtered colimit leg give stage factorization for every bounded topological
source. Equality of original stage morphisms is detected at a later stage.
Thus its Hom functor preserves the original cardinal-filtered closed colimit.
This is not a locally-presentable TopCat or native model assumption.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits Topology

namespace TopCat.BoundedSource

variable {J : Type v} [Category.{w} J] [EssentiallySmall.{u} J]
  [Fact realizedGeneratorCardinal.{u}.IsRegular]
  [IsCardinalFiltered J realizedGeneratorCardinal.{u}]

/-- Every original continuous map from a bounded source factors through an actual closed stage. -/
theorem stage_exists (X : TopCat.{u})
    (hX : HasCardinalLT ↥X realizedGeneratorCardinal.{u})
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom)
    (f : X ⟶ c.pt) : ∃ (j : J) (g : X ⟶ F.obj j), g ≫ c.ι.app j = f := by
  have hPresent : IsCardinalPresentable ↥X realizedGeneratorCardinal.{u} :=
    hX.isCardinalPresentable
  have hFilt : IsFiltered J := isFiltered_of_isCardinalFiltered J realizedGeneratorCardinal.{u}
  obtain ⟨j, f', hf'⟩ :=
    @IsCardinalPresentable.exists_hom_of_isColimit (X := ↥X)
      (κ := realizedGeneratorCardinal.{u}) (Type u) inferInstance inferInstance J
      inferInstance hPresent inferInstance inferInstance _ _
      (isColimitOfPreserves (forget TopCat) hc) ((forget TopCat).map f)
  let stageTop : TopologicalSpace ((F ⋙ forget TopCat).obj j) := (F.obj j).str
  have hClosed : IsClosedEmbedding (c.ι.app j).hom :=
    @TopCat.isClosedEmbedding_ι_of_filtered_of_isClosedEmbedding J inferInstance hFilt
      F c hc hF j
  have hEq : ⇑(c.ι.app j).hom ∘ (f' : ↥X → ↥(F.obj j)) = ⇑f.hom := by
    funext x
    exact ConcreteCategory.congr_hom hf' x
  have hComp : Continuous (⇑(c.ι.app j).hom ∘ (f' : ↥X → ↥(F.obj j))) := by
    rw [hEq]
    exact f.hom.continuous_toFun
  have hCont : @Continuous _ _ _ stageTop (f' : ↥X → ↥(F.obj j)) :=
    hClosed.isEmbedding.continuous_iff.mpr hComp
  refine ⟨j, TopCat.ofHom ⟨f', hCont⟩, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact congrFun hEq x

/-- Equality of original bounded-source stage maps is detected at an actual common later stage. -/
theorem stage_eq (X : TopCat.{u})
    (hX : HasCardinalLT ↥X realizedGeneratorCardinal.{u})
    {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c) {j₁ j₂ : J}
    (g₁ : X ⟶ F.obj j₁) (g₂ : X ⟶ F.obj j₂)
    (h : g₁ ≫ c.ι.app j₁ = g₂ ≫ c.ι.app j₂) :
    ∃ (k : J) (a : j₁ ⟶ k) (b : j₂ ⟶ k), g₁ ≫ F.map a = g₂ ≫ F.map b := by
  have hPresent : IsCardinalPresentable ↥X realizedGeneratorCardinal.{u} :=
    hX.isCardinalPresentable
  have hfType : (forget TopCat.{u}).map g₁ ≫ (forget TopCat.{u}).map (c.ι.app j₁) =
      (forget TopCat.{u}).map g₂ ≫ (forget TopCat.{u}).map (c.ι.app j₂) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]
  obtain ⟨k, a, b, hab⟩ :=
    IsCardinalPresentable.exists_eq_of_isColimit realizedGeneratorCardinal.{u}
      (isColimitOfPreserves (forget TopCat.{u}) hc)
      ((forget TopCat.{u}).map g₁) ((forget TopCat.{u}).map g₂) hfType
  refine ⟨k, a, b, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact ConcreteCategory.congr_hom hab x

/-- Hom from the bounded source preserves the actual original cardinal-filtered closed diagram. -/
theorem preservesClosedColimit (X : TopCat.{u})
    (hX : HasCardinalLT ↥X realizedGeneratorCardinal.{u})
    (F : J ⥤ TopCat.{u})
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom) :
    PreservesColimit F (coyoneda.obj (Opposite.op X)) := by
  refine ⟨fun {c} hc => ?_⟩
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro f
    obtain ⟨j, g, hg⟩ := stage_exists X hX c hc hF f
    exact ⟨j, g, by simpa using hg.symm⟩
  · intro a b x y hxy
    have h : x ≫ c.ι.app a = y ≫ c.ι.app b := by simpa using hxy
    obtain ⟨d, p, q, hpq⟩ := stage_eq X hX c hc x y h
    exact ⟨d, p, q, by simpa using hpq⟩

omit [Fact realizedGeneratorCardinal.{u}.IsRegular] in
/-- Every actual finite simplicial realization has the SAME original source cardinal bound. -/
theorem finiteRealization_bound (X : SSet.{u}) [X.Finite] :
    HasCardinalLT ↥(SSet.toTop.obj X) realizedGeneratorCardinal.{u} := by
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  exact lt_of_le_of_lt (mk_realizedFinite_le X) (Order.lt_succ _)

/-- Finite realizations preserve the original actual closed diagram,
with no source-smallness input. -/
theorem finiteRealization_preservesClosedColimit (X : SSet.{u}) [X.Finite]
    (F : J ⥤ TopCat.{u})
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), IsClosedEmbedding (F.map f).hom) :
    PreservesColimit F (coyoneda.obj (Opposite.op (SSet.toTop.obj X))) :=
  preservesClosedColimit _ (finiteRealization_bound X) F hF

end TopCat.BoundedSource
