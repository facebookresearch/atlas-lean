/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.NatTrans.TerminalArrow
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Preservation by pointwise arrow functors

A natural transformation whose endpoint functors preserve a shape determines an
arrow-valued functor preserving the same shape. The proof uses the joint
reflection of limits and colimits by the two arrow projections.

The terminal-arrow and initial-arrow corollaries retain the chosen terminal and
initial objects. Only the valid dual halves are stated: terminal arrows preserve
all limits, while initial arrows preserve all colimits. Both are accessible at
every regular cardinal.
-/

@[expose] public section

noncomputable section

universe vB uB vC uC vJ uJ w

open CategoryTheory Limits

namespace CategoryTheory.NatTrans

variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {F G : B ⥤ C}

/-- Pointwise arrows preserve a limit shape when both endpoint functors do. -/
theorem arrow_preservesLimitsOfShape (α : F ⟶ G)
    (J : Type uJ) [Category.{vJ} J]
    [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (arrow α) where
  preservesLimit {K} := by
    refine ⟨fun {c} hc => ⟨Comma.fstSndJointlyReflectLimit ?_ ?_⟩⟩
    · change IsLimit (F.mapCone c)
      exact isLimitOfPreserves F hc
    · change IsLimit (G.mapCone c)
      exact isLimitOfPreserves G hc

/-- Pointwise arrows preserve a colimit shape when both endpoint functors do. -/
theorem arrow_preservesColimitsOfShape (α : F ⟶ G)
    (J : Type uJ) [Category.{vJ} J]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J (arrow α) where
  preservesColimit {K} := by
    refine ⟨fun {c} hc => ⟨Comma.fstSndJointlyReflectColimit ?_ ?_⟩⟩
    · change IsColimit (F.mapCocone c)
      exact isColimitOfPreserves F hc
    · change IsColimit (G.mapCocone c)
      exact isColimitOfPreserves G hc

/-- Pointwise arrows are cardinal-accessible when both endpoint functors are. -/
theorem arrow_isCardinalAccessible (α : F ⟶ G)
    (μ : Cardinal.{w}) [Fact μ.IsRegular]
    [F.IsCardinalAccessible μ] [G.IsCardinalAccessible μ] :
    (arrow α).IsCardinalAccessible μ where
  preservesColimitOfShape J _ _ := by
    let _ : PreservesColimitsOfShape J F :=
      F.preservesColimitsOfShape_of_isCardinalAccessible μ J
    let _ : PreservesColimitsOfShape J G :=
      G.preservesColimitsOfShape_of_isCardinalAccessible μ J
    exact arrow_preservesColimitsOfShape α J

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]

/-- An Arrow-valued functor is accessible when both endpoint projections are accessible. -/
theorem isCardinalAccessible_toArrow (T : B ⥤ Arrow C)
    (μ : Cardinal.{w}) [Fact μ.IsRegular]
    [(T ⋙ Arrow.leftFunc).IsCardinalAccessible μ]
    [(T ⋙ Arrow.rightFunc).IsCardinalAccessible μ] :
    T.IsCardinalAccessible μ := by
  let α : T ⋙ Arrow.leftFunc ⟶ T ⋙ Arrow.rightFunc :=
    { app := fun p => (T.obj p).hom
      naturality := fun _ _ f => (T.map f).w }
  let e : T ≅ NatTrans.arrow α :=
    NatIso.ofComponents (fun p => Arrow.isoMk (Iso.refl _) (Iso.refl _)) (by
      intro p q f
      apply Arrow.hom_ext
      · change (T.map f).left ≫ 𝟙 _ = 𝟙 _ ≫ (T.map f).left
        simp only [Category.comp_id, Category.id_comp]
      · change (T.map f).right ≫ 𝟙 _ = 𝟙 _ ≫ (T.map f).right
        simp only [Category.comp_id, Category.id_comp])
  let _ : (NatTrans.arrow α).IsCardinalAccessible μ :=
    NatTrans.arrow_isCardinalAccessible α μ
  exact isCardinalAccessible_of_natIso e.symm μ

end CategoryTheory.Functor

namespace CategoryTheory.Limits

namespace terminal

private theorem const_preservesLimitsOfShape
    (C : Type uC) [Category.{vC} C] [HasTerminal C]
    (J : Type uJ) [Category.{vJ} J] :
    PreservesLimitsOfShape J ((Functor.const C).obj (⊤_ C)) where
  preservesLimit {K} := by
    refine ⟨fun {c} _ => ⟨?_⟩⟩
    exact
      { lift := fun s => terminal.from s.pt
        fac := fun _ _ => terminalIsTerminal.hom_ext _ _
        uniq := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }

/-- The canonical terminal-arrow functor preserves every limit shape, including
the empty shape. -/
theorem arrowFunctor_preservesLimitsOfShape
    (C : Type uC) [Category.{vC} C] [HasTerminal C]
    (J : Type uJ) [Category.{vJ} J] :
    PreservesLimitsOfShape J (terminal.arrowFunctor C) := by
  let _ : PreservesLimitsOfShape J (𝟭 C) := inferInstance
  let _ : PreservesLimitsOfShape J ((Functor.const C).obj (⊤_ C)) :=
    const_preservesLimitsOfShape C J
  exact NatTrans.arrow_preservesLimitsOfShape (terminal.fromNatTrans C) J

/-- The canonical terminal-arrow functor is accessible at every regular
cardinal. -/
theorem arrowFunctor_isCardinalAccessible
    (C : Type uC) [Category.{vC} C] [HasTerminal C]
    (μ : Cardinal.{w}) [Fact μ.IsRegular] :
    (terminal.arrowFunctor C).IsCardinalAccessible μ :=
  NatTrans.arrow_isCardinalAccessible (terminal.fromNatTrans C) μ

end terminal

namespace initial

private theorem const_preservesColimitsOfShape
    (C : Type uC) [Category.{vC} C] [HasInitial C]
    (J : Type uJ) [Category.{vJ} J] :
    PreservesColimitsOfShape J ((Functor.const C).obj (⊥_ C)) where
  preservesColimit {K} := by
    refine ⟨fun {c} _ => ⟨?_⟩⟩
    exact
      { desc := fun s => initial.to s.pt
        fac := fun _ _ => initialIsInitial.hom_ext _ _
        uniq := fun _ _ _ => initialIsInitial.hom_ext _ _ }

/-- The canonical initial-arrow functor preserves every colimit shape, including
the empty shape. -/
theorem arrowFunctor_preservesColimitsOfShape
    (C : Type uC) [Category.{vC} C] [HasInitial C]
    (J : Type uJ) [Category.{vJ} J] :
    PreservesColimitsOfShape J (initial.arrowFunctor C) := by
  let _ : PreservesColimitsOfShape J ((Functor.const C).obj (⊥_ C)) :=
    const_preservesColimitsOfShape C J
  let _ : PreservesColimitsOfShape J (𝟭 C) := inferInstance
  exact NatTrans.arrow_preservesColimitsOfShape (initial.toNatTrans C) J

/-- The canonical initial-arrow functor is accessible at every regular
cardinal. -/
theorem arrowFunctor_isCardinalAccessible
    (C : Type uC) [Category.{vC} C] [HasInitial C]
    (μ : Cardinal.{w}) [Fact μ.IsRegular] :
    (initial.arrowFunctor C).IsCardinalAccessible μ :=
  NatTrans.arrow_isCardinalAccessible (initial.toNatTrans C) μ

end initial

end CategoryTheory.Limits
