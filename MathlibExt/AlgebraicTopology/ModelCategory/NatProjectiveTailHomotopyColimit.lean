/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

import MathlibExt.AlgebraicTopology.ModelCategory.NatProjectiveFreeTail
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedDiagramConstructions
import Mathlib.CategoryTheory.Limits.Final

/-!
# The original source-projective homotopy-colimit comparison for the tail

The original projective factory, original Q and actual predecessor/tail
adjunction produce cofibrancy and both weak source-comparison legs.
No ordinary-suspension stability, Ho-colimit identity or locality is input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra
open CategoryTheory.Functor
namespace HomotopicalAlgebra.NatProjectiveFreeTail
variable {C : Type u} [Category.{v} C]

/-- Actual order adjunction proves finality of the whole original tail functor. -/
instance tail_final : tail.Final :=
  Functor.final_of_adjunction predecessorTailAdjunction

section Projective

variable [ModelCategory C] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] (g : CofibrantGenerationData C κ)
  (s : Functor.EssentialIndexData.{w} ℕ C)

local notation "M" => DerivedDiagramConstructions.projectiveModel g s

/-- The source-built projective right classes make the actual tail/predecessor adjunction Quillen. -/
theorem restriction_isQuillen :
    letI := M
    (restrictionAdjunction C).IsQuillenAdjunction := by
  let := M
  obtain ⟨_, hF, hT, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y a ha
    rw [hF] at ha ⊢
    intro n
    exact ha (n - 1)
  · intro X Y a ha
    rw [hT] at ha ⊢
    intro n
    exact ha (n - 1)

/-- Every genuinely projective-cofibrant original diagram retains cofibrancy under the tail. -/
theorem tail_cofibrant (F : ℕ ⥤ C) :
    letI := M
    IsCofibrant F → IsCofibrant (tail ⋙ F) := by
  let := M
  let := restriction_isQuillen g s
  intro hF
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := restrictionAdjunction C) hF

/-- The actual tail of the original whole projective Q is cofibrant by the source Quillen proof. -/
theorem tail_Q_cofibrant (F : ℕ ⥤ C) :
    letI := M
    IsCofibrant (tail ⋙ (DerivedDiagramConstructions.projectiveReplacements g s).Q.obj F) := by
  let := M
  exact tail_cofibrant g s _
    ((DerivedDiagramConstructions.projectiveReplacements g s).q_cofibrant F)

variable [HasColimitsOfShape ℕ C]

/-- The common comparison source keeps the original Q and every whole diagram map. -/
def tailQFunctor : (ℕ ⥤ C) ⥤ (ℕ ⥤ C) := by
  letI := M
  exact (DerivedDiagramConstructions.projectiveReplacements g s).Q ⋙
    (whiskeringLeft ℕ ℕ C).obj tail

/-- The original whole Q counit produces the source map to the original tail diagram. -/
def toTail : tailQFunctor g s ⟶ (whiskeringLeft ℕ ℕ C).obj tail := by
  letI := M
  exact whiskerRight (DerivedDiagramConstructions.projectiveReplacements g s).q
    ((whiskeringLeft ℕ ℕ C).obj tail)

/-- The actual source counit, after the original projective hocolim functor. -/
def toTailHomotopyColimit :
    tailQFunctor g s ⋙ DerivedDiagramConstructions.projectiveHomotopyColimit g s ⟶
      (whiskeringLeft ℕ ℕ C).obj tail ⋙
        DerivedDiagramConstructions.projectiveHomotopyColimit g s :=
  whiskerRight (toTail g s) (DerivedDiagramConstructions.projectiveHomotopyColimit g s)

/-- All original weak Q vertices prove weakness of the whole tail-hocolim source map. -/
theorem toTailHomotopyColimit_weak (F : ℕ ⥤ C) :
    weakEquivalences C ((toTailHomotopyColimit g s).app F) := by
  apply DerivedDiagramConstructions.projectiveHomotopyColimit_map_weak g s ((toTail g s).app F)
  intro n
  exact DerivedDiagramConstructions.projectiveQ_vertex_weak g s F (n + 1)

/-- The other full comparison leg uses the original Q-counit and actual ordinary tail finality. -/
def toOriginalHomotopyColimit :
    tailQFunctor g s ⋙ DerivedDiagramConstructions.projectiveHomotopyColimit g s ⟶
      DerivedDiagramConstructions.projectiveHomotopyColimit g s := by
  letI := M
  let d := DerivedDiagramConstructions.projectiveReplacements g s
  exact whiskerLeft (tailQFunctor g s) (DerivedDiagramConstructions.colimitComparison d) ≫
    (associator d.Q ((whiskeringLeft ℕ ℕ C).obj tail) colim).hom ≫
      whiskerLeft d.Q (Functor.Final.colimIso tail).hom

/-- Source-produced tail-Q cofibrancy proves weakness of the original finality comparison. -/
theorem toOriginalHomotopyColimit_weak (F : ℕ ⥤ C) :
    weakEquivalences C ((toOriginalHomotopyColimit g s).app F) := by
  let := M
  let d := DerivedDiagramConstructions.projectiveReplacements g s
  let : IsCofibrant (tail ⋙ d.Q.obj F) := tail_Q_cofibrant g s F
  obtain ⟨_, hF, hT, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  have hq := DerivedDiagramConstructions.colimitComparison_weak d hF hT (tail ⋙ d.Q.obj F)
  change weakEquivalences C
    ((DerivedDiagramConstructions.colimitComparison d).app (tail ⋙ d.Q.obj F) ≫
      (𝟙 _ ≫ (Functor.Final.colimIso tail).hom.app (d.Q.obj F)))
  rw [Category.id_comp]
  exact (weakEquivalences C).comp_mem _ _ hq (mem_weakEquivalences _)

/-- The original Q-counit weak leg gives its full natural Iso after the actual localization. -/
def toTailHoIso :
    tailQFunctor g s ⋙ DerivedDiagramConstructions.projectiveHomotopyColimit g s ⋙
        toHomotopyCategory C ≅
      (whiskeringLeft ℕ ℕ C).obj tail ⋙
        DerivedDiagramConstructions.projectiveHomotopyColimit g s ⋙ toHomotopyCategory C := by
  let τ := whiskerRight (toTailHomotopyColimit g s) (toHomotopyCategory C)
  letI (F : ℕ ⥤ C) : IsIso (τ.app F) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (toTailHomotopyColimit_weak g s F)
  letI : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- The source-produced cofibrancy/finality weak leg gives the other full natural Ho Iso. -/
def toOriginalHoIso :
    tailQFunctor g s ⋙ DerivedDiagramConstructions.projectiveHomotopyColimit g s ⋙
        toHomotopyCategory C ≅
      DerivedDiagramConstructions.projectiveHomotopyColimit g s ⋙ toHomotopyCategory C := by
  let τ := whiskerRight (toOriginalHomotopyColimit g s) (toHomotopyCategory C)
  letI (F : ℕ ⥤ C) : IsIso (τ.app F) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (toOriginalHomotopyColimit_weak g s F)
  letI : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- Both original common-source weak legs give the full natural tail-hocolim comparison in Ho. -/
def tailHoIso :
    (whiskeringLeft ℕ ℕ C).obj tail ⋙
        DerivedDiagramConstructions.projectiveHomotopyColimit g s ⋙ toHomotopyCategory C ≅
      DerivedDiagramConstructions.projectiveHomotopyColimit g s ⋙ toHomotopyCategory C :=
  (toTailHoIso g s).symm ≪≫ toOriginalHoIso g s

section Localized

local notation "HP" => toHomotopyCategory (ℕ ⥤ C)
local notation "WP" => weakEquivalences (ℕ ⥤ C)
local notation "PΓ" => DerivedDiagramConstructions.projectiveHomotopyColimit g s

omit [HasColimitsOfShape ℕ C] in
/-- Original pointwise weak classes prove that the complete tail acts on the same localization. -/
private theorem tail_inverts :
    letI := M
    (WP).IsInvertedBy (((whiskeringLeft ℕ ℕ C).obj tail) ⋙ HP) := by
  let := M
  intro F G a ha
  have hW := (FunctorProjective.SourceConstruction.FromData.five_classes g s).1
  rw [hW] at ha
  exact Localization.inverts HP WP _ (by
    rw [hW]
    intro n
    exact ha (n + 1))

/-- The original full tail functor descends through the actual projective weak localization. -/
@[instance_reducible]
def projectiveTail :
    letI := M
    HomotopyCategory (ℕ ⥤ C) ⥤ HomotopyCategory (ℕ ⥤ C) := by
  letI := M
  exact Localization.lift (((whiskeringLeft ℕ ℕ C).obj tail) ⋙ HP) (tail_inverts g s) HP

/-- Both localization comparison maps retain the entire original tail of every whole diagram. -/
def projectiveTailProjection :
    letI := M
    HP ⋙ projectiveTail g s ≅ ((whiskeringLeft ℕ ℕ C).obj tail) ⋙ HP := by
  letI := M
  exact Localization.fac (((whiskeringLeft ℕ ℕ C).obj tail) ⋙ HP) (tail_inverts g s) HP

/-- Source-generated projective classes and Q give the actual derived colimit functor. -/
def sourceDerivedColimit :
    letI := M
    HomotopyCategory (ℕ ⥤ C) ⥤ HomotopyCategory C := by
  letI := M
  obtain ⟨_, hF, hT, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  exact DerivedDiagramConstructions.derivedColimit
    (DerivedDiagramConstructions.projectiveReplacements g s) hF hT

/-- The derived colimit projection is the same entire original projective Q-colimit localization. -/
def sourceDerivedColimitProjection :
    letI := M
    HP ⋙ sourceDerivedColimit g s ≅ PΓ ⋙ toHomotopyCategory C := by
  letI := M
  obtain ⟨_, hF, hT, _, _⟩ := FunctorProjective.SourceConstruction.FromData.five_classes g s
  exact eqToIso (DerivedDiagramConstructions.derivedColimit_projection
    (DerivedDiagramConstructions.projectiveReplacements g s) hF hT)

/-- The full tail and derived-colimit projections preserve both original localization comparisons. -/
def tailDerivedProjection :
    letI := M
    HP ⋙ (projectiveTail g s ⋙ sourceDerivedColimit g s) ≅
      ((whiskeringLeft ℕ ℕ C).obj tail) ⋙ PΓ ⋙ toHomotopyCategory C := by
  letI := M
  exact (associator HP (projectiveTail g s) (sourceDerivedColimit g s)).symm ≪≫
    isoWhiskerRight (projectiveTailProjection g s) (sourceDerivedColimit g s) ≪≫
      associator ((whiskeringLeft ℕ ℕ C).obj tail) HP (sourceDerivedColimit g s) ≪≫
        isoWhiskerLeft ((whiskeringLeft ℕ ℕ C).obj tail) (sourceDerivedColimitProjection g s)

/-- Both actual source weak legs descend to the full natural cofinal-tail Iso on projective Ho. -/
def derivedTailIso :
    letI := M
    projectiveTail g s ⋙ sourceDerivedColimit g s ≅ sourceDerivedColimit g s := by
  letI := M
  letI : Localization.Lifting HP WP
      (((whiskeringLeft ℕ ℕ C).obj tail) ⋙ PΓ ⋙ toHomotopyCategory C)
      (projectiveTail g s ⋙ sourceDerivedColimit g s) := ⟨tailDerivedProjection g s⟩
  letI : Localization.Lifting HP WP (PΓ ⋙ toHomotopyCategory C)
      (sourceDerivedColimit g s) := ⟨sourceDerivedColimitProjection g s⟩
  exact Localization.liftNatIso HP WP
    (((whiskeringLeft ℕ ℕ C).obj tail) ⋙ PΓ ⋙ toHomotopyCategory C)
    (PΓ ⋙ toHomotopyCategory C) (projectiveTail g s ⋙ sourceDerivedColimit g s)
    (sourceDerivedColimit g s) (tailHoIso g s)

/-- Every actual whole-projective Ho morphism retains the same source-derived tail comparison. -/
theorem derivedTailIso_naturality :
    letI := M
    ∀ {F G : HomotopyCategory (ℕ ⥤ C)} (a : F ⟶ G),
      (projectiveTail g s ⋙ sourceDerivedColimit g s).map a ≫ (derivedTailIso g s).hom.app G =
        (derivedTailIso g s).hom.app F ≫ (sourceDerivedColimit g s).map a := by
  let := M
  intro F G a
  exact (derivedTailIso g s).hom.naturality a

end Localized

end Projective

end HomotopicalAlgebra.NatProjectiveFreeTail
