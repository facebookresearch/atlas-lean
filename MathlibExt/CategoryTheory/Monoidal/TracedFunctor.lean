/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Traced

/-!
# Functoriality of symmetric traces

Trace preservation includes the tensor comparison isomorphisms of a strong
monoidal functor. It is closed under identity and composition. Strong symmetric
monoidal functors preserve the canonical trace in symmetric right rigid
categories, without requiring equality of the chosen dual objects.

Source: Joyal, Street and Verity, Traced monoidal categories (1996),
Proposition 3.1, https://doi.org/10.1017/S0305004100074338.
This is the symmetric specialization of the canonical-trace functoriality
statement; no general balanced or tortile category structure is introduced.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

/-- The exact pairing obtained by applying a strong monoidal functor. -/
@[implicit_reducible]
def ExactPairing.map (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' := ε F ≫ F.map (η_ X Y) ≫ δ F X Y
  evaluation' := μ F Y X ≫ F.map (ε_ X Y) ≫ η F
  coevaluation_evaluation' := by
    have h := congrArg (fun f =>
      (F.obj Y ◁ ε F ≫ μ F Y (𝟙_ C)) ≫ F.map f ≫
        (δ F (𝟙_ C) Y ≫ η F ▷ F.obj Y)) (ExactPairing.coevaluation_evaluation X Y)
    simp only [Functor.map_comp, map_whiskerLeft, map_whiskerRight,
      map_associator_inv, map_rightUnitor, map_leftUnitor_inv] at h
    simpa only [whiskerLeft_comp, comp_whiskerRight, Category.assoc, μ_δ_assoc,
      δ_μ_assoc, whiskerLeft_μ_δ_assoc, whiskerRight_δ_μ_assoc,
      whiskerLeft_ε_η_assoc, whiskerRight_ε_η, Category.comp_id] using h
  evaluation_coevaluation' := by
    have h := congrArg (fun f =>
      (ε F ▷ F.obj X ≫ μ F (𝟙_ C) X) ≫ F.map f ≫
        (δ F X (𝟙_ C) ≫ F.obj X ◁ η F)) (ExactPairing.evaluation_coevaluation X Y)
    simp only [Functor.map_comp, map_whiskerLeft, map_whiskerRight,
      map_associator, map_leftUnitor, map_rightUnitor_inv] at h
    simpa only [whiskerLeft_comp, comp_whiskerRight, Category.assoc, μ_δ_assoc,
      δ_μ_assoc, whiskerRight_μ_δ_assoc, whiskerLeft_δ_μ_assoc,
      whiskerRight_ε_η_assoc, whiskerLeft_ε_η, Category.comp_id] using h

namespace SymmetricTrace

variable [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]

/-- Preservation of trace, with the strong monoidal comparison maps explicit. -/
def Preserves (T : SymmetricTrace C) (S : SymmetricTrace D) (F : C ⥤ D)
    [F.Monoidal] : Prop :=
  ∀ {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U),
    F.map (T.trace f) = S.trace (μ F X U ≫ F.map f ≫ δ F Y U)

/-- The identity strong monoidal functor preserves every trace. -/
theorem preserves_id (T : SymmetricTrace C) : T.Preserves T (𝟭 C) := by
  intro X Y U f
  simp

/-- Composition of trace-preserving strong monoidal functors preserves trace. -/
theorem Preserves.comp {T : SymmetricTrace C} {S : SymmetricTrace D}
    {R : SymmetricTrace E} {F : C ⥤ D} {G : D ⥤ E} [F.Monoidal] [G.Monoidal]
    (hF : T.Preserves S F) (hG : S.Preserves R G) : T.Preserves R (F ⋙ G) := by
  intro X Y U f
  change G.map (F.map (T.trace f)) = _
  rw [hF, hG]
  simp [Functor.map_comp]

/-- A strong symmetric monoidal functor preserves feedback through a specified
pairing, using the image pairing on the target. -/
theorem map_traceOfPairing (F : C ⥤ D) [F.Braided] {X Y U V : C}
    [ExactPairing U V] (f : X ⊗ U ⟶ Y ⊗ U) :
    letI := ExactPairing.map F U V
    F.map (traceOfPairing V f) =
      traceOfPairing (F.obj V) (μ F X U ≫ F.map f ≫ δ F Y U) := by
  simp only [traceOfPairing, Functor.map_comp, map_whiskerLeft, map_whiskerRight,
    map_associator, map_associator_inv, map_rightUnitor, map_rightUnitor_inv,
    Functor.map_braiding]
  dsimp +instances only [ExactPairing.coevaluation, ExactPairing.evaluation, ExactPairing.map]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc, μ_δ_assoc,
    whiskerLeft_μ_δ_assoc]

/-- Strong symmetric monoidal functors preserve the canonical right-rigid trace.
The chosen target dual may differ from the image of the chosen source dual. -/
theorem preserves_of_rigid [RightRigidCategory C] [RightRigidCategory D]
    (F : C ⥤ D) [F.Braided] :
    (symmetricTraceOfRigid C).Preserves (symmetricTraceOfRigid D) F := by
  intro X Y U f
  change F.map (traceOfPairing (Uᘁ) f) = traceOfPairing ((F.obj U)ᘁ) _
  let := ExactPairing.map F U (Uᘁ)
  exact (map_traceOfPairing F f).trans (traceOfPairing_independent _)

end SymmetricTrace

end CategoryTheory
