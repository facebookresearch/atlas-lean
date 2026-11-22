/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerNativeFunctorialFactorization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerFibrantObjects

/-!
# Same native original Bergner fibrant replacement

The original combined A1/A2 native factorization of the original
terminal arrow gives a whole fibrant replacement functor. Its natural
inclusion and projection retain the literal original native maps,
every changing object and every complete enriched Hom.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerFibrantReplacement
open OriginalBergnerIntervalFamily
attribute [local instance] Bergner.modelCategory

/-- The SAME original terminal-arrow square associated to each original enriched map. -/
def terminalSquare {C D : Carrier.{u}} (F : C ⟶ D) :
    Arrow.mk (terminal.from C) ⟶ Arrow.mk (terminal.from D) :=
  Arrow.homMk F (𝟙 _) (terminalIsTerminal.hom_ext _ _)

/-- The entire same native original Bergner fibrant replacement functor. -/
def functor : Carrier.{u} ⥤ Carrier.{u} where
  obj C := (NativeFactorization.data (terminal.from C)).Z
  map F := NativeFactorization.map (terminalSquare F)
  map_id C := by
    have h : terminalSquare (𝟙 C) = 𝟙 (Arrow.mk (terminal.from C)) := by
      apply Arrow.hom_ext <;> rfl
    exact (congrArg NativeFactorization.map h).trans (NativeFactorization.map_id _)
  map_comp F G := by
    have h : terminalSquare (F ≫ G) = terminalSquare F ≫ terminalSquare G := by
      apply Arrow.hom_ext
      · rfl
      · exact (Category.id_comp _).symm
    exact (congrArg NativeFactorization.map h).trans (NativeFactorization.map_comp _ _)

/-- The SAME original full native inclusion into the genuine fibrant replacement. -/
def inclusion : 𝟭 Carrier.{u} ⟶ functor.{u} where
  app C := (NativeFactorization.data (terminal.from C)).i
  naturality C D F :=
    (NativeFactorization.i_map (terminalSquare (C := C) (D := D) F)).symm

/-- The actual original native projection to the SAME chosen original terminal object. -/
def projection (C : Carrier.{u}) : functor.obj C ⟶ ⊤_ Carrier.{u} :=
  (NativeFactorization.data (terminal.from C)).p

/-- The complete original terminal factorization keeps its SAME input map. -/
theorem factorization (C : Carrier.{u}) :
    inclusion.app C ≫ projection C = terminal.from C := NativeFactorization.fac _

/-- Every whole original inclusion is genuinely C0 cofibrant and original DK weak. -/
theorem inclusion_original_classes (C : Carrier.{u}) :
    Bergner.cofibrations (inclusion.app C) ∧ EnrichedDwyerKan.weakEquivalences (inclusion.app C) :=
  (NativeFactorization.data (terminal.from C)).hi

/-- The SAME original native inclusion is a genuine model trivial cofibration. -/
theorem inclusion_model_classes (C : Carrier.{u}) :
    Cofibration (inclusion.app C) ∧ WeakEquivalence (inclusion.app C) :=
  ⟨(Bergner.cofibration_iff_original _).mpr (inclusion_original_classes C).1,
    (Bergner.weakEquivalence_iff_original _).mpr (inclusion_original_classes C).2⟩

/-- The SAME native original projection is a genuine original global-model fibration. -/
theorem projection_model_fibration (C : Carrier.{u}) : Fibration (projection C) :=
  (Bergner.fibration_iff_original _).mpr (NativeFactorization.data (terminal.from C)).hp

/-- The complete SAME original native replacement is genuinely fibrant in the original global model. -/
theorem isFibrant (C : Carrier.{u}) : HomotopicalAlgebra.IsFibrant (functor.obj C) :=
  (isFibrant_iff_of_isTerminal (projection C) terminalIsTerminal).mpr (projection_model_fibration C)

/-- Every SAME full original Hom of the genuine native replacement is Kan. -/
theorem homKan (C : Carrier.{u}) (x y : functor.obj C) :
    SSet.KanComplex (x ⟶[SSet.{u}] y) :=
  (Bergner.isFibrant_iff_original_homKan _).mp (isFibrant C) x y

/-- The entire native replacement source is the SAME original small-object intermediate enrichment. -/
theorem object_original (C : Carrier.{u}) :
    functor.obj C = (NativeFactorization.data (terminal.from C)).Z := rfl

/-- The entire replacement map is the SAME original native intermediate map of its terminal square. -/
theorem map_original {C D : Carrier.{u}} (F : C ⟶ D) :
    functor.map F = NativeFactorization.map (terminalSquare F) := rfl

/-- The inclusion is the SAME entire original native small-object inclusion. -/
theorem inclusion_original (C : Carrier.{u}) :
    inclusion.app C = (NativeFactorization.data (terminal.from C)).i := rfl

/-- Every actual original source object retains its SAME native terminal factorization readback. -/
theorem object_factorization (C : Carrier.{u}) (x : C) :
    (projection C).obj ((inclusion.app C).obj x) = (terminal.from C).obj x :=
  NativeFactorization.object_fac _ x

/-- The SAME complete original Hom map retains its actual original terminal factorization and both endpoint equations.
-/
theorem hom_factorization (C : Carrier.{u}) (x y : C) :
    ((inclusion.app C).map x y ≫
      (projection C).map ((inclusion.app C).obj x) ((inclusion.app C).obj y)) ≫
        eqToHom (congrArg₂ (fun a b : (⊤_ Carrier.{u}) => a ⟶[SSet.{u}] b)
          (object_factorization C x) (object_factorization C y)) =
      (terminal.from C).map x y := NativeFactorization.hom_fac _ x y

end CategoryTheory.SimplicialEnrichment.OriginalBergnerFibrantReplacement
