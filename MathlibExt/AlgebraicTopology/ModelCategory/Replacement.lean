/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Functorial cofibrant and fibrant replacements

Functorial factorization of the initial maps as cofibrations followed by
trivial fibrations gives a cofibrant replacement functor with a natural
trivial-fibration counit. Dually, factorization of terminal maps as trivial
cofibrations followed by fibrations gives a fibrant replacement functor with a
natural trivial-cofibration unit. The replacement maps satisfy the original
factorization identities, and their replacement objects are cofibrant or
fibrant, respectively.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

section CofibrantReplacement

variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

noncomputable def cofFactData :
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) :=
  functorialFactorizationData (cofibrations C) (trivialFibrations C)

/-- Functorial cofibrant replacement obtained by factoring `⊥_ C ⟶ X`
as a cofibration followed by a trivial fibration. -/
noncomputable def cofibrantReplacement : C ⥤ C where
  obj X := (cofFactData.factorizationData (initial.to X)).Z
  map {X Y} f :=
    cofFactData.mapZ
      (Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Y))
        (𝟙 (⊥_ C)) f (by simp))
  map_id X := by
    have h :
        Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to X))
            (𝟙 (⊥_ C)) (𝟙 X) (by simp) =
          𝟙 (Arrow.mk (initial.to X)) := by
      apply Arrow.hom_ext <;> simp
    have h1 :
        cofFactData.mapZ
            (Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to X))
              (𝟙 (⊥_ C)) (𝟙 X) (by simp)) = 𝟙 _ := by
      rw [h, cofFactData.mapZ_id]
    exact h1
  map_comp {X Y Z} f g := by
    have h :
        Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Z))
            (𝟙 (⊥_ C)) (f ≫ g) (by simp) =
          Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Y))
              (𝟙 (⊥_ C)) f (by simp) ≫
            Arrow.homMk (f := Arrow.mk (initial.to Y)) (g := Arrow.mk (initial.to Z))
              (𝟙 (⊥_ C)) g (by simp) := by
      apply Arrow.hom_ext <;> simp
    have h1 :
        cofFactData.mapZ
            (Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Z))
              (𝟙 (⊥_ C)) (f ≫ g) (by simp)) =
          cofFactData.mapZ
              (Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Y))
                (𝟙 (⊥_ C)) f (by simp)) ≫
            cofFactData.mapZ
              (Arrow.homMk (f := Arrow.mk (initial.to Y)) (g := Arrow.mk (initial.to Z))
                (𝟙 (⊥_ C)) g (by simp)) := by
      rw [h, cofFactData.mapZ_comp]
    exact h1

/-- The cofibration `⊥_ C ⟶ Q X` from the factorization of `⊥_ C ⟶ X`. -/
noncomputable def initialToCofibrantReplacement (X : C) :
    (⊥_ C) ⟶ cofibrantReplacement.obj X :=
  (cofFactData.factorizationData (initial.to X)).i

instance cofibration_initialToCofibrantReplacement (X : C) :
    Cofibration (initialToCofibrantReplacement (C := C) X) where
  mem := (cofFactData.factorizationData (initial.to X)).hi

/-- Natural trivial fibration `Q X ⟶ X` from cofibrant replacement to the identity. -/
noncomputable def cofibrantReplacementCounit :
    cofibrantReplacement (C := C) ⟶ 𝟭 C where
  app X := (cofFactData.factorizationData (initial.to X)).p
  naturality X Y f := by
    dsimp [cofibrantReplacement]
    exact
      cofFactData.mapZ_p
        (Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Y))
          (𝟙 (⊥_ C)) f (by simp))

/-- Factorization identity for cofibrant replacement. -/
lemma cofibrantReplacement_fac (X : C) :
    initialToCofibrantReplacement (C := C) X ≫
      (cofibrantReplacementCounit (C := C)).app X =
        initial.to X :=
  cofFactData.fac_app (f := Arrow.mk (initial.to X))

instance isCofibrant_cofibrantReplacement (X : C) :
    IsCofibrant ((cofibrantReplacement (C := C)).obj X) := by
  rw [isCofibrant_iff_of_isInitial (initialToCofibrantReplacement (C := C) X)
      initialIsInitial]
  infer_instance

instance fibration_cofibrantReplacementCounit (X : C) :
    Fibration ((cofibrantReplacementCounit (C := C)).app X) where
  mem := (cofFactData.factorizationData (initial.to X)).hp.1

instance weakEquivalence_cofibrantReplacementCounit (X : C) :
    WeakEquivalence ((cofibrantReplacementCounit (C := C)).app X) where
  mem := (cofFactData.factorizationData (initial.to X)).hp.2

end CofibrantReplacement

section FibrantReplacement

variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

noncomputable def fibFactData :
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) :=
  functorialFactorizationData (trivialCofibrations C) (fibrations C)

/-- Functorial fibrant replacement obtained by factoring `X ⟶ ⊤_ C`
as a trivial cofibration followed by a fibration. -/
noncomputable def fibrantReplacement : C ⥤ C where
  obj X := (fibFactData.factorizationData (terminal.from X)).Z
  map {X Y} f :=
    fibFactData.mapZ
      (Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Y))
        f (𝟙 (⊤_ C)) (by simp))
  map_id X := by
    have h :
        Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from X))
            (𝟙 X) (𝟙 (⊤_ C)) (by simp) =
          𝟙 (Arrow.mk (terminal.from X)) := by
      apply Arrow.hom_ext <;> simp
    have h1 :
        fibFactData.mapZ
            (Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from X))
              (𝟙 X) (𝟙 (⊤_ C)) (by simp)) = 𝟙 _ := by
      rw [h, fibFactData.mapZ_id]
    exact h1
  map_comp {X Y Z} f g := by
    have h :
        Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Z))
            (f ≫ g) (𝟙 (⊤_ C)) (by simp) =
          Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Y))
              f (𝟙 (⊤_ C)) (by simp) ≫
            Arrow.homMk (f := Arrow.mk (terminal.from Y)) (g := Arrow.mk (terminal.from Z))
              g (𝟙 (⊤_ C)) (by simp) := by
      apply Arrow.hom_ext <;> simp
    have h1 :
        fibFactData.mapZ
            (Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Z))
              (f ≫ g) (𝟙 (⊤_ C)) (by simp)) =
          fibFactData.mapZ
              (Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Y))
                f (𝟙 (⊤_ C)) (by simp)) ≫
            fibFactData.mapZ
              (Arrow.homMk (f := Arrow.mk (terminal.from Y)) (g := Arrow.mk (terminal.from Z))
                g (𝟙 (⊤_ C)) (by simp)) := by
      rw [h, fibFactData.mapZ_comp]
    exact h1

/-- Natural trivial cofibration `X ⟶ R X` from the identity to fibrant replacement. -/
noncomputable def fibrantReplacementUnit :
    (𝟭 C) ⟶ fibrantReplacement (C := C) where
  app X := (fibFactData.factorizationData (terminal.from X)).i
  naturality X Y f := by
    dsimp [fibrantReplacement]
    exact
      (fibFactData.i_mapZ
        (Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Y))
          f (𝟙 (⊤_ C)) (by simp))).symm

/-- The fibration `R X ⟶ ⊤_ C` from the factorization of `X ⟶ ⊤_ C`. -/
noncomputable def fibrantReplacementToTerminal (X : C) :
    (fibrantReplacement (C := C)).obj X ⟶ (⊤_ C) :=
  (fibFactData.factorizationData (terminal.from X)).p

instance fibration_fibrantReplacementToTerminal (X : C) :
    Fibration (fibrantReplacementToTerminal (C := C) X) where
  mem := (fibFactData.factorizationData (terminal.from X)).hp

/-- Factorization identity for fibrant replacement. -/
lemma fibrantReplacement_fac (X : C) :
    (fibrantReplacementUnit (C := C)).app X ≫
      fibrantReplacementToTerminal (C := C) X =
        terminal.from X :=
  fibFactData.fac_app (f := Arrow.mk (terminal.from X))

instance isFibrant_fibrantReplacement (X : C) :
    IsFibrant ((fibrantReplacement (C := C)).obj X) := by
  rw [isFibrant_iff_of_isTerminal (fibrantReplacementToTerminal (C := C) X)
      terminalIsTerminal]
  infer_instance

instance cofibration_fibrantReplacementUnit (X : C) :
    Cofibration ((fibrantReplacementUnit (C := C)).app X) where
  mem := (fibFactData.factorizationData (terminal.from X)).hi.1

instance weakEquivalence_fibrantReplacementUnit (X : C) :
    WeakEquivalence ((fibrantReplacementUnit (C := C)).app X) where
  mem := (fibFactData.factorizationData (terminal.from X)).hi.2

end FibrantReplacement

end HomotopicalAlgebra
