/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Functorial replacements from the original generation and factor maps

The same fixed-cardinal factorization factories act on the actual initial
and terminal natural maps. The resulting functors retain every square map,
both natural factor arrows, and the original factor equations. Weak-equivalence
preservation is derived from those same natural weak maps and two-out-of-three.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedFunctorialReplacements

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]

/-- The actual initial maps form the original natural transformation to the identity. -/
def initialMap : (Functor.const C).obj (⊥_ C) ⟶ 𝟭 C where
  app X := initial.to X
  naturality _ _ f := by simp

/-- The actual terminal maps form the original natural transformation from the identity. -/
def terminalMap : 𝟭 C ⟶ (Functor.const C).obj (⊤_ C) where
  app X := terminal.from X
  naturality _ _ f := by simp

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- Original I generation factors the entire natural initial map by the same
functor-category factory. -/
def initialFactor (d : CofibrantGenerationData C κ) :
    MapFactorizationData ((cofibrations C).functorCategory C)
      ((trivialFibrations C).functorCategory C)
      (initialMap (C := C)) :=
  ((d.cofibrantFactorizationData).functorCategory C).factorizationData initialMap

/-- Original J generation factors the entire natural terminal map by the same factory. -/
def terminalFactor (d : CofibrantGenerationData C κ) :
    MapFactorizationData ((trivialCofibrations C).functorCategory C)
      ((fibrations C).functorCategory C)
      (terminalMap (C := C)) :=
  ((d.fibrantFactorizationData).functorCategory C).factorizationData terminalMap

/-- The complete cofibrant replacement functor constructed from original I generation. -/
abbrev Q (d : CofibrantGenerationData C κ) : C ⥤ C := (initialFactor d).Z

/-- The complete fibrant replacement functor constructed from original J generation. -/
abbrev R (d : CofibrantGenerationData C κ) : C ⥤ C := (terminalFactor d).Z

/-- The original natural left I factor into Q. -/
abbrev initialLeg (d : CofibrantGenerationData C κ) : (Functor.const C).obj (⊥_ C) ⟶ Q d :=
  (initialFactor d).i

/-- The original natural trivial-fibration I factor is the weak counit Q to Id. -/
abbrev counit (d : CofibrantGenerationData C κ) : Q d ⟶ 𝟭 C := (initialFactor d).p

/-- The original natural trivial-cofibration J factor is the weak unit Id to R. -/
abbrev unit (d : CofibrantGenerationData C κ) : 𝟭 C ⟶ R d := (terminalFactor d).i

/-- The original natural right J factor from R to the terminal object. -/
abbrev terminalLeg (d : CofibrantGenerationData C κ) : R d ⟶ (Functor.const C).obj (⊤_ C) :=
  (terminalFactor d).p

/-- The entire original initial natural map is recovered by the same two I arrows. -/
theorem initial_fac (d : CofibrantGenerationData C κ) : initialLeg d ≫ counit d = initialMap :=
  (initialFactor d).fac

/-- The entire original terminal natural map is recovered by the same two J arrows. -/
theorem terminal_fac (d : CofibrantGenerationData C κ) : unit d ≫ terminalLeg d = terminalMap :=
  (terminalFactor d).fac

/-- Every original Q map is the same I middle-map algorithm on its full initial square. -/
theorem Q_map (d : CofibrantGenerationData C κ) {X Y : C} (f : X ⟶ Y) :
    (Q d).map f = (d.cofibrantFactorizationData).Z.map
      (Arrow.homMk (𝟙 (⊥_ C)) f (by simp [initialMap])) := rfl

/-- Every original R map is the same J middle-map algorithm on its full terminal square. -/
theorem R_map (d : CofibrantGenerationData C κ) {X Y : C} (f : X ⟶ Y) :
    (R d).map f = (d.fibrantFactorizationData).Z.map
      (Arrow.homMk f (𝟙 (⊤_ C)) (by simp [terminalMap])) := rfl

/-- Every original Q object is the original I factorization of its initial arrow. -/
theorem Q_obj (d : CofibrantGenerationData C κ) (X : C) :
    (Q d).obj X = (d.cofibrantFactorizationData).Z.obj (Arrow.mk (initial.to X)) := rfl

/-- Every original R object is the original J factorization of its terminal arrow. -/
theorem R_obj (d : CofibrantGenerationData C κ) (X : C) :
    (R d).obj X = (d.fibrantFactorizationData).Z.obj (Arrow.mk (terminal.from X)) := rfl

/-- Every initial I factor remains a cofibration in the original model. -/
theorem initialLeg_cofibration (d : CofibrantGenerationData C κ) (X : C) :
    cofibrations C ((initialLeg d).app X) := (initialFactor d).hi X

/-- Every original Q counit is a trivial fibration in the same original model. -/
theorem counit_trivialFibration (d : CofibrantGenerationData C κ) (X : C) :
    trivialFibrations C ((counit d).app X) := (initialFactor d).hp X

/-- Every original R unit is a trivial cofibration in the same original model. -/
theorem unit_trivialCofibration (d : CofibrantGenerationData C κ) (X : C) :
    trivialCofibrations C ((unit d).app X) := (terminalFactor d).hi X

/-- Every terminal J factor remains a fibration in the original model. -/
theorem terminalLeg_fibration (d : CofibrantGenerationData C κ) (X : C) :
    fibrations C ((terminalLeg d).app X) := (terminalFactor d).hp X

/-- Every actual generated Q object is cofibrant without an input replacement assumption. -/
theorem Q_isCofibrant (d : CofibrantGenerationData C κ) (X : C) : IsCofibrant ((Q d).obj X) :=
  (isCofibrant_iff_of_isInitial ((initialLeg d).app X) initialIsInitial).mpr
    ((cofibration_iff _).mpr (initialLeg_cofibration d X))

/-- Every actual generated R object is fibrant without an input replacement assumption. -/
theorem R_isFibrant (d : CofibrantGenerationData C κ) (X : C) : IsFibrant ((R d).obj X) :=
  (isFibrant_iff_of_isTerminal ((terminalLeg d).app X) terminalIsTerminal).mpr
    ((fibration_iff _).mpr (terminalLeg_fibration d X))

/-- The complete natural generated Q counit is weak at every original object. -/
theorem counit_weak (d : CofibrantGenerationData C κ) (X : C) :
    weakEquivalences C ((counit d).app X) := (counit_trivialFibration d X).2

/-- The complete natural generated R unit is weak at every original object. -/
theorem unit_weak (d : CofibrantGenerationData C κ) (X : C) :
    weakEquivalences C ((unit d).app X) := (unit_trivialCofibration d X).2

/-- Q preserves each original weak equivalence by its same natural weak
counit and two-out-of-three. -/
theorem Q_map_weak (d : CofibrantGenerationData C κ) {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) : weakEquivalences C ((Q d).map f) := by
  apply (weakEquivalences C).of_postcomp ((Q d).map f) ((counit d).app Y) (counit_weak d Y)
  rw [(counit d).naturality]
  exact (weakEquivalences C).comp_mem _ _ (counit_weak d X) hf

/-- R preserves each original weak equivalence by its same natural weak
unit and two-out-of-three. -/
theorem R_map_weak (d : CofibrantGenerationData C κ) {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) : weakEquivalences C ((R d).map f) := by
  apply (weakEquivalences C).of_precomp ((unit d).app X) ((R d).map f) (unit_weak d X)
  rw [← (unit d).naturality]
  exact (weakEquivalences C).comp_mem _ _ hf (unit_weak d Y)

end HomotopicalAlgebra.GeneratedFunctorialReplacements
