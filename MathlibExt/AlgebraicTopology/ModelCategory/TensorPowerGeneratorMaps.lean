/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
public import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# Actual tensor-power generator maps, including the empty coefficient

Tensoring a map with the empty power is the original map through the actual
unitors. Iteration of fixed-coordinate tensor preservation handles every
positive power. No cofibrancy of the tensor unit is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace HomotopicalAlgebra.TensorPowerGeneratorMaps

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- The empty left coefficient gives the original entire arrow through both actual unitors. -/
def leftUnitArrowIso {X Y : V} (f : X ⟶ Y) : Arrow.mk ((𝟙_ V) ◁ f) ≅ Arrow.mk f :=
  Arrow.isoMk' _ _ (λ_ X) (λ_ Y) (leftUnitor_naturality f).symm

/-- The empty right coefficient gives the original entire arrow through both actual unitors. -/
def rightUnitArrowIso {X Y : V} (f : X ⟶ Y) : Arrow.mk (f ▷ (𝟙_ V)) ≅ Arrow.mk f :=
  Arrow.isoMk' _ _ (ρ_ X) (ρ_ Y) (rightUnitor_naturality f).symm

/-- The source associator compares the complete two-step and block-coefficient tensor arrows. -/
def associatorArrowIso (A B : V) {X Y : V} (f : X ⟶ Y) :
    Arrow.mk ((A ⊗ B) ◁ f) ≅ Arrow.mk (A ◁ (B ◁ f)) :=
  Arrow.isoMk' _ _ (α_ A B X) (α_ A B Y) (associator_naturality_right A B f).symm

/-- Actual fixed-coordinate map preservation iterates through every tensor power, starting at the
unitors. -/
theorem left_mem (P : MorphismProperty V) [P.RespectsIso] (T : V)
    (hTensor : ∀ {X Y : V} (f : X ⟶ Y), P f → P (T ◁ f))
    (n : ℕ) {X Y : V} (f : X ⟶ Y) (hf : P f) : P (tensorPowObj T n ◁ f) := by
  induction n generalizing X Y with
  | zero =>
      exact (P.arrow_mk_iso_iff (leftUnitArrowIso f)).mpr hf
  | succ n ih =>
      have hT : P (T ◁ f) := hTensor f hf
      have hn : P (tensorPowObj T n ◁ (T ◁ f)) := ih (T ◁ f) hT
      exact (P.arrow_mk_iso_iff (associatorArrowIso (tensorPowObj T n) T f)).mpr hn

section Braided

variable [BraidedCategory V]

/-- The whole value braiding compares the right and left coefficient tensor arrows. -/
def braidingArrowIso (A : V) {X Y : V} (f : X ⟶ Y) : Arrow.mk (f ▷ A) ≅ Arrow.mk (A ◁ f) :=
  Arrow.isoMk' _ _ (β_ X A) (β_ Y A) (braiding_naturality_left f A).symm

/-- Every right tensor-power coefficient preserves the complete original map class. -/
theorem right_mem (P : MorphismProperty V) [P.RespectsIso] (T : V)
    (hTensor : ∀ {X Y : V} (f : X ⟶ Y), P f → P (T ◁ f))
    (n : ℕ) {X Y : V} (f : X ⟶ Y) (hf : P f) : P (f ▷ tensorPowObj T n) :=
  (P.arrow_mk_iso_iff (braidingArrowIso (tensorPowObj T n) f)).mpr (left_mem P T hTensor n f hf)

end Braided

variable [ModelCategory V] [SymmetricCategory V] [MonoidalClosed V]
  [IsClosedSymmetricMonoidalModelCategory V]

/-- Cofibrant T gives every left tensor-power cofibration, including the actual degree-zero arrow.
-/
theorem left_cofibration (T : V) [IsCofibrant T] (n : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : cofibrations V f) : cofibrations V (tensorPowObj T n ◁ f) :=
  left_mem (cofibrations V) T
    (fun f hf => (ihomAdjunction_isQuillenAdjunction_of_isCofibrant T).preservesCofibrations f hf)
        n f hf

/-- Cofibrant T gives every left tensor-power trivial cofibration without Cof(unit). -/
theorem left_trivialCofibration (T : V) [IsCofibrant T] (n : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : trivialCofibrations V f) : trivialCofibrations V (tensorPowObj T n ◁ f) :=
  left_mem (trivialCofibrations V) T
    (fun f hf => (ihomAdjunction_isQuillenAdjunction_of_isCofibrant T).preservesTrivialCofibrations
        f hf) n f hf

/-- Cofibrant T gives every right tensor-power cofibration without Cof(unit). -/
theorem right_cofibration (T : V) [IsCofibrant T] (n : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : cofibrations V f) : cofibrations V (f ▷ tensorPowObj T n) :=
  right_mem (cofibrations V) T
    (fun f hf => (ihomAdjunction_isQuillenAdjunction_of_isCofibrant T).preservesCofibrations f hf)
        n f hf

/-- Cofibrant T gives every right tensor-power trivial cofibration without Cof(unit). -/
theorem right_trivialCofibration (T : V) [IsCofibrant T] (n : ℕ) {X Y : V} (f : X ⟶ Y)
    (hf : trivialCofibrations V f) : trivialCofibrations V (f ▷ tensorPowObj T n) :=
  right_mem (trivialCofibrations V) T
    (fun f hf => (ihomAdjunction_isQuillenAdjunction_of_isCofibrant T).preservesTrivialCofibrations
        f hf) n f hf

end HomotopicalAlgebra.TensorPowerGeneratorMaps
