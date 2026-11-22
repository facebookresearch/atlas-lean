/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.Basic
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepExternalAction
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.ExternalModulePresentation
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.OrderedTensorAlgebra

/-!
# The actual sphere module constructed from compatible one-step data

Both original object and morphism functions descend the derived full
tensor-power actions through Day convolution. The inverse one-step accessor
keeps the original degree-one unitor and complete index degree transport.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Spectra.Symmetric.OneStepSpectrum

local notation "I" => Operad.SmallFinBijGroupoid
local notation "idx" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : V}

/-- Compatible one-step data construct a module on the existing symmetric-spectrum carrier. -/
def module (X : OneStepSpectrum T) : SymmetricSpectrum (genericSphereDayMonoid T) :=
  X.externalData.toModule

/-- Every original compatible one-step map supplies the complete external-data map. -/
def externalMap {X Y : OneStepSpectrum T} (f : X ⟶ Y) : X.externalData ⟶ Y.externalData :=
  { map := f.map
    comm := fun a n => f.iterated_comm a.of.len n.of.len }

/-- The actual module map retains all original finite-index components and one-step naturality. -/
def moduleMap {X Y : OneStepSpectrum T} (f : X ⟶ Y) : X.module ⟶ Y.module :=
  DayFunctor.ExternalModule.Data.toModuleMap (externalMap f)

/-- The complete original one-step diagram is retained by the constructed module. -/
theorem module_diagram (X : OneStepSpectrum T) : X.module.X.functor = X.diagram := rfl

/-- The entire original natural transformation is retained by every constructed module morphism. -/
theorem moduleMap_components {X Y : OneStepSpectrum T} (f : X ⟶ Y) :
    (moduleMap f).hom.natTrans = f.map := rfl

/-- The complete object and morphism reconstruction is an actual functor. -/
def toModules : OneStepSpectrum T ⥤ SymmetricSpectrum (genericSphereDayMonoid T) where
  obj := module
  map := moduleMap
  map_id _ := by apply Mod.hom_ext; rfl
  map_comp _ _ := by apply Mod.hom_ext; rfl

/-- The actual degree-one coefficient and index transport extract the original one-step map. -/
abbrev oneStepOfExternal
    (d : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) : OneStep T where
  diagram := d.diagram
  bonding n :=
    ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ d.action.app (idx 1, idx n) ≫
      d.diagram.map (eqToHom (congrArg idx (Nat.one_add n)))

end CategoryTheory.Spectra.Symmetric.OneStepSpectrum
