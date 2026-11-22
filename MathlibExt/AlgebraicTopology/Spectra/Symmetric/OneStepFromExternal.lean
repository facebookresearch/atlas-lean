/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepRecovery

/-!
# The original one-step data recovered from all external sphere coefficients

The original degree-one action produces the one-step map. Every higher
coefficient and both finite actions are then reconstructed by ordered iteration.
All original external-data morphisms preserve those same one-step maps.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped CategoryTheory.MonObj ExternalProduct

namespace CategoryTheory.Spectra.Symmetric.OneStepSpectrum

local notation "I" => Operad.SmallFinBijGroupoid
local notation "idx" => Operad.SmallFinBijGroupoid.card

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : V}

/-- Every complete external sphere action produces the original compatible one-step data. -/
abbrev fromExternal (d : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) :
    OneStepSpectrum T where
  toOneStep := oneStepOfExternal d
  compatible := by
    intro A A' B B' f g
    have h : ((genericSphereSequence T).functor.map f ⊗ₘ d.diagram.map g) ≫
        d.action.app (A', B') = d.action.app (A, B) ≫ d.diagram.map (f ⊗ₘ g) := by
      simpa only [externalProductBifunctor_obj_map, Functor.comp_map,
        tensor_map, ← tensorHom_def] using! d.action.naturality ((f, g) : (A, B) ⟶ (A', B'))
    exact (congrArg (fun t =>
      ((genericSphereSequence T).functor.map f ⊗ₘ d.diagram.map g) ≫ t)
      (iterated_recovery d A'.of.len B'.of.len)).trans
      (h.trans (congrArg (fun t => t ≫ d.diagram.map (f ⊗ₘ g))
        (iterated_recovery d A.of.len B.of.len).symm))

/-- Every original external-data morphism preserves the recovered original one-step maps. -/
def fromExternalMap
    {d e : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X} (f : d ⟶ e) :
    fromExternal d ⟶ fromExternal e where
  map := f.map
  bonding_comm n := by
    let c := eqToHom (congrArg idx (Nat.one_add n))
    let first : (𝟙_ V ⊗ T) ⊗ d.diagram.obj (idx n) ⟶ d.diagram.obj (idx (1 + n)) :=
      d.action.app (idx 1, idx n)
    let second : (𝟙_ V ⊗ T) ⊗ e.diagram.obj (idx n) ⟶ e.diagram.obj (idx (1 + n)) :=
      e.action.app (idx 1, idx n)
    have hn := f.map.naturality c
    have hp : first ≫ f.map.app (idx (1 + n)) =
        ((𝟙_ V ⊗ T) ◁ f.map.app (idx n)) ≫ second := f.comm (idx 1) (idx n)
    have hx := (whisker_exchange (λ_ T).inv (f.map.app (idx n))).symm
    have h₁ := congrArg (fun t => ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ first ≫ t) hn
    have h₂ := congrArg (fun t => ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ t ≫ e.diagram.map c) hp
    have h₃ := congrArg (fun t => t ≫ second ≫ e.diagram.map c) hx
    have h₁' : ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ first ≫ d.diagram.map c ≫
        f.map.app (idx (n + 1)) = ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ first ≫
        f.map.app (idx (1 + n)) ≫ e.diagram.map c := by
      simpa only [Category.assoc] using! h₁
    have h₂' : ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ first ≫
        f.map.app (idx (1 + n)) ≫ e.diagram.map c =
        ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ ((𝟙_ V ⊗ T) ◁ f.map.app (idx n)) ≫
        second ≫ e.diagram.map c := by
      simpa only [Category.assoc] using! h₂
    have h₃' : ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ ((𝟙_ V ⊗ T) ◁ f.map.app (idx n)) ≫
        second ≫ e.diagram.map c =
        (T ◁ f.map.app (idx n)) ≫ ((λ_ T).inv ▷ e.diagram.obj (idx n)) ≫ second ≫ e.diagram.map c := by
      simpa only [Category.assoc] using! h₃
    have hd : (fromExternal d).bonding n ≫ f.map.app (idx (n + 1)) =
        ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ first ≫ d.diagram.map c ≫
        f.map.app (idx (n + 1)) :=
      (Category.assoc ((λ_ T).inv ▷ d.diagram.obj (idx n)) (first ≫ d.diagram.map c)
        (f.map.app (idx (n + 1)))).trans
        (congrArg (fun t => ((λ_ T).inv ▷ d.diagram.obj (idx n)) ≫ t)
          (Category.assoc first (d.diagram.map c) (f.map.app (idx (n + 1)))))
    exact (h₁'.trans (h₂'.trans h₃')).symm.trans hd.symm

/-- The original compatible one-step data give their complete external-action functor. -/
def toExternalFunctor : OneStepSpectrum T ⥤
    DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X where
  obj := externalData
  map := externalMap
  map_id _ := by apply DayFunctor.ExternalModule.Data.Hom.ext; rfl
  map_comp _ _ := by apply DayFunctor.ExternalModule.Data.Hom.ext; rfl

/-- Complete external actions give an actual inverse one-step functor. -/
def fromExternalFunctor : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X ⥤
    OneStepSpectrum T where
  obj := fromExternal
  map := fromExternalMap
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- Every full original tensor-power coefficient is retained by one-step reconstruction. -/
theorem fromExternal_iterated
    (d : DayFunctor.ExternalModule.Data (genericSphereDayMonoid T).X) (A B : I) :
    (fromExternal d).toOneStep.iterated A.of.len B.of.len = d.action.app (A, B) :=
  iterated_recovery d A.of.len B.of.len

end CategoryTheory.Spectra.Symmetric.OneStepSpectrum
