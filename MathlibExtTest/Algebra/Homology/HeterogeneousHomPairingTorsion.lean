/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneous
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Module.ZMod

/-!
# Torsion coefficients in Hom cochain units and comparison maps

The chain tensor unit over the integers has an actual degree-zero Hom cochain with
coefficient ZMod 4. Its counit construction evaluates to the nonzero coefficient three,
and the canonical lift to cycles retains that value. No flatness or projectivity of the
coefficient module is used.

Negating the chain source changes the value three to one. Doubling the coefficient changes
it to two. Applying both actual comparison maps gives two in either order.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open HomologicalComplex HomologicalComplex.LinearHomCochainPairingHeterogeneous

namespace HeterogeneousHomPairingTorsion

local instance : MonoidalCategory (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)

private abbrev K : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ)
private abbrev M : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 4)
private abbrev C : CochainComplex (ModuleCat.{0} ℤ) ℕ :=
  linearHomCochainComplex ℤ K M

private def unitTermIso : K.X 0 ≅ 𝟙_ (ModuleCat.{0} ℤ) :=
  singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{0} ℤ))

private def sample : K.X 0 := unitTermIso.inv.hom (3 : ℤ)
private def coefficientCast : 𝟙_ (ModuleCat.{0} ℤ) ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod 4) (1 : ZMod 4))
private def unitCochain : K.X 0 ⟶ M :=
  linearHomCochainUnitOfCounit ℤ K (𝟙 K) M coefficientCast

private theorem unitCochain_value : unitCochain.hom sample = (3 : ZMod 4) := by
  change coefficientCast.hom (unitTermIso.hom.hom (unitTermIso.inv.hom (3 : ℤ))) = _
  have h : unitTermIso.hom.hom (unitTermIso.inv.hom (3 : ℤ)) = (3 : ℤ) :=
    ConcreteCategory.congr_hom unitTermIso.inv_hom_id (3 : ℤ)
  rw [h]
  change (3 : ℤ) • (1 : ZMod 4) = 3
  decide

example : unitCochain.hom sample ≠ (0 : ZMod 4) := by
  rw [unitCochain_value]
  decide

example : (4 : ℤ) • (3 : ZMod 4) = 0 := by decide

private def cycleMap : 𝟙_ (ModuleCat.{0} ℤ) ⟶ C.cycles 0 :=
  linearHomCochainUnitOfCounitCycles ℤ K (𝟙 K) M coefficientCast
private def cycleValue (z : C.cycles 0) : ZMod 4 :=
  (show K.X 0 ⟶ M from (C.iCycles 0).hom z).hom sample

private theorem cycleValue_zero : cycleValue 0 = 0 := by
  simp only [cycleValue, map_zero]
  change (0 : K.X 0 ⟶ M).hom sample = 0
  rfl

private theorem cycleValue_one : cycleValue (cycleMap.hom (1 : ℤ)) = 3 := by
  have h := linearHomCochainUnitOfCounitCycles_i ℤ K (𝟙 K) M coefficientCast
  have hx := congrArg
    (fun f : 𝟙_ (ModuleCat.{0} ℤ) ⟶ C.X 0 => f.hom (1 : ℤ)) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  change (C.iCycles 0).hom (cycleMap.hom (1 : ℤ)) = (1 : ℤ) • unitCochain at hx
  rw [one_smul] at hx
  exact (congrArg (fun φ : K.X 0 ⟶ M => φ.hom sample) hx).trans unitCochain_value

example : cycleMap.hom (1 : ℤ) ≠ 0 := by
  intro h
  have hv := cycleValue_one
  rw [h, cycleValue_zero] at hv
  exact (by decide : (0 : ZMod 4) ≠ 3) hv

private def doubleCoefficient : M ⟶ M :=
  ModuleCat.ofHom (LinearMap.lsmul ℤ (ZMod 4) (2 : ℤ))
private def sourceMap : C ⟶ C :=
  linearHomCochainComparison ℤ (-𝟙 K) (𝟙 M)
private def coefficientMap : C ⟶ C :=
  linearHomCochainComparison ℤ (𝟙 K) doubleCoefficient

private theorem sourceMap_apply (φ : K.X 0 ⟶ M) :
    (sourceMap.f 0).hom φ = -φ := by
  simpa only [HomologicalComplex.neg_f_apply, HomologicalComplex.id_f,
    Preadditive.neg_comp, Category.id_comp, Category.comp_id] using!
    (linearHomCochainComparison_f_apply ℤ (-𝟙 K) (𝟙 M) 0 φ)

private theorem coefficientMap_apply (φ : K.X 0 ⟶ M) :
    (coefficientMap.f 0).hom φ = φ ≫ doubleCoefficient := by
  simpa only [HomologicalComplex.id_f, Category.id_comp] using!
    (linearHomCochainComparison_f_apply ℤ (𝟙 K) doubleCoefficient 0 φ)

private theorem sourceMap_value :
    ((sourceMap.f 0).hom unitCochain).hom sample = (1 : ZMod 4) := by
  have h := congrArg (fun φ : K.X 0 ⟶ M => φ.hom sample)
    (sourceMap_apply unitCochain)
  calc
    _ = (-unitCochain).hom sample := h
    _ = -(3 : ZMod 4) := by
      rw [ModuleCat.hom_neg, LinearMap.neg_apply, unitCochain_value]
    _ = 1 := by decide

private theorem coefficientMap_value :
    ((coefficientMap.f 0).hom unitCochain).hom sample = (2 : ZMod 4) := by
  have h := congrArg (fun φ : K.X 0 ⟶ M => φ.hom sample)
    (coefficientMap_apply unitCochain)
  calc
    _ = (unitCochain ≫ doubleCoefficient).hom sample := h
    _ = (2 : ℤ) • unitCochain.hom sample := rfl
    _ = 2 := by rw [unitCochain_value]; decide

example : ((sourceMap.f 0).hom unitCochain).hom sample ≠
    unitCochain.hom sample := by
  rw [sourceMap_value, unitCochain_value]
  decide

example : ((coefficientMap.f 0).hom unitCochain).hom sample ≠
    unitCochain.hom sample := by
  rw [coefficientMap_value, unitCochain_value]
  decide

private theorem comparison_routes :
    sourceMap.f 0 ≫ coefficientMap.f 0 = coefficientMap.f 0 ≫ sourceMap.f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (K.X 0 ⟶ M) at φ
  change (coefficientMap.f 0).hom ((sourceMap.f 0).hom φ) =
    (sourceMap.f 0).hom ((coefficientMap.f 0).hom φ)
  have h₁ : @Eq (K.X 0 ⟶ M)
      ((coefficientMap.f 0).hom ((sourceMap.f 0).hom φ))
      (((sourceMap.f 0).hom φ) ≫ doubleCoefficient) := by
    simpa only using! coefficientMap_apply ((sourceMap.f 0).hom φ)
  have hs : @Eq (K.X 0 ⟶ M) ((sourceMap.f 0).hom φ) (-φ) := by
    simpa only using! sourceMap_apply φ
  have h₂ := congrArg (fun ψ : K.X 0 ⟶ M => ψ ≫ doubleCoefficient) hs
  have h₃ : @Eq (K.X 0 ⟶ M) ((-φ) ≫ doubleCoefficient)
      (-(φ ≫ doubleCoefficient)) := Preadditive.neg_comp φ doubleCoefficient
  have hs' : @Eq (K.X 0 ⟶ M)
      ((sourceMap.f 0).hom ((coefficientMap.f 0).hom φ))
      (-((coefficientMap.f 0).hom φ)) := by
    simpa only using! sourceMap_apply ((coefficientMap.f 0).hom φ)
  have hc : @Eq (K.X 0 ⟶ M) ((coefficientMap.f 0).hom φ)
      (φ ≫ doubleCoefficient) := by
    simpa only using! coefficientMap_apply φ
  exact h₁.trans (h₂.trans (h₃.trans
    (hs'.trans (congrArg (fun ψ : K.X 0 ⟶ M => -ψ) hc)).symm))

example :
    (((sourceMap.f 0 ≫ coefficientMap.f 0).hom unitCochain).hom sample) =
      (2 : ZMod 4) := by
  change ((coefficientMap.f 0).hom ((sourceMap.f 0).hom unitCochain)).hom sample = 2
  have h := congrArg (fun φ : K.X 0 ⟶ M => φ.hom sample)
    (coefficientMap_apply ((sourceMap.f 0).hom unitCochain))
  calc
    _ = (((sourceMap.f 0).hom unitCochain) ≫ doubleCoefficient).hom sample := h
    _ = (2 : ℤ) • ((sourceMap.f 0).hom unitCochain).hom sample := rfl
    _ = 2 := by rw [sourceMap_value]; decide

example :
    (((coefficientMap.f 0 ≫ sourceMap.f 0).hom unitCochain).hom sample) =
      (2 : ZMod 4) := by
  rw [← comparison_routes]
  change ((coefficientMap.f 0).hom ((sourceMap.f 0).hom unitCochain)).hom sample = 2
  have h := congrArg (fun φ : K.X 0 ⟶ M => φ.hom sample)
    (coefficientMap_apply ((sourceMap.f 0).hom unitCochain))
  calc
    _ = (((sourceMap.f 0).hom unitCochain) ≫ doubleCoefficient).hom sample := h
    _ = (2 : ℤ) • ((sourceMap.f 0).hom unitCochain).hom sample := rfl
    _ = 2 := by rw [sourceMap_value]; decide

end HeterogeneousHomPairingTorsion
