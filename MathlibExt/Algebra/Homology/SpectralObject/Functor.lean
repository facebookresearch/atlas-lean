/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import MathlibExt.Algebra.Homology.SpectralSequence.Functor
public import MathlibExt.Algebra.Homology.SpectralObjectPageMap

import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Exact coefficient transport of spectral objects

Apply an exact additive functor to the interval functors and connecting
transformations of a spectral object. The comparisons use the existing
kernel, cokernel and short-complex homology preservation APIs. The native
sequence keeps its original recipe and successor homology isomorphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open CategoryTheory.Abelian CategoryTheory.Abelian.SpectralObject

universe v u vD uD vι t k

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]

section Objects

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {ι : Type t} [Category.{vι} ι]

private lemma preservesExact {A B Z : C} (f : A ⟶ B) (g : B ⟶ Z)
    (h : (mk₂ f g).Exact) : (mk₂ (F.map f) (F.map g)).Exact :=
  ((h.exact 0).map F).exact_toComposableArrows

/-- Apply an exact additive functor to every interval and connecting map.
All three exactness laws are obtained from those of the source. -/
def mapSpectralObject (X : SpectralObject C ι) : SpectralObject D ι where
  H n := X.H n ⋙ F
  δ' n₀ n₁ hn := whiskerRight (X.δ' n₀ n₁ hn) F
  exact₁' n₀ n₁ hn I := by exact preservesExact F _ _ (X.exact₁' n₀ n₁ hn I)
  exact₂' n I := by exact preservesExact F _ _ (X.exact₂' n I)
  exact₃' n₀ n₁ hn I := by exact preservesExact F _ _ (X.exact₃' n₀ n₁ hn I)

/-- The mapped interval functor is the original functor followed by F. -/
@[simp]
theorem mapSpectralObject_H (X : SpectralObject C ι) (n : ℤ) :
    (F.mapSpectralObject X).H n = X.H n ⋙ F := rfl

/-- The interval object is exactly the image of the original interval. -/
@[simp]
theorem mapSpectralObject_H_obj (X : SpectralObject C ι) (n : ℤ)
    (I : ComposableArrows ι 1) :
    ((F.mapSpectralObject X).H n).obj I = F.obj ((X.H n).obj I) := rfl

/-- Every indexing map is exactly the mapped original indexing map. -/
@[simp]
theorem mapSpectralObject_H_map (X : SpectralObject C ι) (n : ℤ)
    {I J : ComposableArrows ι 1} (f : I ⟶ J) :
    ((F.mapSpectralObject X).H n).map f = F.map ((X.H n).map f) := rfl

/-- The connecting map is exactly the mapped original connecting map. -/
@[simp]
theorem mapSpectralObject_δ (X : SpectralObject C ι)
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l)
    (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    (F.mapSpectralObject X).δ f g n₀ n₁ hn = F.map (X.δ f g n₀ n₁ hn) := rfl

/-- Apply the exact functor to an actual spectral-object morphism. -/
def mapSpectralObjectHom {X Y : SpectralObject C ι} (φ : X ⟶ Y) :
    F.mapSpectralObject X ⟶ F.mapSpectralObject Y where
  hom n := whiskerRight (φ.hom n) F
  comm := by
    intro n₀ n₁ hn i j l f g
    change F.map (X.δ f g n₀ n₁ hn) ≫ F.map ((φ.hom n₁).app (mk₁ f)) =
      F.map ((φ.hom n₀).app (mk₁ g)) ≫ F.map (Y.δ f g n₀ n₁ hn)
    rw [← F.map_comp, φ.comm, F.map_comp]

/-- A mapped spectral morphism has exactly the mapped interval component. -/
@[simp]
theorem mapSpectralObjectHom_hom_app {X Y : SpectralObject C ι}
    (φ : X ⟶ Y) (n : ℤ) (I : ComposableArrows ι 1) :
    ((F.mapSpectralObjectHom φ).hom n).app I = F.map ((φ.hom n).app I) := rfl

/-- Exact coefficient transport is a functor on spectral objects. -/
def spectralObjectFunctor : SpectralObject C ι ⥤ SpectralObject D ι where
  obj := F.mapSpectralObject
  map := F.mapSpectralObjectHom
  map_id X := by
    apply SpectralObject.Hom.ext
    funext n
    apply NatTrans.ext
    funext I
    simp only [mapSpectralObjectHom_hom_app, SpectralObject.id_hom, NatTrans.id_app,
      F.map_id]
    rfl
  map_comp φ ψ := by
    apply SpectralObject.Hom.ext
    funext n
    apply NatTrans.ext
    funext I
    simp only [mapSpectralObjectHom_hom_app, SpectralObject.comp_hom,
      NatTrans.comp_app, F.map_comp]

end Objects

section Comparisons

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
private lemma mapHomologyIso_π (S : ShortComplex C) :
    (S.map (F)).homologyπ ≫
        (S.mapHomologyIso
          (F)).hom =
      (S.mapCyclesIso
        (F)).hom ≫
        (F).map S.homologyπ := by
  let U := F
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq U, h.mapCyclesIso_eq U]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, (h.map U).homologyπ_comp_homologyIso_hom]
  change ((h.map U).cyclesIso.hom ≫ U.map h.π) ≫ U.map h.homologyIso.inv =
    ((h.map U).cyclesIso.hom ≫ U.map h.cyclesIso.inv) ≫ U.map S.homologyπ
  simp only [Category.assoc, ← U.map_comp]
  rw [h.π_comp_homologyIso_inv]

private lemma mapHomologyIso_inv_π (S : ShortComplex C) :
    (F).map S.homologyπ ≫
        (S.mapHomologyIso
          (F)).inv =
      (S.mapCyclesIso
        (F)).inv ≫
        (S.map (F)).homologyπ := by
  let U := F
  apply (cancel_epi (S.mapCyclesIso U).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← mapHomologyIso_π F S,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma mapCyclesIso_inv_iCycles
    (S : ShortComplex C) :
    (S.mapCyclesIso
      (F)).inv ≫
        (S.map (F)).iCycles =
      (F).map S.iCycles := by
  let U := F
  apply (cancel_epi (S.mapCyclesIso U).hom).1
  rw [Iso.hom_inv_id_assoc]
  exact (S.mapCyclesIso_hom_iCycles U).symm


private lemma mapHomologyIso_hom_ι
    (S : ShortComplex C) :
    (S.mapHomologyIso
      (F)).hom ≫
      (F).map S.homologyι =
    (S.map (F)).homologyι ≫
      (S.mapOpcyclesIso
        (F)).hom := by
  let U := F
  let h := S.rightHomologyData
  rw [← S.mapHomologyIso'_eq_mapHomologyIso U,
    h.mapHomologyIso'_eq U, h.mapOpcyclesIso_eq U]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [Category.assoc, ← U.map_comp, h.homologyIso_inv_comp_homologyι,
    U.map_comp, ← Category.assoc]
  change ((h.map U).homologyIso.hom ≫ (h.map U).ι) ≫ U.map h.opcyclesIso.inv = _
  rw [(h.map U).homologyIso_hom_comp_ι, Category.assoc]

private lemma mapHomologyIso_inv_ι
    (S : ShortComplex C) :
    (S.mapHomologyIso
      (F)).inv ≫
      (S.map (F)).homologyι =
    (F).map S.homologyι ≫
      (S.mapOpcyclesIso
        (F)).inv := by
  let U := F
  apply (cancel_epi (S.mapHomologyIso U).hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, mapHomologyIso_hom_ι,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma mapOpcyclesIso_inv_pOpcycles
    (S : ShortComplex C) :
    (F).map S.pOpcycles ≫
      (S.mapOpcyclesIso
        (F)).inv =
    (S.map (F)).pOpcycles := by
  let U := F
  exact (S.rightHomologyData.map U).p_comp_opcyclesIso_inv

section Intervals

variable {ι : Type t} [Category.{vι} ι]
  (Y : SpectralObject C ι)

/-- The canonical comparison of the spectral cycles with the cycles
of the mapped spectral object. -/
def mapSpectralObjectCyclesIso {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    (F).obj
      (Y.cycles f g n) ≅ (F.mapSpectralObject Y).cycles f g n :=
  PreservesKernel.iso (F)
    (Y.δ f g n (n + 1))

/-- The cycle comparison preserves the original inclusion. -/
@[reassoc]
theorem mapSpectralObjectCyclesIso_hom_iCycles
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    (F.mapSpectralObjectCyclesIso Y f g n).hom ≫
        (F.mapSpectralObject Y).iCycles f g n =
      (F).map
        (Y.iCycles f g n) := by
  apply (cancel_epi (F.mapSpectralObjectCyclesIso Y f g n).inv).1
  simp only [Iso.inv_hom_id_assoc]
  exact (PreservesKernel.iso_inv_ι
    (F)
    (Y.δ f g n (n + 1))).symm

/-- The canonical comparison of spectral opcycles under exact transport. -/
def mapSpectralObjectOpcyclesIso {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    (F).obj
      (Y.opcycles f g n) ≅ (F.mapSpectralObject Y).opcycles f g n :=
  PreservesCokernel.iso (F)
    (Y.δ f g (n - 1) n)

/-- The opcycle comparison preserves the original projection. -/
@[reassoc]
theorem mapSpectralObjectOpcyclesIso_π
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    ((F)).map (Y.pOpcycles f g n) ≫
        (F.mapSpectralObjectOpcyclesIso Y f g n).hom =
      (F.mapSpectralObject Y).pOpcycles f g n :=
  PreservesCokernel.π_iso_hom
    (F) (Y.δ f g (n - 1) n)

/-- The canonical homology comparison identifies the image of an `E` object
with the `E` object of the transported spectral object. -/
def mapSpectralObjectEIso
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F).obj
        (Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≅
      (F.mapSpectralObject Y).E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  ((Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).mapHomologyIso
    (F)).symm

/-- Exact transport preserves every indexing map of spectral cycles. -/
@[reassoc]
theorem mapSpectralObjectCyclesIso_map
    {i j l i' j' l' : ι} (f : i ⟶ j) (g : j ⟶ l)
    (f' : i' ⟶ j') (g' : j' ⟶ l') (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    F.map (Y.cyclesMap f g f' g' α n) ≫
        (F.mapSpectralObjectCyclesIso Y f' g' n).hom =
      (F.mapSpectralObjectCyclesIso Y f g n).hom ≫
        (F.mapSpectralObject Y).cyclesMap f g f' g' α n := by
  let β : mk₁ g ⟶ mk₁ g' := homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)
  apply (cancel_mono ((F.mapSpectralObject Y).iCycles f' g' n)).1
  rw [Category.assoc, F.mapSpectralObjectCyclesIso_hom_iCycles Y f' g' n,
    ← F.map_comp, Y.cyclesMap_i f g f' g' α β n rfl, F.map_comp,
    Category.assoc, (F.mapSpectralObject Y).cyclesMap_i f g f' g' α β n rfl,
    ← Category.assoc, F.mapSpectralObjectCyclesIso_hom_iCycles Y f g n]
  rfl

/-- Exact transport preserves every indexing map of spectral opcycles. -/
@[reassoc]
theorem mapSpectralObjectOpcyclesIso_map
    {i j l i' j' l' : ι} (f : i ⟶ j) (g : j ⟶ l)
    (f' : i' ⟶ j') (g' : j' ⟶ l') (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    F.map (Y.opcyclesMap f g f' g' α n) ≫
        (F.mapSpectralObjectOpcyclesIso Y f' g' n).hom =
      (F.mapSpectralObjectOpcyclesIso Y f g n).hom ≫
        (F.mapSpectralObject Y).opcyclesMap f g f' g' α n := by
  let β : mk₁ f ⟶ mk₁ f' := homMk₁ (α.app 0) (α.app 1) (naturality' α 0 1)
  apply (cancel_epi (F.map (Y.pOpcycles f g n))).1
  rw [← Category.assoc, ← F.map_comp, Y.p_opcyclesMap f g f' g' α β n rfl,
    F.map_comp, Category.assoc, F.mapSpectralObjectOpcyclesIso_π Y f' g' n,
    ← Category.assoc, F.mapSpectralObjectOpcyclesIso_π Y f g n,
    (F.mapSpectralObject Y).p_opcyclesMap f g f' g' α β n rfl]
  rfl


private lemma mapSpectralObjectCyclesIso_cyclesIso
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F).map
        (Y.cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv ≫
      ((Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).mapCyclesIso
        (F)).inv =
    (F.mapSpectralObjectCyclesIso Y f₁ f₂ n₁).hom ≫
      ((F.mapSpectralObject Y).cyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv := by
  let U := F
  let S := Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  apply (cancel_mono (S.map U).iCycles).1
  rw [Category.assoc, mapCyclesIso_inv_iCycles, ← U.map_comp,
    Y.cyclesIso_inv_i f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂]
  change U.map (Y.iCycles f₁ f₂ n₁) =
    ((F.mapSpectralObjectCyclesIso Y f₁ f₂ n₁).hom ≫
      ((F.mapSpectralObject Y).cyclesIso
        f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).inv) ≫
      ((F.mapSpectralObject Y).shortComplex
        f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).iCycles
  rw [Category.assoc,
    (F.mapSpectralObject Y).cyclesIso_inv_i f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    F.mapSpectralObjectCyclesIso_hom_iCycles Y]

/-- The canonical `E` comparison preserves its cycle quotient projection. -/
@[reassoc]
theorem mapSpectralObjectEIso_πE
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F).map
        (Y.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      (F.mapSpectralObjectEIso Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    (F.mapSpectralObjectCyclesIso Y f₁ f₂ n₁).hom ≫
      (F.mapSpectralObject Y).πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  let U := F
  dsimp only [πE, mapSpectralObjectEIso, Iso.symm_hom]
  rw [U.map_comp, Category.assoc, mapHomologyIso_inv_π,
    ← Category.assoc,
    mapSpectralObjectCyclesIso_cyclesIso F Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    Category.assoc]
  rfl


private lemma mapSpectralObjectOpcyclesIso_opcyclesIso
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    ((Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).mapOpcyclesIso
      (F)).inv ≫
      ((F.mapSpectralObject Y).opcyclesIso
        f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
    (F).map
      (Y.opcyclesIso f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (F.mapSpectralObjectOpcyclesIso Y f₂ f₃ n₁).hom := by
  let U := F
  let S := Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  apply (cancel_epi (U.map S.pOpcycles)).1
  rw [← Category.assoc, mapOpcyclesIso_inv_pOpcycles]
  change ((F.mapSpectralObject Y).shortComplex
      f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).pOpcycles ≫
      ((F.mapSpectralObject Y).opcyclesIso
        f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom = _
  rw [(F.mapSpectralObject Y).p_opcyclesIso_hom
      f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    ← Category.assoc, ← U.map_comp,
    Y.p_opcyclesIso_hom f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    F.mapSpectralObjectOpcyclesIso_π Y]

/-- The canonical `E` comparison preserves its opcycle inclusion. -/
@[reassoc]
theorem mapSpectralObjectEIso_ιE
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F.mapSpectralObjectEIso Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
      (F.mapSpectralObject Y).ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
    (F).map
      (Y.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (F.mapSpectralObjectOpcyclesIso Y f₂ f₃ n₁).hom := by
  let U := F
  let S := Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  dsimp only [ιE, mapSpectralObjectEIso, Iso.symm_hom]
  rw [← Category.assoc]
  change ((S.mapHomologyIso U).inv ≫ (S.map U).homologyι) ≫
      ((F.mapSpectralObject Y).opcyclesIso
        f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom = _
  rw [mapHomologyIso_inv_ι F S, Category.assoc,
    mapSpectralObjectOpcyclesIso_opcyclesIso F Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂,
    ← Category.assoc, ← U.map_comp]


/-- The opcycle comparison retains its canonical map into interval homology. -/
@[reassoc]
theorem mapSpectralObjectOpcyclesIso_fromOpcycles
    {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (fg : i ⟶ l) (hfg : f ≫ g = fg)
    (n : ℤ) :
    (F.mapSpectralObjectOpcyclesIso Y f g n).hom ≫
      (F.mapSpectralObject Y).fromOpcycles f g fg hfg n =
    (F).map
      (Y.fromOpcycles f g fg hfg n) := by
  let U := F
  apply (cancel_epi (U.map (Y.pOpcycles f g n))).1
  rw [← Category.assoc, F.mapSpectralObjectOpcyclesIso_π Y,
    (F.mapSpectralObject Y).p_fromOpcycles f g fg hfg n,
    ← U.map_comp, Y.p_fromOpcycles f g fg hfg n]
  rfl

/-- Exact transport retains the spectral cycles-to-opcycles morphism used by
all page differentials. -/
@[reassoc]
theorem mapSpectralObjectCyclesIso_Ψ
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    (F).map
      (Y.Ψ f₁ f₂ f₃ n₀ n₁ hn₁) ≫
      (F.mapSpectralObjectOpcyclesIso Y f₁ f₂ n₁).hom =
    (F.mapSpectralObjectCyclesIso Y f₂ f₃ n₀).hom ≫
      (F.mapSpectralObject Y).Ψ f₁ f₂ f₃ n₀ n₁ hn₁ := by
  let U := F
  apply (cancel_mono ((F.mapSpectralObject Y).fromOpcycles
    f₁ f₂ (f₁ ≫ f₂) rfl n₁)).1
  rw [Category.assoc,
    F.mapSpectralObjectOpcyclesIso_fromOpcycles Y f₁ f₂ (f₁ ≫ f₂) rfl n₁,
    ← U.map_comp, Y.Ψ_fromOpcycles f₁ f₂ f₃ (f₁ ≫ f₂) rfl n₀ n₁ hn₁,
    U.map_comp, Category.assoc,
    (F.mapSpectralObject Y).Ψ_fromOpcycles
      f₁ f₂ f₃ (f₁ ≫ f₂) rfl n₀ n₁ hn₁,
    ← Category.assoc, F.mapSpectralObjectCyclesIso_hom_iCycles Y]
  rfl

/-- The canonical `E` comparisons commute with the actual spectral
object differential, before any page or first-quadrant specialization. -/
@[reassoc]
theorem mapSpectralObjectEIso_d
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    (F).map
      (Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃) ≫
      (F.mapSpectralObjectEIso Y f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃).hom =
    (F.mapSpectralObjectEIso Y f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂).hom ≫
      (F.mapSpectralObject Y).d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ := by
  let U := F
  let Z := F.mapSpectralObject Y
  apply (cancel_epi (U.map (Y.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂))).1
  apply (cancel_mono (Z.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃)).1
  calc
    (U.map (Y.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂) ≫
        (U.map (Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃) ≫
          (F.mapSpectralObjectEIso Y f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃).hom)) ≫
        Z.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ =
      U.map (Y.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂ ≫
        Y.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
          Y.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃) ≫
        (F.mapSpectralObjectOpcyclesIso Y f₂ f₃ n₂).hom := by
          simp only [U, Z, Functor.map_comp, Category.assoc,
            F.mapSpectralObjectEIso_ιE Y f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃]
    _ = U.map (Y.Ψ f₂ f₃ f₄ n₁ n₂ hn₂) ≫
        (F.mapSpectralObjectOpcyclesIso Y f₂ f₃ n₂).hom := by
          rw [Y.πE_d_ιE f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]
    _ = (F.mapSpectralObjectCyclesIso Y f₃ f₄ n₁).hom ≫
        Z.Ψ f₂ f₃ f₄ n₁ n₂ hn₂ :=
          F.mapSpectralObjectCyclesIso_Ψ Y f₂ f₃ f₄ n₁ n₂ hn₂
    _ = (U.map (Y.πE f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂) ≫
        ((F.mapSpectralObjectEIso Y f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂).hom ≫
          Z.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃)) ≫
        Z.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃ := by
          rw [← Z.πE_d_ιE f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]
          simpa only [U, Z, Category.assoc] using
            congrArg (fun a => a ≫
              Z.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
                Z.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃)
              (F.mapSpectralObjectEIso_πE Y
                f₃ f₄ f₅ n₀ n₁ n₂ hn₁ hn₂).symm

/-- The `E` comparison commutes with every indexing three-arrow map. -/
@[reassoc]
theorem mapSpectralObjectEIso_map
    {i₀ i₁ i₂ i₃ j₀ j₁ j₂ j₃ : ι}
    (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (g₁ : j₀ ⟶ j₁) (g₂ : j₁ ⟶ j₂) (g₃ : j₂ ⟶ j₃)
    (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ g₁ g₂ g₃)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F).map
        (Y.map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂) ≫
        (F.mapSpectralObjectEIso Y g₁ g₂ g₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      (F.mapSpectralObjectEIso Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (F.mapSpectralObject Y).map f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂ := by
  exact ShortComplex.mapHomologyIso_inv_naturality
    (Y.shortComplexMap f₁ f₂ f₃ g₁ g₂ g₃ α n₀ n₁ n₂ hn₁ hn₂)
    (F)


end Intervals




section MorphismNaturality

variable {ι : Type t} [Category.{vι} ι] {X Y : SpectralObject C ι}

/-- The canonical E comparison is natural for actual spectral morphisms. -/
@[reassoc]
theorem mapSpectralObjectEIso_naturality (φ : X ⟶ Y)
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    F.map (φ.EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (F.mapSpectralObjectEIso Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      (F.mapSpectralObjectEIso X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (F.mapSpectralObjectHom φ).EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  ShortComplex.mapHomologyIso_inv_naturality
    (φ.shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) F

end MorphismNaturality

end Comparisons

section Pages

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject C ι)
  (data : SpectralSequenceDataCore ι c r₀)

/-- The canonical comparison at every object of a raw spectral page. -/
def mapSpectralObjectPageXIso (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (F).obj
      (Abelian.SpectralObject.SpectralSequence.pageX Y data r x hr) ≅
    Abelian.SpectralObject.SpectralSequence.pageX (F.mapSpectralObject Y) data r x hr :=
  F.mapSpectralObjectEIso Y
    (homOfLE (data.le₀₁ r x hr)) (homOfLE (data.le₁₂ x))
    (homOfLE (data.le₂₃ r x hr))
    (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) (by omega)

/-- The page comparison commutes with the canonical change of presentation
as an `E` object, including all degree and index equality casts. -/
@[reassoc]
theorem mapSpectralObjectPageXIso_presented
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r x hr) (h₁ : i₁ = data.i₁ x)
    (h₂ : i₂ = data.i₂ x) (h₃ : i₃ = data.i₃ r x hr)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg x)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F.mapSpectralObjectPageXIso Y data r hr x).hom ≫
      (Abelian.SpectralObject.SpectralSequence.pageXIso (F.mapSpectralObject Y) data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom =
    (F).map
      (Abelian.SpectralObject.SpectralSequence.pageXIso Y data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom ≫
      (F.mapSpectralObjectEIso Y
        (homOfLE (data.le₀₁' r hr x h₀ h₁)) (homOfLE (data.le₁₂' x h₁ h₂))
        (homOfLE (data.le₂₃' r hr x h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂).hom := by
  subst h₀ h₁ h₂ h₃ h
  obtain rfl : n₀ = data.deg x - 1 := by omega
  obtain rfl : n₂ = data.deg x + 1 := by omega
  simp only [Abelian.SpectralObject.SpectralSequence.pageXIso, mapSpectralObjectPageXIso,
    eqToIso_refl, Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]

/-- Inverse presentation changes also commute with the canonical page
comparison. -/
@[reassoc]
theorem mapSpectralObjectPageXIso_presented_inv
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r x hr) (h₁ : i₁ = data.i₁ x)
    (h₂ : i₂ = data.i₂ x) (h₃ : i₃ = data.i₃ r x hr)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg x)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F).map
      (Abelian.SpectralObject.SpectralSequence.pageXIso Y data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      (F.mapSpectralObjectPageXIso Y data r hr x).hom =
    (F.mapSpectralObjectEIso Y
      (homOfLE (data.le₀₁' r hr x h₀ h₁)) (homOfLE (data.le₁₂' x h₁ h₂))
      (homOfLE (data.le₂₃' r hr x h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂).hom ≫
      (Abelian.SpectralObject.SpectralSequence.pageXIso (F.mapSpectralObject Y) data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv := by
  let U := F
  apply (cancel_mono
    (Abelian.SpectralObject.SpectralSequence.pageXIso (F.mapSpectralObject Y) data r hr x
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [F.mapSpectralObjectPageXIso_presented Y data r hr x
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂,
    ← Category.assoc, ← U.map_comp, Iso.inv_hom_id,
    U.map_id, Category.id_comp]


/-- Every raw page differential commutes with the canonical object
comparisons. The statement includes the zero maps outside the shape relation. -/
@[reassoc]
theorem mapSpectralObjectPageXIso_d
    (r : ℤ) (hr : r₀ ≤ r) (x y : κ) :
    (F).map
      (Abelian.SpectralObject.SpectralSequence.pageD Y data r x y hr) ≫
      (F.mapSpectralObjectPageXIso Y data r hr y).hom =
    (F.mapSpectralObjectPageXIso Y data r hr x).hom ≫
      Abelian.SpectralObject.SpectralSequence.pageD (F.mapSpectralObject Y) data r x y hr := by
  let U := F
  by_cases hxy : (c r).Rel x y
  · have hCast := F.mapSpectralObjectPageXIso_presented_inv Y data r hr y
      (data.i₀ r y hr) (data.i₁ y) (data.i₀ r x hr) (data.i₁ x)
      rfl rfl (data.hc₀₂ r x y hxy hr) (data.hc₁₃ r x y hxy hr)
      (data.deg x) (data.deg x + 1) (data.deg x + 2)
      (data.hc r x y hxy hr) rfl (by omega)
    have hD := F.mapSpectralObjectEIso_d Y
      (homOfLE (data.le₀₁ r y hr))
      (homOfLE (data.le₁₂' y rfl (data.hc₀₂ r x y hxy hr)))
      (homOfLE (data.le₀₁ r x hr)) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r x hr))
      (data.deg x - 1) (data.deg x) (data.deg x + 1) (data.deg x + 2)
      (by omega) rfl (by omega)
    dsimp only [Abelian.SpectralObject.SpectralSequence.pageD]
    rw [dite_eq_left hxy, dite_eq_left hxy, U.map_comp, Category.assoc, hCast,
      ← Category.assoc, hD, Category.assoc]
    rfl
  · simp only [Abelian.SpectralObject.SpectralSequence.pageD, dite_eq_right hxy, Functor.map_zero,
      zero_comp, comp_zero]

/-- The canonical object comparisons assemble into a page-complex
isomorphism, before requiring the successor-page support conditions. -/
def mapSpectralObjectPageIso (r : ℤ) (hr : r₀ ≤ r) :
    ((F).mapHomologicalComplex
      (c r)).obj (Abelian.SpectralObject.SpectralSequence.page Y data r hr) ≅
    Abelian.SpectralObject.SpectralSequence.page (F.mapSpectralObject Y) data r hr :=
  HomologicalComplex.Hom.isoOfComponents
    (F.mapSpectralObjectPageXIso Y data r hr)
    (fun x y _ => (F.mapSpectralObjectPageXIso_d Y data r hr x y).symm)

/-- The page-complex comparison has exactly the canonical `E` comparison
as each component. -/
@[simp]
theorem mapSpectralObjectPageIso_hom_f (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (F.mapSpectralObjectPageIso Y data r hr).hom.f x =
      (F.mapSpectralObjectPageXIso Y data r hr x).hom := rfl

end Pages


section SupportedPages

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject C ι)
  (data : SpectralSequenceDataCore ι c r₀)
  [Y.HasSpectralSequence data]

/-- Exact transport preserves both boundary-vanishing conditions of the
source spectral sequence. -/
instance mapSpectralObject_hasSpectralSequence :
    (F.mapSpectralObject Y).HasSpectralSequence data where
  isZero_H_obj_mk₁_i₀_le r r' x hx n hn hrr' hr :=
    (F).map_isZero
      (Y.isZero_H_obj_mk₁_i₀_le data r r' hrr' hr x hx n hn)
  isZero_H_obj_mk₁_i₃_le r r' x hx n hn hrr' hr :=
    (F).map_isZero
      (Y.isZero_H_obj_mk₁_i₃_le data r r' hrr' hr x hx n hn)


unseal spectralSequence in
/-- The canonical comparison on the actual supported spectral page. -/
def mapSpectralObjectSpectralSequencePageIso (r : ℤ) (hr : r₀ ≤ r) :
    ((F).mapHomologicalComplex
      (c r)).obj ((Y.spectralSequence data).page r hr) ≅
    ((F.mapSpectralObject Y).spectralSequence data).page r hr :=
  F.mapSpectralObjectPageIso Y data r hr

unseal spectralSequence in
/-- The supported page isomorphism retains every canonical object comparison. -/
@[simp]
theorem mapSpectralObjectSpectralSequencePageIso_hom_f
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (F.mapSpectralObjectSpectralSequencePageIso Y data r hr).hom.f x =
      (F.mapSpectralObjectPageXIso Y data r hr x).hom := rfl

unseal spectralSequence in
/-- Exact transport preserves the canonical E-window presentation of every
supported page, including all original index and degree equality casts. -/
@[reassoc]
theorem mapSpectralObjectSpectralSequencePageIso_presented
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r x hr) (h₁ : i₁ = data.i₁ x)
    (h₂ : i₂ = data.i₂ x) (h₃ : i₃ = data.i₃ r x hr)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg x)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F.mapSpectralObjectSpectralSequencePageIso Y data r hr).hom.f x ≫
      ((F.mapSpectralObject Y).spectralSequencePageXIso data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom =
    F.map ((Y.spectralSequencePageXIso data r hr x
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom) ≫
      (F.mapSpectralObjectEIso Y
        (homOfLE (data.le₀₁' r hr x h₀ h₁))
        (homOfLE (data.le₁₂' x h₁ h₂))
        (homOfLE (data.le₂₃' r hr x h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂).hom := by
  simpa only [mapSpectralObjectSpectralSequencePageIso,
    spectralSequencePageXIso, mapSpectralObjectPageIso_hom_f, spectralSequence,
    Functor.mapHomologicalComplex_obj_X] using
    F.mapSpectralObjectPageXIso_presented Y data r hr x i₀ i₁ i₂ i₃
      h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂

end SupportedPages



section FixedPageNaturality

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  {X Y : SpectralObject C ι}
  (data : SpectralSequenceDataCore ι c r₀)

/-- Exact transport is natural for the actual complete-spectral-object
fixed-page maps, before any support assumptions. -/
@[reassoc]
theorem mapSpectralObjectPageIso_naturality (φ : X ⟶ Y)
    (r : ℤ) (hr : r₀ ≤ r) :
    (F.mapHomologicalComplex (c r)).map (φ.pageMap data r hr) ≫
        (F.mapSpectralObjectPageIso Y data r hr).hom =
      (F.mapSpectralObjectPageIso X data r hr).hom ≫
        (F.mapSpectralObjectHom φ).pageMap data r hr := by
  ext x
  exact F.mapSpectralObjectEIso_naturality φ
    (homOfLE (data.le₀₁ r x hr)) (homOfLE (data.le₁₂ x))
    (homOfLE (data.le₂₃ r x hr))
    (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) (by omega)

end FixedPageNaturality
section PageHomologyData

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)
  [Y.HasSpectralSequence data]

/-- The actual kernel/cokernel homology data used for every successor page,
with the canonical predecessor and successor positions, including boundaries. -/
private def pageHomologyData (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀ ≤ r) (x : κ) :
    (((Y.spectralSequence data).page r hr).sc x).HomologyData :=
  Y.spectralSequenceHomologyData data r r' hrr' hr
    ((c r).prev x) x ((c r).next x) rfl rfl
    (data.i₀ r' x (by omega)) (data.i₀ r x hr) (data.i₁ x) (data.i₂ x)
    (data.i₃ r x hr) (data.i₃ r' x (by omega))
    rfl rfl rfl rfl rfl rfl
    (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl (by omega) rfl



unseal spectralSequence in
private theorem spectralSequence_iso_eq_pageHomologyData
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    (Y.spectralSequence data).iso r r' x hrr' hr =
      (pageHomologyData Y data r r' hrr' hr x).left.homologyIso := by
  simp only [spectralSequence, Abelian.SpectralObject.SpectralSequence.homologyIso,
    Abelian.SpectralObject.SpectralSequence.homologyIso', pageHomologyData,
    spectralSequenceHomologyData,
    Abelian.SpectralObject.SpectralSequence.pageXIso, eqToIso_refl, Iso.refl_symm]
  exact Iso.trans_refl _


unseal spectralSequence in
private theorem pageHomologyData_left_i
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    (pageHomologyData Y data r r' hrr' hr x).left.i =
      Y.mapFourδ₁Toδ₀'
        (data.i₀ r' x (by omega)) (data.i₀ r x hr)
        (data.i₁ x) (data.i₂ x) (data.i₃ r x hr)
        (data.i₀_le r r' x hrr' hr) (data.le₀₁ r x hr)
        (data.le₁₂ x) (data.le₂₃ r x hr)
        (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl := by
  dsimp only [pageHomologyData]
  rw [@spectralSequenceHomologyData_left_i]
  simp only [spectralSequencePageXIso, Abelian.SpectralObject.SpectralSequence.pageXIso,
    eqToIso_refl, Iso.refl_inv]
  exact Category.comp_id _

unseal spectralSequence in
private theorem pageHomologyData_left_π
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    (pageHomologyData Y data r r' hrr' hr x).left.π =
      Y.mapFourδ₄Toδ₃'
        (data.i₀ r' x (by omega)) (data.i₁ x) (data.i₂ x)
        (data.i₃ r x hr) (data.i₃ r' x (by omega))
        (data.le₀₁ r' x (by omega)) (data.le₁₂ x) (data.le₂₃ r x hr)
        (data.i₃_le r r' x hrr' hr)
        (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl := by
  rfl

end PageHomologyData

section SupportedSuccessors

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (Y : SpectralObject C ι)
  (data : SpectralSequenceDataCore ι c r₀)
  [Y.HasSpectralSequence data]

unseal spectralSequence in
private def pageHomologyMapData
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor D (c r) x).map
        (F.mapSpectralObjectSpectralSequencePageIso Y data r hr).hom)
      ((pageHomologyData Y data r r' hrr' hr x).left.map
        (F))
      (pageHomologyData (F.mapSpectralObject Y) data r r' hrr' hr x).left := by
  let U := F
  let Z := F.mapSpectralObject Y
  let hY := pageHomologyData Y data r r' hrr' hr x
  let hZ := pageHomologyData Z data r r' hrr' hr x
  let φ := (HomologicalComplex.shortComplexFunctor D (c r) x).map
    (F.mapSpectralObjectSpectralSequencePageIso Y data r hr).hom
  let k := (F.mapSpectralObjectEIso Y
    (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
    (homOfLE (data.le₂₃ r x hr))
    (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl).hom
  let h := (F.mapSpectralObjectSpectralSequencePageIso Y
    data r' (by omega)).hom.f x
  have hi : k ≫ hZ.left.i = (hY.left.map U).i ≫ φ.τ₂ := by
    dsimp only [hY, hZ]
    rw [ShortComplex.LeftHomologyData.map_i,
      pageHomologyData_left_i, pageHomologyData_left_i]
    exact (F.mapSpectralObjectEIso_map Y
      (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r x hr))
      (homOfLE (data.le₀₁ r x hr)) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r x hr))
      (fourδ₁Toδ₀' (data.i₀ r' x (by omega)) (data.i₀ r x hr)
        (data.i₁ x) (data.i₂ x) (data.i₃ r x hr)
        (data.i₀_le r r' x hrr' hr) (data.le₀₁ r x hr)
        (data.le₁₂ x) (data.le₂₃ r x hr))
      (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl).symm
  have hπ : (hY.left.map U).π ≫ h = k ≫ hZ.left.π := by
    dsimp only [hY, hZ]
    rw [ShortComplex.LeftHomologyData.map_π,
      pageHomologyData_left_π, pageHomologyData_left_π]
    exact F.mapSpectralObjectEIso_map Y
      (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r x hr))
      (homOfLE (data.le₀₁ r' x (by omega))) (homOfLE (data.le₁₂ x))
      (homOfLE (data.le₂₃ r' x (by omega)))
      (fourδ₄Toδ₃' (data.i₀ r' x (by omega)) (data.i₁ x) (data.i₂ x)
        (data.i₃ r x hr) (data.i₃ r' x (by omega))
        (data.le₀₁ r' x (by omega)) (data.le₁₂ x) (data.le₂₃ r x hr)
        (data.i₃_le r r' x hrr' hr))
      (data.deg x - 1) (data.deg x) (data.deg x + 1) (by omega) rfl
  refine { φK := k, φH := h, commi := hi, commπ := hπ, commf' := ?_ }
  apply (cancel_mono hZ.left.i).1
  rw [Category.assoc, hi, ← Category.assoc,
    ShortComplex.LeftHomologyData.f'_i, Category.assoc,
    ShortComplex.LeftHomologyData.f'_i]
  exact φ.comm₁₂.symm

unseal spectralSequence in
/-- The canonical comparison of supported pages commutes with the actual
successor homology isomorphisms, at all positions including missing neighbors. -/
theorem mapSpectralObjectSpectralSequencePageIso_comm
    (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    HomologicalComplex.homologyMap
        (F.mapSpectralObjectSpectralSequencePageIso Y data r hr).hom x ≫
      (((F.mapSpectralObject Y).spectralSequence data).iso
        r r' x hrr' hr).hom =
    (((F).mapSpectralSequence
        (Y.spectralSequence data)).iso r r' x hrr' hr).hom ≫
      (F.mapSpectralObjectSpectralSequencePageIso Y
        data r' (by omega)).hom.f x := by
  let U := F
  let S := ((Y.spectralSequence data).page r hr).sc x
  let hY := pageHomologyData Y data r r' hrr' hr x
  have hI : (hY.left.map U).homologyIso.hom =
      (S.mapHomologyIso U).hom ≫ U.map hY.left.homologyIso.hom := by
    rw [hY.left.mapHomologyIso_eq U]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
    exact (Category.comp_id _).symm
  have hcomm := (pageHomologyMapData F Y data r r' hrr' hr x).homologyMap_comm
  change HomologicalComplex.homologyMap
      (F.mapSpectralObjectSpectralSequencePageIso Y data r hr).hom x ≫
      (pageHomologyData (F.mapSpectralObject Y)
        data r r' hrr' hr x).left.homologyIso.hom =
    (hY.left.map U).homologyIso.hom ≫
      (F.mapSpectralObjectSpectralSequencePageIso Y
        data r' (by omega)).hom.f x at hcomm
  rw [hI] at hcomm
  simpa only [Functor.mapSpectralSequence_iso, Iso.trans_hom, Functor.mapIso_hom,
    spectralSequence_iso_eq_pageHomologyData,
    HomologicalComplex.mapHomologyFunctorIso, NatIso.ofComponents.app,
    Category.assoc, S, hY] using hcomm

/-- The transported native sequence has the original pages mapped by F,
with the canonical homology comparisons and original successor maps. -/
def mapSpectralObjectSpectralSequenceIso :
    (F).mapSpectralSequence
      (Y.spectralSequence data) ≅
    (F.mapSpectralObject Y).spectralSequence data := by
  let e := F.mapSpectralObjectSpectralSequencePageIso Y data
  let η :
      (F).mapSpectralSequence
          (Y.spectralSequence data) ⟶
        (F.mapSpectralObject Y).spectralSequence data :=
    { hom r hr := (e r hr).hom
      comm r r' x hrr' hr :=
        F.mapSpectralObjectSpectralSequencePageIso_comm Y data r r' hrr' hr x }
  refine
    { hom := η
      inv := { hom := fun r hr => (e r hr).inv, comm := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro r r' x hrr' hr
    apply (cancel_epi (HomologicalComplex.homologyMap (e r hr).hom x)).1
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      (e r hr).hom_inv_id, HomologicalComplex.homologyMap_id, Category.id_comp,
      ← Category.assoc,
      F.mapSpectralObjectSpectralSequencePageIso_comm Y data r r' hrr' hr x,
      Category.assoc, ← HomologicalComplex.comp_f,
      (e r' (by omega)).hom_inv_id, HomologicalComplex.id_f]
    exact (Category.comp_id _).symm
  · apply SpectralSequence.hom_ext
    intro r hr
    exact (e r hr).hom_inv_id
  · apply SpectralSequence.hom_ext
    intro r hr
    exact (e r hr).inv_hom_id

/-- The whole sequence comparison has the specified canonical page maps. -/
@[simp]
theorem mapSpectralObjectSpectralSequenceIso_hom_hom (r : ℤ) (hr : r₀ ≤ r) :
    (F.mapSpectralObjectSpectralSequenceIso Y data).hom.hom r hr =
      (F.mapSpectralObjectSpectralSequencePageIso Y data r hr).hom := rfl

end SupportedSuccessors


end CategoryTheory.Functor

end
