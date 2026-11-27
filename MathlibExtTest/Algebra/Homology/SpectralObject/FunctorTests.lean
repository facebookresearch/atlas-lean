/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
-- Author: @toskua, Avocado
public import MathlibExt.Algebra.Homology.SpectralObject.Functor

/-!
# Ordinary-import clients of exact spectral-object transport

The source and target coefficient universes are independent. The only
functor assumptions are the standard exact additive-functor assumptions;
neither faithfulness nor a target support or comparison is supplied.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open CategoryTheory.Abelian CategoryTheory.Abelian.SpectralObject

universe vC uC vD uD vι uι uκ

namespace SpectralObjectFunctorTests

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section Intervals

variable {ι : Type uι} [Category.{vι} ι]
  (X : SpectralObject C ι)

example (n : ℤ) (I : ComposableArrows ι 1) :
    ((F.mapSpectralObject X).H n).obj I = F.obj ((X.H n).obj I) :=
  F.mapSpectralObject_H_obj X n I

example (n : ℤ) {I J : ComposableArrows ι 1} (f : I ⟶ J) :
    ((F.mapSpectralObject X).H n).map f = F.map ((X.H n).map f) :=
  F.mapSpectralObject_H_map X n f

example {i j l : ι} (f : i ⟶ j) (g : j ⟶ l)
    (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) :
    (F.mapSpectralObject X).δ f g n₀ n₁ hn = F.map (X.δ f g n₀ n₁ hn) :=
  F.mapSpectralObject_δ X f g n₀ n₁ hn

example {i j l : ι} (f : i ⟶ j) (g : j ⟶ l)
    (fg : i ⟶ l) (hfg : f ≫ g = fg) (n : ℤ) :
    ((F.mapSpectralObject X).sc₂ f g fg hfg n).Exact :=
  (F.mapSpectralObject X).exact₂ f g fg hfg n

example {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    (F.mapSpectralObjectCyclesIso X f g n).hom ≫
        (F.mapSpectralObject X).iCycles f g n = F.map (X.iCycles f g n) :=
  F.mapSpectralObjectCyclesIso_hom_iCycles X f g n

example {i j l : ι} (f : i ⟶ j) (g : j ⟶ l) (n : ℤ) :
    F.map (X.pOpcycles f g n) ≫
        (F.mapSpectralObjectOpcyclesIso X f g n).hom =
      (F.mapSpectralObject X).pOpcycles f g n :=
  F.mapSpectralObjectOpcyclesIso_π X f g n

example {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    F.map (X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (F.mapSpectralObjectEIso X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      (F.mapSpectralObjectCyclesIso X f₁ f₂ n₁).hom ≫
        (F.mapSpectralObject X).πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  F.mapSpectralObjectEIso_πE X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

example {i j l i' j' l' : ι} (f : i ⟶ j) (g : j ⟶ l)
    (f' : i' ⟶ j') (g' : j' ⟶ l') (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    F.map (X.cyclesMap f g f' g' α n) ≫
        (F.mapSpectralObjectCyclesIso X f' g' n).hom =
      (F.mapSpectralObjectCyclesIso X f g n).hom ≫
        (F.mapSpectralObject X).cyclesMap f g f' g' α n :=
  F.mapSpectralObjectCyclesIso_map X f g f' g' α n

example {i j l i' j' l' : ι} (f : i ⟶ j) (g : j ⟶ l)
    (f' : i' ⟶ j') (g' : j' ⟶ l') (α : mk₂ f g ⟶ mk₂ f' g') (n : ℤ) :
    F.map (X.opcyclesMap f g f' g' α n) ≫
        (F.mapSpectralObjectOpcyclesIso X f' g' n).hom =
      (F.mapSpectralObjectOpcyclesIso X f g n).hom ≫
        (F.mapSpectralObject X).opcyclesMap f g f' g' α n :=
  F.mapSpectralObjectOpcyclesIso_map X f g f' g' α n

example {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F.mapSpectralObjectEIso X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (F.mapSpectralObject X).ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      F.map (X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (F.mapSpectralObjectOpcyclesIso X f₂ f₃ n₁).hom :=
  F.mapSpectralObjectEIso_ιE X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

example {Y : SpectralObject C ι} (φ : X ⟶ Y)
    {i j l m : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ l) (f₃ : l ⟶ m)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    F.map (φ.EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
        (F.mapSpectralObjectEIso Y f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom =
      (F.mapSpectralObjectEIso X f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
        (F.mapSpectralObjectHom φ).EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ :=
  F.mapSpectralObjectEIso_naturality φ f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂

end Intervals

section Pages

variable {ι : Type uι} [Preorder ι] {κ : Type uκ}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)

example (r : ℤ) (hr : r₀ ≤ r) (x y : κ) :
    F.map (Abelian.SpectralObject.SpectralSequence.pageD X data r x y hr) ≫
        (F.mapSpectralObjectPageXIso X data r hr y).hom =
      (F.mapSpectralObjectPageXIso X data r hr x).hom ≫
        Abelian.SpectralObject.SpectralSequence.pageD (F.mapSpectralObject X) data r x y hr :=
  F.mapSpectralObjectPageXIso_d X data r hr x y

example (r : ℤ) (hr : r₀ ≤ r) (x y : κ) (hxy : ¬ (c r).Rel x y) :
    F.map (Abelian.SpectralObject.SpectralSequence.pageD X data r x y hr) = 0 := by
  simp only [Abelian.SpectralObject.SpectralSequence.pageD, dite_eq_right hxy, F.map_zero]

example {Y : SpectralObject C ι} (φ : X ⟶ Y) (r : ℤ) (hr : r₀ ≤ r) :
    (F.mapHomologicalComplex (c r)).map (φ.pageMap data r hr) ≫
        (F.mapSpectralObjectPageIso Y data r hr).hom =
      (F.mapSpectralObjectPageIso X data r hr).hom ≫
        (F.mapSpectralObjectHom φ).pageMap data r hr :=
  F.mapSpectralObjectPageIso_naturality data φ r hr

example [X.HasSpectralSequence data] :
    (F.mapSpectralObject X).HasSpectralSequence data := inferInstance

example [X.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (i₀ i₁ i₂ i₃ : ι)
    (h₀ : i₀ = data.i₀ r x hr) (h₁ : i₁ = data.i₁ x)
    (h₂ : i₂ = data.i₂ x) (h₃ : i₃ = data.i₃ r x hr)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg x)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (F.mapSpectralObjectSpectralSequencePageIso X data r hr).hom.f x ≫
      ((F.mapSpectralObject X).spectralSequencePageXIso data r hr x
        i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom =
    F.map ((X.spectralSequencePageXIso data r hr x
      i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom) ≫
      (F.mapSpectralObjectEIso X
        (homOfLE (data.le₀₁' r hr x h₀ h₁))
        (homOfLE (data.le₁₂' x h₁ h₂))
        (homOfLE (data.le₂₃' r hr x h₂ h₃)) n₀ n₁ n₂ hn₁ hn₂).hom :=
  F.mapSpectralObjectSpectralSequencePageIso_presented X data r hr x
    i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂

example [X.HasSpectralSequence data] :
    F.mapSpectralSequence (X.spectralSequence data) ≅
      (F.mapSpectralObject X).spectralSequence data :=
  F.mapSpectralObjectSpectralSequenceIso X data

example [X.HasSpectralSequence data] (r : ℤ) (hr : r₀ ≤ r) :
    (F.mapSpectralObjectSpectralSequenceIso X data).hom.hom r hr =
      (F.mapSpectralObjectSpectralSequencePageIso X data r hr).hom :=
  F.mapSpectralObjectSpectralSequenceIso_hom_hom X data r hr

example [X.HasSpectralSequence data] (r r' : ℤ)
    (hrr' : r + 1 = r') (hr : r₀ ≤ r) (x : κ) :
    HomologicalComplex.homologyMap
        (F.mapSpectralObjectSpectralSequencePageIso X data r hr).hom x ≫
      (((F.mapSpectralObject X).spectralSequence data).iso r r' x hrr' hr).hom =
    ((F.mapSpectralSequence (X.spectralSequence data)).iso r r' x hrr' hr).hom ≫
      (F.mapSpectralObjectSpectralSequencePageIso X data r' (by omega)).hom.f x :=
  F.mapSpectralObjectSpectralSequencePageIso_comm X data r r' hrr' hr x

end Pages

end SpectralObjectFunctorTests

end
