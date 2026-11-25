/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.SpectralObjectPageMap

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v t k

example
    {D : Type u} [Category.{v} D] [Abelian D]
    {ι : Type t} [Preorder ι] {κ : Type k} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    {X Y : SpectralObject D ι} (φ : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (φ.spectralSequencePageMap data r hr).f x ≫
        (Y.spectralSequencePageXIso data r hr x
          (data.i₀ r x) (data.i₁ x) (data.i₂ x) (data.i₃ r x)
          rfl rfl rfl rfl
          (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl
          (sub_add_cancel _ _) rfl).hom =
      (X.spectralSequencePageXIso data r hr x
          (data.i₀ r x) (data.i₁ x) (data.i₂ x) (data.i₃ r x)
          rfl rfl rfl rfl
          (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl
          (sub_add_cancel _ _) rfl).hom ≫
        φ.pageMapComponent data r hr x := by
  exact φ.spectralSequencePageMap_f data r hr x

example
    {D : Type u} [Category.{v} D] [Abelian D]
    {ι : Type t} [Preorder ι] {κ : Type k} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    {X Y : SpectralObject D ι} (φ : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (x : κ) :
    (φ.spectralSequencePageMap data r₀ (le_refl r₀)).f x ≫
        (Y.spectralSequencePageXIso data r₀ (le_refl r₀) x
          (data.i₀ r₀ x) (data.i₁ x) (data.i₂ x) (data.i₃ r₀ x)
          rfl rfl rfl rfl
          (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl
          (sub_add_cancel _ _) rfl).hom =
      (X.spectralSequencePageXIso data r₀ (le_refl r₀) x
          (data.i₀ r₀ x) (data.i₁ x) (data.i₂ x) (data.i₃ r₀ x)
          rfl rfl rfl rfl
          (data.deg x - 1) (data.deg x) (data.deg x + 1) rfl
          (sub_add_cancel _ _) rfl).hom ≫
        φ.pageMapComponent data r₀ (le_refl r₀) x := by
  exact φ.spectralSequencePageMap_f data r₀ (le_refl r₀) x


example {D : Type u} [Category.{v} D] [Abelian D]
    {ι : Type t} [Preorder ι] {κ : Type k} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    {X Y : SpectralObject D ι} (φ : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).page r hr ⟶ (Y.spectralSequence data).page r hr :=
  @SpectralObject.Hom.spectralSequencePageMap.{u, v, t, k}
    D _ _ ι _ κ c r₀ X Y φ data _ _ r hr

end
