/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Basic
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# homotopies of the original sum tensor maps

Both homotopies are the bifunctor homotopies on the existing total tensor. Their source, target,
maps and signs remain the original values.
-/

@[expose] public section
noncomputable section

open CategoryTheory

namespace CochainComplex.ModuleTensor

universe u v w

variable (R : Type u) [CommRing R]

attribute [local instance] tensorHasMapBifunctorAt

/-- The original first-variable tensor maps carry the original homotopy. -/
def mapAtHomotopyFst {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {f f' : P ⟶ P'} (h : Homotopy f f')
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') :
    Homotopy (mapAt R f g) (mapAt R f' g) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h g (ModuleCat.tensorBifunctorAt R) (.up ℤ)

/-- The original second-variable tensor maps carry the original homotopy. -/
def mapAtHomotopySnd {P P' : CochainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P')
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ}
    {g g' : Q ⟶ Q'} (h : Homotopy g g') :
    Homotopy (mapAt R f g) (mapAt R f g') :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ f h (ModuleCat.tensorBifunctorAt R) (.up ℤ)

/-- Two homotopies compose on the same original simultaneous tensor map. -/
def mapAtHomotopy {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {f f' : P ⟶ P'} (hf : Homotopy f f')
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ}
    {g g' : Q ⟶ Q'} (hg : Homotopy g g') :
    Homotopy (mapAt R f g) (mapAt R f' g') :=
  (mapAtHomotopyFst R hf g).trans (mapAtHomotopySnd R f' hg)

end CochainComplex.ModuleTensor
