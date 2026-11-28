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
# Tensor products preserve cochain homotopies

Over a commutative ring, a homotopy in either integer cochain factor gives
a homotopy of the full tensor maps. Homotopies in both factors combine
to compare their simultaneous tensor maps, with the standard signed
tensor differential.
-/

@[expose] public section
noncomputable section

open CategoryTheory

namespace CochainComplex.ModuleTensor

universe u v w

variable (R : Type u) [CommRing R]

attribute [local instance] tensorHasMapBifunctorAt

/--
Let R be a commutative ring. Let P,P' be integer cochain complexes of R-modules in one carrier
universe and Q,Q' such complexes in another. The tensor differential uses d_P⊗1 + (−1)ᵖ 1⊗d_Q
on degree (p,q). For a homotopy h from f : P → P' to f' and a fixed morphism g : Q → Q', the
full tensor maps f⊗g and f'⊗g are homotopic.
-/
def mapAtHomotopyFst {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {f f' : P ⟶ P'} (h : Homotopy f f')
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') :
    Homotopy (mapAt R f g) (mapAt R f' g) :=
  HomologicalComplex.mapBifunctorMapHomotopy₁ h g (ModuleCat.tensorBifunctorAt R) (.up ℤ)

/--
Let R be a commutative ring. Let P,P' be integer cochain complexes of R-modules in one carrier
universe and Q,Q' such complexes in another. The tensor differential uses d_P⊗1 + (−1)ᵖ 1⊗d_Q
on degree (p,q). For a fixed morphism f : P → P' and a homotopy h from g : Q → Q' to g', the
full tensor maps f⊗g and f⊗g' are homotopic.
-/
def mapAtHomotopySnd {P P' : CochainComplex (ModuleCat.{v} R) ℤ} (f : P ⟶ P')
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ}
    {g g' : Q ⟶ Q'} (h : Homotopy g g') :
    Homotopy (mapAt R f g) (mapAt R f g') :=
  HomologicalComplex.mapBifunctorMapHomotopy₂ f h (ModuleCat.tensorBifunctorAt R) (.up ℤ)

/--
Let R be a commutative ring. Let P,P' be integer cochain complexes of R-modules in one carrier
universe and Q,Q' such complexes in another. The tensor differential uses d_P⊗1 + (−1)ᵖ 1⊗d_Q
on degree (p,q). Given homotopies f∼f' and g∼g' in the two factors, the simultaneous maps f⊗g
and f'⊗g' are homotopic. The construction first varies f with g fixed, then varies g with f'
fixed.
-/
def mapAtHomotopy {P P' : CochainComplex (ModuleCat.{v} R) ℤ}
    {f f' : P ⟶ P'} (hf : Homotopy f f')
    {Q Q' : CochainComplex (ModuleCat.{w} R) ℤ}
    {g g' : Q ⟶ Q'} (hg : Homotopy g g') :
    Homotopy (mapAt R f g) (mapAt R f' g') :=
  (mapAtHomotopyFst R hf g).trans (mapAtHomotopySnd R f' hg)

end CochainComplex.ModuleTensor
