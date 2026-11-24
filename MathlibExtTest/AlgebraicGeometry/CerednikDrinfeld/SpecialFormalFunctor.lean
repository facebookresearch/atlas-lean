/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor

@[expose] public noncomputable section

namespace SpecialFormalFunctorTest

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

variable (p : ℕ) [Fact p.Prime]

/-- Consumer with the original binders for the functor of points `G`. -/
theorem exactSource {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]
    (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] :
    (ModuliPackage.G 𝒪 M).obj B = ModuliPackage.GPoint 𝒪 M B :=
  ModuliPackage.G_obj 𝒪 M B

/-- The identity map on points is the identity, with the original binders. -/
theorem exactSourceMapId {𝒪 : Type} [CommRing 𝒪] {O : Type} [CommRing O]
    [Algebra 𝒪 O] (M : ModuliPackage.{0, 0} p O) {B : Type} [CommRing B]
    [Algebra 𝒪 B] (x : ModuliPackage.GPoint 𝒪 M B) :
    x.map (AlgHom.id 𝒪 B) = x :=
  x.map_id

/-- Non-vacuity: the standard formal `O_D`-module over a field of
characteristic `p` has Lie algebra of dimension `2`, so the special
condition is a genuine decomposition condition. -/
example {B : Type} [Field B] (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hX : X.IsSpecial j) :
    IsCompl (X.lieZero j) (X.lieOne j) :=
  hX.1

end SpecialFormalFunctorTest

end
