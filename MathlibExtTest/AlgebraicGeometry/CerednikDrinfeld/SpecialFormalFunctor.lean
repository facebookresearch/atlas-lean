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

/-- Non-vacuity: over any ring of characteristic `p`, the standard special formal
`O_D`-module exists; its Lie algebra is the direct sum of the two eigenlines of `Zp2 p`, and
it has height `4`. -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    IsCompl ((SpecialFormalODModule.standard j).lieZero j)
        ((SpecialFormalODModule.standard j).lieOne j) ∧
      (SpecialFormalODModule.standard j).HasHeight 4 :=
  ⟨(SpecialFormalODModule.standard j).isSpecial.1, (SpecialFormalODModule.standard j).hasHeight⟩

/-- The two eigenlines of the standard module are the coordinate axes of its Lie algebra
`Fin 2 → B`: `Zp2 p` acts on the first coordinate through `j` and on the second through `j`
composed with Frobenius, so each basis vector lies in exactly one of them. -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    (Pi.single 0 1 : Fin 2 → B) ∈ (SpecialFormalODModule.standard j).lieZero j ∧
      (Pi.single 0 1 : Fin 2 → B) ∉ (SpecialFormalODModule.standard j).lieOne j ∧
      (Pi.single 1 1 : Fin 2 → B) ∈ (SpecialFormalODModule.standard j).lieOne j ∧
      (Pi.single 1 1 : Fin 2 → B) ∉ (SpecialFormalODModule.standard j).lieZero j := by
  have : Nontrivial B := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  rw [SpecialFormalODModule.standard_toFormalODModule, Standard.mem_lieZero_iff,
    Standard.mem_lieOne_iff, Standard.mem_lieOne_iff, Standard.mem_lieZero_iff]
  simp

/-- In characteristic `p`, multiplication by `p` on the standard module is
`X i ↦ X i ^ (p ^ 2)`, whose kernel has degree `p ^ 4` (height `4`). -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    (SpecialFormalODModule.standard j).act (p : Zp2 p) =
      fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ 2) := by
  have h := Standard.modB_act_p j
  rw [LubinTate.card_GF] at h
  exact h

/-- Over `𝔽_{p²}`, with `j` the reduction map `W(𝔽_{p²}) → 𝔽_{p²}`, the Lie algebra of the
standard module is two-dimensional and both eigenlines are one-dimensional. -/
example :
    Module.finrank (GaloisField p 2) (SpecialFormalODModule.standard
        (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).Lie = 2 ∧
      Module.finrank (GaloisField p 2) ((SpecialFormalODModule.standard
        (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).lieZero
          WittVector.constantCoeff) = 1 ∧
      Module.finrank (GaloisField p 2) ((SpecialFormalODModule.standard
        (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).lieOne
          WittVector.constantCoeff) = 1 :=
  ⟨Module.finrank_fin_fun _, (Standard.lieZeroEquiv _).finrank_eq.trans (Module.finrank_self _),
    (Standard.lieOneEquiv _).finrank_eq.trans (Module.finrank_self _)⟩

end SpecialFormalFunctorTest

end
