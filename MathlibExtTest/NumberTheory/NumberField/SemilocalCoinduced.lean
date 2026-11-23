/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.SemilocalCoinduced

@[expose] public section

open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport

-- Consumer with the original binders for the finite place variant.
example (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : HeightOneSpectrum (𝓞 E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v))
          ≃+ Additive (Π w : {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v},
            (w.1.adicCompletion K)ˣ),
      ∀ (g : K ≃ₐ[E] K)
        (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v))
        (w w' : {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v)).ρ g f)) w
          = NumberField.PlaceTransport.transportUnits g h (Additive.toMul (e f) w') :=
  NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits E K v

-- Consumer with the original binders for the archimedean variant.
example (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : NumberField.InfinitePlace E) :
    ∃ e : (Rep.coind (NumberField.InfPlaceDecomp.decomp E K
          (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
          ≃+ Additive (Π w : {w : NumberField.InfinitePlace K //
            w.comap (algebraMap E K) = v}, (w.1.Completion)ˣ),
      ∀ (g : K ≃ₐ[E] K)
        (f : Rep.coind (NumberField.InfPlaceDecomp.decomp E K
          (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
        (w w' : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.InfPlaceDecomp.decomp E K
          (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K
            (NumberField.ArchIdele.above E K v))).ρ g f)) w
          = NumberField.InfinitePlaceTransport.transportUnits g h
            (Additive.toMul (e f) w') :=
  NumberField.ArchIdele.exists_addEquiv_coind_localUnits E K v
