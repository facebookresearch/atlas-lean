/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Spectrum.Prime.FreeLocusBasis
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

@[expose] public section

open TensorProduct

universe u v w x

/-- Source-faithful consumer with the original binders: the ring and the
module share one universe and the index type is in `Type`. -/
example {T : Type u} [CommRing T] {M : Type u} [AddCommGroup M] [Module T M]
    [Module.FinitePresentation T M]
    (p : Ideal T) [p.IsPrime]
    (hfree : (⟨p, inferInstance⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M))
    (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t)
        (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) :=
  Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
    p hfree m b hb

/-- Higher-universe consumer: the ring, module, and index type live in
three distinct universes. -/
example {T : Type u} [CommRing T] {M : Type v} [AddCommGroup M] [Module T M]
    [Module.FinitePresentation T M]
    (p : Ideal T) [p.IsPrime]
    (hfree : (⟨p, inferInstance⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type w} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M))
    (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t)
        (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) :=
  Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
    p hfree m b hb
