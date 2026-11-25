/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import MathlibExt.Algebra.Homology.SpectralObject.MonoidActionPageScalars
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped BigOperators
universe u v w t k

example {D : Type u} [Category.{v} D] [Abelian D]
    {ι : Type t} [Preorder ι] {κ : Type k} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    {X Y : SpectralObject D ι} (φ : X ⟶ Y)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).page r hr ⟶ (Y.spectralSequence data).page r hr :=
  φ.spectralSequencePageMap data r hr

variable {M : Type w} [CommMonoid M] {ι : Type t} [Preorder ι] {κ : Type k}
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E)
  (data : SpectralObject.SpectralSequenceDataCore ι c r₀) [E.HasSpectralSequence data]

example (r : ℤ) (hr : r₀ ≤ r) (x : κ) (m : M)
    (v : ((E.monoidModuleSpectralSequence ρ data).page r hr).X x) :
    (E.monoidModulePageForgetIso ρ data r hr).hom.f x (MonoidAlgebra.single m (-1 : ℤ) • v) =
      -((ρ m).asHom.spectralSequencePageMap data r hr).f x ((E.monoidModulePageForgetIso ρ data r hr).hom.f x v) := by
  simpa only [neg_one_zsmul] using E.monoidModulePageForgetIso_single_apply ρ data r hr x m (-1) v

example (r : ℤ) (hr : r₀ ≤ r) (x : κ) (a : MonoidAlgebra ℤ M)
    (v : ((E.monoidModuleSpectralSequence ρ data).page r hr).X x) :
    (E.monoidModulePageForgetIso ρ data r hr).hom.f x (a • v) =
      ∑ m ∈ a.coeff.support, (a.coeff m) • ((ρ m).asHom.spectralSequencePageMap data r hr).f x
        ((E.monoidModulePageForgetIso ρ data r hr).hom.f x v) := by
  exact E.monoidModulePageForgetIso_smul_apply ρ data r hr x a v

section Noninvertible
variable {ι' : Type t} [Preorder ι'] {κ' : Type k} {c' : ℤ → ComplexShape κ'} {r₀' : ℤ}
  (E' : SpectralObject AddCommGrpCat.{u} ι')
  (ρ' : Multiplicative ℕ →* End E')
  (data' : SpectralObject.SpectralSequenceDataCore ι' c' r₀') [E'.HasSpectralSequence data']
example (r : ℤ) (hr : r₀' ≤ r) (x : κ')
    (v : ((E'.monoidModuleSpectralSequence ρ' data').page r hr).X x) :
    (E'.monoidModulePageForgetIso ρ' data' r hr).hom.f x
        (MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℕ)) (2 : ℤ) • v) =
      (2 : ℤ) • ((ρ' (Multiplicative.ofAdd 1)).asHom.spectralSequencePageMap data' r hr).f x
        ((E'.monoidModulePageForgetIso ρ' data' r hr).hom.f x v) := by
  exact E'.monoidModulePageForgetIso_single_apply ρ' data' r hr x _ 2 v
end Noninvertible

end
