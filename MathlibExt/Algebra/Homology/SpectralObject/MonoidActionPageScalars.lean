/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.SpectralObject.Functor
public import MathlibExt.Algebra.Homology.SpectralObjectPageMap
public import MathlibExt.Algebra.Homology.SpectralObject.MonoidActionPages
public import Mathlib.Algebra.Homology.ShortComplex.Linear

import all MathlibExt.Algebra.Homology.SpectralObject.MonoidAction
import all MathlibExt.Algebra.Homology.SpectralObject.MonoidActionPages

/-!
# Scalars on canonical pages of commutative monoid-module lifts

For an actual representation on an abelian-group-valued spectral object, the
constructed module-page forget comparison identifies each monomial scalar
with the original representation's fixed-page map. The recipe, starting page,
positions and carrier/monoid/index universes are arbitrary. Commutativity is
the condition allowing scalar multiplication to define a module-linear
spectral endomorphism. All finite integral coefficients are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open scoped BigOperators

namespace CategoryTheory.Abelian.SpectralObject

universe u v w t k vι


section Scalar
variable {A : Type u} [CommRing A] {ι : Type t} [Category.{vι} ι]

private def scalarHom (Y : SpectralObject (ModuleCat.{v} A) ι) (a : A) : Y ⟶ Y where
  hom n :=
    { app I := a • 𝟙 ((Y.H n).obj I)
      naturality := by intro I J f; simp }
  comm := by intro n₀ n₁ hn i j k f g; simp

private theorem scalarHom_shortComplexMap (Y : SpectralObject (ModuleCat.{v} A) ι) (a : A)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (scalarHom Y a).shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      a • 𝟙 (Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) := by
  apply ShortComplex.Hom.ext <;> rfl

private theorem scalarHom_EMap (Y : SpectralObject (ModuleCat.{v} A) ι) (a : A)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (scalarHom Y a).EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      a • 𝟙 (Y.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) := by
  change ShortComplex.homologyMap
      ((scalarHom Y a).shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) = _
  rw [scalarHom_shortComplexMap, ShortComplex.homologyMap_smul,
    ShortComplex.homologyMap_id]
  rfl

end Scalar

section Integer
variable {D : Type u} [Category.{v} D] [Abelian D]
  {ι : Type t} [Category.{vι} ι] {X Y : SpectralObject D ι}

private def integerHom (φ : X ⟶ Y) (z : ℤ) : X ⟶ Y where
  hom n :=
    { app I := z • (φ.hom n).app I
      naturality := by intro I J f; simp [NatTrans.naturality] }
  comm := by intro n₀ n₁ hn i j k f g; simp [φ.comm]

private theorem integerHom_shortComplexMap (φ : X ⟶ Y) (z : ℤ)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (integerHom φ z).shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      z • φ.shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  let T₁ := X.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  let T₂ := Y.shortComplex f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂
  let ev₁ : (T₁ ⟶ T₂) →+ (T₁.X₁ ⟶ T₂.X₁) :=
    { toFun := fun f => f.τ₁, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let ev₂ : (T₁ ⟶ T₂) →+ (T₁.X₂ ⟶ T₂.X₂) :=
    { toFun := fun f => f.τ₂, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let ev₃ : (T₁ ⟶ T₂) →+ (T₁.X₃ ⟶ T₂.X₃) :=
    { toFun := fun f => f.τ₃, map_zero' := rfl, map_add' := fun _ _ => rfl }
  apply ShortComplex.Hom.ext
  · exact (ev₁.map_zsmul z (φ.shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)).symm
  · exact (ev₂.map_zsmul z (φ.shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)).symm
  · exact (ev₃.map_zsmul z (φ.shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂)).symm

private theorem integerHom_EMap (φ : X ⟶ Y) (z : ℤ)
    {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    (integerHom φ z).EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ =
      z • φ.EMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ := by
  change ShortComplex.homologyMap
      ((integerHom φ z).shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) = _
  rw [integerHom_shortComplexMap]
  exact (ShortComplex.homologyFunctor D).map_zsmul
    (f := φ.shortComplexMap f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) (r := z)

end Integer

section IntervalRecovery
variable {M : Type w} [CommMonoid M] {ι : Type t} [Category.{vι} ι]

local instance : PreservesFiniteColimits
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

private theorem forget_scalar_id_apply (V : ModuleCat.{u} (MonoidAlgebra ℤ M))
    (a : MonoidAlgebra ℤ M) (v : V) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).map (a • 𝟙 V) v = a • v := rfl

private theorem integer_map_apply {V W : AddCommGrpCat.{u}} (f : V ⟶ W) (z : ℤ) (v : V) :
    (z • f) v = z • f v := rfl

private theorem forgotten_scalar_single
    (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E) (m : M) (z : ℤ) :
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectHom
      (scalarHom (E.monoidModule ρ) (MonoidAlgebra.single m z)) ≫
        (E.monoidModuleForgetIso ρ).hom =
      (E.monoidModuleForgetIso ρ).hom ≫ integerHom ((ρ m).asHom) z := by
  cases E
  rename_i H δ h₁ h₂ h₃
  let E : SpectralObject AddCommGrpCat.{u} ι := ⟨H, δ, h₁, h₂, h₃⟩
  apply SpectralObject.Hom.ext
  funext n
  apply NatTrans.ext
  funext I
  apply ConcreteCategory.hom_ext
  intro x
  dsimp only [SpectralObject.comp_hom, NatTrans.comp_app, scalarHom, integerHom,
    Functor.mapSpectralObjectHom_hom_app, SpectralObject.monoidModuleForgetIso,
    eqToIso_refl, Iso.refl_hom, SpectralObject.id_hom, NatTrans.id_app]
  simp only [ConcreteCategory.comp_apply]
  let x' : E.monoidModuleInterval ρ n I := x
  change MonoidAlgebra.single m z • x' = z • ((ρ m).asHom.hom n).app I x'
  exact SpectralObject.monoidModuleInterval_single_apply E ρ n I m z x'

end IntervalRecovery

section PageRecovery
variable {M : Type w} [CommMonoid M] {ι : Type t} [Preorder ι]
  {κ : Type k} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

local instance : PreservesFiniteColimits
    (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

unseal SpectralObject.spectralSequence in
private theorem monoidPage_recovery
    (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀) [E.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) :
    (E.monoidModulePageForgetIso ρ data r hr).hom.f x =
      ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M)) AddCommGrpCat.{u}).mapSpectralObjectPageXIso
          (E.monoidModule ρ) data r hr x).hom ≫
        (E.monoidModuleForgetIso ρ).hom.pageMapComponent data r hr x := by
  cases E
  simp only [SpectralObject.monoidModulePageForgetIso,
    SpectralObject.monoidModuleSpectralSequenceForgetIso,
    Functor.mapIso_hom, SpectralSequence.pageFunctor_map,
    SpectralObject.monoidModuleForgetIso,
    eqToIso_refl, Iso.refl_hom, SpectralObject.Hom.pageMapComponent,
    SpectralObject.Hom.EMap_id]
  rfl

unseal SpectralObject.spectralSequence in
/-- The canonical page forget comparison sends each integral monoid generator
to the actual fixed-page map of the original representation, for every native
page and position. -/
theorem monoidModulePageForgetIso_single_apply
    (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀) [E.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (m : M) (z : ℤ)
    (v : ((E.monoidModuleSpectralSequence ρ data).page r hr).X x) :
    (E.monoidModulePageForgetIso ρ data r hr).hom.f x
        (MonoidAlgebra.single m z • v) =
      z • ((ρ m).asHom.spectralSequencePageMap data r hr).f x
        ((E.monoidModulePageForgetIso ρ data r hr).hom.f x v) := by
  let Y := E.monoidModule ρ
  let σ := scalarHom Y (MonoidAlgebra.single m z)
  let i := (E.monoidModuleForgetIso ρ).hom
  let f₁ := homOfLE (data.le₀₁ r x hr)
  let f₂ := homOfLE (data.le₁₂ x)
  let f₃ := homOfLE (data.le₂₃ r x hr)
  let n₀ := data.deg x - 1
  let n₁ := data.deg x
  let n₂ := data.deg x + 1
  have hσ := forgotten_scalar_single E ρ m z
  have he := congrArg (fun φ => φ.EMap f₁ f₂ f₃ n₀ n₁ n₂ (by omega) (by omega)) hσ
  rw [SpectralObject.Hom.EMap_comp ((forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectHom σ) i
      f₁ f₂ f₃ n₀ n₁ n₂ (by omega) (by omega),
    SpectralObject.Hom.EMap_comp i (integerHom ((ρ m).asHom) z)
      f₁ f₂ f₃ n₀ n₁ n₂ (by omega) (by omega)] at he
  have hn := (forget₂ (ModuleCat.{u} (MonoidAlgebra ℤ M))
      AddCommGrpCat.{u}).mapSpectralObjectEIso_naturality σ
    f₁ f₂ f₃ n₀ n₁ n₂ (by omega) (by omega)
  have h := congrArg (fun f => f ≫ i.EMap f₁ f₂ f₃ n₀ n₁ n₂ (by omega) (by omega)) hn
  simp only [Category.assoc] at h
  rw [he, scalarHom_EMap, integerHom_EMap] at h
  have hv := ConcreteCategory.congr_hom h v
  rw [monoidPage_recovery]
  dsimp only [Y, i, f₁, f₂, f₃, n₀, n₁, n₂] at hv
  simp only [ConcreteCategory.comp_apply, forget_scalar_id_apply, integer_map_apply,
    Functor.mapSpectralObjectPageXIso, SpectralObject.Hom.spectralSequencePageMap,
    SpectralObject.Hom.pageMap, SpectralObject.Hom.pageMapComponent,
    SpectralObject.spectralSequence, SpectralObject.SpectralSequence.page,
    SpectralObject.SpectralSequence.pageX] at hv ⊢
  convert hv using 1

unseal SpectralObject.spectralSequence in
/-- The same canonical comparison sends every scalar to the full finite sum
of the original representation's page maps. -/
theorem monoidModulePageForgetIso_smul_apply
    (E : SpectralObject AddCommGrpCat.{u} ι) (ρ : M →* End E)
    (data : SpectralObject.SpectralSequenceDataCore ι c r₀) [E.HasSpectralSequence data]
    (r : ℤ) (hr : r₀ ≤ r) (x : κ) (a : MonoidAlgebra ℤ M)
    (v : ((E.monoidModuleSpectralSequence ρ data).page r hr).X x) :
    (E.monoidModulePageForgetIso ρ data r hr).hom.f x (a • v) =
      ∑ m ∈ a.coeff.support, (a.coeff m) • ((ρ m).asHom.spectralSequencePageMap data r hr).f x
        ((E.monoidModulePageForgetIso ρ data r hr).hom.f x v) := by
  let e := (E.monoidModulePageForgetIso ρ data r hr).hom.f x
  have ha : a = ∑ m ∈ a.coeff.support, MonoidAlgebra.single m (a.coeff m) :=
    (MonoidAlgebra.sum_coeff_single a).symm
  calc
    e (a • v) = e ((∑ m ∈ a.coeff.support, MonoidAlgebra.single m (a.coeff m)) • v) := by rw [← ha]
    _ = ∑ m ∈ a.coeff.support, e (MonoidAlgebra.single m (a.coeff m) • v) := by
      rw [Finset.sum_smul]
      exact map_sum e.hom _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact monoidModulePageForgetIso_single_apply E ρ data r hr x m (a.coeff m) v

end PageRecovery

end CategoryTheory.Abelian.SpectralObject

end
