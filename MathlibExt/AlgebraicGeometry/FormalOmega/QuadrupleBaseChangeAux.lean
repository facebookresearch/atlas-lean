/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DrinfeldDatum_Iso_subsingleton`
`CF_DrinfeldDatum_BaseChangeAlong_exists_comp`
`CF_DrinfeldDatum_BaseChangeAlong_exists_iso`
`CF_DrinfeldDatum_BaseChangeAlong_tau_unique`
`CF_DrinfeldDatum_exists_isBaseChangeAlong_of_isLocalization`
`CF_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic`
`CF_DrinfeldDatum_IsQuadrupleOf_map_of_isBaseChangeAlong`
`CF_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum

/-!
# Base change of a Drinfeld datum to a localization

Helpers for `QuadrupleBaseChange`: given a Drinfeld datum `Q` over `B` and a localization `C`
of `B`, we build the datum `LocBC.bcDatum S Q` over `C` with modules `C ⊗[B] Q.T₀`,
`C ⊗[B] Q.T₁`.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.DrinfeldDatum.LocBC

/-- The point of `Spec B` below a point `x'` of `Spec C`. -/
abbrev pt (B : Type) {C : Type} [CommRing B] [CommRing C] [Algebra B C]
    (x' : PrimeSpectrum C) : PrimeSpectrum B :=
  PrimeSpectrum.comap (algebraMap B C) x'

section General

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]

/-- The local ring of `C` at `y` is the localization of `B` at the point below `y`. -/
theorem isLocalization_atPrime_locRing (S : Submonoid B) [IsLocalization S C]
    (y : PrimeSpectrum C) :
    haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    IsLocalization.AtPrime (locRing C y) (pt B y).asIdeal :=
  haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S (locRing C y) y.asIdeal

variable (𝒪) in
/-- A semilinear map along `B → C` viewed as a `B`-linear map. -/
def τB (T : Type) [AddCommGroup T] [Module B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') : T →ₗ[B] T' :=
  { toFun := τ, map_add' := fun a b => map_add τ a b, map_smul' := fun b t => by
      rw [LinearMap.map_smulₛₗ]
      change algebraMap B C b • τ t = b • τ t
      exact algebraMap_smul C b (τ t) }

/-- A spanning semilinear map between invertible modules along `B → C` is a base change. -/
theorem isBaseChange_τB (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T']
    [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) :
    IsBaseChange C (τB 𝒪 T T' τ) := by
  have hsurj : Function.Surjective ((τB 𝒪 T T' τ).liftBaseChange C) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← hτ]
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) (fun t => by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul])

variable (𝒪) in
/-- `τ` followed by the localization map to the stalk at `y`. -/
def γ (T : Type) [AddCommGroup T] [Module B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (y : PrimeSpectrum C) : T →ₗ[B] stalk C y T' :=
  ((LocalizedModule.mkLinearMap y.asIdeal.primeCompl T').restrictScalars B).comp (τB 𝒪 T T' τ)

/-- Value of `γ`. -/
theorem γ_apply (T : Type) [AddCommGroup T] [Module B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module B T'] [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (y : PrimeSpectrum C) (t : T) :
    γ 𝒪 T T' τ y t = LocalizedModule.mk (τ t) 1 := rfl

/-- `γ` exhibits the stalk of `T'` at `y` as the localization of `T` at the point below `y`. -/
theorem isLocalizedModule_γ (S : Submonoid B) [IsLocalization S C]
    (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T']
    [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C) :
    IsLocalizedModule (pt B y).asIdeal.primeCompl (γ 𝒪 T T' τ y) := by
  have : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower B C (stalk C y T') := inferInstance
  have : IsScalarTower B (locRing C y) (stalk C y T') := inferInstance
  have : IsLocalization.AtPrime (locRing C y) (pt B y).asIdeal :=
    isLocalization_atPrime_locRing S y
  rw [isLocalizedModule_iff_isBaseChange (pt B y).asIdeal.primeCompl (locRing C y)]
  exact IsBaseChange.comp (isBaseChange_τB T T' τ hτ)
    (IsLocalizedModule.isBaseChange y.asIdeal.primeCompl (locRing C y)
      (LocalizedModule.mkLinearMap y.asIdeal.primeCompl T'))

/-- The comparison isomorphism induced by `γ` on a fraction. -/
theorem iso_γ_mk (S : Submonoid B) [IsLocalization S C]
    (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
    (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T']
    [IsScalarTower B C T']
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C) (t : T) (s : B)
    (hs : s ∈ (pt B y).asIdeal.primeCompl) :
    haveI := isLocalizedModule_γ S T T' τ hτ y
    IsLocalizedModule.iso (pt B y).asIdeal.primeCompl (γ 𝒪 T T' τ y)
        (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk (τ t) (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) := by
  have := isLocalizedModule_γ S T T' τ hτ y
  apply ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (γ 𝒪 T T' τ y) ⟨s, hs⟩)).1
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_smul,
    LocalizedModule.smul'_mk,
    ← algebraMap_smul C s (LocalizedModule.mk (τ t)
      (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl)),
    LocalizedModule.smul'_mk]
  have h1 : LocalizedModule.mk (s • t) (⟨s, hs⟩ : (pt B y).asIdeal.primeCompl) =
      LocalizedModule.mk t 1 := LocalizedModule.mk_cancel ⟨s, hs⟩ t
  have h2 : LocalizedModule.mk (algebraMap B C s • τ t)
      (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) = LocalizedModule.mk (τ t) 1 :=
    LocalizedModule.mk_cancel (⟨algebraMap B C s, hs⟩ : y.asIdeal.primeCompl) (τ t)
  rw [h1, h2, IsLocalizedModule.iso_mk_one, γ_apply]

/-- The comparison isomorphisms of `γ` commute with compatible linear maps. -/
theorem iso_γ_natural (S : Submonoid B) [IsLocalization S C]
    (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀]
    (T₀' : Type) [AddCommGroup T₀'] [Module C T₀'] [Module.Invertible C T₀'] [Module B T₀']
    [IsScalarTower B C T₀']
    (τ₀ : T₀ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T₀')
    (hτ₀ : Submodule.span C (Set.range τ₀) = ⊤)
    (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁]
    (T₁' : Type) [AddCommGroup T₁'] [Module C T₁'] [Module.Invertible C T₁'] [Module B T₁']
    [IsScalarTower B C T₁']
    (τ₁ : T₁ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T₁')
    (hτ₁ : Submodule.span C (Set.range τ₁) = ⊤)
    (y : PrimeSpectrum C) (P : T₀ →ₗ[B] T₁) (P' : T₀' →ₗ[C] T₁')
    (hP : ∀ t, τ₁ (P t) = P' (τ₀ t)) (m : stalk B (pt B y) T₀) :
    haveI := isLocalizedModule_γ S T₀ T₀' τ₀ hτ₀ y
    haveI := isLocalizedModule_γ S T₁ T₁' τ₁ hτ₁ y
    IsLocalizedModule.iso (pt B y).asIdeal.primeCompl (γ 𝒪 T₁ T₁' τ₁ y)
        (LocalizedModule.map (pt B y).asIdeal.primeCompl P m) =
      LocalizedModule.map y.asIdeal.primeCompl P'
        (IsLocalizedModule.iso (pt B y).asIdeal.primeCompl (γ 𝒪 T₀ T₀' τ₀ y) m) := by
  have := isLocalizedModule_γ S T₀ T₀' τ₀ hτ₀ y
  have := isLocalizedModule_γ S T₁ T₁' τ₁ hτ₁ y
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [LocalizedModule.map_mk, iso_γ_mk S T₁ T₁' τ₁ hτ₁ y (P t) s s.2,
      iso_γ_mk S T₀ T₀' τ₀ hτ₀ y t s s.2, LocalizedModule.map_mk, hP]

end General

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]

/-- The `B`-linear map `B ⊗ N → A ⊗ N` induced by `B → A`. -/
def ιB (A : Type) [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
    (N : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B N →ₗ[B] latticeBaseChange 𝒪 K A N :=
  { toFun := LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap
    map_add' := fun a b => map_add _ a b
    map_smul' := fun b p => by
      rw [rTensor_smul_left (IsScalarTower.toAlgHom 𝒪 B A) N b p,
        IsScalarTower.toAlgHom_apply, algebraMap_smul]
      rfl }

/-- `ιB` on a pure tensor `1 ⊗ v`. -/
theorem ιB_one_tmul (N : FullLattice 𝒪 K) (v : ↥N.1) :
    ιB A N ((1 : B) ⊗ₜ[𝒪] v) = (1 : A) ⊗ₜ[𝒪] v :=
  rTensor_one_tmul _ N v

/-- `ιB` is a localization map when `A` is a localization of `B`. -/
theorem isLocalizedModule_ιB (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K) :
    IsLocalizedModule S (ιB (𝒪 := 𝒪) A N) :=
  (isLocalizedModule_iff_isBaseChange S A _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 B A A (↥N.1))
      (fun p => cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B A) (fun _ => rfl) N p))

/-- Membership of `ιB A N p` in the base-changed line `D`, for `A` a localization of `B` at
`S`: it holds iff some `s ∈ S` has `s • p ∈ D`. -/
theorem ιB_mem_lineBaseChange_iff (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K)
    (D : Submodule B (latticeBaseChange 𝒪 K B N)) (p : latticeBaseChange 𝒪 K B N) :
    ιB A N p ∈ lineBaseChange (IsScalarTower.toAlgHom 𝒪 B A) N D ↔ ∃ s ∈ S, s • p ∈ D := by
  have := isLocalizedModule_ιB (𝒪 := 𝒪) (A := A) S N
  have hspan : lineBaseChange (IsScalarTower.toAlgHom 𝒪 B A) N D =
      D.localized' A S (ιB A N) := by
    rw [Submodule.localized'_eq_span]; rfl
  rw [hspan, Submodule.mem_localized']
  constructor
  · rintro ⟨m, hm, s, hms⟩
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hms
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S (ιB A N)).mp hms
    refine ⟨c * s, mul_mem c.2 s.2, ?_⟩
    rw [mul_smul]
    have hc' : (c : B) • ((s : B) • p) = (c : B) • m := by
      rw [← Submonoid.smul_def, ← Submonoid.smul_def c m, hc]
    rw [hc']
    exact D.smul_mem _ hm
  · rintro ⟨s, hs, hsp⟩
    exact ⟨s • p, hsp, ⟨s, hs⟩, by
      rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, map_smul]⟩

end Loc

section Construction

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]

variable (𝒪 B C) in
/-- The canonical semilinear map `T → C ⊗[B] T`. -/
def τbc (T : Type) [AddCommGroup T] [Module B T] :
    T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] C ⊗[B] T :=
  { toFun := fun t => (1 : C) ⊗ₜ[B] t
    map_add' := fun a b => TensorProduct.tmul_add _ a b
    map_smul' := fun b t => by
      change (1 : C) ⊗ₜ[B] (b • t) = (algebraMap B C b) • ((1 : C) ⊗ₜ[B] t)
      rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, algebraMap_smul] }

/-- The image of `τbc` spans `C ⊗[B] T`. -/
theorem span_range_τbc (T : Type) [AddCommGroup T] [Module B T] :
    Submodule.span C (Set.range (τbc 𝒪 B C T)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | tmul c t =>
    have : c ⊗ₜ[B] t = c • ((1 : C) ⊗ₜ[B] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

/-- Base change preserves the relation `P₁ ∘ P₀ = π`. -/
theorem baseChange_comp_apply {T₀ T₁ : Type} [AddCommGroup T₀] [Module B T₀] [AddCommGroup T₁]
    [Module B T₁] (P₀ : T₀ →ₗ[B] T₁) (P₁ : T₁ →ₗ[B] T₀)
    (h : ∀ t, P₁ (P₀ t) = algebraMap 𝒪 B π • t) (z : C ⊗[B] T₀) :
    (P₁.baseChange C) ((P₀.baseChange C) z) = algebraMap 𝒪 C π • z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, smul_add, ha, hb]
  | tmul c t =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h, TensorProduct.tmul_smul,
      IsScalarTower.algebraMap_apply 𝒪 B C, algebraMap_smul C (algebraMap 𝒪 B π) (c ⊗ₜ[B] t)]

end Construction

section Q

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B)
  (x' : PrimeSpectrum C)

/-- Comparison of stalks of `T₀` and `C ⊗[B] T₀`. -/
def β₀Q : stalk B (pt B x') Q.T₀ ≃ₗ[B] stalk C x' (C ⊗[B] Q.T₀) :=
  haveI := isLocalizedModule_γ S Q.T₀ (C ⊗[B] Q.T₀) (τbc 𝒪 B C Q.T₀) (span_range_τbc Q.T₀) x'
  IsLocalizedModule.iso (pt B x').asIdeal.primeCompl (γ 𝒪 Q.T₀ (C ⊗[B] Q.T₀) (τbc 𝒪 B C Q.T₀) x')

/-- `β₀Q` on a fraction. -/
theorem β₀Q_mk (t : Q.T₀) (s : B) (hs : s ∈ (pt B x').asIdeal.primeCompl) :
    β₀Q S Q x' (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk ((1 : C) ⊗ₜ[B] t) (⟨algebraMap B C s, hs⟩ : x'.asIdeal.primeCompl) :=
  iso_γ_mk S Q.T₀ (C ⊗[B] Q.T₀) (τbc 𝒪 B C Q.T₀) (span_range_τbc Q.T₀) x' t s hs

/-- Comparison of stalks of `T₁` and `C ⊗[B] T₁`. -/
def β₁Q : stalk B (pt B x') Q.T₁ ≃ₗ[B] stalk C x' (C ⊗[B] Q.T₁) :=
  haveI := isLocalizedModule_γ S Q.T₁ (C ⊗[B] Q.T₁) (τbc 𝒪 B C Q.T₁) (span_range_τbc Q.T₁) x'
  IsLocalizedModule.iso (pt B x').asIdeal.primeCompl (γ 𝒪 Q.T₁ (C ⊗[B] Q.T₁) (τbc 𝒪 B C Q.T₁) x')

/-- `β₁Q` on a fraction. -/
theorem β₁Q_mk (t : Q.T₁) (s : B) (hs : s ∈ (pt B x').asIdeal.primeCompl) :
    β₁Q S Q x' (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk ((1 : C) ⊗ₜ[B] t) (⟨algebraMap B C s, hs⟩ : x'.asIdeal.primeCompl) :=
  iso_γ_mk S Q.T₁ (C ⊗[B] Q.T₁) (τbc 𝒪 B C Q.T₁) (span_range_τbc Q.T₁) x' t s hs

/-- The `𝒪`-linear map `N₀ → stalk C x' (C ⊗ T₀)` used to define the new `u₀`. -/
def g₀Q : ↥(Q.N₀ (pt B x')) →ₗ[𝒪] stalk C x' (C ⊗[B] Q.T₀) :=
  { toFun := fun v => β₀Q S Q x' (Q.u₀ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v))
    map_add' := fun a b => by rw [TensorProduct.tmul_add, map_add, map_add]
    map_smul' := fun r v => by
      change β₀Q S Q x' (Q.u₀ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] (r • v))) =
        r • β₀Q S Q x' (Q.u₀ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v))
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (locRing B (pt B x')) r
          ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v), map_smul,
        IsScalarTower.algebraMap_apply 𝒪 B (locRing B (pt B x')) r, algebraMap_smul, map_smul]
      exact algebraMap_smul B r _ }

/-- The `𝒪`-linear map `N₁ → stalk C x' (C ⊗ T₁)` used to define the new `u₁`. -/
def g₁Q : ↥(Q.N₁ (pt B x')) →ₗ[𝒪] stalk C x' (C ⊗[B] Q.T₁) :=
  { toFun := fun v => β₁Q S Q x' (Q.u₁ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v))
    map_add' := fun a b => by rw [TensorProduct.tmul_add, map_add, map_add]
    map_smul' := fun r v => by
      change β₁Q S Q x' (Q.u₁ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] (r • v))) =
        r • β₁Q S Q x' (Q.u₁ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v))
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (locRing B (pt B x')) r
          ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v), map_smul,
        IsScalarTower.algebraMap_apply 𝒪 B (locRing B (pt B x')) r, algebraMap_smul, map_smul]
      exact algebraMap_smul B r _ }

/-- The stalk map `u₀` of the base-changed datum. -/
def u₀Q : latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (pt B x')) →ₗ[locRing C x']
    stalk C x' (C ⊗[B] Q.T₀) :=
  (g₀Q S Q x').liftBaseChange (locRing C x')

/-- The stalk map `u₁` of the base-changed datum. -/
def u₁Q : latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (pt B x')) →ₗ[locRing C x']
    stalk C x' (C ⊗[B] Q.T₁) :=
  (g₁Q S Q x').liftBaseChange (locRing C x')

/-- `u₀Q` on a pure tensor. -/
theorem u₀Q_tmul (a : locRing C x') (v : ↥(Q.N₀ (pt B x'))) :
    u₀Q S Q x' (a ⊗ₜ[𝒪] v) =
      a • β₀Q S Q x' (Q.u₀ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- `u₁Q` on a pure tensor. -/
theorem u₁Q_tmul (a : locRing C x') (v : ↥(Q.N₁ (pt B x'))) :
    u₁Q S Q x' (a ⊗ₜ[𝒪] v) =
      a • β₁Q S Q x' (Q.u₁ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- `β` intertwines `Pi₀` with its base change. -/
theorem β_map_Pi₀ (m : stalk B (pt B x') Q.T₀) :
    β₁Q S Q x' (LocalizedModule.map (pt B x').asIdeal.primeCompl Q.Pi₀ m) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₀.baseChange C) (β₀Q S Q x' m) :=
  iso_γ_natural S Q.T₀ (C ⊗[B] Q.T₀) (τbc 𝒪 B C Q.T₀) (span_range_τbc Q.T₀)
    Q.T₁ (C ⊗[B] Q.T₁) (τbc 𝒪 B C Q.T₁) (span_range_τbc Q.T₁) x' Q.Pi₀ (Q.Pi₀.baseChange C)
    (fun _ => (LinearMap.baseChange_tmul _ _ _).symm) m

/-- `β` intertwines `Pi₁` with its base change. -/
theorem β_map_Pi₁ (m : stalk B (pt B x') Q.T₁) :
    β₀Q S Q x' (LocalizedModule.map (pt B x').asIdeal.primeCompl Q.Pi₁ m) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₁.baseChange C) (β₁Q S Q x' m) :=
  iso_γ_natural S Q.T₁ (C ⊗[B] Q.T₁) (τbc 𝒪 B C Q.T₁) (span_range_τbc Q.T₁)
    Q.T₀ (C ⊗[B] Q.T₀) (τbc 𝒪 B C Q.T₀) (span_range_τbc Q.T₀) x' Q.Pi₁ (Q.Pi₁.baseChange C)
    (fun _ => (LinearMap.baseChange_tmul _ _ _).symm) m

/-- `u₀Q` on the image of `B ⊗ N₀`. -/
theorem u₀Q_ιB (p₀ : latticeBaseChange 𝒪 K B (Q.L₀ (pt B x'))) :
    u₀Q S Q x' (ιB (locRing C x') (Q.L₀ (pt B x')) p₀) =
      β₀Q S Q x' (Q.u₀ (pt B x') (ιB (locRing B (pt B x')) (Q.L₀ (pt B x')) p₀)) := by
  induction p₀ using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v =>
    have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B (Q.L₀ (pt B x'))) =
        b • ((1 : B) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have l1 : ιB (locRing C x') (Q.L₀ (pt B x')) (b ⊗ₜ[𝒪] v) =
        b • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    have l2 : ιB (locRing B (pt B x')) (Q.L₀ (pt B x')) (b ⊗ₜ[𝒪] v) =
        b • ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    rw [l1, l2, LinearMap.map_smul_of_tower (u₀Q S Q x'),
      LinearMap.map_smul_of_tower (Q.u₀ (pt B x')), map_smul, u₀Q_tmul, one_smul]

/-- `u₁Q` on the image of `B ⊗ N₁`. -/
theorem u₁Q_ιB (p₀ : latticeBaseChange 𝒪 K B (Q.L₁ (pt B x'))) :
    u₁Q S Q x' (ιB (locRing C x') (Q.L₁ (pt B x')) p₀) =
      β₁Q S Q x' (Q.u₁ (pt B x') (ιB (locRing B (pt B x')) (Q.L₁ (pt B x')) p₀)) := by
  induction p₀ using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v =>
    have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B (Q.L₁ (pt B x'))) =
        b • ((1 : B) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have l1 : ιB (locRing C x') (Q.L₁ (pt B x')) (b ⊗ₜ[𝒪] v) =
        b • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    have l2 : ιB (locRing B (pt B x')) (Q.L₁ (pt B x')) (b ⊗ₜ[𝒪] v) =
        b • ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v) := by
      rw [e1, map_smul, ιB_one_tmul]
    rw [l1, l2, LinearMap.map_smul_of_tower (u₁Q S Q x'),
      LinearMap.map_smul_of_tower (Q.u₁ (pt B x')), map_smul, u₁Q_tmul, one_smul]

/-- `u₀Q` is surjective. -/
theorem u₀Q_surjective : Function.Surjective (u₀Q S Q x') := by
  have : IsScalarTower B C (locRing C x') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro m'
  obtain ⟨m, rfl⟩ := (β₀Q S Q x').surjective m'
  obtain ⟨p, rfl⟩ := Q.u₀_surjective (pt B x') m
  have := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B (pt B x'))
    (pt B x').asIdeal.primeCompl (Q.L₀ (pt B x'))
  obtain ⟨⟨p₀, s⟩, hsp⟩ := IsLocalizedModule.surj (pt B x').asIdeal.primeCompl
    (ιB (locRing B (pt B x')) (Q.L₀ (pt B x'))) p
  have hunit : IsUnit (algebraMap B (locRing C x') s) := by
    rw [IsScalarTower.algebraMap_apply B C (locRing C x')]
    exact IsLocalization.map_units (locRing C x')
      (⟨algebraMap B C s, s.2⟩ : x'.asIdeal.primeCompl)
  refine ⟨((hunit.unit⁻¹ : (locRing C x')ˣ) : locRing C x') •
    ιB (locRing C x') (Q.L₀ (pt B x')) p₀, ?_⟩
  rw [map_smul, u₀Q_ιB, ← hsp, Submonoid.smul_def, LinearMap.map_smul_of_tower, map_smul,
    ← algebraMap_smul (locRing C x') (s : B), smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec,
    one_smul]

/-- `u₁Q` is surjective. -/
theorem u₁Q_surjective : Function.Surjective (u₁Q S Q x') := by
  have : IsScalarTower B C (locRing C x') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro m'
  obtain ⟨m, rfl⟩ := (β₁Q S Q x').surjective m'
  obtain ⟨p, rfl⟩ := Q.u₁_surjective (pt B x') m
  have := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing B (pt B x'))
    (pt B x').asIdeal.primeCompl (Q.L₁ (pt B x'))
  obtain ⟨⟨p₀, s⟩, hsp⟩ := IsLocalizedModule.surj (pt B x').asIdeal.primeCompl
    (ιB (locRing B (pt B x')) (Q.L₁ (pt B x'))) p
  have hunit : IsUnit (algebraMap B (locRing C x') s) := by
    rw [IsScalarTower.algebraMap_apply B C (locRing C x')]
    exact IsLocalization.map_units (locRing C x')
      (⟨algebraMap B C s, s.2⟩ : x'.asIdeal.primeCompl)
  refine ⟨((hunit.unit⁻¹ : (locRing C x')ˣ) : locRing C x') •
    ιB (locRing C x') (Q.L₁ (pt B x')) p₀, ?_⟩
  rw [map_smul, u₁Q_ιB, ← hsp, Submonoid.smul_def, LinearMap.map_smul_of_tower, map_smul,
    ← algebraMap_smul (locRing C x') (s : B), smul_smul, Units.inv_mul_eq_one.mpr hunit.unit_spec,
    one_smul]

/-- Continuity of `u₀Q`. -/
theorem u₀Q_continuous (v : Fin 2 → K) (hv : v ∈ Q.N₀ (pt B x')) :
    ∃ (c : C) (t' : C ⊗[B] Q.T₀), c ∉ x'.asIdeal ∧ ∀ (y' : PrimeSpectrum C)
      (hy : c ∉ y'.asIdeal), ∃ hvy : v ∈ Q.N₀ (pt B y'),
        u₀Q S Q y' ((1 : locRing C y') ⊗ₜ[𝒪] (⟨v, hvy⟩ : ↥(Q.N₀ (pt B y')))) =
          LocalizedModule.mk t' ⟨c, hy⟩ := by
  obtain ⟨b, t, hb, H⟩ := Q.u₀_continuous (pt B x') v hv
  refine ⟨algebraMap B C b, (1 : C) ⊗ₜ[B] t, hb, fun y' hy' => ?_⟩
  obtain ⟨hvy, Hy⟩ := H (pt B y') hy'
  refine ⟨hvy, ?_⟩
  rw [u₀Q_tmul, one_smul, Hy]
  exact β₀Q_mk S Q y' t b hy'

/-- Continuity of `u₁Q`. -/
theorem u₁Q_continuous (v : Fin 2 → K) (hv : v ∈ Q.N₁ (pt B x')) :
    ∃ (c : C) (t' : C ⊗[B] Q.T₁), c ∉ x'.asIdeal ∧ ∀ (y' : PrimeSpectrum C)
      (hy : c ∉ y'.asIdeal), ∃ hvy : v ∈ Q.N₁ (pt B y'),
        u₁Q S Q y' ((1 : locRing C y') ⊗ₜ[𝒪] (⟨v, hvy⟩ : ↥(Q.N₁ (pt B y')))) =
          LocalizedModule.mk t' ⟨c, hy⟩ := by
  obtain ⟨b, t, hb, H⟩ := Q.u₁_continuous (pt B x') v hv
  refine ⟨algebraMap B C b, (1 : C) ⊗ₜ[B] t, hb, fun y' hy' => ?_⟩
  obtain ⟨hvy, Hy⟩ := H (pt B y') hy'
  refine ⟨hvy, ?_⟩
  rw [u₁Q_tmul, one_smul, Hy]
  exact β₁Q_mk S Q y' t b hy'

/-- Compatibility of `u₁Q` with the inclusion `N₀ ⊆ N₁`. -/
theorem u₁Q_incl (w : latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (pt B x'))) :
    u₁Q S Q x' (inclBaseChange (locRing C x') (M' := Q.L₀ (pt B x')) (M := Q.L₁ (pt B x'))
        (Q.le (pt B x')) w) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₀.baseChange C) (u₀Q S Q x' w) := by
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (pt B x'))) =
        a • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [show inclBaseChange (locRing C x') (Q.le (pt B x')) ((1 : locRing C x') ⊗ₜ[𝒪] v) =
        ((1 : locRing C x') ⊗ₜ[𝒪] Submodule.inclusion (Q.le (pt B x')) v :
          latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (pt B x')))
        from LinearMap.baseChange_tmul _ _ _,
      u₁Q_tmul, u₀Q_tmul, one_smul, one_smul,
      show ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] Submodule.inclusion (Q.le (pt B x')) v :
          latticeBaseChange 𝒪 K (locRing B (pt B x')) (Q.L₁ (pt B x'))) =
        inclBaseChange (locRing B (pt B x')) (Q.le (pt B x'))
          ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v) from (LinearMap.baseChange_tmul _ _ _).symm,
      Q.u₁_incl, β_map_Pi₀]

/-- Compatibility of `u₀Q` with multiplication by `π` from `N₁` to `N₀`. -/
theorem u₀Q_smul (w : latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (pt B x'))) :
    u₀Q S Q x' (((smulInto π (Q.smul_le (pt B x'))).baseChange (locRing C x') :
        latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (pt B x')) →ₗ[locRing C x']
          latticeBaseChange 𝒪 K (locRing C x') (Q.L₀ (pt B x'))) w) =
      LocalizedModule.map x'.asIdeal.primeCompl (Q.Pi₁.baseChange C) (u₁Q S Q x' w) := by
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing C x') (Q.L₁ (pt B x'))) =
        a • ((1 : locRing C x') ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [LinearMap.baseChange_tmul, u₀Q_tmul, u₁Q_tmul, one_smul, one_smul,
      show ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] smulInto π (Q.smul_le (pt B x')) v :
          latticeBaseChange 𝒪 K (locRing B (pt B x')) (Q.L₀ (pt B x'))) =
        (smulInto π (Q.smul_le (pt B x'))).baseChange (locRing B (pt B x'))
          ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v) from (LinearMap.baseChange_tmul _ _ _).symm,
      Q.u₀_smul, β_map_Pi₁]

end Q

section Strata

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]

/-- The range of a base-changed map lies in `x' • ⊤` iff the range of the map lies in
`(pt B x') • ⊤`. -/
theorem range_baseChange_le_iff {T₀ T₁ : Type} [AddCommGroup T₀] [Module B T₀]
    [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁] (P : T₀ →ₗ[B] T₁)
    (x' : PrimeSpectrum C) :
    LinearMap.range (P.baseChange C) ≤ x'.asIdeal • (⊤ : Submodule C (C ⊗[B] T₁)) ↔
      LinearMap.range P ≤ (pt B x').asIdeal • (⊤ : Submodule B T₁) := by
  constructor
  · intro h
    rintro _ ⟨t, rfl⟩
    by_contra hnot
    obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem (pt B x').asIdeal (P t) hnot
    let ψ : C ⊗[B] T₁ →ₗ[C] C :=
      (TensorProduct.AlgebraTensorModule.rid B C C).toLinearMap ∘ₗ φ.baseChange C
    have hψ : ψ ((1 : C) ⊗ₜ[B] P t) = algebraMap B C (φ (P t)) := by
      simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
        TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
    have key : ∀ z ∈ (x'.asIdeal • ⊤ : Submodule C (C ⊗[B] T₁)), ψ z ∈ x'.asIdeal := by
      intro z hz
      refine Submodule.smul_induction_on (p := fun z => ψ z ∈ x'.asIdeal) hz
        (fun r hr n _ => ?_) (fun a b ha hb => ?_)
      · change ψ (r • n) ∈ _
        rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ hr
      · change ψ (a + b) ∈ _
        rw [map_add]; exact Ideal.add_mem _ ha hb
    have hmem : (P.baseChange C) ((1 : C) ⊗ₜ[B] t) ∈
        (x'.asIdeal • ⊤ : Submodule C (C ⊗[B] T₁)) := h ⟨_, rfl⟩
    rw [LinearMap.baseChange_tmul] at hmem
    have := key _ hmem
    rw [hψ] at this
    exact hφ this
  · intro h
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul c t =>
      rw [LinearMap.baseChange_tmul]
      refine Submodule.smul_induction_on
        (p := fun n => c ⊗ₜ[B] n ∈ (x'.asIdeal • ⊤ : Submodule C (C ⊗[B] T₁)))
        (h ⟨t, rfl⟩) (fun b hb n _ => ?_) (fun a b ha hb => ?_)
      · change c ⊗ₜ[B] (b • n) ∈ _
        rw [TensorProduct.tmul_smul, ← algebraMap_smul C b (c ⊗ₜ[B] n)]
        exact Submodule.smul_mem_smul hb Submodule.mem_top
      · rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ ha hb

/-- For a localization `C` of `B`, `x' • ⊤` (over `C`) lies in `(pt B x') • ⊤` (over `B`). -/
theorem smul_top_restrictScalars_le (S : Submonoid B) [IsLocalization S C]
    (x' : PrimeSpectrum C)
    (M : Type) [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M] (m : M)
    (hm : m ∈ (x'.asIdeal • ⊤ : Submodule C M)) :
    m ∈ ((pt B x').asIdeal • ⊤ : Submodule B M) := by
  refine Submodule.smul_induction_on (p := fun m => m ∈ ((pt B x').asIdeal • ⊤ :
    Submodule B M)) hm (fun c hc n _ => ?_) (fun a b ha hb => Submodule.add_mem _ ha hb)
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj S c
  have hb : b ∈ (pt B x').asIdeal := by
    change algebraMap B C b ∈ x'.asIdeal
    rw [← hbs]; exact Ideal.mul_mem_right _ _ hc
  have hunit : IsUnit (algebraMap B C s) := IsLocalization.map_units C s
  have : c • n = b • (((hunit.unit⁻¹ : Cˣ) : C) • n) := by
    rw [← algebraMap_smul C b, smul_smul, ← hbs, mul_assoc,
      Units.mul_inv_eq_one.mpr hunit.unit_spec.symm, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul hb Submodule.mem_top

end Strata

section Inj

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B)
  (x' : PrimeSpectrum C)

/-- The `injective₀` hypothesis for the base-changed datum reduces to that of `Q`. -/
theorem inj₀Q (v : ↥(Q.N₀ (pt B x')))
    (h : u₀Q S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x'.asIdeal.primeCompl
          (Q.Pi₁.baseChange C))).restrictScalars C ⊔
        x'.asIdeal • (⊤ : Submodule C (stalk C x' (C ⊗[B] Q.T₀)))) :
    Q.u₀ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map (pt B x').asIdeal.primeCompl
          Q.Pi₁)).restrictScalars B ⊔
        (pt B x').asIdeal • (⊤ : Submodule B (stalk B (pt B x') Q.T₀)) := by
  rw [u₀Q_tmul, one_smul] at h
  obtain ⟨r', hr', z', hz', hsum⟩ := Submodule.mem_sup.mp h
  rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hr'
  obtain ⟨a', rfl⟩ := hr'
  obtain ⟨a, rfl⟩ := (β₁Q S Q x').surjective a'
  rw [← β_map_Pi₁] at hsum
  set u := Q.u₀ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v)
  set r := LocalizedModule.map (pt B x').asIdeal.primeCompl Q.Pi₁ a
  have hz : z' = β₀Q S Q x' (u - r) := by
    rw [map_sub, ← hsum, add_sub_cancel_left]
  have hzB := smul_top_restrictScalars_le S x' _ z' hz'
  rw [hz] at hzB
  have hn : u - r ∈ ((pt B x').asIdeal • ⊤ : Submodule B (stalk B (pt B x') Q.T₀)) := by
    have h2 := Submodule.mem_map_of_mem (f := (β₀Q S Q x').symm.toLinearMap) hzB
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at h2
    exact h2
  rw [← add_sub_cancel r u]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right hn)

/-- The `injective₁` hypothesis for the base-changed datum reduces to that of `Q`. -/
theorem inj₁Q (v : ↥(Q.N₁ (pt B x')))
    (h : u₁Q S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x'.asIdeal.primeCompl
          (Q.Pi₀.baseChange C))).restrictScalars C ⊔
        x'.asIdeal • (⊤ : Submodule C (stalk C x' (C ⊗[B] Q.T₁)))) :
    Q.u₁ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map (pt B x').asIdeal.primeCompl
          Q.Pi₀)).restrictScalars B ⊔
        (pt B x').asIdeal • (⊤ : Submodule B (stalk B (pt B x') Q.T₁)) := by
  rw [u₁Q_tmul, one_smul] at h
  obtain ⟨r', hr', z', hz', hsum⟩ := Submodule.mem_sup.mp h
  rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hr'
  obtain ⟨a', rfl⟩ := hr'
  obtain ⟨a, rfl⟩ := (β₀Q S Q x').surjective a'
  rw [← β_map_Pi₀] at hsum
  set u := Q.u₁ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪] v)
  set r := LocalizedModule.map (pt B x').asIdeal.primeCompl Q.Pi₀ a
  have hz : z' = β₁Q S Q x' (u - r) := by
    rw [map_sub, ← hsum, add_sub_cancel_left]
  have hzB := smul_top_restrictScalars_le S x' _ z' hz'
  rw [hz] at hzB
  have hn : u - r ∈ ((pt B x').asIdeal • ⊤ : Submodule B (stalk B (pt B x') Q.T₁)) := by
    have h2 := Submodule.mem_map_of_mem (f := (β₁Q S Q x').symm.toLinearMap) hzB
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] at h2
    exact h2
  rw [← add_sub_cancel r u]
  exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨a, rfl⟩) (Submodule.mem_sup_right hn)

end Inj

section Datum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
variable (S : Submonoid B) [IsLocalization S C] (Q : DrinfeldDatum (K := K) π B)

/-- The base change of a Drinfeld datum `Q` over `B` to a localization `C` of `B`. -/
def bcDatum : DrinfeldDatum (K := K) π C where
  N₀ := fun x' => Q.N₀ (pt B x')
  N₁ := fun x' => Q.N₁ (pt B x')
  full₀ := fun _ => Q.full₀ _
  full₁ := fun _ => Q.full₁ _
  le := fun _ => Q.le _
  smul_le := fun _ => Q.smul_le _
  isOpen_setOf_mem₀ := fun v =>
    (Q.isOpen_setOf_mem₀ v).preimage (PrimeSpectrum.continuous_comap (algebraMap B C))
  isOpen_setOf_mem₁ := fun v =>
    (Q.isOpen_setOf_mem₁ v).preimage (PrimeSpectrum.continuous_comap (algebraMap B C))
  T₀ := C ⊗[B] Q.T₀
  T₁ := C ⊗[B] Q.T₁
  invertible₀ := inferInstance
  invertible₁ := inferInstance
  Pi₀ := Q.Pi₀.baseChange C
  Pi₁ := Q.Pi₁.baseChange C
  Pi₁_Pi₀ := baseChange_comp_apply Q.Pi₀ Q.Pi₁ Q.Pi₁_Pi₀
  Pi₀_Pi₁ := baseChange_comp_apply Q.Pi₁ Q.Pi₀ Q.Pi₀_Pi₁
  u₀ := fun x' => u₀Q S Q x'
  u₁ := fun x' => u₁Q S Q x'
  u₁_incl := fun x' w => u₁Q_incl S Q x' w
  u₀_smul := fun x' w => u₀Q_smul S Q x' w
  u₀_surjective := fun x' => u₀Q_surjective S Q x'
  u₁_surjective := fun x' => u₁Q_surjective S Q x'
  u₀_continuous := fun x' v hv => u₀Q_continuous S Q x' v hv
  u₁_continuous := fun x' v hv => u₁Q_continuous S Q x' v hv
  locallyConstant₀ := fun x' h => by
    obtain ⟨U, hU, hxU, HU⟩ := Q.locallyConstant₀ _ ((range_baseChange_le_iff Q.Pi₀ x').mp h)
    exact ⟨_, hU.preimage (PrimeSpectrum.continuous_comap (algebraMap B C)), hxU,
      fun y' hy' hy's => HU _ hy' ((range_baseChange_le_iff Q.Pi₀ y').mp hy's)⟩
  locallyConstant₁ := fun x' h => by
    obtain ⟨U, hU, hxU, HU⟩ := Q.locallyConstant₁ _ ((range_baseChange_le_iff Q.Pi₁ x').mp h)
    exact ⟨_, hU.preimage (PrimeSpectrum.continuous_comap (algebraMap B C)), hxU,
      fun y' hy' hy's => HU _ hy' ((range_baseChange_le_iff Q.Pi₁ y').mp hy's)⟩
  injective₀ := fun x' v h => Q.injective₀ _ v (inj₀Q S Q x' v h)
  injective₁ := fun x' v h => Q.injective₁ _ v (inj₁Q S Q x' v h)
  hasDetIndex₀ := fun x' h => Q.hasDetIndex₀ _ ((range_baseChange_le_iff Q.Pi₀ x').mp h)
  hasDetIndex₁ := fun x' h => Q.hasDetIndex₁ _ ((range_baseChange_le_iff Q.Pi₁ x').mp h)

/-- `bcDatum S Q` is a base change of `Q` along `B → C`. -/
theorem isBaseChangeAlong_bcDatum :
    Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B C) (bcDatum S Q) :=
  ⟨{ N₀_eq := fun _ => rfl
     N₁_eq := fun _ => rfl
     τ₀ := τbc 𝒪 B C Q.T₀
     τ₁ := τbc 𝒪 B C Q.T₁
     span_range_τ₀ := span_range_τbc Q.T₀
     span_range_τ₁ := span_range_τbc Q.T₁
     τ₁_Pi₀ := fun t => by
       change (1 : C) ⊗ₜ[B] Q.Pi₀ t = (Q.Pi₀.baseChange C) ((1 : C) ⊗ₜ[B] t)
       rw [LinearMap.baseChange_tmul]
     τ₀_Pi₁ := fun t => by
       change (1 : C) ⊗ₜ[B] Q.Pi₁ t = (Q.Pi₁.baseChange C) ((1 : C) ⊗ₜ[B] t)
       rw [LinearMap.baseChange_tmul]
     u₀_eq := fun x' v _ hv' t s hs H => by
       have H' : Q.u₀ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪]
           (⟨v, hv'⟩ : ↥(Q.N₀ (pt B x')))) = LocalizedModule.mk t ⟨s, hs⟩ := H
       change u₀Q S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q.N₀ (pt B x')))) = _
       rw [u₀Q_tmul, one_smul, H']
       exact β₀Q_mk S Q x' t s hs
     u₁_eq := fun x' v _ hv' t s hs H => by
       have H' : Q.u₁ (pt B x') ((1 : locRing B (pt B x')) ⊗ₜ[𝒪]
           (⟨v, hv'⟩ : ↥(Q.N₁ (pt B x')))) = LocalizedModule.mk t ⟨s, hs⟩ := H
       change u₁Q S Q x' ((1 : locRing C x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q.N₁ (pt B x')))) = _
       rw [u₁Q_tmul, one_smul, H']
       exact β₁Q_mk S Q x' t s hs }⟩

end Datum

end CerednikDrinfeld.FormalOmega.DrinfeldDatum.LocBC

end
