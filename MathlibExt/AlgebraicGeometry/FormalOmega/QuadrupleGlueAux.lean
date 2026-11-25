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
`CF_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap`
`CF_exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top`
`CF_DrinfeldDatum_exists_forall_isBaseChangeAlong_away_of_overlap`
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
import MathlibExt.AlgebraicGeometry.FormalOmega.InvertibleModule
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleBaseChange

/-!
# Auxiliary lemmas for gluing Drinfeld data

Helper lemmas used in `MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleGlue`: localization
bookkeeping, semilinear maps along localizations, and identifications of stalks.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.QuadrupleGlueAux

open CerednikDrinfeld.FormalOmega.DrinfeldDatum

section Rings

variable {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S] {T : Type} [CommRing T]
  [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- If `S` is the localization of `R` away from `x` and `T` the localization away from `x * y`,
then `T` is the localization of `S` away from the image of `y`. -/
theorem away_cancel (x y : R) [IsLocalization.Away x S] [IsLocalization.Away (x * y) T] :
    IsLocalization.Away (algebraMap R S y) T := by
  have hle : Submonoid.powers (x * y) ≤ Submonoid.powers x ⊔ Submonoid.powers y := by
    rintro _ ⟨n, rfl⟩
    change (x * y) ^ n ∈ _
    rw [mul_pow]
    exact Submonoid.mem_sup.mpr ⟨_, ⟨n, rfl⟩, _, ⟨n, rfl⟩, rfl⟩
  have h1 : IsLocalization (Submonoid.powers x ⊔ Submonoid.powers y) T := by
    refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (x * y)) _ hle ?_
    intro n hn
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hn
    refine ⟨(x * y) ^ (a + b), ⟨a + b, rfl⟩, ?_⟩
    rw [mul_pow, pow_add, pow_add]
    exact mul_dvd_mul (Dvd.intro _ rfl) (Dvd.intro_left _ rfl)
  have h2 : IsLocalization ((Submonoid.powers x ⊔ Submonoid.powers y).map (algebraMap R S)) T :=
    IsLocalization.isLocalization_of_submonoid_le S T (Submonoid.powers x) _ le_sup_left
  have hle' : Submonoid.powers (algebraMap R S y) ≤
      (Submonoid.powers x ⊔ Submonoid.powers y).map (algebraMap R S) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨y ^ n, Submonoid.mem_sup.mpr ⟨1, ⟨0, (pow_zero x)⟩, _, ⟨n, rfl⟩, one_mul _⟩,
      map_pow _ _ _⟩
  refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers (algebraMap R S y)) _ hle'
    ?_).mpr h2
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hm
  refine ⟨algebraMap R S y ^ b, ⟨b, rfl⟩, ?_⟩
  rw [map_mul, map_pow, map_pow]
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := S) x).pow a
  exact ⟨↑u⁻¹, by rw [← hu, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

end Rings

section Restrict

variable {B : Type} [CommRing B] {A : Type} [CommRing A] [Algebra B A]
  {M : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M]
  {N : Type} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower B A N]

/-- A localization map over `A` at the image of `S` is a localization map over `B` at `S`. -/
theorem isLocalizedModule_restrictScalars (S : Submonoid B) (g : M →ₗ[A] N)
    [h : IsLocalizedModule (S.map (algebraMap B A)) g] :
    IsLocalizedModule S (g.restrictScalars B) where
  map_units s := by
    have hu := h.map_units ⟨algebraMap B A s, s, s.2, rfl⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    have heq : ∀ n : N, (algebraMap B (Module.End B N) ↑s) n =
        (algebraMap A (Module.End A N) (algebraMap B A ↑s)) n :=
      fun n => by simp only [Module.algebraMap_end_apply, algebraMap_smul]
    exact ⟨fun a b hab => hu.1 (by rw [← heq, ← heq]; exact hab), fun n => by
      obtain ⟨m, hm⟩ := hu.2 n; exact ⟨m, by rw [heq]; exact hm⟩⟩
  surj n := by
    obtain ⟨⟨m, ⟨_, s, hs, rfl⟩⟩, e⟩ := h.surj n
    exact ⟨⟨m, ⟨s, hs⟩⟩, by
      simpa only [Submonoid.smul_def, algebraMap_smul, LinearMap.restrictScalars_apply] using e⟩
  exists_of_eq {m m'} e := by
    obtain ⟨⟨_, s, hs, rfl⟩, hc⟩ :=
      h.exists_of_eq (by simpa only [LinearMap.restrictScalars_apply] using e)
    exact ⟨⟨s, hs⟩, by simpa only [Submonoid.smul_def, algebraMap_smul] using hc⟩

end Restrict

section SemilinearGen

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C]
  {M : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M]
  {N : Type} [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]

/-- A map semilinear along an algebra map `φ : A → C` compatible with `B`, as a `B`-linear map. -/
def linB (φ : A →ₐ[𝒪] C) (hφ : ∀ b, φ (algebraMap B A b) = algebraMap B C b)
    (τ : M →ₛₗ[(φ : A →+* C)] N) : M →ₗ[B] N where
  toFun := τ
  map_add' a b := map_add τ a b
  map_smul' b m := by
    rw [← algebraMap_smul A b m, LinearMap.map_smulₛₗ]
    change φ (algebraMap B A b) • τ m = b • τ m
    rw [hφ, algebraMap_smul]

end SemilinearGen

section Semilinear

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [Algebra A C] [IsScalarTower 𝒪 A C]
  [IsScalarTower B A C]
  {M : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M]
  {N : Type} [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]

/-- The structure map `A → C` is compatible with the `B`-algebra structures. -/
theorem toAlgHom_algebraMap (b : B) :
    (IsScalarTower.toAlgHom 𝒪 A C) (algebraMap B A b) = algebraMap B C b :=
  (IsScalarTower.algebraMap_apply B A C b).symm

/-- A spanning semilinear map between invertible modules along a localization away from `y` is a
`B`-linear localization map. -/
theorem isLocalizedModule_linB (y : B) [IsLocalization.Away (algebraMap B A y) C]
    [Module.Invertible A M] [Module.Invertible C N]
    (τ : M →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] N)
    (hτ : Submodule.span C (Set.range τ) = ⊤) :
    IsLocalizedModule (Submonoid.powers y)
      (linB (IsScalarTower.toAlgHom 𝒪 A C) toAlgHom_algebraMap τ) := by
  let : Module A N := Module.compHom N (algebraMap A C)
  have : IsScalarTower A C N := ⟨fun a c n => by
    change (a • c) • n = (algebraMap A C a) • (c • n); rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower B A N := ⟨fun b a n => by
    change (algebraMap A C (b • a)) • n = b • ((algebraMap A C a) • n)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul]⟩
  let τA : M →ₗ[A] N :=
    { toFun := τ
      map_add' := fun a b => map_add τ a b
      map_smul' := fun a m => by rw [LinearMap.map_smulₛₗ]; rfl }
  have hsurj : Function.Surjective (τA.liftBaseChange C) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← hτ]
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩)
  have hbc : IsBaseChange C τA :=
    IsBaseChange.of_equiv
      (LinearEquiv.ofBijective _ (Module.Invertible.bijective_of_surjective hsurj))
      (fun t => by rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul])
  have hA : IsLocalizedModule (Submonoid.powers (algebraMap B A y)) τA :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap B A y)) C τA).mpr hbc
  have : IsLocalizedModule ((Submonoid.powers y).map (algebraMap B A)) τA := by
    rw [Submonoid.map_powers]; exact hA
  exact isLocalizedModule_restrictScalars (Submonoid.powers y) τA

end Semilinear

section Witness

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}

/-- Two base-change witnesses along equal algebra maps have equal maps `τ₀`, `τ₁`. -/
theorem tau_eq_of_eq {A : Type} [CommRing A] [Algebra 𝒪 A] {D : Type} [CommRing D] [Algebra 𝒪 D]
    {g g' : A →ₐ[𝒪] D} (hg : g = g') {Q : DrinfeldDatum (K := K) π A}
    {Q' : DrinfeldDatum (K := K) π D} (W : Q.BaseChangeAlong g Q') (W' : Q.BaseChangeAlong g' Q') :
    (∀ t, W.τ₀ t = W'.τ₀ t) ∧ (∀ t, W.τ₁ t = W'.τ₁ t) := by
  subst hg
  exact BaseChangeAlong.tau_unique g W W'

/-- Transport a base-change witness along an equality of algebra maps. -/
def castAlong {A : Type} [CommRing A] [Algebra 𝒪 A] {D : Type} [CommRing D] [Algebra 𝒪 D]
    {g g' : A →ₐ[𝒪] D} (hg : g = g') {Q : DrinfeldDatum (K := K) π A}
    {Q' : DrinfeldDatum (K := K) π D} (W : Q.BaseChangeAlong g Q') : Q.BaseChangeAlong g' Q' :=
  hg ▸ W

/-- Composites of base-change witnesses along two equal composite maps agree. -/
theorem comp_eq_comp {A : Type} [CommRing A] [Algebra 𝒪 A] {C₁ : Type} [CommRing C₁]
    [Algebra 𝒪 C₁] {C₂ : Type} [CommRing C₂] [Algebra 𝒪 C₂] {D : Type} [CommRing D] [Algebra 𝒪 D]
    (ga : A →ₐ[𝒪] C₁) (ha : C₁ →ₐ[𝒪] D) (gb : A →ₐ[𝒪] C₂) (hb : C₂ →ₐ[𝒪] D)
    (heq : ha.comp ga = hb.comp gb)
    {Q : DrinfeldDatum (K := K) π A} {Qa : DrinfeldDatum (K := K) π C₁}
    {Qb : DrinfeldDatum (K := K) π C₂} {Q₃ : DrinfeldDatum (K := K) π D}
    (Wa : Q.BaseChangeAlong ga Qa) (Wa' : Qa.BaseChangeAlong ha Q₃)
    (Wb : Q.BaseChangeAlong gb Qb) (Wb' : Qb.BaseChangeAlong hb Q₃) :
    (∀ t, Wa'.τ₀ (Wa.τ₀ t) = Wb'.τ₀ (Wb.τ₀ t)) ∧ (∀ t, Wa'.τ₁ (Wa.τ₁ t) = Wb'.τ₁ (Wb.τ₁ t)) := by
  obtain ⟨Wca, hca₀, hca₁⟩ := BaseChangeAlong.exists_comp ga ha Wa Wa'
  obtain ⟨Wcb, hcb₀, hcb₁⟩ := BaseChangeAlong.exists_comp gb hb Wb Wb'
  obtain ⟨h₀, h₁⟩ := tau_eq_of_eq heq Wca Wcb
  exact ⟨fun t => by rw [← hca₀, h₀, hcb₀], fun t => by rw [← hca₁, h₁, hcb₁]⟩

end Witness

section Lift

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]

/-- Algebra maps out of a localization of `B` that agree on `B` are equal. -/
theorem algHom_ext_of_isLocalization (S : Submonoid B) {A : Type} [CommRing A] [Algebra 𝒪 A]
    [Algebra B A] [IsScalarTower 𝒪 B A] [IsLocalization S A] {D : Type} [CommRing D]
    [Algebra 𝒪 D] [Algebra B D] (φ ψ : A →ₐ[𝒪] D)
    (hφ : ∀ b, φ (algebraMap B A b) = algebraMap B D b)
    (hψ : ∀ b, ψ (algebraMap B A b) = algebraMap B D b) : φ = ψ := by
  have h : (φ : A →+* D) = (ψ : A →+* D) :=
    IsLocalization.ringHom_ext S (RingHom.ext fun b => by simp [hφ, hψ])
  exact AlgHom.ext fun a => RingHom.congr_fun h a

/-- The `𝒪`-algebra map out of a localization away from `x` to an algebra where `x` is a unit. -/
noncomputable def liftAlgHom (x : B) {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
    [IsScalarTower 𝒪 B A] [IsLocalization.Away x A] {D : Type} [CommRing D] [Algebra 𝒪 D]
    [Algebra B D] [IsScalarTower 𝒪 B D] (hx : IsUnit (algebraMap B D x)) : A →ₐ[𝒪] D :=
  { IsLocalization.Away.lift x hx with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_ofClass]
      rw [IsScalarTower.algebraMap_apply 𝒪 B A, IsLocalization.Away.lift_eq,
        ← IsScalarTower.algebraMap_apply] }

/-- `liftAlgHom` is compatible with the maps from `B`. -/
theorem liftAlgHom_algebraMap (x : B) {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
    [IsScalarTower 𝒪 B A] [IsLocalization.Away x A] {D : Type} [CommRing D] [Algebra 𝒪 D]
    [Algebra B D] [IsScalarTower 𝒪 B D] (hx : IsUnit (algebraMap B D x)) (b : B) :
    liftAlgHom (𝒪 := 𝒪) x hx (algebraMap B A b) = algebraMap B D b :=
  IsLocalization.Away.lift_eq x hx b

end Lift

section Triple

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
  {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
  {C₁ : Type} [CommRing C₁] [Algebra 𝒪 C₁] [Algebra B C₁] [Algebra A C₁]
  [IsScalarTower B A C₁] [IsScalarTower 𝒪 A C₁]
  {C₂ : Type} [CommRing C₂] [Algebra 𝒪 C₂] [Algebra B C₂] [Algebra A C₂] [IsScalarTower B A C₂]
  [IsScalarTower 𝒪 A C₂]
  {D : Type} [CommRing D] [Algebra 𝒪 D] [Algebra B D] [Algebra C₂ D]
  [IsScalarTower B C₂ D] [IsScalarTower 𝒪 C₂ D]

/-- Two routes `A → D` through `C₁` and `C₂` agree when `A` is a localization of `B`. -/
theorem comp_eq_of_isLocalization (S : Submonoid B) [IsLocalization S A] (h : C₁ →ₐ[𝒪] D)
    (hh : ∀ b, h (algebraMap B C₁ b) = algebraMap B D b) :
    h.comp (IsScalarTower.toAlgHom 𝒪 A C₁) =
      (IsScalarTower.toAlgHom 𝒪 C₂ D).comp (IsScalarTower.toAlgHom 𝒪 A C₂) := by
  apply algHom_ext_of_isLocalization S
  · intro b
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply B A C₁ b,
      hh]
  · intro b
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply,
      ← IsScalarTower.algebraMap_apply B A C₂ b, ← IsScalarTower.algebraMap_apply B C₂ D b]

/-- On a triple overlap, the base change of `Q₁` along `h : C₁ → D` exists and is `Q₃`. -/
theorem nonempty_witness_lift (S : Submonoid B) [IsLocalization S A] (x y : B)
    [IsLocalization.Away x C₁] [IsLocalization.Away (x * y) D] (h : C₁ →ₐ[𝒪] D)
    (hh : ∀ b, h (algebraMap B C₁ b) = algebraMap B D b)
    {Q : DrinfeldDatum (K := K) π A} {Q₁ : DrinfeldDatum (K := K) π C₁}
    {Q₂ : DrinfeldDatum (K := K) π C₂} {Q₃ : DrinfeldDatum (K := K) π D}
    (Wa : Q.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 A C₁) Q₁)
    (Wb : Q.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 A C₂) Q₂)
    (Wc : Q₂.BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 C₂ D) Q₃) :
    Nonempty (Q₁.BaseChangeAlong h Q₃) := by
  let alg : Algebra C₁ D := (h : C₁ →+* D).toAlgebra
  have : IsScalarTower B C₁ D := IsScalarTower.of_algebraMap_eq (fun b => (hh b).symm)
  have : IsScalarTower 𝒪 C₁ D := IsScalarTower.of_algebraMap_eq (fun r => (h.commutes r).symm)
  have : IsLocalization.Away (algebraMap B C₁ y) D := away_cancel x y
  obtain ⟨Q₃', hQ₃'⟩ := exists_isBaseChangeAlong_of_isLocalization Q₁
    (Submonoid.powers (algebraMap B C₁ y)) D
  have hta : IsScalarTower.toAlgHom 𝒪 C₁ D = h := AlgHom.ext fun _ => rfl
  let Wd : Q₁.BaseChangeAlong h Q₃' := castAlong hta hQ₃'.some
  obtain ⟨Wb3, -, -⟩ := BaseChangeAlong.exists_comp _ _ Wb Wc
  obtain ⟨Wa3, -, -⟩ := BaseChangeAlong.exists_comp _ _ Wa Wd
  have hm := comp_eq_of_isLocalization (A := A) (C₂ := C₂) S h hh
  obtain ⟨e, -, -⟩ := BaseChangeAlong.exists_iso _ (castAlong hm Wa3) Wb3
  exact isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic h ⟨Wd⟩ ⟨e⟩

end Triple

/-- Glue the maps `Π₀`, `Π₁` from local pieces to localization-glued modules `N0`, `N1`. -/
theorem piGlue
    {B : Type} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤) (c : B)
    (M0 M1 : Fin k → Type) [∀ i, AddCommGroup (M0 i)] [∀ i, Module B (M0 i)]
    [∀ i, AddCommGroup (M1 i)] [∀ i, Module B (M1 i)]
    (X0 X1 : Fin k → Fin k → Type) [∀ i j, AddCommGroup (X0 i j)] [∀ i j, Module B (X0 i j)]
    [∀ i j, AddCommGroup (X1 i j)] [∀ i j, Module B (X1 i j)]
    (ρl0 : ∀ i j, M0 i →ₗ[B] X0 i j) (ρr0 : ∀ i j, M0 j →ₗ[B] X0 i j)
    (ρl1 : ∀ i j, M1 i →ₗ[B] X1 i j) (ρr1 : ∀ i j, M1 j →ₗ[B] X1 i j)
    (hρr0 : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr0 i j))
    (hρr1 : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr1 i j))
    (N0 N1 : Type) [AddCommGroup N0] [Module B N0] [AddCommGroup N1] [Module B N1]
    (p0 : ∀ i, N0 →ₗ[B] M0 i) (p1 : ∀ i, N1 →ₗ[B] M1 i)
    (hp0 : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p0 i))
    (hp1 : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p1 i))
    (hp0c : ∀ i j, ρl0 i j ∘ₗ p0 i = ρr0 i j ∘ₗ p0 j)
    (hp1c : ∀ i j, ρl1 i j ∘ₗ p1 i = ρr1 i j ∘ₗ p1 j)
    (P0 : ∀ i, M0 i →ₗ[B] M1 i) (P1 : ∀ i, M1 i →ₗ[B] M0 i)
    (hP10 : ∀ i m, P1 i (P0 i m) = c • m) (hP01 : ∀ i m, P0 i (P1 i m) = c • m)
    (Y0 : ∀ i j, X0 i j →ₗ[B] X1 i j) (Y1 : ∀ i j, X1 i j →ₗ[B] X0 i j)
    (hl0 : ∀ i j m, ρl1 i j (P0 i m) = Y0 i j (ρl0 i j m))
    (hr0 : ∀ i j m, ρr1 i j (P0 j m) = Y0 i j (ρr0 i j m))
    (hl1 : ∀ i j m, ρl0 i j (P1 i m) = Y1 i j (ρl1 i j m))
    (hr1 : ∀ i j m, ρr0 i j (P1 j m) = Y1 i j (ρr1 i j m)) :
    ∃ (Pi0 : N0 →ₗ[B] N1) (Pi1 : N1 →ₗ[B] N0),
      (∀ i t, p1 i (Pi0 t) = P0 i (p0 i t)) ∧ (∀ i t, p0 i (Pi1 t) = P1 i (p1 i t)) ∧
      (∀ t, Pi1 (Pi0 t) = c • t) ∧ (∀ t, Pi0 (Pi1 t) = c • t) := by
  have hg0 : ∀ i j, ρl1 i j ∘ₗ (P0 i ∘ₗ p0 i) = ρr1 i j ∘ₗ (P0 j ∘ₗ p0 j) := by
    intro i j
    ext t
    simp only [LinearMap.comp_apply]
    rw [hl0, hr0, ← LinearMap.comp_apply (ρl0 i j), hp0c, LinearMap.comp_apply]
  obtain ⟨Pi0, hPi0, -⟩ := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M1
    X1 ρl1 ρr1 hρr1 N1 p1 hp1 hp1c N0 (fun i => P0 i ∘ₗ p0 i) hg0
  have hg1 : ∀ i j, ρl0 i j ∘ₗ (P1 i ∘ₗ p1 i) = ρr0 i j ∘ₗ (P1 j ∘ₗ p1 j) := by
    intro i j
    ext t
    simp only [LinearMap.comp_apply]
    rw [hl1, hr1, ← LinearMap.comp_apply (ρl1 i j), hp1c, LinearMap.comp_apply]
  obtain ⟨Pi1, hPi1, -⟩ := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M0
    X0 ρl0 ρr0 hρr0 N0 p0 hp0 hp0c N1 (fun i => P1 i ∘ₗ p1 i) hg1
  have hPi0' : ∀ i t, p1 i (Pi0 t) = P0 i (p0 i t) := fun i t => by
    simpa using congrArg (fun F : N0 →ₗ[B] M1 i => F t) (hPi0 i)
  have hPi1' : ∀ i t, p0 i (Pi1 t) = P1 i (p1 i t) := fun i t => by
    simpa using congrArg (fun F : N1 →ₗ[B] M0 i => F t) (hPi1 i)
  refine ⟨Pi0, Pi1, hPi0', hPi1', ?_, ?_⟩
  · have hgc : ∀ i j, ρl0 i j ∘ₗ (c • p0 i) = ρr0 i j ∘ₗ (c • p0 j) := by
      intro i j
      rw [LinearMap.comp_smul, LinearMap.comp_smul, hp0c]
    have U0 := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M0 X0 ρl0 ρr0
      hρr0 N0 p0 hp0 hp0c N0 (fun i => c • p0 i) hgc
    have h1 : ∀ i, p0 i ∘ₗ (Pi1 ∘ₗ Pi0) = c • p0 i := by
      intro i; ext t
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hPi1', hPi0', hP10]
    have h2 : ∀ i, p0 i ∘ₗ (c • (LinearMap.id : N0 →ₗ[B] N0)) = c • p0 i := by
      intro i; rw [LinearMap.comp_smul, LinearMap.comp_id]
    intro t
    simpa using congrArg (fun F : N0 →ₗ[B] N0 => F t) (U0.unique h1 h2)
  · have hgc : ∀ i j, ρl1 i j ∘ₗ (c • p1 i) = ρr1 i j ∘ₗ (c • p1 j) := by
      intro i j
      rw [LinearMap.comp_smul, LinearMap.comp_smul, hp1c]
    have U1 := IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top f hf M1 X1 ρl1 ρr1
      hρr1 N1 p1 hp1 hp1c N1 (fun i => c • p1 i) hgc
    have h1 : ∀ i, p1 i ∘ₗ (Pi0 ∘ₗ Pi1) = c • p1 i := by
      intro i; ext t
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hPi0', hPi1', hP01]
    have h2 : ∀ i, p1 i ∘ₗ (c • (LinearMap.id : N1 →ₗ[B] N1)) = c • p1 i := by
      intro i; rw [LinearMap.comp_smul, LinearMap.comp_id]
    intro t
    simpa using congrArg (fun F : N1 →ₗ[B] N1 => F t) (U1.unique h1 h2)

/-- The triple-overlap ring `C j l` localized away from `f i`. -/
abbrev D3 {B : Type} [CommRing B] {k : ℕ} (f : Fin k → B) (C : Fin k → Fin k → Type)
    [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] (i j l : Fin k) : Type :=
  Localization.Away (algebraMap B (C j l) (f i))

section Stalks

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]

/-- The local ring of a localization at a prime is a localization of `B` at the prime below. -/
theorem isLocalization_atPrime_locRing (S : Submonoid B) [IsLocalization S C]
    (y : PrimeSpectrum C) :
    haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    IsLocalization.AtPrime (locRing C y) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal :=
  haveI : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S (locRing C y) y.asIdeal

variable (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
  (T' : Type) [AddCommGroup T'] [Module C T'] [Module.Invertible C T'] [Module B T']
  [IsScalarTower B C T']

/-- A semilinear map along `B → C` viewed as a `B`-linear map. -/
def τB (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T') :
    T →ₗ[B] T' :=
  { toFun := τ, map_add' := fun a b => map_add τ a b, map_smul' := fun b t => by
      rw [LinearMap.map_smulₛₗ]
      change algebraMap B C b • τ t = b • τ t
      exact algebraMap_smul C b (τ t) }

/-- A spanning semilinear map between invertible modules is a base change. -/
theorem isBaseChange_τB
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) :
    IsBaseChange C (τB T T' τ) := by
  have hsurj : Function.Surjective ((τB T T' τ).liftBaseChange C) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, ← top_le_iff, ← hτ]
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) (fun t => by
    rw [LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul])

/-- The composite `T → T' → (T')_y` of a semilinear map with the stalk map at `y`. -/
noncomputable def γ (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (y : PrimeSpectrum C) : T →ₗ[B] stalk C y T' :=
  ((LocalizedModule.mkLinearMap y.asIdeal.primeCompl T').restrictScalars B).comp (τB T T' τ)

omit [Module.Invertible B T] [Module.Invertible C T'] in
/-- Evaluation of `γ`. -/
theorem γ_apply (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (y : PrimeSpectrum C) (t : T) : γ T T' τ y t = LocalizedModule.mk (τ t) 1 := rfl

/-- `γ` is a localization map at the prime below `y`. -/
theorem isLocalizedModule_γ (S : Submonoid B) [IsLocalization S C]
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T')
    (hτ : Submodule.span C (Set.range τ) = ⊤) (y : PrimeSpectrum C) :
    IsLocalizedModule (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl
      (γ T T' τ y) := by
  have : IsScalarTower B C (locRing C y) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower B (locRing C y) (stalk C y T') := inferInstance
  have : IsLocalization.AtPrime (locRing C y) (PrimeSpectrum.comap (algebraMap B C) y).asIdeal :=
    isLocalization_atPrime_locRing S y
  rw [isLocalizedModule_iff_isBaseChange
    (PrimeSpectrum.comap (algebraMap B C) y).asIdeal.primeCompl (locRing C y)]
  exact IsBaseChange.comp (isBaseChange_τB T T' τ hτ)
    (IsLocalizedModule.isBaseChange y.asIdeal.primeCompl (locRing C y)
      (LocalizedModule.mkLinearMap y.asIdeal.primeCompl T'))

end Stalks

section Loc

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]

/-- The base change map `B ⊗ N → A ⊗ N` as a `B`-linear map. -/
noncomputable def ιB (A : Type) [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
    (N : FullLattice 𝒪 K) : latticeBaseChange 𝒪 K B N →ₗ[B] latticeBaseChange 𝒪 K A N :=
  { toFun := LinearMap.rTensor (↥N.1) (IsScalarTower.toAlgHom 𝒪 B A).toLinearMap
    map_add' := fun a b => map_add _ a b
    map_smul' := fun b p => by
      rw [rTensor_smul_left (IsScalarTower.toAlgHom 𝒪 B A) N b p, IsScalarTower.toAlgHom_apply,
        algebraMap_smul]
      rfl }

/-- `ιB` sends `1 ⊗ v` to `1 ⊗ v`. -/
theorem ιB_one_tmul (N : FullLattice 𝒪 K) (v : ↥N.1) :
    ιB A N ((1 : B) ⊗ₜ[𝒪] v) = (1 : A) ⊗ₜ[𝒪] v :=
  rTensor_one_tmul _ N v

/-- `ιB` is a localization map when `A` is a localization of `B`. -/
theorem isLocalizedModule_ιB (S : Submonoid B) [IsLocalization S A] (N : FullLattice 𝒪 K) :
    IsLocalizedModule S (ιB (𝒪 := 𝒪) A N) :=
  (isLocalizedModule_iff_isBaseChange S A _).mpr
    (IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 B A A (↥N.1))
      (fun p => cancelBaseChange_one_tmul (IsScalarTower.toAlgHom 𝒪 B A) (fun _ => rfl) N p))

end Loc

/-- `LocalizedModule.map` on a fraction. -/
theorem locMap_mk {R : Type} [CommRing R] (S : Submonoid R) {M N : Type} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (m : M) (s : S) :
    LocalizedModule.map S g (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s :=
  IsLocalizedModule.map_LocalizedModules S g m s

section Chart

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
  (S : Submonoid B) [IsLocalization S A]
  (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
  (T' : Type) [AddCommGroup T'] [Module A T'] [Module.Invertible A T'] [Module B T']
  [IsScalarTower B A T']
  (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T')
  (hτ : Submodule.span A (Set.range τ) = ⊤)
  (x : PrimeSpectrum B) (y : PrimeSpectrum A) (hy : PrimeSpectrum.comap (algebraMap B A) y = x)

include S hτ hy in
/-- `γ` is a localization map at `x` when `y` lies over `x`. -/
theorem isLocalizedModule_γ' : IsLocalizedModule x.asIdeal.primeCompl (γ T T' τ y) :=
  hy ▸ isLocalizedModule_γ T T' S τ hτ y

/-- The identification of the stalk of `T` at `x` with the stalk of `T'` at `y` over `x`. -/
noncomputable def βx : stalk B x T ≃ₗ[B] stalk A y T' :=
  haveI := isLocalizedModule_γ' (𝒪 := 𝒪) S T T' τ hτ x y hy
  IsLocalizedModule.iso x.asIdeal.primeCompl (γ (𝒪 := 𝒪) T T' τ y)

include hy in
/-- Elements outside `x` map to elements outside `y`. -/
theorem mem_primeCompl_of {s : B} (hs : s ∈ x.asIdeal.primeCompl) :
    algebraMap B A s ∈ y.asIdeal.primeCompl := by
  subst hy; exact hs

/-- `βx` on fractions. -/
theorem βx_mk (t : T) (s : B) (hs : s ∈ x.asIdeal.primeCompl) :
    βx (𝒪 := 𝒪) S T T' τ hτ x y hy (LocalizedModule.mk t ⟨s, hs⟩) =
      LocalizedModule.mk (τ t)
        (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl) := by
  have := isLocalizedModule_γ' (𝒪 := 𝒪) S T T' τ hτ x y hy
  change IsLocalizedModule.iso x.asIdeal.primeCompl (γ (𝒪 := 𝒪) T T' τ y)
    (LocalizedModule.mk t ⟨s, hs⟩) = _
  apply ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (γ (𝒪 := 𝒪) T T' τ y) ⟨s, hs⟩)).1
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_smul,
    LocalizedModule.smul'_mk, ← algebraMap_smul A s (LocalizedModule.mk (τ t)
      (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl)),
    LocalizedModule.smul'_mk]
  have h1 : LocalizedModule.mk (s • t) (⟨s, hs⟩ : x.asIdeal.primeCompl) =
      LocalizedModule.mk t 1 :=
    LocalizedModule.mk_cancel ⟨s, hs⟩ t
  have h2 : LocalizedModule.mk (algebraMap B A s • τ t)
      (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl) =
        LocalizedModule.mk (τ t) 1 :=
    LocalizedModule.mk_cancel
      (⟨algebraMap B A s, mem_primeCompl_of x y hy hs⟩ : y.asIdeal.primeCompl) (τ t)
  rw [h1, h2, IsLocalizedModule.iso_mk_one, γ_apply]

end Chart

section ChartNat

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
  (S : Submonoid B) [IsLocalization S A]
  (T₀ : Type) [AddCommGroup T₀] [Module B T₀] [Module.Invertible B T₀]
  (T₀' : Type) [AddCommGroup T₀'] [Module A T₀'] [Module.Invertible A T₀'] [Module B T₀']
  [IsScalarTower B A T₀']
  (τ₀ : T₀ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T₀')
  (hτ₀ : Submodule.span A (Set.range τ₀) = ⊤)
  (T₁ : Type) [AddCommGroup T₁] [Module B T₁] [Module.Invertible B T₁]
  (T₁' : Type) [AddCommGroup T₁'] [Module A T₁'] [Module.Invertible A T₁'] [Module B T₁']
  [IsScalarTower B A T₁']
  (τ₁ : T₁ →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T₁')
  (hτ₁ : Submodule.span A (Set.range τ₁) = ⊤)
  (x : PrimeSpectrum B) (y : PrimeSpectrum A) (hy : PrimeSpectrum.comap (algebraMap B A) y = x)

/-- `βx` is natural in compatible maps `P`, `P'`. -/
theorem βx_natural (P : T₀ →ₗ[B] T₁) (P' : T₀' →ₗ[A] T₁') (hP : ∀ t, τ₁ (P t) = P' (τ₀ t))
    (m : stalk B x T₀) :
    βx (𝒪 := 𝒪) S T₁ T₁' τ₁ hτ₁ x y hy (LocalizedModule.map x.asIdeal.primeCompl P m) =
      LocalizedModule.map y.asIdeal.primeCompl P' (βx (𝒪 := 𝒪) S T₀ T₀' τ₀ hτ₀ x y hy m) := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [locMap_mk, βx_mk S T₁ T₁' τ₁ hτ₁ x y hy (P t) s s.2,
      βx_mk S T₀ T₀' τ₀ hτ₀ x y hy t s s.2, locMap_mk, hP]

end ChartNat

section TauP

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A] (g : B)
  [IsLocalization.Away g A]
  (T : Type) [AddCommGroup T] [Module B T]
  (T' : Type) [AddCommGroup T'] [Module A T'] [Module B T'] [IsScalarTower B A T']
  (p : T →ₗ[B] T') [IsLocalizedModule (Submonoid.powers g) p]

/-- A `B`-linear map into an `A`-module as a semilinear map along `B → A`. -/
def τp : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T' :=
  { toFun := p, map_add' := fun a b => map_add p a b, map_smul' := fun b t => by
      rw [map_smul]
      change b • p t = algebraMap B A b • p t
      exact (algebraMap_smul A b (p t)).symm }

/-- Evaluation of `τp`. -/
theorem τp_apply (t : T) : τp (𝒪 := 𝒪) (A := A) T T' p t = p t := rfl

include g in
/-- The range of a localization map spans. -/
theorem span_range_τp : Submodule.span A (Set.range (τp (𝒪 := 𝒪) (A := A) T T' p)) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalizedModule.surj (Submonoid.powers g) p m
  have hunit : IsUnit (algebraMap B A s) := IsLocalization.map_units A s
  have : m = ((hunit.unit⁻¹ : Aˣ) : A) • p t := by
    rw [← hts, Submonoid.smul_def, ← algebraMap_smul A (s : B), smul_smul,
      Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

end TauP

section Transfer

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
  (SA : Submonoid B) [IsLocalization SA A]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
  (SC : Submonoid B) [IsLocalization SC C]
  [Algebra A C] [IsScalarTower B A C] [IsScalarTower 𝒪 A C]
  (T : Type) [AddCommGroup T] [Module B T] [Module.Invertible B T]
  {T' : Type} [AddCommGroup T'] [Module A T'] [Module.Invertible A T'] [Module B T']
  [IsScalarTower B A T']
  {T'' : Type} [AddCommGroup T''] [Module C T''] [Module.Invertible C T''] [Module B T'']
  [IsScalarTower B C T'']

/-- Transfer a stalk identity along a base-change map `σ : T' → T''` over `A → C`. -/
theorem transfer (σ : T' →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] T'')
    (x : PrimeSpectrum B) (w : PrimeSpectrum C)
    (a : stalk A (pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w) T') (b : stalk C w T'')
    (hU : ∀ (t : T') (s : A) (hs : (IsScalarTower.toAlgHom 𝒪 A C) s ∉ w.asIdeal),
      a = LocalizedModule.mk t ⟨s, hs⟩ → b = LocalizedModule.mk (σ t) ⟨_, hs⟩)
    (τA : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T')
    (hτA : Submodule.span A (Set.range τA) = ⊤)
    (q : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T'')
    (hq : Submodule.span C (Set.range q) = ⊤) (hqτ : ∀ t, q t = σ (τA t))
    (hw : PrimeSpectrum.comap (algebraMap B C) w = x)
    (hy : PrimeSpectrum.comap (algebraMap B A) (pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w) = x)
    (m : stalk B x T) (H : a = βx (𝒪 := 𝒪) SA T T' τA hτA x _ hy m) :
    b = βx (𝒪 := 𝒪) SC T T'' q hq x w hw m := by
  induction m using LocalizedModule.induction_on with
  | h t s =>
    rw [βx_mk] at H
    rw [βx_mk, hU (τA t) (algebraMap B A s) (mem_primeCompl_of x _ hy s.2) H]
    congr 1
    · exact (hqτ t).symm
    · apply Subtype.ext
      change (IsScalarTower.toAlgHom 𝒪 A C) (algebraMap B A s) = algebraMap B C s
      rw [IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply]

end Transfer

section Geo

variable {B : Type} [CommRing B]

/-- Some `f i` lies outside any given prime when the `f i` span the unit ideal. -/
theorem exists_not_mem_of_span {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (x : PrimeSpectrum B) : ∃ i : Fin k, f i ∉ x.asIdeal := by
  by_contra h
  push Not at h
  apply x.isPrime.ne_top
  rw [eq_top_iff, ← hf]
  exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)

/-- A prime not containing `g` comes from the localization away from `g`. -/
theorem exists_comap_eq {A : Type} [CommRing A] [Algebra B A] (g : B) [IsLocalization.Away g A]
    (x : PrimeSpectrum B) (hx : g ∉ x.asIdeal) :
    ∃ y : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap B A) y = x := by
  have : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B A)) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]; exact hx
  exact this

/-- `comap` along a localization away from `g` is injective. -/
theorem comap_injective {A : Type} [CommRing A] [Algebra B A] (g : B) [IsLocalization.Away g A]
    {y y' : PrimeSpectrum A}
    (h : PrimeSpectrum.comap (algebraMap B A) y = PrimeSpectrum.comap (algebraMap B A) y') :
    y = y' :=
  PrimeSpectrum.localization_comap_injective A (Submonoid.powers g) h

/-- A prime in the image of `comap` along a localization away from `g` does not contain `g`. -/
theorem not_mem_of_comap_eq {A : Type} [CommRing A] [Algebra B A] (g : B)
    [IsLocalization.Away g A] {x : PrimeSpectrum B} {y : PrimeSpectrum A}
    (hy : PrimeSpectrum.comap (algebraMap B A) y = x) : g ∉ x.asIdeal := by
  have : x ∈ Set.range (PrimeSpectrum.comap (algebraMap B A)) := ⟨y, hy⟩
  rwa [PrimeSpectrum.localization_away_comap_range _ g] at this

/-- `comap` of a point under a tower. -/
theorem comap_pointUnder {𝒪 : Type} [CommRing 𝒪] [Algebra 𝒪 B] {A : Type} [CommRing A]
    [Algebra 𝒪 A] [Algebra B A] {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [Algebra A C]
    [IsScalarTower B A C] [IsScalarTower 𝒪 A C] (w : PrimeSpectrum C) :
    PrimeSpectrum.comap (algebraMap B A) (pointUnder (IsScalarTower.toAlgHom 𝒪 A C) w) =
      PrimeSpectrum.comap (algebraMap B C) w := by
  apply PrimeSpectrum.ext
  ext b
  change algebraMap A C (algebraMap B A b) ∈ w.asIdeal ↔ algebraMap B C b ∈ w.asIdeal
  rw [← IsScalarTower.algebraMap_apply]

end Geo

section Span

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A] [IsScalarTower 𝒪 B A]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C]
  [Algebra A C] [IsScalarTower B A C] [IsScalarTower 𝒪 A C]
  {T : Type} [AddCommGroup T] [Module B T] {T' : Type} [AddCommGroup T'] [Module A T']
  {T'' : Type} [AddCommGroup T''] [Module C T'']

/-- Composition of semilinear maps along `B → A → C`. -/
def compσ (σ : T' →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] T'')
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T') :
    T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B C : B →ₐ[𝒪] C) : B →+* C)] T'' :=
  { toFun := fun t => σ (τ t)
    map_add' := fun a b => by rw [map_add, map_add]
    map_smul' := fun b t => by
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
      change (IsScalarTower.toAlgHom 𝒪 A C) ((IsScalarTower.toAlgHom 𝒪 B A) b) • σ (τ t) =
        algebraMap B C b • σ (τ t)
      rw [IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply,
        ← IsScalarTower.algebraMap_apply] }

/-- The composite of spanning semilinear maps spans. -/
theorem span_range_compσ
    (σ : T' →ₛₗ[((IsScalarTower.toAlgHom 𝒪 A C : A →ₐ[𝒪] C) : A →+* C)] T'')
    (τ : T →ₛₗ[((IsScalarTower.toAlgHom 𝒪 B A : B →ₐ[𝒪] A) : B →+* A)] T')
    (hσ : Submodule.span C (Set.range σ) = ⊤) (hτ : Submodule.span A (Set.range τ) = ⊤) :
    Submodule.span C (Set.range (compσ σ τ)) = ⊤ := by
  have key : ∀ t' : T', σ t' ∈ Submodule.span C (Set.range (compσ σ τ)) := by
    intro t'
    have ht' : t' ∈ Submodule.span A (Set.range τ) := by rw [hτ]; exact Submodule.mem_top
    induction ht' using Submodule.span_induction with
    | mem u hu => obtain ⟨t, rfl⟩ := hu; exact Submodule.subset_span ⟨t, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul a u _ hu => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hu
  rw [eq_top_iff, ← hσ]
  apply Submodule.span_le.mpr
  rintro _ ⟨t', rfl⟩
  exact key t'

end Span

/-- The image of `𝔭 • ⊤` under a `B`-linear map to an `A`-module lies in `y • ⊤`. -/
theorem map_smul_top_le {B : Type} [CommRing B] {A : Type} [CommRing A] [Algebra B A]
    (y : PrimeSpectrum A) {M : Type} [AddCommGroup M] [Module B M]
    {M' : Type} [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower B A M']
    (e : M →ₗ[B] M') :
    ((PrimeSpectrum.comap (algebraMap B A) y).asIdeal • (⊤ : Submodule B M)).map e ≤
      (y.asIdeal • (⊤ : Submodule A M')).restrictScalars B := by
  rintro _ ⟨m, hm, rfl⟩
  rw [Submodule.restrictScalars_mem]
  refine Submodule.smul_induction_on hm (fun b hb n _ => ?_) (fun m₁ m₂ h₁ h₂ => ?_)
  · have hb' : algebraMap B A b ∈ y.asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hb
      exact hb
    rw [LinearMap.map_smul, ← algebraMap_smul A b (e n)]
    exact Submodule.smul_mem_smul hb' Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

/-- If `range P ⊆ 𝔭 • ⊤` then `range P' ⊆ y • ⊤` for the localized map `P'` at `y` over `𝔭`. -/
theorem range_le_smul_top_of_isLocalizedModule
    {B : Type} [CommRing B] {A : Type} [CommRing A] [Algebra B A] (g : B)
    [IsLocalization.Away g A]
    {T₀ T₁ : Type} [AddCommGroup T₀] [Module B T₀] [AddCommGroup T₁] [Module B T₁]
    {T₀' T₁' : Type} [AddCommGroup T₀'] [Module A T₀'] [Module B T₀'] [IsScalarTower B A T₀']
    [AddCommGroup T₁'] [Module A T₁'] [Module B T₁'] [IsScalarTower B A T₁']
    (p₀ : T₀ →ₗ[B] T₀') [IsLocalizedModule (Submonoid.powers g) p₀] (p₁ : T₁ →ₗ[B] T₁')
    (P : T₀ →ₗ[B] T₁) (P' : T₀' →ₗ[A] T₁') (hP : ∀ t, p₁ (P t) = P' (p₀ t))
    (y : PrimeSpectrum A)
    (h : LinearMap.range P ≤
      (PrimeSpectrum.comap (algebraMap B A) y).asIdeal • (⊤ : Submodule B T₁)) :
    LinearMap.range P' ≤ y.asIdeal • (⊤ : Submodule A T₁') := by
  rintro _ ⟨t', rfl⟩
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalizedModule.surj (Submonoid.powers g) p₀ t'
  obtain ⟨u, hu⟩ := IsLocalization.map_units A s
  have e1 : P' (p₀ t) = (algebraMap B A (s : B)) • P' t' := by
    rw [← hts, Submonoid.smul_def, ← algebraMap_smul A (s : B) t', LinearMap.map_smul]
  have e2 : P' t' = ((u⁻¹ : Aˣ) : A) • P' (p₀ t) := by
    rw [e1, ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [e2, ← hP]
  exact Submodule.smul_mem _ _ (map_smul_top_le y p₁ (Submodule.mem_map_of_mem (h ⟨t, rfl⟩)))

/-- Including along an equality of lattices and back is the identity. -/
theorem inclBaseChange_inclBaseChange {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] (B : Type) [CommRing B] [Algebra 𝒪 B] (M M' : FullLattice 𝒪 K) (h : M'.1 = M.1)
    (p : latticeBaseChange 𝒪 K B M) :
    inclBaseChange B (M' := M') (M := M) (le_of_eq h)
      (inclBaseChange B (M' := M) (M := M') (le_of_eq h.symm) p) = p := by
  induction p using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul b w =>
    simp only [inclBaseChange, LinearMap.baseChange_tmul]
    rfl

end CerednikDrinfeld.FormalOmega.QuadrupleGlueAux

end
