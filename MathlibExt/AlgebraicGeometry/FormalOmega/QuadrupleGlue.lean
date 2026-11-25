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
import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeStd
import MathlibExt.AlgebraicGeometry.FormalOmega.InvertibleModule
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleBaseChange
import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleGlueAux

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega
open CerednikDrinfeld.FormalOmega.QuadrupleGlueAux

/-- Gluing the invertible modules of Drinfeld data on the pieces `Spec B_{f i}` of a cover along
base-change witnesses on the overlaps `C i j` gives invertible `B`-modules `T₀`, `T₁` with maps
`Π₀`, `Π₁` that localize to the given ones and are compatible with the witnesses. -/
theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
    (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)]
    [∀ i j, Algebra 𝒪 (C i j)]
    [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
    [∀ i j, Algebra (Localization.Away (f i)) (C i j)]
    [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
    (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
    (Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
    (Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j))
    [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
    [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁] :
    ∃ (T₀ T₁ : Type) (_ : AddCommGroup T₀) (_ : AddCommGroup T₁) (_ : Module B T₀)
      (_ : Module B T₁) (_ : Module.Invertible B T₀) (_ : Module.Invertible B T₁)
      (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀) (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀)
      (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁),
      (∀ t, Pi₁ (Pi₀ t) = algebraMap 𝒪 B π • t) ∧ (∀ t, Pi₀ (Pi₁ t) = algebraMap 𝒪 B π • t) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)) ∧
      (∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) ∧ (∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t)) ∧
      (∀ i j t, (Wl i j).τ₀ (p₀ i t) = (Wr i j).τ₀ (p₀ j t)) ∧
      (∀ i j t, (Wl i j).τ₁ (p₁ i t) = (Wr i j).τ₁ (p₁ j t)) := by
  classical
  let mC₀ : ∀ i j, Module B (Q₂ i j).T₀ := fun i j => Module.compHom _ (algebraMap B (C i j))
  have tC₀ : ∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₀ := fun i j => ⟨fun b c t => by
    change (b • c) • t = algebraMap B (C i j) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  let mC₁ : ∀ i j, Module B (Q₂ i j).T₁ := fun i j => Module.compHom _ (algebraMap B (C i j))
  have tC₁ : ∀ i j, IsScalarTower B (C i j) (Q₂ i j).T₁ := fun i j => ⟨fun b c t => by
    change (b • c) • t = algebraMap B (C i j) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  have ex3 : ∀ i j l : Fin k, ∃ Q₃ : DrinfeldDatum (K := K) π (D3 f C i j l),
      (Q₂ j l).IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)) Q₃ :=
    fun i j l => DrinfeldDatum.exists_isBaseChangeAlong_of_isLocalization (Q₂ j l)
      (Submonoid.powers (algebraMap B (C j l) (f i))) (D3 f C i j l)
  choose Q₃ hQ₃ using ex3
  let W₃ : ∀ i j l, (Q₂ j l).BaseChangeAlong
      (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)) (Q₃ i j l) := fun i j l => (hQ₃ i j l).some
  let mD₀ : ∀ i j l, Module B (Q₃ i j l).T₀ := fun i j l =>
    Module.compHom _ (algebraMap B (D3 f C i j l))
  have tD₀ : ∀ i j l, IsScalarTower B (D3 f C i j l) (Q₃ i j l).T₀ := fun i j l => ⟨fun b c t => by
    change (b • c) • t = algebraMap B (D3 f C i j l) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  let mD₁ : ∀ i j l, Module B (Q₃ i j l).T₁ := fun i j l =>
    Module.compHom _ (algebraMap B (D3 f C i j l))
  have tD₁ : ∀ i j l, IsScalarTower B (D3 f C i j l) (Q₃ i j l).T₁ := fun i j l => ⟨fun b c t => by
    change (b • c) • t = algebraMap B (D3 f C i j l) b • (c • t); rw [Algebra.smul_def, mul_smul]⟩
  have huC : ∀ i j, IsUnit (algebraMap B (C i j) (f i)) ∧ IsUnit (algebraMap B (C i j) (f j)) :=
    fun i j => ⟨IsLocalization.Away.isUnit_of_dvd (f i * f j) (Dvd.intro _ rfl),
      IsLocalization.Away.isUnit_of_dvd (f i * f j) (Dvd.intro_left _ rfl)⟩
  have huD : ∀ i j l (b : B), IsUnit (algebraMap B (C j l) b) →
      IsUnit (algebraMap B (D3 f C i j l) b) := fun i j l b hb => by
    rw [IsScalarTower.algebraMap_apply B (C j l) (D3 f C i j l)]; exact hb.map _
  have hui : ∀ i j l, IsUnit (algebraMap B (D3 f C i j l) (f i)) := fun i j l => by
    rw [IsScalarTower.algebraMap_apply B (C j l) (D3 f C i j l)]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap B (C j l) (f i))
  have hu1 : ∀ i j l, IsUnit (algebraMap B (D3 f C i j l) (f i * f j)) := fun i j l => by
    rw [map_mul]; exact (hui i j l).mul (huD i j l _ (huC j l).1)
  have hu2 : ∀ i j l, IsUnit (algebraMap B (D3 f C i j l) (f i * f l)) := fun i j l => by
    rw [map_mul]; exact (hui i j l).mul (huD i j l _ (huC j l).2)
  let h1 : ∀ i j l, C i j →ₐ[𝒪] D3 f C i j l := fun i j l => liftAlgHom (f i * f j) (hu1 i j l)
  let h2 : ∀ i j l, C i l →ₐ[𝒪] D3 f C i j l := fun i j l => liftAlgHom (f i * f l) (hu2 i j l)
  have hh1 : ∀ i j l (b : B), h1 i j l (algebraMap B (C i j) b) = algebraMap B (D3 f C i j l) b :=
    fun i j l b => liftAlgHom_algebraMap (f i * f j) (hu1 i j l) b
  have hh2 : ∀ i j l (b : B), h2 i j l (algebraMap B (C i l) b) = algebraMap B (D3 f C i j l) b :=
    fun i j l b => liftAlgHom_algebraMap (f i * f l) (hu2 i j l) b
  have aw0 : ∀ i j l, IsLocalization.Away (f i * (f j * f l)) (D3 f C i j l) := fun i j l =>
    IsLocalization.Away.mul (C j l) (D3 f C i j l) (f j * f l) (f i)
  have aw1 : ∀ i j l, IsLocalization.Away (f i * f j * f l) (D3 f C i j l) := fun i j l => by
    rw [mul_assoc]; exact aw0 i j l
  have aw2 : ∀ i j l, IsLocalization.Away (f i * f l * f j) (D3 f C i j l) := fun i j l => by
    rw [mul_assoc, mul_comm (f l)]; exact aw0 i j l
  have hW₁ : ∀ i j l, Nonempty ((Q₂ i j).BaseChangeAlong (h1 i j l) (Q₃ i j l)) := fun i j l =>
    nonempty_witness_lift (A := Localization.Away (f j)) (Submonoid.powers (f j)) (f i * f j)
      (f l) (h1 i j l) (hh1 i j l) (Wr i j) (Wl j l) (W₃ i j l)
  have hW₂ : ∀ i j l, Nonempty ((Q₂ i l).BaseChangeAlong (h2 i j l) (Q₃ i j l)) := fun i j l =>
    nonempty_witness_lift (A := Localization.Away (f l)) (Submonoid.powers (f l)) (f i * f l)
      (f j) (h2 i j l) (hh2 i j l) (Wr i l) (Wr j l) (W₃ i j l)
  let W₁ : ∀ i j l, (Q₂ i j).BaseChangeAlong (h1 i j l) (Q₃ i j l) := fun i j l => (hW₁ i j l).some
  let W₂ : ∀ i j l, (Q₂ i l).BaseChangeAlong (h2 i j l) (Q₃ i j l) := fun i j l => (hW₂ i j l).some
  have hm1 : ∀ i j l, (h1 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j))
      = (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)).comp
        (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C j l)) :=
    fun i j l => comp_eq_of_isLocalization (Submonoid.powers (f j)) (h1 i j l) (hh1 i j l)
  have hm2 : ∀ i j l, (h2 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f l)) (C i l))
      = (IsScalarTower.toAlgHom 𝒪 (C j l) (D3 f C i j l)).comp
        (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f l)) (C j l)) :=
    fun i j l => comp_eq_of_isLocalization (Submonoid.powers (f l)) (h2 i j l) (hh2 i j l)
  have hm12 : ∀ i j l,
      (h1 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) =
        (h2 i j l).comp (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i l)) := by
    intro i j l
    apply algHom_ext_of_isLocalization (Submonoid.powers (f i))
    · intro b
      rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
        ← IsScalarTower.algebraMap_apply B _ (C i j) b, hh1]
    · intro b
      rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
        ← IsScalarTower.algebraMap_apply B _ (C i l) b, hh2]
  have towBl : ∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j) := fun i j => inferInstance
  have towBr : ∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j) := fun i j => inferInstance
  have hWW : ∀ i, (∀ t, (Wl i i).τ₀ t = (Wr i i).τ₀ t) ∧ (∀ t, (Wl i i).τ₁ t = (Wr i i).τ₁ t) :=
    fun i => tau_eq_of_eq (by
      apply algHom_ext_of_isLocalization (Submonoid.powers (f i))
      · intro b; exact (@IsScalarTower.algebraMap_apply B _ _ _ _ _ _ (_) _ (towBl i i) b).symm
      · intro b; exact (@IsScalarTower.algebraMap_apply B _ _ _ _ _ _ (_) _ (towBr i i) b).symm)
      (Wl i i) (Wr i i)
  let ρl₀ : ∀ i j, (Q i).T₀ →ₗ[B] (Q₂ i j).T₀ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wl i j).τ₀
  let ρr₀ : ∀ i j, (Q j).T₀ →ₗ[B] (Q₂ i j).T₀ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wr i j).τ₀
  have hρr₀ : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr₀ i j) := fun i j => by
    have : IsLocalization.Away (f j * f i) (C i j) := by rw [mul_comm]; infer_instance
    have : IsLocalization.Away (algebraMap B (Localization.Away (f j)) (f i)) (C i j) :=
      away_cancel (f j) (f i)
    exact isLocalizedModule_linB (f i) (Wr i j).τ₀ (Wr i j).span_range_τ₀
  let σ₃₀ : ∀ i j l, (Q₂ j l).T₀ →ₗ[B] (Q₃ i j l).T₀ := fun i j l =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (W₃ i j l).τ₀
  have hσ₃₀ : ∀ i j l, IsLocalizedModule (Submonoid.powers (f i)) (σ₃₀ i j l) := fun i j l =>
    isLocalizedModule_linB (f i) (W₃ i j l).τ₀ (W₃ i j l).span_range_τ₀
  let σ₁₀ : ∀ i j l, (Q₂ i j).T₀ →ₗ[B] (Q₃ i j l).T₀ := fun i j l =>
    linB (h1 i j l) (hh1 i j l) (W₁ i j l).τ₀
  let σ₂₀ : ∀ i j l, (Q₂ i l).T₀ →ₗ[B] (Q₃ i j l).T₀ := fun i j l =>
    linB (h2 i j l) (hh2 i j l) (W₂ i j l).τ₀
  have hdiag₀ : ∀ i, ρl₀ i i = ρr₀ i i := fun i =>
    LinearMap.ext fun t => (hWW i).1 t
  have hcoc₁₀ : ∀ i j l, σ₁₀ i j l ∘ₗ ρl₀ i j = σ₂₀ i j l ∘ₗ ρl₀ i l := fun i j l =>
    LinearMap.ext fun t =>
      (comp_eq_comp _ _ _ _ (hm12 i j l) (Wl i j) (W₁ i j l) (Wl i l) (W₂ i j l)).1 t
  have hcoc₂₀ : ∀ i j l, σ₁₀ i j l ∘ₗ ρr₀ i j = σ₃₀ i j l ∘ₗ ρl₀ j l := fun i j l =>
    LinearMap.ext fun t =>
      (comp_eq_comp _ _ _ _ (hm1 i j l) (Wr i j) (W₁ i j l) (Wl j l) (W₃ i j l)).1 t
  have hcoc₃₀ : ∀ i j l, σ₂₀ i j l ∘ₗ ρr₀ i l = σ₃₀ i j l ∘ₗ ρr₀ j l := fun i j l =>
    LinearMap.ext fun t =>
      (comp_eq_comp _ _ _ _ (hm2 i j l) (Wr i l) (W₂ i j l) (Wr j l) (W₃ i j l)).1 t
  have hid₀ : ∀ i, IsLocalizedModule (Submonoid.powers (f i))
      (LinearMap.id : (Q i).T₀ →ₗ[B] (Q i).T₀) := fun i =>
    isLocalizedModule_id (Submonoid.powers (f i)) ((Q i).T₀) (Localization.Away (f i))
  obtain ⟨T₀, _iT₀a, _iT₀m, p₀, hp₀, hp₀c⟩ :=
    IsLocalizedModule.exists_forall_isLocalizedModule_comp_eq_of_span_eq_top f hf
      (fun i => (Q i).T₀) hid₀ (fun i j => (Q₂ i j).T₀) ρl₀ ρr₀ hρr₀ hdiag₀
      (fun i j l => (Q₃ i j l).T₀) σ₁₀ σ₂₀ σ₃₀ hσ₃₀ hcoc₁₀ hcoc₂₀ hcoc₃₀
  have hinv₀ : Module.Invertible B T₀ :=
    Module.Invertible.of_isLocalizedModule_of_span_range_eq_top f hf T₀ (fun i => (Q i).T₀)
      (fun i => Localization.Away (f i)) p₀ hp₀ (fun i => (Q i).invertible₀)
  let ρl₁ : ∀ i j, (Q i).T₁ →ₗ[B] (Q₂ i j).T₁ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wl i j).τ₁
  let ρr₁ : ∀ i j, (Q j).T₁ →ₗ[B] (Q₂ i j).T₁ := fun i j =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (Wr i j).τ₁
  have hρr₁ : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr₁ i j) := fun i j => by
    have : IsLocalization.Away (f j * f i) (C i j) := by rw [mul_comm]; infer_instance
    have : IsLocalization.Away (algebraMap B (Localization.Away (f j)) (f i)) (C i j) :=
      away_cancel (f j) (f i)
    exact isLocalizedModule_linB (f i) (Wr i j).τ₁ (Wr i j).span_range_τ₁
  let σ₃₁ : ∀ i j l, (Q₂ j l).T₁ →ₗ[B] (Q₃ i j l).T₁ := fun i j l =>
    linB (IsScalarTower.toAlgHom 𝒪 _ _) toAlgHom_algebraMap (W₃ i j l).τ₁
  have hσ₃₁ : ∀ i j l, IsLocalizedModule (Submonoid.powers (f i)) (σ₃₁ i j l) := fun i j l =>
    isLocalizedModule_linB (f i) (W₃ i j l).τ₁ (W₃ i j l).span_range_τ₁
  let σ₁₁ : ∀ i j l, (Q₂ i j).T₁ →ₗ[B] (Q₃ i j l).T₁ := fun i j l =>
    linB (h1 i j l) (hh1 i j l) (W₁ i j l).τ₁
  let σ₂₁ : ∀ i j l, (Q₂ i l).T₁ →ₗ[B] (Q₃ i j l).T₁ := fun i j l =>
    linB (h2 i j l) (hh2 i j l) (W₂ i j l).τ₁
  have hdiag₁ : ∀ i, ρl₁ i i = ρr₁ i i := fun i =>
    LinearMap.ext fun t => (hWW i).2 t
  have hcoc₁₁ : ∀ i j l, σ₁₁ i j l ∘ₗ ρl₁ i j = σ₂₁ i j l ∘ₗ ρl₁ i l := fun i j l =>
    LinearMap.ext fun t =>
      (comp_eq_comp _ _ _ _ (hm12 i j l) (Wl i j) (W₁ i j l) (Wl i l) (W₂ i j l)).2 t
  have hcoc₂₁ : ∀ i j l, σ₁₁ i j l ∘ₗ ρr₁ i j = σ₃₁ i j l ∘ₗ ρl₁ j l := fun i j l =>
    LinearMap.ext fun t =>
      (comp_eq_comp _ _ _ _ (hm1 i j l) (Wr i j) (W₁ i j l) (Wl j l) (W₃ i j l)).2 t
  have hcoc₃₁ : ∀ i j l, σ₂₁ i j l ∘ₗ ρr₁ i l = σ₃₁ i j l ∘ₗ ρr₁ j l := fun i j l =>
    LinearMap.ext fun t =>
      (comp_eq_comp _ _ _ _ (hm2 i j l) (Wr i l) (W₂ i j l) (Wr j l) (W₃ i j l)).2 t
  have hid₁ : ∀ i, IsLocalizedModule (Submonoid.powers (f i))
      (LinearMap.id : (Q i).T₁ →ₗ[B] (Q i).T₁) := fun i =>
    isLocalizedModule_id (Submonoid.powers (f i)) ((Q i).T₁) (Localization.Away (f i))
  obtain ⟨T₁, _iT₁a, _iT₁m, p₁, hp₁, hp₁c⟩ :=
    IsLocalizedModule.exists_forall_isLocalizedModule_comp_eq_of_span_eq_top f hf
      (fun i => (Q i).T₁) hid₁ (fun i j => (Q₂ i j).T₁) ρl₁ ρr₁ hρr₁ hdiag₁
      (fun i j l => (Q₃ i j l).T₁) σ₁₁ σ₂₁ σ₃₁ hσ₃₁ hcoc₁₁ hcoc₂₁ hcoc₃₁
  have hinv₁ : Module.Invertible B T₁ :=
    Module.Invertible.of_isLocalizedModule_of_span_range_eq_top f hf T₁ (fun i => (Q i).T₁)
      (fun i => Localization.Away (f i)) p₁ hp₁ (fun i => (Q i).invertible₁)
  obtain ⟨Pi0, Pi1, hA, hB, hC, hD⟩ := piGlue f hf (algebraMap 𝒪 B π)
    (fun i => (Q i).T₀) (fun i => (Q i).T₁) (fun i j => (Q₂ i j).T₀) (fun i j => (Q₂ i j).T₁)
    ρl₀ ρr₀ ρl₁ ρr₁ hρr₀ hρr₁ T₀ T₁ p₀ p₁ hp₀ hp₁ hp₀c hp₁c
    (fun i => ((Q i).Pi₀).restrictScalars B) (fun i => ((Q i).Pi₁).restrictScalars B)
    (fun i m => by
      rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, (Q i).Pi₁_Pi₀,
        IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f i)), algebraMap_smul])
    (fun i m => by
      rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, (Q i).Pi₀_Pi₁,
        IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away (f i)), algebraMap_smul])
    (fun i j => ((Q₂ i j).Pi₀).restrictScalars B) (fun i j => ((Q₂ i j).Pi₁).restrictScalars B)
    (fun i j m => (Wl i j).τ₁_Pi₀ m) (fun i j m => (Wr i j).τ₁_Pi₀ m)
    (fun i j m => (Wl i j).τ₀_Pi₁ m) (fun i j m => (Wr i j).τ₀_Pi₁ m)
  exact ⟨T₀, T₁, inferInstance, inferInstance, inferInstance, inferInstance, hinv₀, hinv₁, Pi0,
    Pi1, p₀, p₁, hC, hD, hp₀, hp₁, hA, hB, fun i j t => LinearMap.congr_fun (hp₀c i j) t,
    fun i j t => LinearMap.congr_fun (hp₁c i j) t⟩

/-- Point-wise data on the pieces `Spec B_{f i}` of a cover that agree over the same points of
`Spec B` glue to point-wise data on `Spec B` with open membership loci. -/
theorem CerednikDrinfeld.FormalOmega.exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
    (hf : Ideal.span (Set.range f) = ⊤)
    (N : ∀ i : Fin k, PrimeSpectrum (Localization.Away (f i)) → Submodule 𝒪 (Fin 2 → K))
    (hN : ∀ (i : Fin k) (v : Fin 2 → K),
      IsOpen {y : PrimeSpectrum (Localization.Away (f i)) | v ∈ N i y})
    (hcompat : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i)))
      (z : PrimeSpectrum (Localization.Away (f j))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z →
          N i y = N j z) :
    ∃ Ng : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K),
      (∀ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
          Ng (DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y)
            = N i y) ∧
      ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ Ng x} := by
  classical
  have cover : ∀ x : PrimeSpectrum B, ∃ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
      DrinfeldDatum.pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y = x := by
    intro x
    obtain ⟨i, hi⟩ := exists_not_mem_of_span f hf x
    obtain ⟨y, hy⟩ := exists_comap_eq (A := Localization.Away (f i)) (f i) x hi
    exact ⟨i, y, hy⟩
  choose ι υ hιυ using cover
  refine ⟨fun x => N (ι x) (υ x), fun i y => hcompat _ _ _ _ (hιυ _), fun v => ?_⟩
  have hset : {x : PrimeSpectrum B | v ∈ N (ι x) (υ x)} =
      ⋃ i, PrimeSpectrum.comap (algebraMap B (Localization.Away (f i))) ''
        {y : PrimeSpectrum (Localization.Away (f i)) | v ∈ N i y} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hv
      exact ⟨ι x, υ x, hv, hιυ x⟩
    · rintro ⟨i, y, hy, rfl⟩
      let x' := PrimeSpectrum.comap (algebraMap B (Localization.Away (f i))) y
      have key := hcompat (ι x') i (υ x') y (hιυ x')
      change v ∈ N (ι x') (υ x')
      rw [key]
      exact hy
  rw [hset]
  exact isOpen_iUnion fun i => (PrimeSpectrum.localization_away_isOpenEmbedding
    (Localization.Away (f i)) (f i)).isOpenMap _ (hN i v)

section Side

open CerednikDrinfeld.FormalOmega.DrinfeldDatum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} {f : Fin k → B}
  {L : ∀ i, PrimeSpectrum (Localization.Away (f i)) → FullLattice 𝒪 K}
  {T : Fin k → Type} [∀ i, AddCommGroup (T i)] [∀ i, Module (Localization.Away (f i)) (T i)]
  [∀ i, Module.Invertible (Localization.Away (f i)) (T i)] [∀ i, Module B (T i)]
  [∀ i, IsScalarTower B (Localization.Away (f i)) (T i)]
  (u : ∀ i y, latticeBaseChange 𝒪 K (locRing (Localization.Away (f i)) y) (L i y) →ₗ[locRing
    (Localization.Away (f i)) y] stalk (Localization.Away (f i)) y (T i))
  {Ng : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)}
  (hN : ∀ i y, Ng (pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) =
    (L i y).1)
  {Tg : Type} [AddCommGroup Tg] [Module B Tg] [Module.Invertible B Tg] [Module 𝒪 Tg]
  [IsScalarTower 𝒪 B Tg]
  (p : ∀ i, Tg →ₗ[B] T i) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p i)]
  {L' : ∀ i, PrimeSpectrum (Localization.Away (f i)) → FullLattice 𝒪 K}
  {T' : Fin k → Type} [∀ i, AddCommGroup (T' i)] [∀ i, Module (Localization.Away (f i)) (T' i)]
  [∀ i, Module.Invertible (Localization.Away (f i)) (T' i)] [∀ i, Module B (T' i)]
  [∀ i, IsScalarTower B (Localization.Away (f i)) (T' i)]
  (u' : ∀ i y, latticeBaseChange 𝒪 K (locRing (Localization.Away (f i)) y) (L' i y) →ₗ[locRing
    (Localization.Away (f i)) y] stalk (Localization.Away (f i)) y (T' i))
  {Ng' : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)}
  (hN' : ∀ i y, Ng' (pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) =
    (L' i y).1)
  {Tg' : Type} [AddCommGroup Tg'] [Module B Tg'] [Module.Invertible B Tg'] [Module 𝒪 Tg']
  [IsScalarTower 𝒪 B Tg']
  (p' : ∀ i, Tg' →ₗ[B] T' i) [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p' i)]
  {ι : PrimeSpectrum B → Fin k}
  {υ : ∀ x : PrimeSpectrum B, PrimeSpectrum (Localization.Away (f (ι x)))}
  (hιυ : ∀ x, pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) (υ x) = x)

/-- The chart identification of stalks at `x` through the piece `ι x`. -/
private abbrev glue_βι (x : PrimeSpectrum B) :
    stalk B x Tg ≃ₗ[B] stalk (Localization.Away (f (ι x))) (υ x) (T (ι x)) :=
  βx (Submonoid.powers (f (ι x))) Tg (T (ι x))
    (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg (T (ι x)) (p (ι x)))
    (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x))) x (υ x) (hιυ x)

include hN hιυ in
private theorem glue_eq_chart (x : PrimeSpectrum B) : Ng x = (L (ι x) (υ x)).1 := by
  rw [← hN (ι x) (υ x), hιυ x]

include hN hιυ in
private theorem glue_mem_chart (x : PrimeSpectrum B) {v : Fin 2 → K} (hv : v ∈ Ng x) :
    v ∈ (L (ι x) (υ x)).1 :=
  glue_eq_chart hN hιυ x ▸ hv

include hN hιυ in
private theorem glue_full (x : PrimeSpectrum B) : Submodule.IsFullLattice K (Ng x) := by
  rw [glue_eq_chart hN hιυ x]; exact (L (ι x) (υ x)).2

/-- The glued lattice at `x`. -/
private abbrev glueL (x : PrimeSpectrum B) : FullLattice 𝒪 K := ⟨Ng x, glue_full hN hιυ x⟩

/-- The glued stalk map on lattice vectors. -/
private def glue_gg (x : PrimeSpectrum B) : ↥(Ng x) →ₗ[𝒪] stalk B x Tg where
  toFun v := (glue_βι p hιυ x).symm (u (ι x) (υ x)
    ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, glue_mem_chart hN hιυ x v.2⟩))
  map_add' a b := by
    change (glue_βι p hιυ x).symm _ = (glue_βι p hιυ x).symm _ + (glue_βι p hιυ x).symm _
    rw [← map_add, ← map_add, ← TensorProduct.tmul_add]; rfl
  map_smul' r v := by
    change (glue_βι p hιυ x).symm _ = r • (glue_βι p hιυ x).symm _
    rw [← algebraMap_smul B r ((glue_βι p hιυ x).symm _), ← map_smul,
      ← algebraMap_smul (locRing (Localization.Away (f (ι x))) (υ x)) (algebraMap 𝒪 B r),
      ← IsScalarTower.algebraMap_apply, ← map_smul, algebraMap_smul, ← TensorProduct.tmul_smul]
    rfl

/-- The glued stalk map at `x`. -/
private def glue_ug (x : PrimeSpectrum B) :
    latticeBaseChange 𝒪 K (locRing B x) (glueL hN hιυ x) →ₗ[locRing B x] stalk B x Tg :=
  (glue_gg u hN p hιυ x).liftBaseChange (locRing B x)

private theorem glue_ug_tmul (x : PrimeSpectrum B) (a : locRing B x) (v : ↥(Ng x)) :
    glue_ug u hN p hιυ x (a ⊗ₜ[𝒪] v) = a • (glue_βι p hιυ x).symm (u (ι x) (υ x)
      ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪] ⟨v, glue_mem_chart hN hιυ x v.2⟩)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _

private theorem glue_βι_ug (x : PrimeSpectrum B) (v : ↥(Ng x)) :
    glue_βι p hιυ x (glue_ug u hN p hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] v)) = u (ι x) (υ x)
      ((1 : locRing (Localization.Away (f (ι x))) (υ x)) ⊗ₜ[𝒪]
        ⟨v, glue_mem_chart hN hιυ x v.2⟩) := by
  rw [glue_ug_tmul, one_smul, LinearEquiv.apply_symm_apply]

private theorem glue_ug_ιB (x : PrimeSpectrum B)
    (q : latticeBaseChange 𝒪 K B (glueL hN hιυ x)) :
    glue_βι p hιυ x (glue_ug u hN p hιυ x (ιB (locRing B x) _ q)) =
      u (ι x) (υ x) (ιB (locRing (Localization.Away (f (ι x))) (υ x)) (L (ι x) (υ x))
        (inclBaseChange B (M' := glueL hN hιυ x) (M := L (ι x) (υ x))
          (le_of_eq (glue_eq_chart hN hιυ x)) q)) := by
  induction q using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v =>
    have e1 : (b ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K B (glueL hN hιυ x)) =
        b • ((1 : B) ⊗ₜ[𝒪] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e2 : inclBaseChange B (M' := glueL hN hιυ x) (M := L (ι x) (υ x))
          (le_of_eq (glue_eq_chart hN hιυ x)) (b ⊗ₜ[𝒪] v) =
        b • ((1 : B) ⊗ₜ[𝒪] (⟨v, glue_mem_chart hN hιυ x v.2⟩ : ↥(L (ι x) (υ x)).1)) := by
      rw [e1, map_smul]; rfl
    rw [e2, e1, map_smul, ιB_one_tmul, LinearMap.map_smul_of_tower, map_smul, glue_βι_ug,
      map_smul, ιB_one_tmul, LinearMap.map_smul_of_tower]

include hιυ in
private theorem glue_ug_surjective (hus : ∀ i y, Function.Surjective (u i y))
    (x : PrimeSpectrum B) : Function.Surjective (glue_ug u hN p hιυ x) := by
  intro m
  obtain ⟨q, hq⟩ := hus (ι x) (υ x) (glue_βι p hιυ x m)
  have : IsScalarTower B (Localization.Away (f (ι x)))
      (locRing (Localization.Away (f (ι x))) (υ x)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsLocalization x.asIdeal.primeCompl (locRing (Localization.Away (f (ι x))) (υ x)) := by
    have h := isLocalization_atPrime_locRing (Submonoid.powers (f (ι x))) (υ x)
    rwa [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x
      from hιυ x] at h
  have := isLocalizedModule_ιB (𝒪 := 𝒪) (A := locRing (Localization.Away (f (ι x))) (υ x))
    x.asIdeal.primeCompl (L (ι x) (υ x))
  obtain ⟨⟨q₀, s⟩, hsq⟩ := IsLocalizedModule.surj x.asIdeal.primeCompl
    (ιB (locRing (Localization.Away (f (ι x))) (υ x)) (L (ι x) (υ x))) q
  have hunit : IsUnit (algebraMap B (locRing B x) s) := IsLocalization.map_units (locRing B x) s
  have key : glue_ug u hN p hιυ x (ιB (locRing B x) _
      (inclBaseChange B (M' := L (ι x) (υ x)) (M := glueL hN hιυ x)
        (le_of_eq (glue_eq_chart hN hιυ x).symm) q₀)) = (s : B) • m := by
    apply (glue_βι p hιυ x).injective
    rw [glue_ug_ιB, inclBaseChange_inclBaseChange B (L (ι x) (υ x)) (glueL hN hιυ x)
      (glue_eq_chart hN hιυ x) q₀, ← hsq, Submonoid.smul_def, LinearMap.map_smul_of_tower, hq,
      map_smul]
  refine ⟨((hunit.unit⁻¹ : (locRing B x)ˣ) : locRing B x) • ιB (locRing B x) _
      (inclBaseChange B (M' := L (ι x) (υ x)) (M := glueL hN hιυ x)
        (le_of_eq (glue_eq_chart hN hιυ x).symm) q₀), ?_⟩
  rw [map_smul, key, ← algebraMap_smul (locRing B x) (s : B) m, smul_smul,
    Units.inv_mul_eq_one.mpr hunit.unit_spec, one_smul]

omit [∀ i, Module.Invertible (Localization.Away (f i)) (T i)] [Module.Invertible B Tg]
  [Module 𝒪 Tg] [IsScalarTower 𝒪 B Tg] [∀ i, Module.Invertible (Localization.Away (f i)) (T' i)]
  [Module.Invertible B Tg'] [Module 𝒪 Tg'] [IsScalarTower 𝒪 B Tg']
  [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p' i)] in
include hN hιυ in
private theorem glue_hasDetIndex (P : Tg →ₗ[B] Tg') (Pl : ∀ i, T i →ₗ[Localization.Away (f i)] T' i)
    (hP : ∀ i t, p' i (P t) = Pl i (p i t)) (e : ℤ)
    (hdi : ∀ i y, LinearMap.range (Pl i) ≤ y.asIdeal • (⊤ : Submodule _ (T' i)) →
      HasDetIndex π (L i y).1 e)
    (x : PrimeSpectrum B) (h : LinearMap.range P ≤ x.asIdeal • (⊤ : Submodule B Tg')) :
    HasDetIndex π (Ng x) e := by
  rw [glue_eq_chart hN hιυ x]
  refine hdi _ _ (range_le_smul_top_of_isLocalizedModule (f (ι x)) (p (ι x)) (p' (ι x)) P
    (Pl (ι x)) (hP (ι x)) (υ x) ?_)
  rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x from hιυ x]
  exact h

omit [∀ i, Module.Invertible (Localization.Away (f i)) (T i)] [Module.Invertible B Tg]
  [Module 𝒪 Tg] [IsScalarTower 𝒪 B Tg] [∀ i, Module.Invertible (Localization.Away (f i)) (T' i)]
  [Module.Invertible B Tg'] [Module 𝒪 Tg'] [IsScalarTower 𝒪 B Tg']
  [∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p' i)] in
include hN hιυ in
private theorem glue_locallyConstant (P : Tg →ₗ[B] Tg')
    (Pl : ∀ i, T i →ₗ[Localization.Away (f i)] T' i) (hP : ∀ i t, p' i (P t) = Pl i (p i t))
    (hlc : ∀ i y, LinearMap.range (Pl i) ≤ y.asIdeal • (⊤ : Submodule _ (T' i)) →
      ∃ U : Set (PrimeSpectrum (Localization.Away (f i))), IsOpen U ∧ y ∈ U ∧
        ∀ y' ∈ U, LinearMap.range (Pl i) ≤ y'.asIdeal • (⊤ : Submodule _ (T' i)) →
          (L i y').1 = (L i y).1)
    (x : PrimeSpectrum B) (h : LinearMap.range P ≤ x.asIdeal • (⊤ : Submodule B Tg')) :
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ x' ∈ U, LinearMap.range P ≤ x'.asIdeal • (⊤ : Submodule B Tg') → Ng x' = Ng x := by
  have push : ∀ (y : PrimeSpectrum (Localization.Away (f (ι x)))),
      LinearMap.range P ≤ (PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y
        ).asIdeal • (⊤ : Submodule B Tg') →
      LinearMap.range (Pl (ι x)) ≤ y.asIdeal • ⊤ := fun y hy =>
    range_le_smul_top_of_isLocalizedModule (f (ι x)) (p (ι x)) (p' (ι x)) P (Pl (ι x)) (hP (ι x))
      y hy
  obtain ⟨U, hU, hxU, HU⟩ := hlc (ι x) (υ x) (push (υ x) (by
    rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x
      from hιυ x]; exact h))
  refine ⟨PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) '' U,
    (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away (f (ι x)))
      (f (ι x))).isOpenMap _ hU, ⟨υ x, hxU, hιυ x⟩, ?_⟩
  rintro _ ⟨y, hyU, rfl⟩ hy
  rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y =
      pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) y from rfl,
    hN (ι x) y, HU y hyU (push y hy), glue_eq_chart hN hιυ x]

omit [Module 𝒪 Tg] [IsScalarTower 𝒪 B Tg] [Module 𝒪 Tg'] [IsScalarTower 𝒪 B Tg'] in
/-- Membership in `range (map P) ⊔ 𝔭 • ⊤` transports along the chart identification. -/
private theorem glue_βι_mem_sup (P : Tg' →ₗ[B] Tg) (Pl : ∀ i, T' i →ₗ[Localization.Away (f i)] T i)
    (hP : ∀ i t, p i (P t) = Pl i (p' i t)) (x : PrimeSpectrum B) (m : stalk B x Tg)
    (h : m ∈ (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl P)).restrictScalars B ⊔
      x.asIdeal • (⊤ : Submodule B (stalk B x Tg))) :
    glue_βι p hιυ x m ∈ (LinearMap.range (LocalizedModule.map (υ x).asIdeal.primeCompl
      (Pl (ι x)))).restrictScalars (Localization.Away (f (ι x))) ⊔ (υ x).asIdeal •
        (⊤ : Submodule (Localization.Away (f (ι x)))
          (stalk (Localization.Away (f (ι x))) (υ x) (T (ι x)))) := by
  obtain ⟨r, hr, z, hz, hrz⟩ := Submodule.mem_sup.mp h
  rw [← hrz, map_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [Submodule.restrictScalars_mem, LinearMap.mem_range] at hr ⊢
    obtain ⟨a, rfl⟩ := hr
    exact ⟨glue_βι p' hιυ x a, (βx_natural (Submonoid.powers (f (ι x))) Tg' (T' (ι x))
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg' (T' (ι x)) (p' (ι x)))
      (span_range_τp (f (ι x)) Tg' (T' (ι x)) (p' (ι x))) Tg (T (ι x))
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg (T (ι x)) (p (ι x)))
      (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x))) x (υ x) (hιυ x) P (Pl (ι x))
      (fun t => hP (ι x) t) a).symm⟩
  · have hz' : z ∈ ((PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x)
        ).asIdeal • ⊤ : Submodule B (stalk B x Tg)) := by
      rw [show PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) (υ x) = x
        from hιυ x]; exact hz
    exact map_smul_top_le (υ x) (glue_βι p hιυ x).toLinearMap (Submodule.mem_map_of_mem hz')

include hιυ in
private theorem glue_ug_incl (hle : ∀ x, Ng x ≤ Ng' x)
    (hlel : ∀ i y, (L i y).1 ≤ (L' i y).1) (Pg : Tg →ₗ[B] Tg')
    (Pl : ∀ i, T i →ₗ[Localization.Away (f i)] T' i) (hP : ∀ i t, p' i (Pg t) = Pl i (p i t))
    (hincl : ∀ i y w, u' i y (inclBaseChange _ (hlel i y) w) =
      LocalizedModule.map y.asIdeal.primeCompl (Pl i) (u i y w))
    (x : PrimeSpectrum B) (w : latticeBaseChange 𝒪 K (locRing B x) (glueL hN hιυ x)) :
    glue_ug u' hN' p' hιυ x (inclBaseChange (locRing B x) (M' := glueL hN hιυ x)
        (M := glueL hN' hιυ x) (hle x) w) =
      LocalizedModule.map x.asIdeal.primeCompl Pg (glue_ug u hN p hιυ x w) := by
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing B x) (glueL hN hιυ x)) =
        a • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [inclBaseChange, LinearMap.baseChange_tmul, glue_ug_tmul, glue_ug_tmul, one_smul, one_smul]
    apply (glue_βι p' hιυ x).injective
    rw [LinearEquiv.apply_symm_apply, βx_natural (Submonoid.powers (f (ι x))) Tg (T (ι x))
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg (T (ι x)) (p (ι x)))
      (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x))) Tg' (T' (ι x))
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg' (T' (ι x)) (p' (ι x)))
      (span_range_τp (f (ι x)) Tg' (T' (ι x)) (p' (ι x))) x (υ x) (hιυ x) Pg (Pl (ι x))
      (fun t => hP (ι x) t), LinearEquiv.apply_symm_apply, ← hincl, inclBaseChange,
      LinearMap.baseChange_tmul]
    rfl

include hιυ in
private theorem glue_ug_smul (hsg : ∀ x, ∀ v ∈ Ng' x, algebraMap 𝒪 K π • v ∈ Ng x)
    (hsl : ∀ i y, ∀ v ∈ (L' i y).1, algebraMap 𝒪 K π • v ∈ (L i y).1) (Pg : Tg' →ₗ[B] Tg)
    (Pl : ∀ i, T' i →ₗ[Localization.Away (f i)] T i) (hP : ∀ i t, p i (Pg t) = Pl i (p' i t))
    (hsmul : ∀ i y w, u i y ((smulInto π (hsl i y)).baseChange _ w) =
      LocalizedModule.map y.asIdeal.primeCompl (Pl i) (u' i y w))
    (x : PrimeSpectrum B) (w : latticeBaseChange 𝒪 K (locRing B x) (glueL hN' hιυ x)) :
    glue_ug u hN p hιυ x (((smulInto π (hsg x)).baseChange (locRing B x) :
        latticeBaseChange 𝒪 K (locRing B x) (glueL hN' hιυ x) →ₗ[locRing B x]
          latticeBaseChange 𝒪 K (locRing B x) (glueL hN hιυ x)) w) =
      LocalizedModule.map x.asIdeal.primeCompl Pg (glue_ug u' hN' p' hιυ x w) := by
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a v =>
    have e1 : (a ⊗ₜ[𝒪] v : latticeBaseChange 𝒪 K (locRing B x) (glueL hN' hιυ x)) =
        a • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e1, map_smul, map_smul, map_smul, map_smul]
    congr 1
    rw [LinearMap.baseChange_tmul, glue_ug_tmul, glue_ug_tmul, one_smul, one_smul]
    apply (glue_βι p hιυ x).injective
    rw [LinearEquiv.apply_symm_apply, βx_natural (Submonoid.powers (f (ι x))) Tg' (T' (ι x))
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg' (T' (ι x)) (p' (ι x)))
      (span_range_τp (f (ι x)) Tg' (T' (ι x)) (p' (ι x))) Tg (T (ι x))
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg (T (ι x)) (p (ι x)))
      (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x))) x (υ x) (hιυ x) Pg (Pl (ι x))
      (fun t => hP (ι x) t), LinearEquiv.apply_symm_apply, ← hsmul, LinearMap.baseChange_tmul]
    rfl


variable {C : Fin k → Fin k → Type} [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)]
  [∀ i j, Algebra 𝒪 (C i j)] [∀ i j, IsScalarTower 𝒪 B (C i j)]
  [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
  [∀ i j, Algebra (Localization.Away (f i)) (C i j)]
  [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
  [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)]
  [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
  [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)]
  [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
  {L₂ : ∀ i j, PrimeSpectrum (C i j) → FullLattice 𝒪 K}
  {T₂ : Fin k → Fin k → Type} [∀ i j, AddCommGroup (T₂ i j)] [∀ i j, Module (C i j) (T₂ i j)]
  [∀ i j, Module.Invertible (C i j) (T₂ i j)] [∀ i j, Module B (T₂ i j)]
  [∀ i j, IsScalarTower B (C i j) (T₂ i j)]
  {u₂ : ∀ i j w, latticeBaseChange 𝒪 K (locRing (C i j) w) (L₂ i j w) →ₗ[locRing (C i j) w]
    stalk (C i j) w (T₂ i j)}
  {τl : ∀ i j, T i →ₛₗ[((IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j) :
    Localization.Away (f i) →ₐ[𝒪] C i j) : Localization.Away (f i) →+* C i j)] T₂ i j}
  {τr : ∀ i j, T j →ₛₗ[((IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j) :
    Localization.Away (f j) →ₐ[𝒪] C i j) : Localization.Away (f j) →+* C i j)] T₂ i j}
  (hτl : ∀ i j, Submodule.span (C i j) (Set.range (τl i j)) = ⊤)
  (hNl : ∀ i j w, (L₂ i j w).1 =
    (L i (pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) w)).1)
  (hul : ∀ i j w v
    (hv : v ∈ (L i (pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) w)).1)
    (hv' : v ∈ (L₂ i j w).1) t (s : Localization.Away (f i))
    (hs : (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) s ∉ w.asIdeal),
    u i _ ((1 : locRing _ _) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(L i _).1)) = LocalizedModule.mk t ⟨s, hs⟩ →
    u₂ i j w ((1 : locRing _ w) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(L₂ i j w).1)) =
      LocalizedModule.mk (τl i j t) ⟨_, hs⟩)
  (hur : ∀ i j w v
    (hv : v ∈ (L j (pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) w)).1)
    (hv' : v ∈ (L₂ i j w).1) t (s : Localization.Away (f j))
    (hs : (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) s ∉ w.asIdeal),
    u j _ ((1 : locRing _ _) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(L j _).1)) = LocalizedModule.mk t ⟨s, hs⟩ →
    u₂ i j w ((1 : locRing _ w) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(L₂ i j w).1)) =
      LocalizedModule.mk (τr i j t) ⟨_, hs⟩)
  (hc : ∀ i j t, τl i j (p i t) = τr i j (p j t))

include hτl hNl hul hur hc in
private theorem glue_chart (x : PrimeSpectrum B) (j : Fin k)
    (z : PrimeSpectrum (Localization.Away (f j)))
    (hz : pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z = x)
    (v : Fin 2 → K) (hv : v ∈ Ng x) (hv' : v ∈ (L j z).1) :
    u j z ((1 : locRing (Localization.Away (f j)) z) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(L j z).1)) =
      βx (Submonoid.powers (f j)) Tg (T j)
        (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) Tg (T j) (p j))
        (span_range_τp (f j) Tg (T j) (p j)) x z hz
        (glue_ug u hN p hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Ng x)))) := by
  have hfij : f (ι x) * f j ∉ x.asIdeal := fun h => (x.isPrime.mem_or_mem h).elim
    (not_mem_of_comap_eq (f (ι x)) (hιυ x)) (not_mem_of_comap_eq (f j) hz)
  obtain ⟨w, hw⟩ := exists_comap_eq (A := C (ι x) j) (f (ι x) * f j) x hfij
  have hwl : PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x))))
      (pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w) = x := by
    rw [comap_pointUnder]; exact hw
  have hwr : PrimeSpectrum.comap (algebraMap B (Localization.Away (f j)))
      (pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w) = x := by
    rw [comap_pointUnder]; exact hw
  have hwy : pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w =
      υ x := comap_injective (f (ι x)) (hwl.trans (hιυ x).symm)
  have hwz : pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w = z :=
    comap_injective (f j) (hwr.trans hz.symm)
  set m := glue_ug u hN p hιυ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Ng x))) with hm
  set m' := (βx (Submonoid.powers (f j)) Tg (T j)
    (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) Tg (T j) (p j))
    (span_range_τp (f j) Tg (T j) (p j)) x z hz).symm
      (u j z ((1 : locRing (Localization.Away (f j)) z) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(L j z).1))) with hm'
  have Hi : ∀ (y' : PrimeSpectrum (Localization.Away (f (ι x))))
      (hy' : PrimeSpectrum.comap (algebraMap B (Localization.Away (f (ι x)))) y' = x)
      (hvy' : v ∈ (L (ι x) y').1), y' = υ x →
      u (ι x) y' ((1 : locRing (Localization.Away (f (ι x))) y') ⊗ₜ[𝒪]
        (⟨v, hvy'⟩ : ↥(L (ι x) y').1)) = βx (Submonoid.powers (f (ι x))) Tg (T (ι x))
          (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg (T (ι x)) (p (ι x)))
          (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x))) x y' hy' m := by
    rintro y' hy' hvy' rfl
    rw [hm, glue_ug_tmul, one_smul, LinearEquiv.apply_symm_apply]
  have Hj : ∀ (z' : PrimeSpectrum (Localization.Away (f j)))
      (hz' : PrimeSpectrum.comap (algebraMap B (Localization.Away (f j))) z' = x)
      (hvz' : v ∈ (L j z').1), z' = z →
      u j z' ((1 : locRing (Localization.Away (f j)) z') ⊗ₜ[𝒪] (⟨v, hvz'⟩ : ↥(L j z').1)) =
        βx (Submonoid.powers (f j)) Tg (T j)
          (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) Tg (T j) (p j))
          (span_range_τp (f j) Tg (T j) (p j)) x z' hz' m' := by
    rintro z' hz' hvz' rfl
    rw [hm', LinearEquiv.apply_symm_apply]
  have hvl : v ∈ (L (ι x)
      (pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f (ι x))) (C (ι x) j)) w)).1 := by
    rw [hwy]; exact glue_mem_chart hN hιυ x hv
  have hv'' : v ∈ (L₂ (ι x) j w).1 := by rw [hNl]; exact hvl
  have hvr : v ∈ (L j
      (pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C (ι x) j)) w)).1 := by
    rw [hwz]; exact hv'
  have hq := span_range_compσ _ _ (hτl (ι x) j) (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x)))
  have H1 := transfer (Submonoid.powers (f (ι x))) (Submonoid.powers (f (ι x) * f j)) Tg
    (τl (ι x) j) x w _ _ (hul (ι x) j w v hvl hv'')
    (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg (T (ι x)) (p (ι x)))
    (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x))) _ hq (fun t => rfl) hw hwl m
    (Hi _ hwl hvl hwy)
  have H2 := transfer (Submonoid.powers (f j)) (Submonoid.powers (f (ι x) * f j)) Tg
    (τr (ι x) j) x w _ _ (hur (ι x) j w v hvr hv'')
    (τp (𝒪 := 𝒪) (A := Localization.Away (f j)) Tg (T j) (p j))
    (span_range_τp (f j) Tg (T j) (p j)) _ hq (fun t => hc (ι x) j t) hw hwr m'
    (Hj _ hwr hvr hwz)
  have hmm' : m = m' := (βx _ _ _ _ _ _ _ _).injective (H1.symm.trans H2)
  rw [Hj z hz hv' rfl, ← hmm']

include hτl hNl hul hur hc in
private theorem glue_ug_continuous
    (hcont : ∀ i y v, v ∈ (L i y).1 → ∃ (c : Localization.Away (f i)) (t : T i),
      c ∉ y.asIdeal ∧ ∀ (y' : PrimeSpectrum (Localization.Away (f i))) (hy : c ∉ y'.asIdeal),
        ∃ hv : v ∈ (L i y').1, u i y' ((1 : locRing _ y') ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(L i y').1)) =
          LocalizedModule.mk t ⟨c, hy⟩)
    (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Ng x) :
    ∃ (b : B) (t : Tg), b ∉ x.asIdeal ∧ ∀ (x' : PrimeSpectrum B) (hx' : b ∉ x'.asIdeal),
      ∃ hv' : v ∈ Ng x', glue_ug u hN p hιυ x' ((1 : locRing B x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Ng x')))
        = LocalizedModule.mk t ⟨b, hx'⟩ := by
  obtain ⟨c, t', hc', H⟩ := hcont (ι x) (υ x) v (glue_mem_chart hN hιυ x hv)
  obtain ⟨⟨b₀, ⟨_, a, rfl⟩⟩, hb₀⟩ := IsLocalization.surj (Submonoid.powers (f (ι x))) c
  obtain ⟨⟨t₀, ⟨_, e, rfl⟩⟩, ht₀⟩ :=
    IsLocalizedModule.surj (Submonoid.powers (f (ι x))) (p (ι x)) t'
  have hb₀' : c * algebraMap B (Localization.Away (f (ι x))) (f (ι x)) ^ a = algebraMap B _ b₀ := by
    simpa only [map_pow] using hb₀
  have ht₀' : f (ι x) ^ e • t' = p (ι x) t₀ := by simpa only [Submonoid.smul_def] using ht₀
  clear hb₀ ht₀
  have hmem : ∀ (y : PrimeSpectrum (Localization.Away (f (ι x)))) (b : B),
      b ∈ (pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) y).asIdeal ↔
        algebraMap B _ b ∈ y.asIdeal := fun _ _ => Iff.rfl
  refine ⟨f (ι x) ^ (e + 1) * b₀, f (ι x) ^ (a + 1) • t₀, ?_, ?_⟩
  · intro hb
    rcases x.isPrime.mem_or_mem hb with h1 | h2
    · exact not_mem_of_comap_eq (f (ι x)) (hιυ x) (x.isPrime.mem_of_pow_mem _ h1)
    · have h3 : algebraMap B (Localization.Away (f (ι x))) b₀ ∈ (υ x).asIdeal := by
        rw [← hmem, hιυ x]; exact h2
      rw [← hb₀'] at h3
      rcases (υ x).isPrime.mem_or_mem h3 with h4 | h5
      · exact hc' h4
      · exact (υ x).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h5
          ((IsLocalization.Away.algebraMap_isUnit (f (ι x))).pow a))
  · intro x' hx'
    have hfi : f (ι x) ∉ x'.asIdeal := fun h =>
      hx' (Ideal.mul_mem_right b₀ _ (Ideal.pow_mem_of_mem x'.asIdeal h (e + 1) e.succ_pos))
    have hb₀x' : b₀ ∉ x'.asIdeal := fun h => hx' (Ideal.mul_mem_left _ _ h)
    obtain ⟨y', hy'⟩ := exists_comap_eq (A := Localization.Away (f (ι x))) (f (ι x)) x' hfi
    have hy'' : pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (ι x)))) y' = x' :=
      hy'
    have hcy' : c ∉ y'.asIdeal := by
      intro h
      apply hb₀x'
      have h' : algebraMap B _ b₀ ∈ y'.asIdeal := by rw [← hb₀']; exact Ideal.mul_mem_right _ _ h
      rwa [← hmem, hy''] at h'
    obtain ⟨hvy', Hy'⟩ := H y' hcy'
    have hv' : v ∈ Ng x' := by rw [← hy'', hN]; exact hvy'
    refine ⟨hv', ?_⟩
    have key := glue_chart u hN p hιυ hτl hNl hul hur hc x' (ι x) y' hy'' v hv' hvy'
    rw [Hy'] at key
    apply (βx (Submonoid.powers (f (ι x))) Tg (T (ι x))
      (τp (𝒪 := 𝒪) (A := Localization.Away (f (ι x))) Tg (T (ι x)) (p (ι x)))
      (span_range_τp (f (ι x)) Tg (T (ι x)) (p (ι x))) x' y' hy'').injective
    rw [← key]; erw [βx_mk]; rw [τp_apply, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def]
    rw [map_smul, ← ht₀', ← algebraMap_smul (Localization.Away (f (ι x))) (f (ι x) ^ (a + 1)),
      ← algebraMap_smul (Localization.Away (f (ι x))) (f (ι x) ^ e), smul_smul, smul_smul,
      map_mul, ← hb₀', map_pow, map_pow, map_pow]
    congr 1
    ring

include hτl hNl hul hur hc in
private theorem glue_u_eq (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))) (v : Fin 2 → K)
    (hv : v ∈ Ng (pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y))
    (hv' : v ∈ (L i y).1) (t : Tg) (s : B)
    (hs : (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) s ∉ y.asIdeal)
    (H : glue_ug u hN p hιυ _ ((1 : locRing B _) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Ng _))) =
      LocalizedModule.mk t ⟨s, hs⟩) :
    u i y ((1 : locRing _ y) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(L i y).1)) =
      LocalizedModule.mk (τp (𝒪 := 𝒪) (A := Localization.Away (f i)) Tg (T i) (p i) t)
        ⟨_, hs⟩ := by
  rw [glue_chart u hN p hιυ hτl hNl hul hur hc _ i y rfl v hv hv', H]
  exact βx_mk (Submonoid.powers (f i)) Tg (T i)
    (τp (𝒪 := 𝒪) (A := Localization.Away (f i)) Tg (T i) (p i))
    (span_range_τp (f i) Tg (T i) (p i)) _ y rfl t s hs

end Side

/-- Drinfeld data on the pieces `Spec B_{f i}` of a cover that are base changed from common data
on the overlaps `C i j` glue to a Drinfeld datum on `Spec B` whose base change to each piece is
the given one. -/
theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B)
    (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)]
    [∀ i j, Algebra 𝒪 (C i j)]
    [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
    [∀ i j, Algebra (Localization.Away (f i)) (C i j)]
    [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
    (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
    (hl : ∀ i j : Fin k, (Q i).IsBaseChangeAlong
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
    (hr : ∀ i j : Fin k, (Q j).IsBaseChangeAlong
      (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j)) :
    ∃ Qg : DrinfeldDatum (K := K) π B,
      ∀ i : Fin k, Qg.IsBaseChangeAlong
        (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) (Q i) := by
  classical
  let : ∀ i : Fin k, Module B (Q i).T₀ := fun i =>
    Module.compHom _ (algebraMap B (Localization.Away (f i)))
  have : ∀ i : Fin k, IsScalarTower B (Localization.Away (f i)) (Q i).T₀ :=
      fun i => ⟨fun b a t => by
    change (b • a) • t = algebraMap B (Localization.Away (f i)) b • (a • t)
    rw [Algebra.smul_def, mul_smul]⟩
  let : ∀ i : Fin k, Module B (Q i).T₁ := fun i =>
    Module.compHom _ (algebraMap B (Localization.Away (f i)))
  have : ∀ i : Fin k, IsScalarTower B (Localization.Away (f i)) (Q i).T₁ :=
      fun i => ⟨fun b a t => by
    change (b • a) • t = algebraMap B (Localization.Away (f i)) b • (a • t)
    rw [Algebra.smul_def, mul_smul]⟩
  let : ∀ i j : Fin k, Module B (Q₂ i j).T₀ := fun i j => Module.compHom _ (algebraMap B (C i j))
  have : ∀ i j : Fin k, IsScalarTower B (C i j) (Q₂ i j).T₀ := fun i j => ⟨fun b a t => by
    change (b • a) • t = algebraMap B (C i j) b • (a • t); rw [Algebra.smul_def, mul_smul]⟩
  let : ∀ i j : Fin k, Module B (Q₂ i j).T₁ := fun i j => Module.compHom _ (algebraMap B (C i j))
  have : ∀ i j : Fin k, IsScalarTower B (C i j) (Q₂ i j).T₁ := fun i j => ⟨fun b a t => by
    change (b • a) • t = algebraMap B (C i j) b • (a • t); rw [Algebra.smul_def, mul_smul]⟩
  let Wl := fun i j => (hl i j).some
  let Wr := fun i j => (hr i j).some
  obtain ⟨T₀, T₁, _, _, _, _, _, _, Pi₀, Pi₁, p₀, p₁, hP10, hP01, hp₀, hp₁, hPi₀, hPi₁, hc₀, hc₁⟩ :=
    DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap f hf Q C Q₂ Wl Wr
  have : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i) := hp₀
  have : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i) := hp₁
  let : Module 𝒪 T₀ := Module.compHom T₀ (algebraMap 𝒪 B)
  have : IsScalarTower 𝒪 B T₀ := ⟨fun r b t => by
    change (r • b) • t = algebraMap 𝒪 B r • (b • t); rw [Algebra.smul_def, mul_smul]⟩
  let : Module 𝒪 T₁ := Module.compHom T₁ (algebraMap 𝒪 B)
  have : IsScalarTower 𝒪 B T₁ := ⟨fun r b t => by
    change (r • b) • t = algebraMap 𝒪 B r • (b • t); rw [Algebra.smul_def, mul_smul]⟩
  have hpt : ∀ (i j : Fin k) (y : PrimeSpectrum (Localization.Away (f i)))
      (z : PrimeSpectrum (Localization.Away (f j))),
      pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y =
        pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f j))) z →
      ∃ w : PrimeSpectrum (C i j),
        pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) w = y ∧
        pointUnder (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) w = z := by
    intro i j y z hyz
    obtain ⟨w, hw⟩ := exists_comap_eq (A := C i j) (f i * f j) _ (fun h =>
      ((PrimeSpectrum.isPrime _).mem_or_mem h).elim (not_mem_of_comap_eq (f i) rfl)
        (not_mem_of_comap_eq (f j) hyz.symm))
    refine ⟨w, comap_injective (f i) ?_, comap_injective (f j) ?_⟩
    · rw [comap_pointUnder]; exact hw
    · rw [comap_pointUnder, hw]; exact hyz
  obtain ⟨N₀g, hN₀, hO₀⟩ := exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
    f hf (fun i => (Q i).N₀) (fun i v => (Q i).isOpen_setOf_mem₀ v) (fun i j y z hyz => by
      obtain ⟨w, hwy, hwz⟩ := hpt i j y z hyz
      rw [← hwy, ← hwz, ← (Wl i j).N₀_eq w, ← (Wr i j).N₀_eq w])
  obtain ⟨N₁g, hN₁, hO₁⟩ := exists_forall_pointUnder_eq_and_isOpen_setOf_mem_of_span_eq_top
    f hf (fun i => (Q i).N₁) (fun i v => (Q i).isOpen_setOf_mem₁ v) (fun i j y z hyz => by
      obtain ⟨w, hwy, hwz⟩ := hpt i j y z hyz
      rw [← hwy, ← hwz, ← (Wl i j).N₁_eq w, ← (Wr i j).N₁_eq w])
  have cover : ∀ x : PrimeSpectrum B, ∃ (i : Fin k) (y : PrimeSpectrum (Localization.Away (f i))),
      pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y = x := fun x => by
    obtain ⟨i, hi⟩ := exists_not_mem_of_span f hf x
    obtain ⟨y, hy⟩ := exists_comap_eq (A := Localization.Away (f i)) (f i) x hi
    exact ⟨i, y, hy⟩
  choose ι υ hιυ using cover
  have hN₀' : ∀ i y, N₀g (pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) =
      ((Q i).L₀ y).1 := hN₀
  have hN₁' : ∀ i y, N₁g (pointUnder (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) y) =
      ((Q i).L₁ y).1 := hN₁
  have hle : ∀ x, N₀g x ≤ N₁g x := fun x => by
    rw [glue_eq_chart hN₀' hιυ x, glue_eq_chart hN₁' hιυ x]; exact (Q (ι x)).le (υ x)
  have hsm : ∀ x, ∀ v ∈ N₁g x, algebraMap 𝒪 K π • v ∈ N₀g x := fun x => by
    rw [glue_eq_chart hN₀' hιυ x, glue_eq_chart hN₁' hιυ x]; exact (Q (ι x)).smul_le (υ x)
  let Qg : DrinfeldDatum (K := K) π B :=
    { N₀ := N₀g
      N₁ := N₁g
      full₀ := glue_full hN₀' hιυ
      full₁ := glue_full hN₁' hιυ
      le := hle
      smul_le := hsm
      isOpen_setOf_mem₀ := hO₀
      isOpen_setOf_mem₁ := hO₁
      T₀ := T₀
      T₁ := T₁
      invertible₀ := inferInstance
      invertible₁ := inferInstance
      Pi₀ := Pi₀
      Pi₁ := Pi₁
      Pi₁_Pi₀ := hP10
      Pi₀_Pi₁ := hP01
      u₀ := glue_ug (fun i => (Q i).u₀) hN₀' p₀ hιυ
      u₁ := glue_ug (fun i => (Q i).u₁) hN₁' p₁ hιυ
      u₁_incl := glue_ug_incl _ hN₀' p₀ _ hN₁' p₁ hιυ hle (fun i => (Q i).le) Pi₀
        (fun i => (Q i).Pi₀) hPi₀ (fun i => (Q i).u₁_incl)
      u₀_smul := glue_ug_smul _ hN₀' p₀ _ hN₁' p₁ hιυ hsm (fun i => (Q i).smul_le) Pi₁
        (fun i => (Q i).Pi₁) hPi₁ (fun i => (Q i).u₀_smul)
      u₀_surjective := glue_ug_surjective _ hN₀' p₀ hιυ (fun i => (Q i).u₀_surjective)
      u₁_surjective := glue_ug_surjective _ hN₁' p₁ hιυ (fun i => (Q i).u₁_surjective)
      u₀_continuous := glue_ug_continuous (L₂ := fun i j => (Q₂ i j).L₀) _ hN₀' p₀ hιυ
        (fun i j => (Wl i j).span_range_τ₀)
        (fun i j => (Wl i j).N₀_eq) (fun i j => (Wl i j).u₀_eq) (fun i j => (Wr i j).u₀_eq) hc₀
        (fun i => (Q i).u₀_continuous)
      u₁_continuous := glue_ug_continuous (L₂ := fun i j => (Q₂ i j).L₁) _ hN₁' p₁ hιυ
        (fun i j => (Wl i j).span_range_τ₁)
        (fun i j => (Wl i j).N₁_eq) (fun i j => (Wl i j).u₁_eq) (fun i j => (Wr i j).u₁_eq) hc₁
        (fun i => (Q i).u₁_continuous)
      locallyConstant₀ := glue_locallyConstant hN₀' p₀ p₁ hιυ Pi₀ (fun i => (Q i).Pi₀) hPi₀
        (fun i => (Q i).locallyConstant₀)
      locallyConstant₁ := glue_locallyConstant hN₁' p₁ p₀ hιυ Pi₁ (fun i => (Q i).Pi₁) hPi₁
        (fun i => (Q i).locallyConstant₁)
      injective₀ := fun x v h => by
        obtain ⟨w, hw, hvw⟩ := (Q (ι x)).injective₀ (υ x) _ (by
          rw [← glue_βι_ug (fun i => (Q i).u₀) hN₀' p₀ hιυ x v]
          exact glue_βι_mem_sup p₀ p₁ hιυ Pi₁ (fun i => (Q i).Pi₁) hPi₁ x _ h)
        exact ⟨w, by rw [glue_eq_chart hN₁' hιυ x]; exact hw, hvw⟩
      injective₁ := fun x v h => by
        have := (Q (ι x)).injective₁ (υ x) ⟨v, glue_mem_chart hN₁' hιυ x v.2⟩ (by
          rw [← glue_βι_ug (fun i => (Q i).u₁) hN₁' p₁ hιυ x v]
          exact glue_βι_mem_sup p₁ p₀ hιυ Pi₀ (fun i => (Q i).Pi₀) hPi₀ x _ h)
        rw [glue_eq_chart hN₀' hιυ x]; exact this
      hasDetIndex₀ := glue_hasDetIndex hN₀' p₀ p₁ hιυ Pi₀ (fun i => (Q i).Pi₀) hPi₀ 0
        (fun i => (Q i).hasDetIndex₀)
      hasDetIndex₁ := glue_hasDetIndex hN₁' p₁ p₀ hιυ Pi₁ (fun i => (Q i).Pi₁) hPi₁ (-1)
        (fun i => (Q i).hasDetIndex₁) }
  refine ⟨Qg, fun i => ⟨
    { N₀_eq := fun y => (hN₀ i y).symm
      N₁_eq := fun y => (hN₁ i y).symm
      τ₀ := τp (𝒪 := 𝒪) (A := Localization.Away (f i)) T₀ (Q i).T₀ (p₀ i)
      τ₁ := τp (𝒪 := 𝒪) (A := Localization.Away (f i)) T₁ (Q i).T₁ (p₁ i)
      span_range_τ₀ := span_range_τp (f i) T₀ (Q i).T₀ (p₀ i)
      span_range_τ₁ := span_range_τp (f i) T₁ (Q i).T₁ (p₁ i)
      τ₁_Pi₀ := fun t => hPi₀ i t
      τ₀_Pi₁ := fun t => hPi₁ i t
      u₀_eq := glue_u_eq (L₂ := fun i j => (Q₂ i j).L₀) _ hN₀' p₀ hιυ
        (fun i j => (Wl i j).span_range_τ₀)
        (fun i j => (Wl i j).N₀_eq) (fun i j => (Wl i j).u₀_eq) (fun i j => (Wr i j).u₀_eq) hc₀ i
      u₁_eq := glue_u_eq (L₂ := fun i j => (Q₂ i j).L₁) _ hN₁' p₁ hιυ
        (fun i j => (Wl i j).span_range_τ₁)
        (fun i j => (Wl i j).N₁_eq) (fun i j => (Wl i j).u₁_eq) (fun i j => (Wr i j).u₁_eq) hc₁
          i }⟩⟩

end
