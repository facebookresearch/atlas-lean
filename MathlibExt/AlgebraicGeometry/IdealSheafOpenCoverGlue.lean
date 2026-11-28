/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Gluing ideal sheaves along an open cover

Ideal sheaves on the members of an open cover that agree on overlaps glue to an ideal sheaf on
the whole scheme.
-/


set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry
namespace Scheme
namespace IdealSheafData
namespace Glue
open AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry

lemma appIso_of_comp_eq {V U X : Scheme.{u}} (a : V ⟶ U) (f : U ⟶ X) (c : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion f] [IsOpenImmersion c] (hc : c = a ≫ f) (W : V.Opens)
    (e : f ''ᵁ a ''ᵁ W = c ''ᵁ W) :
    c.appIso W = X.presheaf.mapIso (eqToIso e).op ≪≫ f.appIso (a ''ᵁ W) ≪≫ a.appIso W := by
  subst hc
  exact Scheme.Hom.comp_appIso a f W

lemma image_eq_of_comp_eq {V U X : Scheme.{u}} (a : V ⟶ U) (f : U ⟶ X) (c : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion f] [IsOpenImmersion c] (hc : c = a ≫ f) (W : V.Opens) :
    f ''ᵁ a ''ᵁ W = c ''ᵁ W := by
  subst hc
  exact (Scheme.Hom.comp_image a f W).symm

lemma mem_map_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) (K : Ideal R) (x : R) : φ x ∈ K.map φ ↔ x ∈ K := by
  rw [Ideal.mem_map_iff_of_surjective φ hφ.2]
  exact ⟨fun ⟨y, hy, hxy⟩ => hφ.1 hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

lemma appIso_hom_naturality_apply {Y' X' : Scheme.{u}} (g : Y' ⟶ X') [IsOpenImmersion g]
    {U V : Y'.Opens} (i : Opposite.op U ⟶ Opposite.op V) (y : Γ(X', g ''ᵁ U)) :
    (g.appIso V).hom (X'.presheaf.map (g.opensFunctor.op.map i) y) =
      Y'.presheaf.map i ((g.appIso U).hom y) := by
  have hnat : (g.appIso U).hom ≫ Y'.presheaf.map i =
      X'.presheaf.map (g.opensFunctor.op.map i) ≫ (g.appIso V).hom := by
    simp only [Functor.op_map, Scheme.Hom.appIso_hom', Scheme.Hom.appLE_map]
    exact (Scheme.Hom.map_appLE _ _ _).symm
  have := ConcreteCategory.congr_hom hnat y
  simp only [Functor.op_obj, Functor.op_map]
  exact this.symm

variable {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : ∀ i, (𝒰.X i).IdealSheafData)

def imA (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens) : X.affineOpens :=
  ⟨𝒰.f i ''ᵁ (W : (𝒰.X i).Opens), W.2.image_of_isOpenImmersion _⟩

@[local simp] lemma coe_imA (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens) :
    (imA 𝒰 i W : X.Opens) = 𝒰.f i ''ᵁ (W : (𝒰.X i).Opens) := rfl

noncomputable def T (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens) : Ideal Γ(X,
    𝒰.f i ''ᵁ (W : (𝒰.X i).Opens)) :=
  ((I i).ideal W).map ((𝒰.f i).appIso W).inv.hom

lemma T_eq_comap (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens) :
    T 𝒰 I i W = ((I i).ideal W).comap ((𝒰.f i).appIso W).hom.hom := by
  have surj : Function.Surjective ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv).2
  ext x
  rw [T, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective _ surj]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  · intro hx
    exact ⟨_, hx, by rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩

lemma T_map_of_le (i : 𝒰.I₀) {W W' : (𝒰.X i).affineOpens} (h : W' ≤ W) :
    (T 𝒰 I i W).map (X.presheaf.map (homOfLE ((𝒰.f i).image_mono h)).op).hom = T 𝒰 I i W' := by
  rw [T, T, Ideal.map_map, ← CommRingCat.hom_comp]
  have : ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv ≫
      X.presheaf.map (homOfLE ((𝒰.f i).image_mono h)).op =
      (𝒰.X i).presheaf.map (homOfLE h).op ≫ ((𝒰.f i).appIso (W' : (𝒰.X i).Opens)).inv := by
    rw [Scheme.Hom.appIso_inv_naturality]
    rfl
  rw [this, CommRingCat.hom_comp, ← Ideal.map_map, (I i).map_ideal h]

noncomputable def J (V : X.affineOpens) : Ideal Γ(X, V) :=
  ⨅ (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens) (h : 𝒰.f i ''ᵁ (W : (𝒰.X i).Opens) ≤ (V : X.Opens)),
    (T 𝒰 I i W).comap (X.presheaf.map (homOfLE h).op).hom

lemma mem_J_iff {V : X.affineOpens} (s : Γ(X, V)) :
    s ∈ J 𝒰 I V ↔ ∀ (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens)
      (h : 𝒰.f i ''ᵁ (W : (𝒰.X i).Opens) ≤ (V : X.Opens)),
      X.presheaf.map (homOfLE h).op s ∈ T 𝒰 I i W := by
  simp [J, Ideal.mem_comap]

lemma J_map_le {V V' : X.affineOpens} (h : V' ≤ V) :
    (J 𝒰 I V).map (X.presheaf.map (homOfLE h).op).hom ≤ J 𝒰 I V' := by
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  rw [Ideal.mem_comap, mem_J_iff]
  intro i W hW
  rw [mem_J_iff] at hs
  have := hs i W (hW.trans h)
  convert this using 1
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma T_eq_of_image_eq
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b)
    {i j : 𝒰.I₀} (W₁ : (𝒰.X i).affineOpens) (W : (𝒰.X j).affineOpens)
    (e : 𝒰.f i ''ᵁ (W₁ : (𝒰.X i).Opens) = 𝒰.f j ''ᵁ (W : (𝒰.X j).Opens)) :
    T 𝒰 I i W₁ = (T 𝒰 I j W).map (X.presheaf.map (eqToHom e).op).hom := by
  have hWaff : IsAffine (W : (𝒰.X j).Opens) := W.2
  let b : ↑(W : (𝒰.X j).Opens) ⟶ 𝒰.X j := (W : (𝒰.X j).Opens).ι
  let c : ↑(W : (𝒰.X j).Opens) ⟶ X := b ≫ 𝒰.f j
  have hc_range : Set.range c ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨x, rfl⟩
    have : (𝒰.f j) (b x) ∈ (𝒰.f j ''ᵁ (W : (𝒰.X j).Opens) : X.Opens) := ⟨b x, by exact x.2, rfl⟩
    rw [← e] at this
    obtain ⟨y, -, hy⟩ := this
    exact ⟨y, hy⟩
  let a : ↑(W : (𝒰.X j).Opens) ⟶ 𝒰.X i := IsOpenImmersion.lift (𝒰.f i) c hc_range
  have fac : a ≫ 𝒰.f i = c := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (a ≫ 𝒰.f i) := by rw [fac]; infer_instance
  have ha : IsOpenImmersion a := IsOpenImmersion.of_comp a (𝒰.f i)
  have hcomp := hI a b fac
  have s1 : b ''ᵁ ⊤ = (W : (𝒰.X j).Opens) := Scheme.Opens.ι_image_top _
  have key : 𝒰.f i ''ᵁ (a ''ᵁ ⊤) = 𝒰.f i ''ᵁ (W₁ : (𝒰.X i).Opens) := by
    rw [image_eq_of_comp_eq a (𝒰.f i) c fac.symm, ← image_eq_of_comp_eq b (𝒰.f j) c rfl, s1, e]
  have s2 : a ''ᵁ ⊤ = (W₁ : (𝒰.X i).Opens) :=
    le_antisymm ((Scheme.Hom.image_le_image_iff _ _ _).mp key.le)
      ((Scheme.Hom.image_le_image_iff _ _ _).mp key.ge)
  have hev := congrArg (fun K : IdealSheafData _ => K.ideal ⟨⊤, isAffineOpen_top _⟩) hcomp
  simp only [ideal_comap_of_isOpenImmersion] at hev
  have ei : 𝒰.f i ''ᵁ a ''ᵁ ⊤ = c ''ᵁ ⊤ := image_eq_of_comp_eq a (𝒰.f i) c fac.symm ⊤
  have ej : 𝒰.f j ''ᵁ b ''ᵁ ⊤ = c ''ᵁ ⊤ := image_eq_of_comp_eq b (𝒰.f j) c rfl ⊤
  have Ei := appIso_of_comp_eq a (𝒰.f i) c fac.symm ⊤ ei
  have Ej := appIso_of_comp_eq b (𝒰.f j) c rfl ⊤ ej
  have hb : b.appIso ⊤ = Iso.refl _ := Scheme.Opens.ι_appIso _ _
  have RI : ∀ z : Γ(X, c ''ᵁ ⊤), (a.appIso ⊤).inv
      (((𝒰.f j).appIso (b ''ᵁ ⊤)).hom (X.presheaf.map (eqToHom ej).op z)) =
      ((𝒰.f i).appIso (a ''ᵁ ⊤)).hom (X.presheaf.map (eqToHom ei).op z) := by
    intro z
    have h1 := congrArg (fun φ : Γ(X, c ''ᵁ ⊤) ≅ Γ(↑(W : (𝒰.X j).Opens), ⊤) => φ.hom.hom z) Ei
    have h2 := congrArg (fun φ : Γ(X, c ''ᵁ ⊤) ≅ Γ(↑(W : (𝒰.X j).Opens), ⊤) => φ.hom.hom z) Ej
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, eqToHom_op,
      CommRingCat.hom_comp, RingHom.comp_apply, hb] at h1 h2
    apply (ConcreteCategory.bijective_of_isIso (a.appIso ⊤).hom).1
    change (a.appIso ⊤).hom.hom ((a.appIso ⊤).inv.hom _) = (a.appIso ⊤).hom.hom _
    erw [CommRingCat.hom_inv_apply]
    have h3 := h2.symm.trans h1
    simp only [eqToHom_op] at h3 ⊢
    exact h3
  let qj := (𝒰.X j).presheaf.map (eqToHom s1).op
  let qi := (𝒰.X i).presheaf.map (eqToHom s2).op
  let rj := X.presheaf.map ((𝒰.f j).opensFunctor.op.map (eqToHom s1).op)
  let ri := X.presheaf.map ((𝒰.f i).opensFunctor.op.map (eqToHom s2).op)
  let ρ := X.presheaf.map (eqToHom e).op
  have hqj : Function.Bijective qj.hom := ConcreteCategory.bijective_of_isIso qj
  have hqi : Function.Bijective qi.hom := ConcreteCategory.bijective_of_isIso qi
  have Mj : (I j).ideal ⟨b ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion b⟩ =
      ((I j).ideal W).map qj.hom := ((I j).map_ideal' _).symm
  have Mi : (I i).ideal ⟨a ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion a⟩ =
      ((I i).ideal W₁).map qi.hom := ((I i).map_ideal' _).symm
  have main : ∀ t : Γ(X, 𝒰.f j ''ᵁ (W : (𝒰.X j).Opens)), ρ t ∈ T 𝒰 I i W₁ ↔ t ∈ T 𝒰 I j W := by
    intro t
    let z : Γ(X, c ''ᵁ ⊤) := X.presheaf.map (eqToHom ej.symm).op (rj t)
    have hzj : X.presheaf.map (eqToHom ej).op z = rj t := by
      change (X.presheaf.map (eqToHom ej.symm).op ≫ X.presheaf.map (eqToHom ej).op) (rj t) = rj t
      rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
        CategoryTheory.Functor.map_id]
      rfl
    have hzi : X.presheaf.map (eqToHom ei).op z = ri (ρ t) := by
      change (X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) t =
        (X.presheaf.map _ ≫ X.presheaf.map _) t
      simp only [← Functor.map_comp]
      rfl
    have RI' : (a.appIso ⊤).inv (((𝒰.f j).appIso (b ''ᵁ ⊤)).hom (rj t)) =
        ((𝒰.f i).appIso (a ''ᵁ ⊤)).hom (ri (ρ t)) := by
      rw [← hzj, RI z, hzi]
    rw [T_eq_comap, T_eq_comap, Ideal.mem_comap, Ideal.mem_comap,
      ← mem_map_iff_of_bijective _ hqj ((I j).ideal W), ← Mj,
      ← mem_map_iff_of_bijective _ hqi ((I i).ideal W₁), ← Mi,
      ← appIso_hom_naturality_apply (𝒰.f j) (eqToHom s1).op,
      ← appIso_hom_naturality_apply (𝒰.f i) (eqToHom s2).op]
    change ((𝒰.f i).appIso (a ''ᵁ ⊤)).hom (ri (ρ t)) ∈ _ ↔ ((𝒰.f j).appIso (b ''ᵁ ⊤)).hom (rj t) ∈ _
    rw [← RI']
    have := Ideal.ext_iff.mp hev (((𝒰.f j).appIso (b ''ᵁ ⊤)).hom (rj t))
    simp only [hb] at this
    exact this
  apply le_antisymm
  · intro x hx
    obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso ρ).2 x
    exact Ideal.mem_map_of_mem _ ((main t).mp hx)
  · rw [Ideal.map_le_iff_le_comap]
    intro t ht
    exact (main t).mpr ht

lemma J_imA (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens)
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) :
    J 𝒰 I (imA 𝒰 i W) = T 𝒰 I i W := by
  apply le_antisymm
  · intro s hs
    have := (mem_J_iff 𝒰 I s).mp hs i W le_rfl
    simp only [coe_imA, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      CommRingCat.hom_id] at this
    exact this
  · intro s hs
    rw [mem_J_iff]
    intro j W' h
    have hrange : (𝒰.f j ''ᵁ (W' : (𝒰.X j).Opens)) ≤ (𝒰.f i).opensRange := by
      rintro x hx
      obtain ⟨y, -, rfl⟩ := h hx
      exact ⟨y, rfl⟩
    let W₁ : (𝒰.X i).affineOpens := ⟨(𝒰.f i) ⁻¹ᵁ (𝒰.f j ''ᵁ (W' : (𝒰.X j).Opens)),
      (W'.2.image_of_isOpenImmersion (𝒰.f j)).preimage_of_isOpenImmersion (𝒰.f i) hrange⟩
    have e : 𝒰.f i ''ᵁ (W₁ : (𝒰.X i).Opens) = 𝒰.f j ''ᵁ (W' : (𝒰.X j).Opens) := by
      change 𝒰.f i ''ᵁ (𝒰.f i) ⁻¹ᵁ _ = _
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hrange]
    have hW₁ : W₁ ≤ W := by
      change (W₁ : (𝒰.X i).Opens) ≤ W
      rw [← Scheme.Hom.image_le_image_iff (𝒰.f i), e]
      exact h
    have hs1 : X.presheaf.map (homOfLE ((𝒰.f i).image_mono hW₁)).op s ∈ T 𝒰 I i W₁ := by
      rw [← T_map_of_le 𝒰 I i hW₁]
      exact Ideal.mem_map_of_mem _ hs
    rw [T_eq_of_image_eq 𝒰 I hI W₁ W' e] at hs1
    have hcomp : X.presheaf.map (homOfLE ((𝒰.f i).image_mono hW₁)).op s =
        X.presheaf.map (eqToHom e).op (X.presheaf.map (homOfLE h).op s) := by
      change _ = (X.presheaf.map _ ≫ X.presheaf.map _) s
      rw [← Functor.map_comp]
      rfl
    rw [hcomp, mem_map_iff_of_bijective _ (ConcreteCategory.bijective_of_isIso _)] at hs1
    exact hs1

section L3

omit 𝒰 in
lemma presheaf_map_eq {U V : X.Opens} (i j : Opposite.op U ⟶ Opposite.op V) :
    X.presheaf.map i = X.presheaf.map j := by
  rw [Subsingleton.elim i j]

omit 𝒰 in
lemma presheaf_map_map_apply {A B C : (X.Opens)ᵒᵖ} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C)
    (x : X.presheaf.obj A) :
    X.presheaf.map j (X.presheaf.map i x) = X.presheaf.map k x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (i ≫ j) k]

lemma mem_ideal_of_forall_basicOpen {Y : Scheme.{u}} (K : Y.IdealSheafData) (W : Y.affineOpens)
    (s : Set Γ(Y, W)) (hs : Ideal.span s = ⊤) (y : Γ(Y, W))
    (h : ∀ g ∈ s,
        Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op y ∈ K.ideal (Y.affineBasicOpen g)) :
    y ∈ K.ideal W := by
  have inst := W.2.isLocalization_basicOpen
  refine Submodule.mem_of_isLocalized_span s hs (fun g => Γ(Y, Y.basicOpen g.1))
    (fun g => Algebra.linearMap Γ(Y, W.1) Γ(Y, Y.basicOpen g.1)) ?_
  rintro ⟨g, hg⟩
  rw [← Submodule.restrictScalars_localized' Γ(Y, Y.basicOpen g), Submodule.restrictScalars_mem,
    Ideal.localized'_eq_map, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
  change (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom y ∈
    (K.ideal W).map (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom
  rw [K.map_ideal_basicOpen]
  exact h g hg

omit I in
lemma algebraMap_basicOpen_apply {U : X.Opens} (f : Γ(X, U)) (x : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) x = X.presheaf.map (homOfLE (X.basicOpen_le f)).op x :=
  rfl

lemma J_map_congr {U₁ U₂ U₁' U₂' : X.affineOpens} (e : U₁ = U₂) (e' : U₁' = U₂')
    (h₁ : U₁' ≤ U₁) (h₂ : U₂' ≤ U₂)
    (H : J 𝒰 I U₁' = (J 𝒰 I U₁).map (X.presheaf.map (homOfLE h₁).op).hom) :
    J 𝒰 I U₂' = (J 𝒰 I U₂).map (X.presheaf.map (homOfLE h₂).op).hom := by
  subst e e'
  exact H

lemma J_basicOpen_basicOpen
    (hJ : ∀ (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens), J 𝒰 I (imA 𝒰 i W) = T 𝒰 I i W)
    {V : X.affineOpens} {g : Γ(X, V)} {i : 𝒰.I₀} {W : (𝒰.X i).affineOpens}
    (e : 𝒰.f i ''ᵁ (W : (𝒰.X i).Opens) = X.basicOpen g) (h' : Γ(X, X.basicOpen g)) :
    J 𝒰 I (X.affineBasicOpen (U := X.affineBasicOpen g) h') =
      (J 𝒰 I (X.affineBasicOpen g)).map (X.presheaf.map (homOfLE (X.basicOpen_le h')).op).hom := by
  have hgr : X.basicOpen g ≤ (𝒰.f i).opensRange := by
    rw [← e]; exact (𝒰.f i).image_le_opensRange _
  have hle : X.basicOpen h' ≤ (𝒰.f i).opensRange := (X.basicOpen_le h').trans hgr
  have hW'aff : IsAffineOpen ((𝒰.f i) ⁻¹ᵁ X.basicOpen h') :=
    (X.affineBasicOpen (U := X.affineBasicOpen g) h').2.preimage_of_isOpenImmersion (𝒰.f i) hle
  let W' : (𝒰.X i).affineOpens := ⟨(𝒰.f i) ⁻¹ᵁ X.basicOpen h', hW'aff⟩
  have e' : 𝒰.f i ''ᵁ (W' : (𝒰.X i).Opens) = X.basicOpen h' := by
    change 𝒰.f i ''ᵁ (𝒰.f i) ⁻¹ᵁ X.basicOpen h' = _
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]
  have hW'W : W' ≤ W := by
    intro x hx
    have hx1 : (𝒰.f i) x ∈ X.basicOpen h' := hx
    have hx2 : (𝒰.f i) x ∈ (𝒰.f i ''ᵁ (W : (𝒰.X i).Opens) : X.Opens) := by
      rw [e]; exact X.basicOpen_le h' hx1
    exact ((𝒰.f i).isOpenEmbedding.injective.mem_set_image).mp hx2
  have E : imA 𝒰 i W = X.affineBasicOpen g := Subtype.ext e
  have E' : imA 𝒰 i W' = X.affineBasicOpen (U := X.affineBasicOpen g) h' := Subtype.ext e'
  refine J_map_congr 𝒰 I E E' ((𝒰.f i).image_mono hW'W) (X.basicOpen_le h') ?_
  rw [hJ i W', hJ i W]
  exact (T_map_of_le 𝒰 I i hW'W).symm

lemma mem_J_of_forall_basicOpen {V : X.affineOpens} (x : Γ(X, V)) (s : Set Γ(X, V))
    (hs : Ideal.span s = ⊤)
    (hx : ∀ g ∈ s, X.presheaf.map (homOfLE (X.basicOpen_le g)).op x ∈ J 𝒰 I (X.affineBasicOpen g)) :
    x ∈ J 𝒰 I V := by
  rw [mem_J_iff]
  intro i W hW
  rw [T_eq_comap, Ideal.mem_comap]
  let φ : Γ(X, V) →+* Γ(𝒰.X i, W) :=
    ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).hom.hom.comp (X.presheaf.map (homOfLE hW).op).hom
  have hs' : Ideal.span (φ '' s) = ⊤ := by rw [← Ideal.map_span, hs, Ideal.map_top]
  refine mem_ideal_of_forall_basicOpen (I i) W (φ '' s) hs' _ ?_
  rintro _ ⟨g, hg, rfl⟩
  let Wg : (𝒰.X i).affineOpens := (𝒰.X i).affineBasicOpen (φ g)
  have himg : 𝒰.f i ''ᵁ (Wg : (𝒰.X i).Opens) ≤ X.basicOpen g := by
    change 𝒰.f i ''ᵁ ((𝒰.X i).basicOpen (φ g)) ≤ _
    rw [Scheme.image_basicOpen (𝒰.f i)]
    change X.basicOpen (((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv
      (((𝒰.f i).appIso (W : (𝒰.X i).Opens)).hom ((X.presheaf.map (homOfLE hW).op) g))) ≤ _
    rw [CategoryTheory.Iso.hom_inv_id_apply, Scheme.basicOpen_res]
    exact inf_le_right
  have hWgV : 𝒰.f i ''ᵁ (Wg : (𝒰.X i).Opens) ≤ (V : X.Opens) := himg.trans (X.basicOpen_le g)
  have hWgW : (Wg : (𝒰.X i).Opens) ≤ (W : (𝒰.X i).Opens) := (𝒰.X i).basicOpen_le (φ g)
  have h1 := (mem_J_iff 𝒰 I _).mp (hx g hg) i Wg himg
  rw [T_eq_comap, Ideal.mem_comap] at h1
  have h2 : (X.presheaf.map (homOfLE himg).op) ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op)
      x) =
      X.presheaf.map ((𝒰.f i).opensFunctor.op.map (homOfLE hWgW).op)
        (X.presheaf.map (homOfLE hW).op x) :=
    (presheaf_map_map_apply _ _ (homOfLE hWgV).op x).trans
      (presheaf_map_map_apply (homOfLE hW).op ((𝒰.f i).opensFunctor.op.map (homOfLE hWgW).op)
        (homOfLE hWgV).op x).symm
  change ((𝒰.f i).appIso (Wg : (𝒰.X i).Opens)).hom
    ((X.presheaf.map (homOfLE himg).op) ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op) x)) ∈ _
        at h1
  rw [h2, appIso_hom_naturality_apply] at h1
  exact h1

omit I in
lemma exists_good_cover (V : X.affineOpens) :
    ∃ s : Finset Γ(X, V), Ideal.span (s : Set Γ(X, V)) = ⊤ ∧
      ∀ g ∈ s, ∃ (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens),
        𝒰.f i ''ᵁ (W : (𝒰.X i).Opens) = X.basicOpen g := by
  classical
  let good : Set Γ(X, V) := {g | ∃ (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens),
    𝒰.f i ''ᵁ (W : (𝒰.X i).Opens) = X.basicOpen g}
  have hcov : (V : X.Opens) ≤ ⨆ g : good, X.basicOpen g.1 := by
    intro x hxV
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    have hyV : y ∈ (𝒰.f i) ⁻¹ᵁ (V : X.Opens) := by
      change (𝒰.f i) y ∈ (V : X.Opens)
      rw [hy]; exact hxV
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
      (𝒰.X i).isBasis_affineOpens.exists_subset_of_mem_open hyV ((𝒰.f i) ⁻¹ᵁ (V : X.Opens)).isOpen
    have hxU : x ∈ (𝒰.f i ''ᵁ U : X.Opens) := by
      rw [← hy]; exact ⟨y, hyU, rfl⟩
    obtain ⟨g, hgU, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxU⟩ hxV
    have hle : X.basicOpen g ≤ (𝒰.f i).opensRange := hgU.trans ((𝒰.f i).image_le_opensRange U)
    have hgood : g ∈ good := ⟨i, ⟨(𝒰.f i) ⁻¹ᵁ X.basicOpen g,
        (X.affineBasicOpen g).2.preimage_of_isOpenImmersion (𝒰.f i) hle⟩, by
      change 𝒰.f i ''ᵁ (𝒰.f i) ⁻¹ᵁ X.basicOpen g = _
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]⟩
    exact Opens.mem_iSup.mpr ⟨⟨g, hgood⟩, hxg⟩
  have hspan : Ideal.span good = ⊤ := V.2.self_le_iSup_basicOpen_iff.mp hcov
  obtain ⟨s, hs, hs1⟩ :=
    Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hspan)
  exact ⟨s, (Ideal.eq_top_iff_one _).mpr hs1, fun g hg => hs hg⟩

lemma J_basicOpen_le'
    (hJ : ∀ (i : 𝒰.I₀) (W : (𝒰.X i).affineOpens), J 𝒰 I (imA 𝒰 i W) = T 𝒰 I i W)
    (V : X.affineOpens) (h : Γ(X, V)) :
    J 𝒰 I (X.affineBasicOpen h) ≤
      (J 𝒰 I V).map (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom := by
  classical
  intro s hs
  change Γ(X, X.basicOpen h) at s
  obtain ⟨sV, hspan, hgood⟩ := exists_good_cover 𝒰 V
  have instV : ∀ f : Γ(X, V), IsLocalization.Away f Γ(X, X.basicOpen f) :=
    V.2.isLocalization_basicOpen
  obtain ⟨⟨t₀, ⟨_, m, rfl⟩⟩, hst⟩ :=
    IsLocalization.surj (M := Submonoid.powers h) (S := Γ(X, X.basicOpen h)) s
  have key : ∀ g ∈ sV, ∃ n : ℕ,
      X.presheaf.map (homOfLE (X.basicOpen_le g)).op (h ^ n * t₀) ∈ J 𝒰 I (X.affineBasicOpen g) :=
          by
    intro g hg
    obtain ⟨i, W, eg⟩ := hgood g hg
    let ρ : Γ(X, V) →+* Γ(X, X.basicOpen g) := (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom
    let h' : Γ(X, X.basicOpen g) := ρ h
    have instg : ∀ f : Γ(X, X.basicOpen g), IsLocalization.Away f Γ(X, X.basicOpen f) :=
      (X.affineBasicOpen g).2.isLocalization_basicOpen
    have hD : X.basicOpen h' ≤ X.basicOpen h := by
      change X.basicOpen ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op) h) ≤ _
      rw [Scheme.basicOpen_res]; exact inf_le_right
    have hDV : X.basicOpen h' ≤ (V : X.Opens) := hD.trans (X.basicOpen_le h)
    have hσ : (X.presheaf.map (homOfLE hD).op) s ∈
        (J 𝒰 I (X.affineBasicOpen g)).map (algebraMap Γ(X, X.basicOpen g) Γ(X,
            X.basicOpen h')) := by
      have := J_map_le 𝒰 I (V := X.affineBasicOpen h)
        (V' := X.affineBasicOpen (U := X.affineBasicOpen g) h') hD (Ideal.mem_map_of_mem _ hs)
      rw [J_basicOpen_basicOpen 𝒰 I hJ eg h'] at this
      exact this
    obtain ⟨⟨⟨y, hy⟩, ⟨_, n, rfl⟩⟩, hyn⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers h') _).mp hσ
    have hst' : (X.presheaf.map (homOfLE hD).op) s *
        algebraMap Γ(X, X.basicOpen g) Γ(X, X.basicOpen h') (h' ^ m) =
        algebraMap Γ(X, X.basicOpen g) Γ(X, X.basicOpen h') (ρ t₀) := by
      have := congrArg (X.presheaf.map (homOfLE hD).op) hst
      rw [map_mul] at this
      rw [algebraMap_basicOpen_apply, algebraMap_basicOpen_apply,
        show h' ^ m = ρ (h ^ m) from by rw [map_pow],
        presheaf_map_map_apply _ _ (homOfLE hDV).op, presheaf_map_map_apply _ _ (homOfLE hDV).op]
      rw [algebraMap_basicOpen_apply, algebraMap_basicOpen_apply,
        presheaf_map_map_apply _ _ (homOfLE hDV).op, presheaf_map_map_apply _ _ (homOfLE hDV).op]
        at this
      exact this
    have hcomb : algebraMap Γ(X, X.basicOpen g) Γ(X, X.basicOpen h') (ρ t₀ * h' ^ n) =
        algebraMap Γ(X, X.basicOpen g) Γ(X, X.basicOpen h') (y * h' ^ m) := by
      rw [map_mul, map_mul, ← hst', ← hyn]
      ring
    obtain ⟨⟨_, e, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h') _).mp hcomb
    refine ⟨e + n, ?_⟩
    have hrw : ρ (h ^ (e + n) * t₀) = h' ^ e * (ρ t₀ * h' ^ n) := by
      rw [map_mul, map_pow]; ring
    change ρ (h ^ (e + n) * t₀) ∈ _
    rw [hrw]
    rw [show (h' ^ e) * (ρ t₀ * h' ^ n) = (h' ^ e) * (y * h' ^ m) from hc]
    exact Ideal.mul_mem_left _ _ (by rw [mul_comm]; exact Ideal.mul_mem_left _ _ hy)
  choose! nf hnf using key
  let N := sV.sup nf
  have hN : ∀ g ∈ (sV : Set Γ(X, V)),
      X.presheaf.map (homOfLE (X.basicOpen_le g)).op (h ^ N * t₀) ∈ J 𝒰 I (X.affineBasicOpen g) :=
          by
    intro g hg
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show nf g ≤ N from Finset.le_sup (f := nf) hg)
    rw [hd, pow_add, mul_comm (h ^ nf g) (h ^ d), mul_assoc, map_mul]
    exact Ideal.mul_mem_left _ _ (hnf g hg)
  have hmem : h ^ N * t₀ ∈ J 𝒰 I V := mem_J_of_forall_basicOpen 𝒰 I _ _ hspan hN
  change s ∈ (J 𝒰 I V).map (algebraMap Γ(X, V) Γ(X, X.basicOpen h))
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers h)]
  refine ⟨⟨⟨h ^ N * t₀, hmem⟩, ⟨h ^ (N + m), N + m, rfl⟩⟩, ?_⟩
  change s * algebraMap _ _ (h ^ (N + m)) = algebraMap _ _ (h ^ N * t₀)
  change s * algebraMap _ _ (h ^ m) = algebraMap _ _ t₀ at hst
  rw [pow_add, map_mul, map_mul, ← hst]
  ring

end L3

lemma J_basicOpen_le (V : X.affineOpens) (h : Γ(X, V))
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) :
    J 𝒰 I (X.affineBasicOpen h) ≤
      (J 𝒰 I V).map (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom :=
  J_basicOpen_le' 𝒰 I (fun i W => J_imA 𝒰 I i W hI) V h

noncomputable def glued
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) : X.IdealSheafData where
  ideal := J 𝒰 I
  map_ideal_basicOpen V h :=
    le_antisymm (J_map_le 𝒰 I (V := V) (V' := X.affineBasicOpen h) (X.basicOpen_le h))
      (J_basicOpen_le 𝒰 I V h hI)

theorem comap_glued
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) (i : 𝒰.I₀) :
    (glued 𝒰 I hI).comap (𝒰.f i) = I i := by
  apply IdealSheafData.ext
  funext W
  rw [ideal_comap_of_isOpenImmersion]
  change (J 𝒰 I (imA 𝒰 i W)).comap ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv.hom = (I i).ideal W
  rw [J_imA 𝒰 I i W hI, T_eq_comap]
  ext x
  change ((𝒰.f i).appIso (W : (𝒰.X i).Opens)).hom.hom
      (((𝒰.f i).appIso (W : (𝒰.X i).Opens)).inv.hom x) ∈ (I i).ideal W ↔ x ∈ (I i).ideal W
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end AlgebraicGeometry.Scheme.IdealSheafData.Glue

/-- Ideal sheaves on the members of an open cover that agree on overlaps glue to an ideal sheaf
on the whole scheme. -/
public theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) (I : ∀ i, (𝒰.X i).IdealSheafData)
    (hI : ∀ ⦃i j : 𝒰.I₀⦄ ⦃V : Scheme.{u}⦄ (a : V ⟶ 𝒰.X i) (b : V ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = b ≫ 𝒰.f j → (I i).comap a = (I j).comap b) :
    ∃ I₀ : X.IdealSheafData, ∀ i, I₀.comap (𝒰.f i) = I i :=
  ⟨AlgebraicGeometry.Scheme.IdealSheafData.Glue.glued 𝒰 I hI,
    AlgebraicGeometry.Scheme.IdealSheafData.Glue.comap_glued 𝒰 I hI⟩
