/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_LevelArithmeticModP.lean`,
`Theorems/Thm_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP.lean`,
`Theorems/Thm_Representation_nonempty_equiv_torsionBy_quotient_of_coprime.lean`,
`P2M/Sol/S_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP.lean`
and
`P2M/Sol/S_Representation_nonempty_equiv_torsionBy_quotient_of_coprime.lean`
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

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Semisimple

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RepresentationTheory.Maschke

@[expose] public section

open CategoryTheory

open scoped Pointwise

universe u v w

namespace Rep

variable {k : Type u} {G : Type v} [CommRing k] [Group G]




theorem torsionBy_le_comap {M : Type w} [AddCommGroup M] {iM : Module k M} (ρ :
  Representation k G M) (a : k)
    (g : G) : Submodule.torsionBy k M a ≤ (Submodule.torsionBy k M a).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap, Submodule.mem_torsionBy_iff, ← map_smul]
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [hx, map_zero]

theorem smul_top_le_comap {M : Type w} [AddCommGroup M] {iM : Module k M} (ρ :
  Representation k G M) (a : k)
    (g : G) : (a • (⊤ : Submodule k M)) ≤ (a • (⊤ : Submodule k M)).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap]
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

theorem nsmul_quot_eq_zero {V : Type w} [AddCommGroup V] {iV : Module k V} (p : ℕ) (x : V ⧸
  ((p : k) • (⊤ : Submodule k V))) :
    p • x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ←
    Nat.cast_smul_eq_nsmul k]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

theorem nsmul_torsionBy_eq_zero {V : Type w} [AddCommGroup V] {iV : Module k V} (p : ℕ) (x :
  ↥(Submodule.torsionBy k V (p : k))) :
    p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul k]
  exact Subtype.ext ((Submodule.mem_torsionBy_iff (p : k) (x : V)).1 x.2)

-- The two `ZMod p`-module structures below are reducible defs, not instances (see note
-- [reducible non-instances]): for `k = ZMod p` the quotient and the submodule already carry
-- Mathlib's module structures, and global instances would compete with them. `modP`, `torsionP`
-- and the `Rep` objects carry them; this file, and any importer that needs them as instances,
-- opts in with `attribute [local instance] Rep.zmodModuleQuot Rep.zmodModuleTorsion`.
abbrev zmodModuleQuot {V : Type w} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) (V ⧸ ((p : k) • (⊤ : Submodule k V))) :=
  AddCommGroup.zmodModule (nsmul_quot_eq_zero p)

abbrev zmodModuleTorsion {V : Type w} [AddCommGroup V] {iV : Module k V} (p : ℕ) :
    Module (ZMod p) ↥(Submodule.torsionBy k V (p : k)) :=
  AddCommGroup.zmodModule (nsmul_torsionBy_eq_zero p)

attribute [local instance] zmodModuleQuot zmodModuleTorsion

def toZMod (p : ℕ) {M : Type w} [AddCommGroup M] [Module (ZMod p) M] {inst : Module k M} (σ :
  Representation k G M) :
    Representation (ZMod p) G M where
  toFun g := (σ g).toAddMonoidHom.toZModLinearMap p
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp] theorem toZMod_apply (p : ℕ) {M : Type w} [AddCommGroup M] [Module (ZMod p) M] {inst :
  Module k M}
    (σ : Representation k G M) (g : G) (m : M) : toZMod p σ g m = σ g m := rfl

def modP (p : ℕ) {V : Type w} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) :
    Representation (ZMod p) G (V ⧸ ((p : k) • (⊤ : Submodule k V))) :=
  toZMod p (ρ.quotient _ (smul_top_le_comap ρ (p : k)))

def torsionP (p : ℕ) {V : Type w} [AddCommGroup V] {iV : Module k V} (ρ : Representation k G V) :
    Representation (ZMod p) G ↥(Submodule.torsionBy k V (p : k)) :=
  toZMod p (ρ.subrepresentation _ (torsionBy_le_comap ρ (p : k)))

@[simp] theorem modP_apply_mk (p : ℕ) {V : Type w} [AddCommGroup V] {iV : Module k V} (ρ :
  Representation k G V) (g : G) (v : V) :
    modP p ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl

@[simp] theorem torsionP_apply_coe (p : ℕ) {V : Type w} [AddCommGroup V] {iV : Module k V} (ρ :
  Representation k G V) (g : G)
    (v : ↥(Submodule.torsionBy k V (p : k))) : ((torsionP p ρ g v : ↥(Submodule.torsionBy k V (p :
      k))) : V) = ρ g v := rfl

abbrev repModP (p : ℕ) (A : Rep.{w} k G) : Rep.{w} (ZMod p) G := Rep.of (modP p A.ρ)

abbrev repTorsionP (p : ℕ) (A : Rep.{w} k G) : Rep.{w} (ZMod p) G := Rep.of (torsionP p A.ρ)

def repModPMap (p : ℕ) {A B : Rep.{w} k G} (f : A ⟶ B) : repModP p A ⟶ repModP p B :=
  Rep.ofHom ⟨(Submodule.mapQ ((p : k) • (⊤ : Submodule k A)) ((p : k) • (⊤ : Submodule k B))
    f.hom.toLinearMap (fun x hx => by
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _
        Submodule.mem_top)).toAddMonoidHom.toZModLinearMap p,
    fun g => LinearMap.ext fun x => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (f.hom (A.ρ g a)) = Submodule.Quotient.mk (B.ρ g (f.hom a))
      rw [Rep.hom_comm_apply]⟩

@[simp] theorem repModPMap_hom_mk (p : ℕ) {A B : Rep.{w} k G} (f : A ⟶ B) (a : A) :
    (repModPMap p f).hom (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f.hom a) := rfl

def repTorsionPMap (p : ℕ) {A B : Rep.{w} k G} (f : A ⟶ B) : repTorsionP p A ⟶ repTorsionP p B :=
  Rep.ofHom ⟨(f.hom.toLinearMap.restrict (p := Submodule.torsionBy k A (p : k)) (q :=
    Submodule.torsionBy k B (p : k)) (fun x hx => by
      rw [Submodule.mem_torsionBy_iff] at hx ⊢
      rw [← map_smul, hx, map_zero])).toAddMonoidHom.toZModLinearMap p,
    fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply f g (x : A))⟩

@[simp] theorem repTorsionPMap_hom_apply_coe (p : ℕ) {A B : Rep.{w} k G} (f : A ⟶ B) (a :
  ↥(Submodule.torsionBy k A (p : k))) :
    (((repTorsionPMap p f).hom a : ↥(Submodule.torsionBy k B (p : k))) : B) = f.hom a := rfl

@[simp] theorem repModPMap_id (p : ℕ) (A : Rep.{w} k G) :
    repModPMap p (𝟙 A) = 𝟙 (repModP p A) := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

@[simp] theorem repModPMap_comp (p : ℕ) {A B C : Rep.{w} k G} (f : A ⟶ B) (g : B ⟶ C) :
    repModPMap p (f ≫ g) = repModPMap p f ≫ repModPMap p g := by
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

@[simp] theorem repTorsionPMap_id (p : ℕ) (A : Rep.{w} k G) :
    repTorsionPMap p (𝟙 A) = 𝟙 (repTorsionP p A) :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

@[simp] theorem repTorsionPMap_comp (p : ℕ) {A B C : Rep.{w} k G} (f : A ⟶ B) (g : B ⟶ C) :
    repTorsionPMap p (f ≫ g) = repTorsionPMap p f ≫ repTorsionPMap p g :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

-- Reduction modulo `p` as a functor; its object and morphism maps are `repModP` and
-- `repModPMap`.
abbrev modPFunctor (p : ℕ) : Rep.{w} k G ⥤ Rep.{w} (ZMod p) G where
  obj := repModP p
  map := repModPMap p
  map_id := repModPMap_id p
  map_comp := repModPMap_comp p

-- The `p`-torsion as a functor; its object and morphism maps are `repTorsionP` and
-- `repTorsionPMap`.
abbrev torsionPFunctor (p : ℕ) : Rep.{w} k G ⥤ Rep.{w} (ZMod p) G where
  obj := repTorsionP p
  map := repTorsionPMap p
  map_id := repTorsionPMap_id p
  map_comp := repTorsionPMap_comp p

end Rep

namespace Representation

open CategoryTheory

open scoped Pointwise



set_option autoImplicit false



section Compl

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]



omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_compl_addSubgroup [Finite G] [NeZero ((Nat.card G : ℕ) : ZMod p)]
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (τ : Representation (ZMod p) G M) (W : AddSubgroup M) (hW : ∀ g, ∀ x ∈ W, τ g x ∈ W) :
    ∃ W' : AddSubgroup M, (∀ g, ∀ x ∈ W', τ g x ∈ W') ∧ (∀ x, x ∈ W → x ∈ W' → x = 0) ∧ (∀ x, ∃ y
      ∈ W, ∃ z ∈ W', x = y + z) := by
  let Wsub : Subrepresentation τ :=
    ⟨(AddSubgroup.toZModSubmodule p) W, fun g v hv => hW g v hv⟩
  have hex : ∃ q : Subrepresentation τ, IsCompl Wsub q := by
    obtain ⟨q, hq⟩ := exists_isCompl
      (Subrepresentation.subrepresentationSubmoduleOrderIso Wsub)
    exact ⟨Subrepresentation.subrepresentationSubmoduleOrderIso.symm q,
      (Subrepresentation.subrepresentationSubmoduleOrderIso.isCompl_iff).2 hq⟩
  obtain ⟨Wc, hWc⟩ := hex
  refine ⟨Wc.toSubmodule.toAddSubgroup, fun g x hx => Wc.apply_mem_toSubmodule g hx, fun x hxW
    hxW' => ?_, fun x => ?_⟩
  · have hx : x ∈ (⟨(AddSubgroup.toZModSubmodule p) W, fun g v hv => hW g v hv⟩ :
    Subrepresentation τ) ⊓ Wc := ⟨hxW, hxW'⟩
    rw [hWc.inf_eq_bot] at hx
    exact hx
  · have hx : x ∈ (⟨(AddSubgroup.toZModSubmodule p) W, fun g v hv => hW g v hv⟩ :
    Subrepresentation τ) ⊔ Wc := by
      rw [hWc.sup_eq_top]; trivial
    rw [← SetLike.mem_coe, Subrepresentation.coe_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    exact ⟨y, hy, z, hz, rfl⟩

private noncomputable def toZMod (p : ℕ) {M : Type*} [AddCommGroup M] [Module (ZMod p) M] {inst :
  Module ℤ M} (σ : @Representation ℤ G M _ _ _ inst) :
    Representation (ZMod p) G M where
  toFun g := (σ g).toAddMonoidHom.toZModLinearMap p
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Finite G] [Fact p.Prime] in
private theorem toZMod_apply (p : ℕ) {M : Type*} [AddCommGroup M] [Module (ZMod p) M] {inst :
  Module ℤ M} (σ : @Representation ℤ G M _ _ _ inst)
    (g : G) (m : M) : toZMod p σ g m = σ g m := rfl

private theorem exists_isCompl_of_coprime (hG : (Nat.card G).Coprime p) {M : Type*} [AddCommGroup
  M] {inst : Module ℤ M}
    (σ : @Representation ℤ G M _ _ _ inst) (hM : ∀ m : M, p • m = 0)
    (W : @Submodule ℤ M _ _ inst) (hW : ∀ g, W ≤ W.comap (σ g)) :
    ∃ W' : @Submodule ℤ M _ _ inst, (∀ g, W' ≤ W'.comap (σ g)) ∧ IsCompl W W' := by
  haveI : NeZero ((Nat.card G : ℕ) : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => (Nat.Prime.coprime_iff_not_dvd (Fact.out)).1 (Nat.Coprime.symm hG) h⟩
  obtain ⟨W', h1, h2, h3⟩ := @exists_compl_addSubgroup G _ p _ _ _ M _ (AddCommGroup.zmodModule hM)
    (@toZMod G _ p M _ (AddCommGroup.zmodModule hM) inst σ) W.toAddSubgroup (fun g x hx => hW g hx)
  refine ⟨{ carrier := W', add_mem' := fun ha hb => W'.add_mem ha hb, zero_mem' := W'.zero_mem,
            smul_mem' := fun c x hx => by
              change inst.smul c x ∈ W'
              rw [int_smul_eq_zsmul]
              exact W'.zsmul_mem hx c }, fun g x hx => h1 g x hx, ?_⟩
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot ℤ).2 (h2 x hx.1 hx.2)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨y, hy, z, hz, rfl⟩ := h3 x
    exact Submodule.add_mem_sup hy hz

end Compl



section Generic

variable {k G : Type*} [CommRing k] [Group G]

private noncomputable def equivOfSubsingleton {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] {iV
  : Module k V} {iV' : Module k V'}
    (ρ : Representation k G V) (ρ' : Representation k G V') [Subsingleton V] [Subsingleton V'] :
      ρ.Equiv ρ' :=
  Representation.Equiv.mk
    { toFun := 0, invFun := 0, map_add' := fun _ _ => Subsingleton.elim _ _, map_smul' := fun _ _
      => Subsingleton.elim _ _,
      left_inv := fun _ => Subsingleton.elim _ _, right_inv := fun _ => Subsingleton.elim _ _ }
    (fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _)

private theorem nonempty_equiv_of_isCompl {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] {iV :
  Module k V} {iV' : Module k V'}
    (ρ : Representation k G V) (ρ' : Representation k G V')
    (W₁ W₂ : Submodule k V) (h₁ : ∀ g, W₁ ≤ W₁.comap (ρ g)) (h₂ : ∀ g, W₂ ≤ W₂.comap (ρ g)) (hc :
      IsCompl W₁ W₂)
    (W₁' W₂' : Submodule k V') (h₁' : ∀ g, W₁' ≤ W₁'.comap (ρ' g)) (h₂' : ∀ g, W₂' ≤ W₂'.comap (ρ'
      g)) (hc' : IsCompl W₁' W₂')
    (e₁ : (ρ.subrepresentation W₁ h₁).Equiv (ρ'.subrepresentation W₁' h₁'))
    (e₂ : (ρ.subrepresentation W₂ h₂).Equiv (ρ'.subrepresentation W₂' h₂')) :
    Nonempty (ρ.Equiv ρ') := by
  let E : V ≃ₗ[k] V' :=
    (Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm ≪≫ₗ (e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv)
      ≪≫ₗ
      Submodule.prodEquivOfIsCompl W₁' W₂' hc'
  have hE : ∀ (a : W₁) (b : W₂), E ((a : V) + (b : V)) = (e₁ a : V') + (e₂ b : V') := fun a b => by
    have : (a : V) + (b : V) = Submodule.prodEquivOfIsCompl W₁ W₂ hc (a, b) :=
      (Submodule.coe_prodEquivOfIsCompl' _ _ hc (a, b)).symm
    rw [this]
    change Submodule.prodEquivOfIsCompl W₁' W₂' hc' ((e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv)
      ((Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm (Submodule.prodEquivOfIsCompl W₁ W₂ hc (a,
        b)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl']
    rfl
  refine ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun v => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W₁ W₂ hc).surjective v
  rw [Submodule.coe_prodEquivOfIsCompl']
  change E (ρ g ((a : V) + (b : V))) = ρ' g (E ((a : V) + (b : V)))
  have ha : ρ g (a : V) = ((ρ.subrepresentation W₁ h₁ g a : W₁) : V) := rfl
  have hb : ρ g (b : V) = ((ρ.subrepresentation W₂ h₂ g b : W₂) : V) := rfl
  rw [map_add, ha, hb, hE, hE, map_add]
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e₁.toIntertwiningMap g a
  have h2 := Representation.IntertwiningMap.isIntertwining _ _ e₂.toIntertwiningMap g b
  simp only [Representation.Equiv.coe_toIntertwiningMap] at h1 h2
  rw [h1, h2]
  rfl

private theorem nonempty_equiv_range_of_isCompl_ker {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {iM : Module k M} {iN : Module k N}
    (ρ : Representation k G M) (σ : Representation k G N) (φ : M →ₗ[k] N) (hφ : ∀ g (m : M), φ (ρ
      g m) = σ g (φ m))
    (C : Submodule k M) (hC : ∀ g, C ≤ C.comap (ρ g)) (hc : IsCompl (LinearMap.ker φ) C)
    (hR : ∀ g, LinearMap.range φ ≤ (LinearMap.range φ).comap (σ g)) :
    Nonempty ((ρ.subrepresentation C hC).Equiv (σ.subrepresentation (LinearMap.range φ) hR)) := by
  let ψ : C →ₗ[k] LinearMap.range φ := (φ ∘ₗ C.subtype).codRestrict _ (fun c => ⟨c, rfl⟩)
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h : φ (x : M) = φ (y : M) := congrArg Subtype.val hxy
    have hk : (x : M) - (y : M) ∈ LinearMap.ker φ := by rw [LinearMap.mem_ker, map_sub, h, sub_self]
    have hC' : (x : M) - (y : M) ∈ C := C.sub_mem x.2 y.2
    have hmem : (x : M) - (y : M) ∈ LinearMap.ker φ ⊓ C := ⟨hk, hC'⟩
    rw [hc.inf_eq_bot] at hmem
    have h0 : (x : M) - (y : M) = 0 := (Submodule.mem_bot k).1 hmem
    exact Subtype.ext (sub_eq_zero.1 h0)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨_, m, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ hc).surjective m
    refine ⟨b, Subtype.ext ?_⟩
    change φ (b : M) = φ (Submodule.prodEquivOfIsCompl _ _ hc (a, b))
    rw [Submodule.coe_prodEquivOfIsCompl', map_add, LinearMap.mem_ker.1 a.2, zero_add]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩) fun g => LinearMap.ext
    fun c => Subtype.ext ?_⟩
  exact hφ g (c : M)

private theorem nonempty_equiv_of_isCompl_ker_of_surjective {M N : Type*} [AddCommGroup M]
  [AddCommGroup N] {iM : Module k M} {iN : Module k N}
    (ρ : Representation k G M) (σ : Representation k G N) (φ : M →ₗ[k] N) (hφ : ∀ g (m : M), φ (ρ
      g m) = σ g (φ m))
    (C : Submodule k M) (hC : ∀ g, C ≤ C.comap (ρ g)) (hc : IsCompl (LinearMap.ker φ) C) (hs :
      Function.Surjective φ) :
    Nonempty ((ρ.subrepresentation C hC).Equiv σ) := by
  let ψ : C →ₗ[k] N := φ ∘ₗ C.subtype
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h : φ (x : M) = φ (y : M) := hxy
    have hk : (x : M) - (y : M) ∈ LinearMap.ker φ := by rw [LinearMap.mem_ker, map_sub, h, sub_self]
    have hC' : (x : M) - (y : M) ∈ C := C.sub_mem x.2 y.2
    have hmem : (x : M) - (y : M) ∈ LinearMap.ker φ ⊓ C := ⟨hk, hC'⟩
    rw [hc.inf_eq_bot] at hmem
    have h0 : (x : M) - (y : M) = 0 := (Submodule.mem_bot k).1 hmem
    exact Subtype.ext (sub_eq_zero.1 h0)
  have hsurj : Function.Surjective ψ := by
    intro n
    obtain ⟨m, rfl⟩ := hs n
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ hc).surjective m
    refine ⟨b, ?_⟩
    change φ (b : M) = φ (Submodule.prodEquivOfIsCompl _ _ hc (a, b))
    rw [Submodule.coe_prodEquivOfIsCompl', map_add, LinearMap.mem_ker.1 a.2, zero_add]
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩) fun g => LinearMap.ext
    fun c => ?_⟩
  exact hφ g (c : M)

private theorem torsionBy_le_comap {M : Type*} [AddCommGroup M] {iM : Module k M} (ρ :
  Representation k G M) (a : k) (g : G) :
    Submodule.torsionBy k M a ≤ (Submodule.torsionBy k M a).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap, Submodule.mem_torsionBy_iff, ← map_smul]
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [hx, map_zero]


private theorem smul_top_le_comap {M : Type*} [AddCommGroup M] {iM : Module k M} (ρ :
  Representation k G M) (a : k) (g : G) :
    (a • (⊤ : Submodule k M)) ≤ (a • (⊤ : Submodule k M)).comap (ρ g) := fun x hx => by
  rw [Submodule.mem_comap]
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

end Generic



section Main


variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in

private theorem nonempty_equiv_e₁ {A : Type*} [AddCommGroup A] (ρ : Representation ℤ G A)
    (hT : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (hP : ∀ g, ((p : ℤ) • (⊤ : Submodule ℤ A)) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g))
    (hW₁ : ∀ g, ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (Submodule.torsionBy ℤ A (p : ℤ)).subtype ≤
      (((p : ℤ) • (⊤ : Submodule ℤ A)).comap (Submodule.torsionBy ℤ A (p : ℤ)).subtype).comap
        (ρ.subrepresentation _ hT g))
    (hTB : ∀ g, Submodule.torsionBy ℤ ↥((p : ℤ) • (⊤ : Submodule ℤ A)) (p : ℤ) ≤
      (Submodule.torsionBy ℤ ↥((p : ℤ) • (⊤ : Submodule ℤ A)) (p : ℤ)).comap (ρ.subrepresentation
        _ hP g)) :
    Nonempty (((ρ.subrepresentation _ hT).subrepresentation _ hW₁).Equiv ((ρ.subrepresentation _
      hP).subrepresentation _ hTB)) := by
  refine ⟨Representation.Equiv.mk
    { toFun := fun x => ⟨⟨((x : Submodule.torsionBy ℤ A (p : ℤ)) : A), x.2⟩, ?_⟩
      invFun := fun y => ⟨⟨((y : ↥((p : ℤ) • (⊤ : Submodule ℤ A))) : A), ?_⟩, y.1.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } fun g => LinearMap.ext fun _ => rfl⟩
  · rw [Submodule.mem_torsionBy_iff]
    apply Subtype.ext
    have hx := (Submodule.mem_torsionBy_iff _ _).1 (x : Submodule.torsionBy ℤ A (p : ℤ)).2
    exact hx
  · rw [Submodule.mem_torsionBy_iff]
    have hy := congrArg Subtype.val ((Submodule.mem_torsionBy_iff _ _).1 y.2)
    exact hy

private noncomputable def mulp (p : ℕ) (A : Type*) [AddCommGroup A] : A →ₗ[ℤ] ↥((p : ℤ) • (⊤ :
  Submodule ℤ A)) :=
  LinearMap.codRestrict _ ((p : ℤ) • LinearMap.id) (fun a => Submodule.smul_mem_pointwise_smul _ _
    _ Submodule.mem_top)

omit [Finite G] [Fact p.Prime] in
private theorem mulp_apply_coe {A : Type*} [AddCommGroup A] (a : A) : ((mulp p A a : ↥((p : ℤ) • (⊤
  : Submodule ℤ A))) : A) = (p : ℤ) • a := rfl

private theorem main (hG : (Nat.card G).Coprime p) (n : ℕ) : ∀ (A : Type*) [AddCommGroup A] [Finite
  A] (ρ : Representation ℤ G A)
    (h1 : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤ (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (h2 : ∀ g, ((p : ℤ) • (⊤ : Submodule ℤ A)) ≤ ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g)),
    Nat.card A = n → Nonempty ((ρ.subrepresentation _ h1).Equiv (ρ.quotient _ h2)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ ρ h1 h2 hn

  set T : Submodule ℤ A := Submodule.torsionBy ℤ A (p : ℤ) with hTdef
  set P : Submodule ℤ A := (p : ℤ) • (⊤ : Submodule ℤ A) with hPdef
  have hp0 : ∀ a : A, p • a ∈ P := fun a => by
    rw [← natCast_zsmul]; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  by_cases htop : P = ⊤
  ·
    have hsurj : Function.Surjective (fun a : A => (p : ℤ) • a) := fun b => by
      have hb : b ∈ P := htop ▸ Submodule.mem_top
      obtain ⟨a, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hb
      exact ⟨a, rfl⟩
    have hinj : Function.Injective (fun a : A => (p : ℤ) • a) := Finite.injective_iff_surjective.2
      hsurj
    haveI : Subsingleton T := ⟨fun x y => Subtype.ext (hinj (by
      have hx := (Submodule.mem_torsionBy_iff (p : ℤ) (x : A)).1 x.2
      have hy := (Submodule.mem_torsionBy_iff (p : ℤ) (y : A)).1 y.2
      change (p : ℤ) • (x : A) = (p : ℤ) • (y : A)
      rw [hx, hy]))⟩
    haveI : Subsingleton (A ⧸ P) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective P y
      rw [(Submodule.Quotient.mk_eq_zero P).2 (htop ▸ Submodule.mem_top),
        (Submodule.Quotient.mk_eq_zero P).2 (htop ▸ Submodule.mem_top)]⟩
    exact ⟨equivOfSubsingleton _ _⟩
  ·
    obtain ⟨a₀, ha₀⟩ : ∃ a : A, a ∉ P := by
      by_contra h
      exact htop (eq_top_iff.2 fun a _ => not_not.1 (not_exists.1 h a))
    have hlt : Nat.card ↥P < n := hn ▸ Finite.card_subtype_lt ha₀

    set ρB := ρ.subrepresentation P h2 with hρB
    have h1B := torsionBy_le_comap ρB (p : ℤ)
    have h2B := smul_top_le_comap ρB (p : ℤ)
    obtain ⟨eB⟩ := ih _ hlt ↥P ρB h1B h2B rfl

    set ρT := ρ.subrepresentation T h1 with hρT
    set ρV := ρ.quotient P h2 with hρV

    set W₁ : Submodule ℤ T := P.comap T.subtype with hW₁def
    have hW₁ : ∀ g, W₁ ≤ W₁.comap (ρT g) := fun g x hx => h2 g hx

    set f := P.mkQ ∘ₗ T.subtype with hfdef
    have hf : ∀ g (t : T), f (ρT g t) = ρV g (f t) := fun g t => rfl
    have hkerf : LinearMap.ker f = W₁ := Submodule.ext fun x => by
      rw [LinearMap.mem_ker]
      exact Submodule.Quotient.mk_eq_zero P
    have hK₀ : ∀ g, LinearMap.range f ≤ (LinearMap.range f).comap (ρV g) := by
      rintro g _ ⟨t, rfl⟩
      exact ⟨ρT g t, hf g t⟩

    have hTp : ∀ t : T, p • t = 0 := fun t => by
      rw [← natCast_zsmul]
      exact Subtype.ext ((Submodule.mem_torsionBy_iff (p : ℤ) (t : A)).1 t.2)
    have hVp : ∀ x : A ⧸ P, p • x = 0 := fun x => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
      rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hp0 a

    obtain ⟨C₁, hC₁, hcW⟩ := exists_isCompl_of_coprime hG ρT hTp W₁ hW₁
    obtain ⟨C₂, hC₂, hcK⟩ := exists_isCompl_of_coprime hG ρV hVp (LinearMap.range f) hK₀

    obtain ⟨e₂⟩ := nonempty_equiv_range_of_isCompl_ker ρT ρV f hf C₁ hC₁ (hkerf ▸ hcW) hK₀

    set PB : Submodule ℤ ↥P := (p : ℤ) • (⊤ : Submodule ℤ ↥P) with hPBdef
    have hmulP : P ≤ PB.comap (mulp p A) := fun a ha => by
      rw [Submodule.mem_comap]
      have : mulp p A a = (p : ℤ) • (⟨a, ha⟩ : ↥P) := Subtype.ext rfl
      rw [this]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    set gq := P.mapQ PB (mulp p A) hmulP with hgqdef
    have hmulρ : ∀ g (a : A), mulp p A (ρ g a) = ρB g (mulp p A a) := fun g a =>
      Subtype.ext (by change (p : ℤ) • ρ g a = ρ g ((p : ℤ) • a); rw [map_smul])
    have hgq : ∀ g (x : A ⧸ P), gq (ρV g x) = (ρB.quotient PB h2B) g (gq x) := fun g x => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
      change gq (Submodule.Quotient.mk (ρ g a)) = (ρB.quotient PB h2B) g (Submodule.Quotient.mk
        (mulp p A a))
      change Submodule.Quotient.mk (mulp p A (ρ g a)) = Submodule.Quotient.mk (ρB g (mulp p A a))
      rw [hmulρ]
    have hgs : Function.Surjective gq := fun y => by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective PB y
      obtain ⟨a, -, ha⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 b.2
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (mulp p A a) = Submodule.Quotient.mk b
      congr 1
      exact Subtype.ext ha
    have hkerg : LinearMap.ker gq = LinearMap.range f := by
      apply le_antisymm
      · intro x hx
        obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P x
        have hx' : Submodule.Quotient.mk (p := PB) (mulp p A a) = 0 := hx
        rw [Submodule.Quotient.mk_eq_zero] at hx'
        obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx'
        have hb' : (p : ℤ) • (b : A) = (p : ℤ) • a := congrArg Subtype.val hb
        have hab : a - b ∈ T := by
          rw [Submodule.mem_torsionBy_iff, smul_sub, hb', sub_self]
        refine ⟨⟨a - b, hab⟩, ?_⟩
        change Submodule.Quotient.mk (p := P) (a - (b : A)) = Submodule.Quotient.mk a
        rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero P).2 b.2, sub_zero]
      · rintro _ ⟨t, rfl⟩
        change Submodule.Quotient.mk (p := PB) (mulp p A (t : A)) = 0
        have : mulp p A (t : A) = 0 := Subtype.ext ((Submodule.mem_torsionBy_iff (p : ℤ) (t :
          A)).1 t.2)
        rw [this, Submodule.Quotient.mk_zero]

    obtain ⟨e₃⟩ := nonempty_equiv_of_isCompl_ker_of_surjective ρV (ρB.quotient PB h2B) gq hgq C₂
      hC₂ (hkerg ▸ hcK) hgs

    have hTB : ∀ g, Submodule.torsionBy ℤ ↥P (p : ℤ) ≤ (Submodule.torsionBy ℤ ↥P (p : ℤ)).comap
      (ρB g) := h1B
    obtain ⟨e₁⟩ := nonempty_equiv_e₁ ρ h1 h2 hW₁ hTB

    exact nonempty_equiv_of_isCompl ρT ρV W₁ C₁ hW₁ hC₁ hcW C₂ (LinearMap.range f) hC₂ hK₀ hcK.symm
      (e₁.trans (eB.trans e₃.symm)) e₂

end Main

/-- The `p`-torsion subrepresentation of a finite integral representation
of a finite group of order coprime to `p` is equivalent to its quotient
by the image of multiplication by `p`. -/
theorem nonempty_equiv_torsionBy_quotient_of_coprime {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hG : (Nat.card G).Coprime p) {A : Type*} [AddCommGroup A]
    [Finite A] (ρ : Representation ℤ G A)
    (h1 : ∀ g, Submodule.torsionBy ℤ A (p : ℤ) ≤
      (Submodule.torsionBy ℤ A (p : ℤ)).comap (ρ g))
    (h2 : ∀ g, (p : ℤ) • (⊤ : Submodule ℤ A) ≤
      ((p : ℤ) • (⊤ : Submodule ℤ A)).comap (ρ g)) :
    Nonempty ((ρ.subrepresentation _ h1).Equiv (ρ.quotient _ h2)) :=
  main hG _ A ρ h1 h2 rfl

end Representation

namespace Rep

open CategoryTheory

attribute [local instance] zmodModuleQuot zmodModuleTorsion

set_option maxHeartbeats 800000 in
/-- For a finite integral representation of a finite group whose order is
coprime to `p`, the `p`-torsion subrepresentation is isomorphic to the
mod-`p` reduction. The isomorphism comes from comparing both sides with a
common complement: Maschke semisimplicity over `ZMod p` supplies invariant
complements of the `p`-multiplication kernel and image, and induction on
the cardinality of the carrier identifies the remaining pieces. -/
theorem nonempty_repTorsionP_iso_repModP {G : Type v} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hG : (Nat.card G).Coprime p) (A : Rep.{w} ℤ G) [Finite A] :
    Nonempty (repTorsionP p A ≅ repModP p A) := by
  obtain @⟨V, hV1, hV2, ρ⟩ := A
  obtain rfl : hV2 = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  obtain ⟨e⟩ := Representation.nonempty_equiv_torsionBy_quotient_of_coprime hG ρ
    (Representation.torsionBy_le_comap ρ (p : ℤ)) (Representation.smul_top_le_comap ρ (p : ℤ))
  refine ⟨Rep.mkIso (Representation.Equiv.mk
    (e.toLinearEquiv.toAddEquiv.toLinearEquiv fun c x => ZMod.map_smul e.toLinearEquiv c x)
    fun g => LinearMap.ext fun x => ?_)⟩
  exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x

end Rep
